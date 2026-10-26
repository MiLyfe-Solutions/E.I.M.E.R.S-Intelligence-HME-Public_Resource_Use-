import V185TrunkScan23Chunk0838

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4965327 : List Nat := [1, 1, 2, 1, 1, 6, 3, 1, 3, 2, 2]
def baseStart_4965327 : Nat := 118140960795 + 4965327 * 2 ^ 59
def prefixEnd_4965327 : Nat := 4983230072969 + 3 ^ 40 * 4965327 * 2
def baseEnd_4965327 : Nat := 2549599357747199868977383

theorem tailTrace_4965327 : CollatzResearch.WordTrace tailWord_4965327 prefixEnd_4965327 2549599357747199868977383 := by
  unfold tailWord_4965327
  simp only [CollatzResearch.WordTrace]
  refine ⟨181100353682475764183158235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120733569121650509455438823 181100353682475764183158235)
  ·
    refine ⟨271650530523713646274737353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181100353682475764183158235 271650530523713646274737353)
    ·
      refine ⟨203737897892785234706053015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271650530523713646274737353 203737897892785234706053015)
      ·
        refine ⟨305606846839177852059079523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203737897892785234706053015 305606846839177852059079523)
        ·
          refine ⟨458410270258766778088619285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305606846839177852059079523 458410270258766778088619285)
          ·
            refine ⟨21487981418379692722904029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 458410270258766778088619285 21487981418379692722904029)
            ·
              refine ⟨8057993031892384771089011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21487981418379692722904029 8057993031892384771089011)
              ·
                refine ⟨12086989547838577156633517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8057993031892384771089011 12086989547838577156633517)
                ·
                  refine ⟨4532621080439466433737569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12086989547838577156633517 4532621080439466433737569)
                  ·
                    refine ⟨3399465810329599825303177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4532621080439466433737569 3399465810329599825303177)
                    ·
                      refine ⟨2549599357747199868977383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399465810329599825303177 2549599357747199868977383)
                      ·
                        rfl

theorem cell23_4965327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 1, 3, 2, 2].length) (baseStart_4965327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965327 prefixEnd_4965327 := by exact prefixLift 4965327
  have htrace : WordTrace (prefixWord ++ tailWord_4965327) baseStart_4965327 baseEnd_4965327 := by
    simpa [prefixWord, tailWord_4965327, baseEnd_4965327] using wordTrace_append hprefix tailTrace_4965327
  have hstable : (prefixWord ++ tailWord_4965327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965327).length < 2 ^ (prefixWord ++ tailWord_4965327).sum := by decide
  have hdescent : baseEnd_4965327 < baseStart_4965327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965330 : List Nat := [3, 2, 2, 3, 1, 1, 2, 2, 1, 1, 5]
def baseStart_4965330 : Nat := 118140960795 + 4965330 * 2 ^ 59
def prefixEnd_4965330 : Nat := 4983230072969 + 3 ^ 40 * 4965330 * 2
def baseEnd_4965330 : Nat := 2549600898189163357239869

theorem tailTrace_4965330 : CollatzResearch.WordTrace tailWord_4965330 prefixEnd_4965330 2549600898189163357239869 := by
  unfold tailWord_4965330
  simp only [CollatzResearch.WordTrace]
  refine ⟨45275115775366223923879361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120733642067643263797011629 45275115775366223923879361)
  ·
    refine ⟨33956336831524667942909521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45275115775366223923879361 33956336831524667942909521)
    ·
      refine ⟨25467252623643500957182141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33956336831524667942909521 25467252623643500957182141)
      ·
        refine ⟨9550219733866312858943303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25467252623643500957182141 9550219733866312858943303)
        ·
          refine ⟨14325329600799469288414955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9550219733866312858943303 14325329600799469288414955)
          ·
            refine ⟨21487994401199203932622433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14325329600799469288414955 21487994401199203932622433)
            ·
              refine ⟨16115995800899402949466825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21487994401199203932622433 16115995800899402949466825)
              ·
                refine ⟨12086996850674552212100119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16115995800899402949466825 12086996850674552212100119)
                ·
                  refine ⟨18130495276011828318150179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12086996850674552212100119 18130495276011828318150179)
                  ·
                    refine ⟨27195742914017742477225269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18130495276011828318150179 27195742914017742477225269)
                    ·
                      refine ⟨2549600898189163357239869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27195742914017742477225269 2549600898189163357239869)
                      ·
                        rfl

theorem cell23_4965330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_4965330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965330 prefixEnd_4965330 := by exact prefixLift 4965330
  have htrace : WordTrace (prefixWord ++ tailWord_4965330) baseStart_4965330 baseEnd_4965330 := by
    simpa [prefixWord, tailWord_4965330, baseEnd_4965330] using wordTrace_append hprefix tailTrace_4965330
  have hstable : (prefixWord ++ tailWord_4965330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965330).length < 2 ^ (prefixWord ++ tailWord_4965330).sum := by decide
  have hdescent : baseEnd_4965330 < baseStart_4965330 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965337 : List Nat := [1, 2, 1, 2, 5, 1, 4, 1, 2, 4]
def baseStart_4965337 : Nat := 118140960795 + 4965337 * 2 ^ 59
def prefixEnd_4965337 : Nat := 4983230072969 + 3 ^ 40 * 4965337 * 2
def baseEnd_4965337 : Nat := 849868164184581609950779

theorem tailTrace_4965337 : CollatzResearch.WordTrace tailWord_4965337 prefixEnd_4965337 849868164184581609950779 := by
  unfold tailWord_4965337
  simp only [CollatzResearch.WordTrace]
  refine ⟨181100718412439535891022265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120733812274959690594014843 181100718412439535891022265)
  ·
    refine ⟨135825538809329651918266699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181100718412439535891022265 135825538809329651918266699)
    ·
      refine ⟨203738308213994477877400049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135825538809329651918266699 203738308213994477877400049)
      ·
        refine ⟨152803731160495858408050037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203738308213994477877400049 152803731160495858408050037)
        ·
          refine ⟨14325349796296486725754691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152803731160495858408050037 14325349796296486725754691)
          ·
            refine ⟨21488024694444730088632037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14325349796296486725754691 21488024694444730088632037)
            ·
              refine ⟨4029004630208386891618507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21488024694444730088632037 4029004630208386891618507)
              ·
                refine ⟨6043506945312580337427761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029004630208386891618507 6043506945312580337427761)
                ·
                  refine ⟨4532630208984435253070821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6043506945312580337427761 4532630208984435253070821)
                  ·
                    refine ⟨849868164184581609950779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4532630208984435253070821 849868164184581609950779)
                    ·
                      rfl

theorem cell23_4965337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 4, 1, 2, 4].length) (baseStart_4965337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965337 prefixEnd_4965337 := by exact prefixLift 4965337
  have htrace : WordTrace (prefixWord ++ tailWord_4965337) baseStart_4965337 baseEnd_4965337 := by
    simpa [prefixWord, tailWord_4965337, baseEnd_4965337] using wordTrace_append hprefix tailTrace_4965337
  have hstable : (prefixWord ++ tailWord_4965337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965337).length < 2 ^ (prefixWord ++ tailWord_4965337).sum := by decide
  have hdescent : baseEnd_4965337 < baseStart_4965337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965377 : List Nat := [1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 3]
def baseStart_4965377 : Nat := 118140960795 + 4965377 * 2 ^ 59
def prefixEnd_4965377 : Nat := 4983230072969 + 3 ^ 40 * 4965377 * 2
def baseEnd_4965377 : Nat := 2549625031779924673352153

theorem tailTrace_4965377 : CollatzResearch.WordTrace tailWord_4965377 prefixEnd_4965377 2549625031779924673352153 := by
  unfold tailWord_4965377
  simp only [CollatzResearch.WordTrace]
  refine ⟨181102177332294622722478385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120734784888196415148318923 181102177332294622722478385)
  ·
    refine ⟨135826632999220967041858789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181102177332294622722478385 135826632999220967041858789)
    ·
      refine ⟨25467493687353931320348523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135826632999220967041858789 25467493687353931320348523)
      ·
        refine ⟨38201240531030896980522785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25467493687353931320348523 38201240531030896980522785)
        ·
          refine ⟨28650930398273172735392089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38201240531030896980522785 28650930398273172735392089)
          ·
            refine ⟨21488197798704879551544067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28650930398273172735392089 21488197798704879551544067)
            ·
              refine ⟨32232296698057319327316101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21488197798704879551544067 32232296698057319327316101)
              ·
                refine ⟨6043555630885747373871769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32232296698057319327316101 6043555630885747373871769)
                ·
                  refine ⟨4532666723164310530403827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6043555630885747373871769 4532666723164310530403827)
                  ·
                    refine ⟨6799000084746465795605741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4532666723164310530403827 6799000084746465795605741)
                    ·
                      refine ⟨2549625031779924673352153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6799000084746465795605741 2549625031779924673352153)
                      ·
                        rfl

theorem cell23_4965377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_4965377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965377 prefixEnd_4965377 := by exact prefixLift 4965377
  have htrace : WordTrace (prefixWord ++ tailWord_4965377) baseStart_4965377 baseEnd_4965377 := by
    simpa [prefixWord, tailWord_4965377, baseEnd_4965377] using wordTrace_append hprefix tailTrace_4965377
  have hstable : (prefixWord ++ tailWord_4965377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965377).length < 2 ^ (prefixWord ++ tailWord_4965377).sum := by decide
  have hdescent : baseEnd_4965377 < baseStart_4965377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965383 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 4]
def baseStart_4965383 : Nat := 118140960795 + 4965383 * 2 ^ 59
def prefixEnd_4965383 : Nat := 4983230072969 + 3 ^ 40 * 4965383 * 2
def baseEnd_4965383 : Nat := 2549628112663851649877125

theorem tailTrace_4965383 : CollatzResearch.WordTrace tailWord_4965383 prefixEnd_4965383 2549628112663851649877125 := by
  unfold tailWord_4965383
  simp only [CollatzResearch.WordTrace]
  refine ⟨181102396170272885747196803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120734930780181923831464535 181102396170272885747196803)
  ·
    refine ⟨271653594255409328620795205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181102396170272885747196803 271653594255409328620795205)
    ·
      refine ⟨50935048922889249116399101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271653594255409328620795205 50935048922889249116399101)
      ·
        refine ⟨19100643346083468418649663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50935048922889249116399101 19100643346083468418649663)
        ·
          refine ⟨28650965019125202627974495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19100643346083468418649663 28650965019125202627974495)
          ·
            refine ⟨42976447528687803941961743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28650965019125202627974495 42976447528687803941961743)
            ·
              refine ⟨64464671293031705912942615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42976447528687803941961743 64464671293031705912942615)
              ·
                refine ⟨96697006939547558869413923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64464671293031705912942615 96697006939547558869413923)
                ·
                  refine ⟨145045510409321338304120885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96697006939547558869413923 145045510409321338304120885)
                  ·
                    refine ⟨13598016600873875466011333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 145045510409321338304120885 13598016600873875466011333)
                    ·
                      refine ⟨2549628112663851649877125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13598016600873875466011333 2549628112663851649877125)
                      ·
                        rfl

theorem cell23_4965383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_4965383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965383 prefixEnd_4965383 := by exact prefixLift 4965383
  have htrace : WordTrace (prefixWord ++ tailWord_4965383) baseStart_4965383 baseEnd_4965383 := by
    simpa [prefixWord, tailWord_4965383, baseEnd_4965383] using wordTrace_append hprefix tailTrace_4965383
  have hstable : (prefixWord ++ tailWord_4965383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965383).length < 2 ^ (prefixWord ++ tailWord_4965383).sum := by decide
  have hdescent : baseEnd_4965383 < baseStart_4965383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965413 : List Nat := [1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 4]
def baseStart_4965413 : Nat := 118140960795 + 4965413 * 2 ^ 59
def prefixEnd_4965413 : Nat := 4983230072969 + 3 ^ 40 * 4965413 * 2
def baseEnd_4965413 : Nat := 2549643517083486532501987

theorem tailTrace_4965413 : CollatzResearch.WordTrace tailWord_4965413 prefixEnd_4965413 2549643517083486532501987 := by
  unfold tailWord_4965413
  simp only [CollatzResearch.WordTrace]
  refine ⟨181103490360164200870788893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120735660240109467247192595 181103490360164200870788893)
  ·
    refine ⟨67913808885061575326545835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181103490360164200870788893 67913808885061575326545835)
    ·
      refine ⟨101870713327592362989818753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67913808885061575326545835 101870713327592362989818753)
      ·
        refine ⟨76403034995694272242364065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101870713327592362989818753 76403034995694272242364065)
        ·
          refine ⟨57302276246770704181773049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76403034995694272242364065 57302276246770704181773049)
          ·
            refine ⟨42976707185078028136329787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57302276246770704181773049 42976707185078028136329787)
            ·
              refine ⟨64465060777617042204494681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42976707185078028136329787 64465060777617042204494681)
              ·
                refine ⟨48348795583212781653371011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64465060777617042204494681 48348795583212781653371011)
                ·
                  refine ⟨72523193374819172480056517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48348795583212781653371011 72523193374819172480056517)
                  ·
                    refine ⟨13598098757778594840010597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 72523193374819172480056517 13598098757778594840010597)
                    ·
                      refine ⟨2549643517083486532501987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13598098757778594840010597 2549643517083486532501987)
                      ·
                        rfl

theorem cell23_4965413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 2, 1, 4, 4].length) (baseStart_4965413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965413 prefixEnd_4965413 := by exact prefixLift 4965413
  have htrace : WordTrace (prefixWord ++ tailWord_4965413) baseStart_4965413 baseEnd_4965413 := by
    simpa [prefixWord, tailWord_4965413, baseEnd_4965413] using wordTrace_append hprefix tailTrace_4965413
  have hstable : (prefixWord ++ tailWord_4965413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965413).length < 2 ^ (prefixWord ++ tailWord_4965413).sum := by decide
  have hdescent : baseEnd_4965413 < baseStart_4965413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965434 : List Nat := [3, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2]
def baseStart_4965434 : Nat := 118140960795 + 4965434 * 2 ^ 59
def prefixEnd_4965434 : Nat := 4983230072969 + 3 ^ 40 * 4965434 * 2
def baseEnd_4965434 : Nat := 2549654300177230950339391

theorem tailTrace_4965434 : CollatzResearch.WordTrace tailWord_4965434 prefixEnd_4965434 2549654300177230950339391 := by
  unfold tailWord_4965434
  simp only [CollatzResearch.WordTrace]
  refine ⟨45276064073272030364325839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120736170862058747638202237 45276064073272030364325839)
  ·
    refine ⟨67914096109908045546488759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45276064073272030364325839 67914096109908045546488759)
    ·
      refine ⟨101871144164862068319733139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67914096109908045546488759 101871144164862068319733139)
      ·
        refine ⟨152806716247293102479599709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101871144164862068319733139 152806716247293102479599709)
        ·
          refine ⟨57302518592734913429849891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152806716247293102479599709 57302518592734913429849891)
          ·
            refine ⟨85953777889102370144774837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57302518592734913429849891 85953777889102370144774837)
            ·
              refine ⟨8058166677103347201072641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85953777889102370144774837 8058166677103347201072641)
              ·
                refine ⟨6043625007827510400804481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8058166677103347201072641 6043625007827510400804481)
                ·
                  refine ⟨4532718755870632800603361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6043625007827510400804481 4532718755870632800603361)
                  ·
                    refine ⟨3399539066902974600452521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4532718755870632800603361 3399539066902974600452521)
                    ·
                      refine ⟨2549654300177230950339391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399539066902974600452521 2549654300177230950339391)
                      ·
                        rfl

theorem cell23_4965434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2].length) (baseStart_4965434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965434 prefixEnd_4965434 := by exact prefixLift 4965434
  have htrace : WordTrace (prefixWord ++ tailWord_4965434) baseStart_4965434 baseEnd_4965434 := by
    simpa [prefixWord, tailWord_4965434, baseEnd_4965434] using wordTrace_append hprefix tailTrace_4965434
  have hstable : (prefixWord ++ tailWord_4965434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965434).length < 2 ^ (prefixWord ++ tailWord_4965434).sum := by decide
  have hdescent : baseEnd_4965434 < baseStart_4965434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965440 : List Nat := [2, 1, 1, 2, 2, 3, 1, 6, 5]
def baseStart_4965440 : Nat := 118140960795 + 4965440 * 2 ^ 59
def prefixEnd_4965440 : Nat := 4983230072969 + 3 ^ 40 * 4965440 * 2
def baseEnd_4965440 : Nat := 283295264562350880762707

theorem tailTrace_4965440 : CollatzResearch.WordTrace tailWord_4965440 prefixEnd_4965440 283295264562350880762707 := by
  unfold tailWord_4965440
  simp only [CollatzResearch.WordTrace]
  refine ⟨90552237565533192241010887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120736316754044256321347849 90552237565533192241010887)
  ·
    refine ⟨135828356348299788361516331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90552237565533192241010887 135828356348299788361516331)
    ·
      refine ⟨203742534522449682542274497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135828356348299788361516331 203742534522449682542274497)
      ·
        refine ⟨152806900891837261906705873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203742534522449682542274497 152806900891837261906705873)
        ·
          refine ⟨114605175668877946430029405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152806900891837261906705873 114605175668877946430029405)
          ·
            refine ⟨42976940875829229911261027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114605175668877946430029405 42976940875829229911261027)
            ·
              refine ⟨64465411313743844866891541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42976940875829229911261027 64465411313743844866891541)
              ·
                refine ⟨3021816155331742728135541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64465411313743844866891541 3021816155331742728135541)
                ·
                  refine ⟨283295264562350880762707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021816155331742728135541 283295264562350880762707)
                  ·
                    rfl

theorem cell23_4965440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 6, 5].length) (baseStart_4965440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965440 prefixEnd_4965440 := by exact prefixLift 4965440
  have htrace : WordTrace (prefixWord ++ tailWord_4965440) baseStart_4965440 baseEnd_4965440 := by
    simpa [prefixWord, tailWord_4965440, baseEnd_4965440] using wordTrace_append hprefix tailTrace_4965440
  have hstable : (prefixWord ++ tailWord_4965440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965440).length < 2 ^ (prefixWord ++ tailWord_4965440).sum := by decide
  have hdescent : baseEnd_4965440 < baseStart_4965440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965450 : List Nat := [3, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3]
def baseStart_4965450 : Nat := 118140960795 + 4965450 * 2 ^ 59
def prefixEnd_4965450 : Nat := 4983230072969 + 3 ^ 40 * 4965450 * 2
def baseEnd_4965450 : Nat := 2549662515867702887739317

theorem tailTrace_4965450 : CollatzResearch.WordTrace tailWord_4965450 prefixEnd_4965450 2549662515867702887739317 := by
  unfold tailWord_4965450
  simp only [CollatzResearch.WordTrace]
  refine ⟨45276209965257539047471451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120736559907353437459923869 45276209965257539047471451)
  ·
    refine ⟨67914314947886308571207177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45276209965257539047471451 67914314947886308571207177)
    ·
      refine ⟨50935736210914731428405383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67914314947886308571207177 50935736210914731428405383)
      ·
        refine ⟨76403604316372097142608075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50935736210914731428405383 76403604316372097142608075)
        ·
          refine ⟨114605406474558145713912113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76403604316372097142608075 114605406474558145713912113)
          ·
            refine ⟨85954054855918609285434085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114605406474558145713912113 85954054855918609285434085)
            ·
              refine ⟨16116385285484739241018891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85954054855918609285434085 16116385285484739241018891)
              ·
                refine ⟨24174577928227108861528337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16116385285484739241018891 24174577928227108861528337)
                ·
                  refine ⟨18130933446170331646146253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24174577928227108861528337 18130933446170331646146253)
                  ·
                    refine ⟨6799100042313874367304845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18130933446170331646146253 6799100042313874367304845)
                    ·
                      refine ⟨2549662515867702887739317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6799100042313874367304845 2549662515867702887739317)
                      ·
                        rfl

theorem cell23_4965450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 4, 1, 2, 3, 3].length) (baseStart_4965450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965450 prefixEnd_4965450 := by exact prefixLift 4965450
  have htrace : WordTrace (prefixWord ++ tailWord_4965450) baseStart_4965450 baseEnd_4965450 := by
    simpa [prefixWord, tailWord_4965450, baseEnd_4965450] using wordTrace_append hprefix tailTrace_4965450
  have hstable : (prefixWord ++ tailWord_4965450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965450).length < 2 ^ (prefixWord ++ tailWord_4965450).sum := by decide
  have hdescent : baseEnd_4965450 < baseStart_4965450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965463 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 5]
def baseStart_4965463 : Nat := 118140960795 + 4965463 * 2 ^ 59
def prefixEnd_4965463 : Nat := 4983230072969 + 3 ^ 40 * 4965463 * 2
def baseEnd_4965463 : Nat := 2549669191116211336876757

theorem tailTrace_4965463 : CollatzResearch.WordTrace tailWord_4965463 prefixEnd_4965463 2549669191116211336876757 := by
  unfold tailWord_4965463
  simp only [CollatzResearch.WordTrace]
  refine ⟨181105314009983059410109043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120736876006655372940072695 181105314009983059410109043)
  ·
    refine ⟨271657971014974589115163565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181105314009983059410109043 271657971014974589115163565)
    ·
      refine ⟨101871739130615470918186337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271657971014974589115163565 101871739130615470918186337)
      ·
        refine ⟨76403804347961603188639753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101871739130615470918186337 76403804347961603188639753)
        ·
          refine ⟨57302853260971202391479815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76403804347961603188639753 57302853260971202391479815)
          ·
            refine ⟨85954279891456803587219723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57302853260971202391479815 85954279891456803587219723)
            ·
              refine ⟨128931419837185205380829585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85954279891456803587219723 128931419837185205380829585)
              ·
                refine ⟨96698564877888904035622189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128931419837185205380829585 96698564877888904035622189)
                ·
                  refine ⟨36261961829208339013358321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96698564877888904035622189 36261961829208339013358321)
                  ·
                    refine ⟨27196471371906254260018741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36261961829208339013358321 27196471371906254260018741)
                    ·
                      refine ⟨2549669191116211336876757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27196471371906254260018741 2549669191116211336876757)
                      ·
                        rfl

theorem cell23_4965463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 5].length) (baseStart_4965463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965463 prefixEnd_4965463 := by exact prefixLift 4965463
  have htrace : WordTrace (prefixWord ++ tailWord_4965463) baseStart_4965463 baseEnd_4965463 := by
    simpa [prefixWord, tailWord_4965463, baseEnd_4965463] using wordTrace_append hprefix tailTrace_4965463
  have hstable : (prefixWord ++ tailWord_4965463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965463).length < 2 ^ (prefixWord ++ tailWord_4965463).sum := by decide
  have hdescent : baseEnd_4965463 < baseStart_4965463 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965474 : List Nat := [3, 3, 2, 2, 1, 1, 3, 3, 5]
def baseStart_4965474 : Nat := 118140960795 + 4965474 * 2 ^ 59
def prefixEnd_4965474 : Nat := 4983230072969 + 3 ^ 40 * 4965474 * 2
def baseEnd_4965474 : Nat := 283297204378156754871023

theorem tailTrace_4965474 : CollatzResearch.WordTrace tailWord_4965474 prefixEnd_4965474 283297204378156754871023 := by
  unfold tailWord_4965474
  simp only [CollatzResearch.WordTrace]
  refine ⟨45276428803235802072189869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120737143475295472192506317 45276428803235802072189869)
  ·
    refine ⟨16978660801213425777071201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45276428803235802072189869 16978660801213425777071201)
    ·
      refine ⟨12733995600910069332803401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16978660801213425777071201 12733995600910069332803401)
      ·
        refine ⟨9550496700682551999602551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12733995600910069332803401 9550496700682551999602551)
        ·
          refine ⟨14325745051023827999403827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9550496700682551999602551 14325745051023827999403827)
          ·
            refine ⟨21488617576535741999105741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14325745051023827999403827 21488617576535741999105741)
            ·
              refine ⟨8058231591200903249664653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21488617576535741999105741 8058231591200903249664653)
              ·
                refine ⟨3021836846700338718624245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8058231591200903249664653 3021836846700338718624245)
                ·
                  refine ⟨283297204378156754871023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3021836846700338718624245 283297204378156754871023)
                  ·
                    rfl

theorem cell23_4965474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 3, 5].length) (baseStart_4965474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965474 prefixEnd_4965474 := by exact prefixLift 4965474
  have htrace : WordTrace (prefixWord ++ tailWord_4965474) baseStart_4965474 baseEnd_4965474 := by
    simpa [prefixWord, tailWord_4965474, baseEnd_4965474] using wordTrace_append hprefix tailTrace_4965474
  have hstable : (prefixWord ++ tailWord_4965474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965474).length < 2 ^ (prefixWord ++ tailWord_4965474).sum := by decide
  have hdescent : baseEnd_4965474 < baseStart_4965474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965527 : List Nat := [1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 3]
def baseStart_4965527 : Nat := 118140960795 + 4965527 * 2 ^ 59
def prefixEnd_4965527 : Nat := 4983230072969 + 3 ^ 40 * 4965527 * 2
def baseEnd_4965527 : Nat := 2549702053878099086476463

theorem tailTrace_4965527 : CollatzResearch.WordTrace tailWord_4965527 prefixEnd_4965527 2549702053878099086476463 := by
  unfold tailWord_4965527
  simp only [CollatzResearch.WordTrace]
  refine ⟨181107648281751198340438835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120738432187834132226959223 181107648281751198340438835)
  ·
    refine ⟨271661472422626797510658253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181107648281751198340438835 271661472422626797510658253)
    ·
      refine ⟨101873052158485049066496845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271661472422626797510658253 101873052158485049066496845)
      ·
        refine ⟨38202394559431893399936317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101873052158485049066496845 38202394559431893399936317)
        ·
          refine ⟨14325897959786960024976119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38202394559431893399936317 14325897959786960024976119)
          ·
            refine ⟨21488846939680440037464179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14325897959786960024976119 21488846939680440037464179)
            ·
              refine ⟨32233270409520660056196269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21488846939680440037464179 32233270409520660056196269)
              ·
                refine ⟨12087476403570247521073601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32233270409520660056196269 12087476403570247521073601)
                ·
                  refine ⟨9065607302677685640805201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12087476403570247521073601 9065607302677685640805201)
                  ·
                    refine ⟨6799205477008264230603901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9065607302677685640805201 6799205477008264230603901)
                    ·
                      refine ⟨2549702053878099086476463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6799205477008264230603901 2549702053878099086476463)
                      ·
                        rfl

theorem cell23_4965527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 3, 2, 2, 3].length) (baseStart_4965527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965527 prefixEnd_4965527 := by exact prefixLift 4965527
  have htrace : WordTrace (prefixWord ++ tailWord_4965527) baseStart_4965527 baseEnd_4965527 := by
    simpa [prefixWord, tailWord_4965527, baseEnd_4965527] using wordTrace_append hprefix tailTrace_4965527
  have hstable : (prefixWord ++ tailWord_4965527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965527).length < 2 ^ (prefixWord ++ tailWord_4965527).sum := by decide
  have hdescent : baseEnd_4965527 < baseStart_4965527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965558 : List Nat := [5, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2]
def baseStart_4965558 : Nat := 118140960795 + 4965558 * 2 ^ 59
def prefixEnd_4965558 : Nat := 4983230072969 + 3 ^ 40 * 4965558 * 2
def baseEnd_4965558 : Nat := 2549717971778388465188821

theorem tailTrace_4965558 : CollatzResearch.WordTrace tailWord_4965558 prefixEnd_4965558 2549717971778388465188821 := by
  unfold tailWord_4965558
  simp only [CollatzResearch.WordTrace]
  refine ⟨11319298684039930664676083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120739185963092593756544885 11319298684039930664676083)
  ·
    refine ⟨16978948026059895997014125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11319298684039930664676083 16978948026059895997014125)
    ·
      refine ⟨6367105509772460998880297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16978948026059895997014125 6367105509772460998880297)
      ·
        refine ⟨4775329132329345749160223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6367105509772460998880297 4775329132329345749160223)
        ·
          refine ⟨7162993698494018623740335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775329132329345749160223 7162993698494018623740335)
          ·
            refine ⟨10744490547741027935610503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7162993698494018623740335 10744490547741027935610503)
            ·
              refine ⟨16116735821611541903415755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10744490547741027935610503 16116735821611541903415755)
              ·
                refine ⟨24175103732417312855123633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16116735821611541903415755 24175103732417312855123633)
                ·
                  refine ⟨18131327799312984641342725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24175103732417312855123633 18131327799312984641342725)
                  ·
                    refine ⟨3399623962371184620251761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18131327799312984641342725 3399623962371184620251761)
                    ·
                      refine ⟨2549717971778388465188821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399623962371184620251761 2549717971778388465188821)
                      ·
                        rfl

theorem cell23_4965558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_4965558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965558 prefixEnd_4965558 := by exact prefixLift 4965558
  have htrace : WordTrace (prefixWord ++ tailWord_4965558) baseStart_4965558 baseEnd_4965558 := by
    simpa [prefixWord, tailWord_4965558, baseEnd_4965558] using wordTrace_append hprefix tailTrace_4965558
  have hstable : (prefixWord ++ tailWord_4965558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965558).length < 2 ^ (prefixWord ++ tailWord_4965558).sum := by decide
  have hdescent : baseEnd_4965558 < baseStart_4965558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965567 : List Nat := [1, 1, 2, 2, 2, 2, 2, 2, 4, 3, 2]
def baseStart_4965567 : Nat := 118140960795 + 4965567 * 2 ^ 59
def prefixEnd_4965567 : Nat := 4983230072969 + 3 ^ 40 * 4965567 * 2
def baseEnd_4965567 : Nat := 2549722593104278929976279

theorem tailTrace_4965567 : CollatzResearch.WordTrace tailWord_4965567 prefixEnd_4965567 2549722593104278929976279 := by
  unfold tailWord_4965567
  simp only [CollatzResearch.WordTrace]
  refine ⟨181109107201606285171894955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120739404801070856781263303 181109107201606285171894955)
  ·
    refine ⟨271663660802409427757842433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181109107201606285171894955 271663660802409427757842433)
    ·
      refine ⟨203747745601807070818381825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271663660802409427757842433 203747745601807070818381825)
      ·
        refine ⟨152810809201355303113786369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203747745601807070818381825 152810809201355303113786369)
        ·
          refine ⟨114608106901016477335339777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152810809201355303113786369 114608106901016477335339777)
          ·
            refine ⟨85956080175762358001504833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114608106901016477335339777 85956080175762358001504833)
            ·
              refine ⟨64467060131821768501128625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85956080175762358001504833 64467060131821768501128625)
              ·
                refine ⟨48350295098866326375846469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64467060131821768501128625 48350295098866326375846469)
                ·
                  refine ⟨9065680331037436195471213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48350295098866326375846469 9065680331037436195471213)
                  ·
                    refine ⟨3399630124139038573301705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9065680331037436195471213 3399630124139038573301705)
                    ·
                      refine ⟨2549722593104278929976279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399630124139038573301705 2549722593104278929976279)
                      ·
                        rfl

theorem cell23_4965567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_4965567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965567 prefixEnd_4965567 := by exact prefixLift 4965567
  have htrace : WordTrace (prefixWord ++ tailWord_4965567) baseStart_4965567 baseEnd_4965567 := by
    simpa [prefixWord, tailWord_4965567, baseEnd_4965567] using wordTrace_append hprefix tailTrace_4965567
  have hstable : (prefixWord ++ tailWord_4965567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965567).length < 2 ^ (prefixWord ++ tailWord_4965567).sum := by decide
  have hdescent : baseEnd_4965567 < baseStart_4965567 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965680 : List Nat := [2, 1, 1, 1, 2, 2, 4, 1, 1, 8]
def baseStart_4965680 : Nat := 118140960795 + 4965680 * 2 ^ 59
def prefixEnd_4965680 : Nat := 4983230072969 + 3 ^ 40 * 4965680 * 2
def baseEnd_4965680 : Nat := 849926872139412329287753

theorem tailTrace_4965680 : CollatzResearch.WordTrace tailWord_4965680 prefixEnd_4965680 849926872139412329287753 := by
  unfold tailWord_4965680
  simp only [CollatzResearch.WordTrace]
  refine ⟨90556614325098452735379247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120742152433464603647172329 90556614325098452735379247)
  ·
    refine ⟨135834921487647679103068871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90556614325098452735379247 135834921487647679103068871)
    ·
      refine ⟨203752382231471518654603307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135834921487647679103068871 203752382231471518654603307)
      ·
        refine ⟨305628573347207277981904961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203752382231471518654603307 305628573347207277981904961)
        ·
          refine ⟨229221430010405458486428721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305628573347207277981904961 229221430010405458486428721)
          ·
            refine ⟨171916072507804093864821541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229221430010405458486428721 171916072507804093864821541)
            ·
              refine ⟨32234263595213267599654039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171916072507804093864821541 32234263595213267599654039)
              ·
                refine ⟨48351395392819901399481059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32234263595213267599654039 48351395392819901399481059)
                ·
                  refine ⟨72527093089229852099221589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48351395392819901399481059 72527093089229852099221589)
                  ·
                    refine ⟨849926872139412329287753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72527093089229852099221589 849926872139412329287753)
                    ·
                      rfl

theorem cell23_4965680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 4, 1, 1, 8].length) (baseStart_4965680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965680 prefixEnd_4965680 := by exact prefixLift 4965680
  have htrace : WordTrace (prefixWord ++ tailWord_4965680) baseStart_4965680 baseEnd_4965680 := by
    simpa [prefixWord, tailWord_4965680, baseEnd_4965680] using wordTrace_append hprefix tailTrace_4965680
  have hstable : (prefixWord ++ tailWord_4965680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965680).length < 2 ^ (prefixWord ++ tailWord_4965680).sum := by decide
  have hdescent : baseEnd_4965680 < baseStart_4965680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965681 : List Nat := [1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 3]
def baseStart_4965681 : Nat := 118140960795 + 4965681 * 2 ^ 59
def prefixEnd_4965681 : Nat := 4983230072969 + 3 ^ 40 * 4965681 * 2
def baseEnd_4965681 : Nat := 2549781129898891483950755

theorem tailTrace_4965681 : CollatzResearch.WordTrace tailWord_4965681 prefixEnd_4965681 2549781129898891483950755 := by
  unfold tailWord_4965681
  simp only [CollatzResearch.WordTrace]
  refine ⟨181113265123193282641544897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120742176748795521761029931 181113265123193282641544897)
  ·
    refine ⟨135834948842394961981158673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181113265123193282641544897 135834948842394961981158673)
    ·
      refine ⟨101876211631796221485869005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135834948842394961981158673 101876211631796221485869005)
      ·
        refine ⟨38203579361923583057200877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101876211631796221485869005 38203579361923583057200877)
        ·
          refine ⟨14326342260721343646450329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38203579361923583057200877 14326342260721343646450329)
          ·
            refine ⟨10744756695541007734837747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14326342260721343646450329 10744756695541007734837747)
            ·
              refine ⟨16117135043311511602256621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10744756695541007734837747 16117135043311511602256621)
              ·
                refine ⟨6043925641241816850846233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16117135043311511602256621 6043925641241816850846233)
                ·
                  refine ⟨4532944230931362638134675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6043925641241816850846233 4532944230931362638134675)
                  ·
                    refine ⟨6799416346397043957202013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4532944230931362638134675 6799416346397043957202013)
                    ·
                      refine ⟨2549781129898891483950755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6799416346397043957202013 2549781129898891483950755)
                      ·
                        rfl

theorem cell23_4965681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 2, 1, 3, 2, 1, 3].length) (baseStart_4965681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965681 prefixEnd_4965681 := by exact prefixLift 4965681
  have htrace : WordTrace (prefixWord ++ tailWord_4965681) baseStart_4965681 baseEnd_4965681 := by
    simpa [prefixWord, tailWord_4965681, baseEnd_4965681] using wordTrace_append hprefix tailTrace_4965681
  have hstable : (prefixWord ++ tailWord_4965681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965681).length < 2 ^ (prefixWord ++ tailWord_4965681).sum := by decide
  have hdescent : baseEnd_4965681 < baseStart_4965681 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965702 : List Nat := [6, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_4965702 : Nat := 118140960795 + 4965702 * 2 ^ 59
def prefixEnd_4965702 : Nat := 4983230072969 + 3 ^ 40 * 4965702 * 2
def baseEnd_4965702 : Nat := 2549791912992635901788159

theorem tailTrace_4965702 : CollatzResearch.WordTrace tailWord_4965702 prefixEnd_4965702 2549791912992635901788159 := by
  unfold tailWord_4965702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5659813470503662600876855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120742687370744802152039573 5659813470503662600876855)
  ·
    refine ⟨8489720205755493901315283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5659813470503662600876855 8489720205755493901315283)
    ·
      refine ⟨12734580308633240851972925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8489720205755493901315283 12734580308633240851972925)
      ·
        refine ⟨4775467615737465319489847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12734580308633240851972925 4775467615737465319489847)
        ·
          refine ⟨7163201423606197979234771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775467615737465319489847 7163201423606197979234771)
          ·
            refine ⟨10744802135409296968852157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7163201423606197979234771 10744802135409296968852157)
            ·
              refine ⟨4029300800778486363319559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10744802135409296968852157 4029300800778486363319559)
              ·
                refine ⟨6043951201167729544979339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029300800778486363319559 6043951201167729544979339)
                ·
                  refine ⟨9065926801751594317469009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6043951201167729544979339 9065926801751594317469009)
                  ·
                    refine ⟨6799445101313695738101757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9065926801751594317469009 6799445101313695738101757)
                    ·
                      refine ⟨2549791912992635901788159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6799445101313695738101757 2549791912992635901788159)
                      ·
                        rfl

theorem cell23_4965702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_4965702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965702 prefixEnd_4965702 := by exact prefixLift 4965702
  have htrace : WordTrace (prefixWord ++ tailWord_4965702) baseStart_4965702 baseEnd_4965702 := by
    simpa [prefixWord, tailWord_4965702, baseEnd_4965702] using wordTrace_append hprefix tailTrace_4965702
  have hstable : (prefixWord ++ tailWord_4965702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965702).length < 2 ^ (prefixWord ++ tailWord_4965702).sum := by decide
  have hdescent : baseEnd_4965702 < baseStart_4965702 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965708 : List Nat := [2, 2, 1, 3, 2, 3, 3, 1, 1, 3, 2]
def baseStart_4965708 : Nat := 118140960795 + 4965708 * 2 ^ 59
def prefixEnd_4965708 : Nat := 4983230072969 + 3 ^ 40 * 4965708 * 2
def baseEnd_4965708 : Nat := 2549794993876562878313131

theorem tailTrace_4965708 : CollatzResearch.WordTrace tailWord_4965708 prefixEnd_4965708 2549794993876562878313131 := by
  unfold tailWord_4965708
  simp only [CollatzResearch.WordTrace]
  refine ⟨90557124947047733126388889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120742833262730310835185185 90557124947047733126388889)
  ·
    refine ⟨67917843710285799844791667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90557124947047733126388889 67917843710285799844791667)
    ·
      refine ⟨101876765565428699767187501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67917843710285799844791667 101876765565428699767187501)
      ·
        refine ⟨38203787087035762412695313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101876765565428699767187501 38203787087035762412695313)
        ·
          refine ⟨28652840315276821809521485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38203787087035762412695313 28652840315276821809521485)
          ·
            refine ⟨10744815118228808178570557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28652840315276821809521485 10744815118228808178570557)
            ·
              refine ⟨4029305669335803066963959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10744815118228808178570557 4029305669335803066963959)
              ·
                refine ⟨6043958504003704600445939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029305669335803066963959 6043958504003704600445939)
                ·
                  refine ⟨9065937756005556900668909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6043958504003704600445939 9065937756005556900668909)
                  ·
                    refine ⟨3399726658502083837750841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9065937756005556900668909 3399726658502083837750841)
                    ·
                      refine ⟨2549794993876562878313131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399726658502083837750841 2549794993876562878313131)
                      ·
                        rfl

theorem cell23_4965708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 3, 1, 1, 3, 2].length) (baseStart_4965708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965708 prefixEnd_4965708 := by exact prefixLift 4965708
  have htrace : WordTrace (prefixWord ++ tailWord_4965708) baseStart_4965708 baseEnd_4965708 := by
    simpa [prefixWord, tailWord_4965708, baseEnd_4965708] using wordTrace_append hprefix tailTrace_4965708
  have hstable : (prefixWord ++ tailWord_4965708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965708).length < 2 ^ (prefixWord ++ tailWord_4965708).sum := by decide
  have hdescent : baseEnd_4965708 < baseStart_4965708 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965721 : List Nat := [1, 2, 1, 2, 2, 2, 3, 4, 2, 2, 2]
def baseStart_4965721 : Nat := 118140960795 + 4965721 * 2 ^ 59
def prefixEnd_4965721 : Nat := 4983230072969 + 3 ^ 40 * 4965721 * 2
def baseEnd_4965721 : Nat := 2549801669125071327450571

theorem tailTrace_4965721 : CollatzResearch.WordTrace tailWord_4965721 prefixEnd_4965721 2549801669125071327450571 := by
  unfold tailWord_4965721
  simp only [CollatzResearch.WordTrace]
  refine ⟨181114724043048369473001017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120743149362032246315334011 181114724043048369473001017)
  ·
    refine ⟨135836043032286277104750763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181114724043048369473001017 135836043032286277104750763)
    ·
      refine ⟨203754064548429415657126145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135836043032286277104750763 203754064548429415657126145)
      ·
        refine ⟨152815548411322061742844609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203754064548429415657126145 152815548411322061742844609)
        ·
          refine ⟨114611661308491546307133457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152815548411322061742844609 114611661308491546307133457)
          ·
            refine ⟨85958745981368659730350093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114611661308491546307133457 85958745981368659730350093)
            ·
              refine ⟨32234529743013247398881285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85958745981368659730350093 32234529743013247398881285)
              ·
                refine ⟨6043974326814983887290241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32234529743013247398881285 6043974326814983887290241)
                ·
                  refine ⟨4532980745111237915467681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6043974326814983887290241 4532980745111237915467681)
                  ·
                    refine ⟨3399735558833428436600761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4532980745111237915467681 3399735558833428436600761)
                    ·
                      refine ⟨2549801669125071327450571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399735558833428436600761 2549801669125071327450571)
                      ·
                        rfl

theorem cell23_4965721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 4, 2, 2, 2].length) (baseStart_4965721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965721 prefixEnd_4965721 := by exact prefixLift 4965721
  have htrace : WordTrace (prefixWord ++ tailWord_4965721) baseStart_4965721 baseEnd_4965721 := by
    simpa [prefixWord, tailWord_4965721, baseEnd_4965721] using wordTrace_append hprefix tailTrace_4965721
  have hstable : (prefixWord ++ tailWord_4965721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965721).length < 2 ^ (prefixWord ++ tailWord_4965721).sum := by decide
  have hdescent : baseEnd_4965721 < baseStart_4965721 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965738 : List Nat := [3, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2]
def baseStart_4965738 : Nat := 118140960795 + 4965738 * 2 ^ 59
def prefixEnd_4965738 : Nat := 4983230072969 + 3 ^ 40 * 4965738 * 2
def baseEnd_4965738 : Nat := 2549810398296197760937993

theorem tailTrace_4965738 : CollatzResearch.WordTrace tailWord_4965738 prefixEnd_4965738 2549810398296197760937993 := by
  unfold tailWord_4965738
  simp only [CollatzResearch.WordTrace]
  refine ⟨45278836020996695344092467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120743562722657854250913245 45278836020996695344092467)
  ·
    refine ⟨67918254031495043016138701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45278836020996695344092467 67918254031495043016138701)
    ·
      refine ⟨25469345261810641131052013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67918254031495043016138701 25469345261810641131052013)
      ·
        refine ⟨9551004473178990424144505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25469345261810641131052013 9551004473178990424144505)
        ·
          refine ⟨7163253354884242818108379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9551004473178990424144505 7163253354884242818108379)
          ·
            refine ⟨10744880032326364227162569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7163253354884242818108379 10744880032326364227162569)
            ·
              refine ⟨8058660024244773170371927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10744880032326364227162569 8058660024244773170371927)
              ·
                refine ⟨12087990036367159755557891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8058660024244773170371927 12087990036367159755557891)
                ·
                  refine ⟨18131985054550739633336837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12087990036367159755557891 18131985054550739633336837)
                  ·
                    refine ⟨3399747197728263681250657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18131985054550739633336837 3399747197728263681250657)
                    ·
                      refine ⟨2549810398296197760937993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399747197728263681250657 2549810398296197760937993)
                      ·
                        rfl

theorem cell23_4965738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_4965738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965738 prefixEnd_4965738 := by exact prefixLift 4965738
  have htrace : WordTrace (prefixWord ++ tailWord_4965738) baseStart_4965738 baseEnd_4965738 := by
    simpa [prefixWord, tailWord_4965738, baseEnd_4965738] using wordTrace_append hprefix tailTrace_4965738
  have hstable : (prefixWord ++ tailWord_4965738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965738).length < 2 ^ (prefixWord ++ tailWord_4965738).sum := by decide
  have hdescent : baseEnd_4965738 < baseStart_4965738 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965757 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 1, 7]
def baseStart_4965757 : Nat := 118140960795 + 4965757 * 2 ^ 59
def prefixEnd_4965757 : Nat := 4983230072969 + 3 ^ 40 * 4965757 * 2
def baseEnd_4965757 : Nat := 849940051476211062200135

theorem tailTrace_4965757 : CollatzResearch.WordTrace tailWord_4965757 prefixEnd_4965757 849940051476211062200135 := by
  unfold tailWord_4965757
  simp only [CollatzResearch.WordTrace]
  refine ⟨181116037070917947621311525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120744024713945298414207683 181116037070917947621311525)
  ·
    refine ⟨33959256950797115178995911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181116037070917947621311525 33959256950797115178995911)
    ·
      refine ⟨50938885426195672768493867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33959256950797115178995911 50938885426195672768493867)
      ·
        refine ⟨76408328139293509152740801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50938885426195672768493867 76408328139293509152740801)
        ·
          refine ⟨57306246104470131864555601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76408328139293509152740801 57306246104470131864555601)
          ·
            refine ⟨42979684578352598898416701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57306246104470131864555601 42979684578352598898416701)
            ·
              refine ⟨16117381716882224586906263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42979684578352598898416701 16117381716882224586906263)
              ·
                refine ⟨24176072575323336880359395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16117381716882224586906263 24176072575323336880359395)
                ·
                  refine ⟨36264108862985005320539093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24176072575323336880359395 36264108862985005320539093)
                  ·
                    refine ⟨849940051476211062200135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36264108862985005320539093 849940051476211062200135)
                    ·
                      rfl

theorem cell23_4965757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 1, 7].length) (baseStart_4965757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965757 prefixEnd_4965757 := by exact prefixLift 4965757
  have htrace : WordTrace (prefixWord ++ tailWord_4965757) baseStart_4965757 baseEnd_4965757 := by
    simpa [prefixWord, tailWord_4965757, baseEnd_4965757] using wordTrace_append hprefix tailTrace_4965757
  have hstable : (prefixWord ++ tailWord_4965757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965757).length < 2 ^ (prefixWord ++ tailWord_4965757).sum := by decide
  have hdescent : baseEnd_4965757 < baseStart_4965757 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965794 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 1, 3, 4]
def baseStart_4965794 : Nat := 118140960795 + 4965794 * 2 ^ 59
def prefixEnd_4965794 : Nat := 4983230072969 + 3 ^ 40 * 4965794 * 2
def baseEnd_4965794 : Nat := 2549839153212849541837735

theorem tailTrace_4965794 : CollatzResearch.WordTrace tailWord_4965794 prefixEnd_4965794 2549839153212849541837735 := by
  unfold tailWord_4965794
  simp only [CollatzResearch.WordTrace]
  refine ⟨45279346642945975735102109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120744924381189268626938957 45279346642945975735102109)
  ·
    refine ⟨16979754991104740900663291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45279346642945975735102109 16979754991104740900663291)
    ·
      refine ⟨25469632486657111350994937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16979754991104740900663291 25469632486657111350994937)
      ·
        refine ⟨19102224364992833513246203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25469632486657111350994937 19102224364992833513246203)
        ·
          refine ⟨28653336547489250269869305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19102224364992833513246203 28653336547489250269869305)
          ·
            refine ⟨21490002410616937702401979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28653336547489250269869305 21490002410616937702401979)
            ·
              refine ⟨32235003615925406553602969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21490002410616937702401979 32235003615925406553602969)
              ·
                refine ⟨24176252711944054915202227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32235003615925406553602969 24176252711944054915202227)
                ·
                  refine ⟨36264379067916082372803341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24176252711944054915202227 36264379067916082372803341)
                  ·
                    refine ⟨13599142150468530889801253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36264379067916082372803341 13599142150468530889801253)
                    ·
                      refine ⟨2549839153212849541837735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13599142150468530889801253 2549839153212849541837735)
                      ·
                        rfl

theorem cell23_4965794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_4965794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965794 prefixEnd_4965794 := by exact prefixLift 4965794
  have htrace : WordTrace (prefixWord ++ tailWord_4965794) baseStart_4965794 baseEnd_4965794 := by
    simpa [prefixWord, tailWord_4965794, baseEnd_4965794] using wordTrace_append hprefix tailTrace_4965794
  have hstable : (prefixWord ++ tailWord_4965794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965794).length < 2 ^ (prefixWord ++ tailWord_4965794).sum := by decide
  have hdescent : baseEnd_4965794 < baseStart_4965794 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965804 : List Nat := [2, 2, 1, 1, 1, 1, 6, 2, 3, 4]
def baseStart_4965804 : Nat := 118140960795 + 4965804 * 2 ^ 59
def prefixEnd_4965804 : Nat := 4983230072969 + 3 ^ 40 * 4965804 * 2
def baseEnd_4965804 : Nat := 849948096006464834237563

theorem tailTrace_4965804 : CollatzResearch.WordTrace tailWord_4965804 prefixEnd_4965804 849948096006464834237563 := by
  unfold tailWord_4965804
  simp only [CollatzResearch.WordTrace]
  refine ⟨90558875650873837324136233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120745167534498449765514977 90558875650873837324136233)
  ·
    refine ⟨67919156738155377993102175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90558875650873837324136233 67919156738155377993102175)
    ·
      refine ⟨101878735107233066989653263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67919156738155377993102175 101878735107233066989653263)
      ·
        refine ⟨152818102660849600484479895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101878735107233066989653263 152818102660849600484479895)
        ·
          refine ⟨229227153991274400726719843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152818102660849600484479895 229227153991274400726719843)
          ·
            refine ⟨343840730986911601090079765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229227153991274400726719843 343840730986911601090079765)
            ·
              refine ⟨16117534265011481301097489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 343840730986911601090079765 16117534265011481301097489)
              ·
                refine ⟨12088150698758610975823117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16117534265011481301097489 12088150698758610975823117)
                ·
                  refine ⟨4533056512034479115933669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12088150698758610975823117 4533056512034479115933669)
                  ·
                    refine ⟨849948096006464834237563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4533056512034479115933669 849948096006464834237563)
                    ·
                      rfl

theorem cell23_4965804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 4].length) (baseStart_4965804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965804 prefixEnd_4965804 := by exact prefixLift 4965804
  have htrace : WordTrace (prefixWord ++ tailWord_4965804) baseStart_4965804 baseEnd_4965804 := by
    simpa [prefixWord, tailWord_4965804, baseEnd_4965804] using wordTrace_append hprefix tailTrace_4965804
  have hstable : (prefixWord ++ tailWord_4965804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965804).length < 2 ^ (prefixWord ++ tailWord_4965804).sum := by decide
  have hdescent : baseEnd_4965804 < baseStart_4965804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965864 : List Nat := [2, 1, 4, 1, 1, 2, 3, 1, 3, 5]
def baseStart_4965864 : Nat := 118140960795 + 4965864 * 2 ^ 59
def prefixEnd_4965864 : Nat := 4983230072969 + 3 ^ 40 * 4965864 * 2
def baseEnd_4965864 : Nat := 849958365619554755987471

theorem tailTrace_4965864 : CollatzResearch.WordTrace tailWord_4965864 prefixEnd_4965864 849958365619554755987471 := by
  unfold tailWord_4965864
  simp only [CollatzResearch.WordTrace]
  refine ⟨90559969840765152447728323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120746626454353536596971097 90559969840765152447728323)
  ·
    refine ⟨135839954761147728671592485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90559969840765152447728323 135839954761147728671592485)
    ·
      refine ⟨25469991517715199125923591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135839954761147728671592485 25469991517715199125923591)
      ·
        refine ⟨38204987276572798688885387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25469991517715199125923591 38204987276572798688885387)
        ·
          refine ⟨57307480914859198033328081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38204987276572798688885387 57307480914859198033328081)
          ·
            refine ⟨42980610686144398524996061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57307480914859198033328081 42980610686144398524996061)
            ·
              refine ⟨16117729007304149446873523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42980610686144398524996061 16117729007304149446873523)
              ·
                refine ⟨24176593510956224170310285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16117729007304149446873523 24176593510956224170310285)
                ·
                  refine ⟨9066222566608584063866357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24176593510956224170310285 9066222566608584063866357)
                  ·
                    refine ⟨849958365619554755987471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9066222566608584063866357 849958365619554755987471)
                    ·
                      rfl

theorem cell23_4965864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 3, 1, 3, 5].length) (baseStart_4965864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965864 prefixEnd_4965864 := by exact prefixLift 4965864
  have htrace : WordTrace (prefixWord ++ tailWord_4965864) baseStart_4965864 baseEnd_4965864 := by
    simpa [prefixWord, tailWord_4965864, baseEnd_4965864] using wordTrace_append hprefix tailTrace_4965864
  have hstable : (prefixWord ++ tailWord_4965864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965864).length < 2 ^ (prefixWord ++ tailWord_4965864).sum := by decide
  have hdescent : baseEnd_4965864 < baseStart_4965864 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965871 : List Nat := [1, 1, 2, 1, 4, 1, 3, 3, 2, 3, 2]
def baseStart_4965871 : Nat := 118140960795 + 4965871 * 2 ^ 59
def prefixEnd_4965871 : Nat := 4983230072969 + 3 ^ 40 * 4965871 * 2
def baseEnd_4965871 : Nat := 2549878691223245740574881

theorem tailTrace_4965871 : CollatzResearch.WordTrace tailWord_4965871 prefixEnd_4965871 2549878691223245740574881 := by
  unfold tailWord_4965871
  simp only [CollatzResearch.WordTrace]
  refine ⟨181120194992504945090961467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120746796661669963393974311 181120194992504945090961467)
  ·
    refine ⟨271680292488757417636442201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181120194992504945090961467 271680292488757417636442201)
    ·
      refine ⟨203760219366568063227331651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271680292488757417636442201 203760219366568063227331651)
      ·
        refine ⟨305640329049852094840997477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203760219366568063227331651 305640329049852094840997477)
        ·
          refine ⟨57307561696847267782687027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305640329049852094840997477 57307561696847267782687027)
          ·
            refine ⟨85961342545270901674030541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57307561696847267782687027 85961342545270901674030541)
            ·
              refine ⟨32235503454476588127761453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85961342545270901674030541 32235503454476588127761453)
              ·
                refine ⟨12088313795428720547910545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32235503454476588127761453 12088313795428720547910545)
                ·
                  refine ⟨9066235346571540410932909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12088313795428720547910545 9066235346571540410932909)
                  ·
                    refine ⟨3399838254964327654099841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9066235346571540410932909 3399838254964327654099841)
                    ·
                      refine ⟨2549878691223245740574881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399838254964327654099841 2549878691223245740574881)
                      ·
                        rfl

theorem cell23_4965871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 2, 3, 2].length) (baseStart_4965871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965871 prefixEnd_4965871 := by exact prefixLift 4965871
  have htrace : WordTrace (prefixWord ++ tailWord_4965871) baseStart_4965871 baseEnd_4965871 := by
    simpa [prefixWord, tailWord_4965871, baseEnd_4965871] using wordTrace_append hprefix tailTrace_4965871
  have hstable : (prefixWord ++ tailWord_4965871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965871).length < 2 ^ (prefixWord ++ tailWord_4965871).sum := by decide
  have hdescent : baseEnd_4965871 < baseStart_4965871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965895 : List Nat := [1, 1, 4, 3, 2, 2, 1, 4, 1, 1, 3]
def baseStart_4965895 : Nat := 118140960795 + 4965895 * 2 ^ 59
def prefixEnd_4965895 : Nat := 4983230072969 + 3 ^ 40 * 4965895 * 2
def baseEnd_4965895 : Nat := 2549891014758953646674771

theorem tailTrace_4965895 : CollatzResearch.WordTrace tailWord_4965895 prefixEnd_4965895 2549891014758953646674771 := by
  unfold tailWord_4965895
  simp only [CollatzResearch.WordTrace]
  refine ⟨181121070344417997189835139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120747380229611998126556759 181121070344417997189835139)
  ·
    refine ⟨271681605516626995784752709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181121070344417997189835139 271681605516626995784752709)
    ·
      refine ⟨50940301034367561709641133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271681605516626995784752709 50940301034367561709641133)
      ·
        refine ⟨19102612887887835641115425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50940301034367561709641133 19102612887887835641115425)
        ·
          refine ⟨14326959665915876730836569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19102612887887835641115425 14326959665915876730836569)
          ·
            refine ⟨10745219749436907548127427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14326959665915876730836569 10745219749436907548127427)
            ·
              refine ⟨16117829624155361322191141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10745219749436907548127427 16117829624155361322191141)
              ·
                refine ⟨3022093054529130247910839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16117829624155361322191141 3022093054529130247910839)
                ·
                  refine ⟨4533139581793695371866259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022093054529130247910839 4533139581793695371866259)
                  ·
                    refine ⟨6799709372690543057799389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533139581793695371866259 6799709372690543057799389)
                    ·
                      refine ⟨2549891014758953646674771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6799709372690543057799389 2549891014758953646674771)
                      ·
                        rfl

theorem cell23_4965895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 4, 1, 1, 3].length) (baseStart_4965895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965895 prefixEnd_4965895 := by exact prefixLift 4965895
  have htrace : WordTrace (prefixWord ++ tailWord_4965895) baseStart_4965895 baseEnd_4965895 := by
    simpa [prefixWord, tailWord_4965895, baseEnd_4965895] using wordTrace_append hprefix tailTrace_4965895
  have hstable : (prefixWord ++ tailWord_4965895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965895).length < 2 ^ (prefixWord ++ tailWord_4965895).sum := by decide
  have hdescent : baseEnd_4965895 < baseStart_4965895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965921 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 3]
def baseStart_4965921 : Nat := 118140960795 + 4965921 * 2 ^ 59
def prefixEnd_4965921 : Nat := 4983230072969 + 3 ^ 40 * 4965921 * 2
def baseEnd_4965921 : Nat := 2549904365255970544949651

theorem tailTrace_4965921 : CollatzResearch.WordTrace tailWord_4965921 prefixEnd_4965921 2549904365255970544949651 := by
  unfold tailWord_4965921
  simp only [CollatzResearch.WordTrace]
  refine ⟨181122018642323803630281617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120748012428215869086854411 181122018642323803630281617)
  ·
    refine ⟨135841513981742852722711213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181122018642323803630281617 135841513981742852722711213)
    ·
      refine ⟨50940567743153569771016705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135841513981742852722711213 50940567743153569771016705)
      ·
        refine ⟨38205425807365177328262529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50940567743153569771016705 38205425807365177328262529)
        ·
          refine ⟨28654069355523882996196897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38205425807365177328262529 28654069355523882996196897)
          ·
            refine ⟨21490552016642912247147673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28654069355523882996196897 21490552016642912247147673)
            ·
              refine ⟨16117914012482184185360755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21490552016642912247147673 16117914012482184185360755)
              ·
                refine ⟨24176871018723276278041133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16117914012482184185360755 24176871018723276278041133)
                ·
                  refine ⟨9066326632021228604265425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24176871018723276278041133 9066326632021228604265425)
                  ·
                    refine ⟨6799744974015921453199069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9066326632021228604265425 6799744974015921453199069)
                    ·
                      refine ⟨2549904365255970544949651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6799744974015921453199069 2549904365255970544949651)
                      ·
                        rfl

theorem cell23_4965921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_4965921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965921 prefixEnd_4965921 := by exact prefixLift 4965921
  have htrace : WordTrace (prefixWord ++ tailWord_4965921) baseStart_4965921 baseEnd_4965921 := by
    simpa [prefixWord, tailWord_4965921, baseEnd_4965921] using wordTrace_append hprefix tailTrace_4965921
  have hstable : (prefixWord ++ tailWord_4965921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965921).length < 2 ^ (prefixWord ++ tailWord_4965921).sum := by decide
  have hdescent : baseEnd_4965921 < baseStart_4965921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965961 : List Nat := [1, 2, 1, 1, 2, 2, 1, 3, 5, 3, 2]
def baseStart_4965961 : Nat := 118140960795 + 4965961 * 2 ^ 59
def prefixEnd_4965961 : Nat := 4983230072969 + 3 ^ 40 * 4965961 * 2
def baseEnd_4965961 : Nat := 2549924904482150388449467

theorem tailTrace_4965961 : CollatzResearch.WordTrace tailWord_4965961 prefixEnd_4965961 2549924904482150388449467 := by
  unfold tailWord_4965961
  simp only [CollatzResearch.WordTrace]
  refine ⟨181123477562178890461737737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120748985041452593641158491 181123477562178890461737737)
  ·
    refine ⟨135842608171634167846303303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181123477562178890461737737 135842608171634167846303303)
    ·
      refine ⟨203763912257451251769454955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135842608171634167846303303 203763912257451251769454955)
      ·
        refine ⟨305645868386176877654182433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203763912257451251769454955 305645868386176877654182433)
        ·
          refine ⟨229234401289632658240636825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305645868386176877654182433 229234401289632658240636825)
          ·
            refine ⟨171925800967224493680477619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229234401289632658240636825 171925800967224493680477619)
            ·
              refine ⟨257888701450836740520716429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171925800967224493680477619 257888701450836740520716429)
              ·
                refine ⟨96708263044063777695268661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257888701450836740520716429 96708263044063777695268661)
                ·
                  refine ⟨9066399660380979158931437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96708263044063777695268661 9066399660380979158931437)
                  ·
                    refine ⟨3399899872642867184599289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9066399660380979158931437 3399899872642867184599289)
                    ·
                      refine ⟨2549924904482150388449467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3399899872642867184599289 2549924904482150388449467)
                      ·
                        rfl

theorem cell23_4965961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 5, 3, 2].length) (baseStart_4965961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965961 prefixEnd_4965961 := by exact prefixLift 4965961
  have htrace : WordTrace (prefixWord ++ tailWord_4965961) baseStart_4965961 baseEnd_4965961 := by
    simpa [prefixWord, tailWord_4965961, baseEnd_4965961] using wordTrace_append hprefix tailTrace_4965961
  have hstable : (prefixWord ++ tailWord_4965961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965961).length < 2 ^ (prefixWord ++ tailWord_4965961).sum := by decide
  have hdescent : baseEnd_4965961 < baseStart_4965961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4965965 : List Nat := [1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 4]
def baseStart_4965965 : Nat := 118140960795 + 4965965 * 2 ^ 59
def prefixEnd_4965965 : Nat := 4983230072969 + 3 ^ 40 * 4965965 * 2
def baseEnd_4965965 : Nat := 2549926958404768372799449

theorem tailTrace_4965965 : CollatzResearch.WordTrace tailWord_4965965 prefixEnd_4965965 2549926958404768372799449 := by
  unfold tailWord_4965965
  simp only [CollatzResearch.WordTrace]
  refine ⟨181123623454164399144883349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120749082302776266096588899 181123623454164399144883349)
  ·
    refine ⟨8490169849413956209916407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181123623454164399144883349 8490169849413956209916407)
    ·
      refine ⟨12735254774120934314874611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8490169849413956209916407 12735254774120934314874611)
      ·
        refine ⟨19102882161181401472311917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12735254774120934314874611 19102882161181401472311917)
        ·
          refine ⟨7163580810443025552116969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19102882161181401472311917 7163580810443025552116969)
          ·
            refine ⟨5372685607832269164087727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7163580810443025552116969 5372685607832269164087727)
            ·
              refine ⟨8059028411748403746131591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5372685607832269164087727 8059028411748403746131591)
              ·
                refine ⟨12088542617622605619197387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8059028411748403746131591 12088542617622605619197387)
                ·
                  refine ⟨18132813926433908428796081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12088542617622605619197387 18132813926433908428796081)
                  ·
                    refine ⟨13599610444825431321597061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18132813926433908428796081 13599610444825431321597061)
                    ·
                      refine ⟨2549926958404768372799449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13599610444825431321597061 2549926958404768372799449)
                      ·
                        rfl

theorem cell23_4965965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 1, 1, 2, 4].length) (baseStart_4965965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4965965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4965965 prefixEnd_4965965 := by exact prefixLift 4965965
  have htrace : WordTrace (prefixWord ++ tailWord_4965965) baseStart_4965965 baseEnd_4965965 := by
    simpa [prefixWord, tailWord_4965965, baseEnd_4965965] using wordTrace_append hprefix tailTrace_4965965
  have hstable : (prefixWord ++ tailWord_4965965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4965965).length < 2 ^ (prefixWord ++ tailWord_4965965).sum := by decide
  have hdescent : baseEnd_4965965 < baseStart_4965965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4965965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966071 : List Nat := [1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 5]
def baseStart_4966071 : Nat := 118140960795 + 4966071 * 2 ^ 59
def prefixEnd_4966071 : Nat := 4983230072969 + 3 ^ 40 * 4966071 * 2
def baseEnd_4966071 : Nat := 2549981387354144958073961

theorem tailTrace_4966071 : CollatzResearch.WordTrace tailWord_4966071 prefixEnd_4966071 2549981387354144958073961 := by
  unfold tailWord_4966071
  simp only [CollatzResearch.WordTrace]
  refine ⟨181127489591780379248242067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120751659727853586165494711 181127489591780379248242067)
  ·
    refine ⟨271691234387670568872363101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181127489591780379248242067 271691234387670568872363101)
    ·
      refine ⟨101884212895376463327136163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271691234387670568872363101 101884212895376463327136163)
      ·
        refine ⟨152826319343064694990704245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101884212895376463327136163 152826319343064694990704245)
        ·
          refine ⟨14327467438412315155378523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152826319343064694990704245 14327467438412315155378523)
          ·
            refine ⟨21491201157618472733067785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14327467438412315155378523 21491201157618472733067785)
            ·
              refine ⟨16118400868213854549800839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21491201157618472733067785 16118400868213854549800839)
              ·
                refine ⟨24177601302320781824701259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16118400868213854549800839 24177601302320781824701259)
                ·
                  refine ⟨36266401953481172737051889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24177601302320781824701259 36266401953481172737051889)
                  ·
                    refine ⟨27199801465110879552788917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36266401953481172737051889 27199801465110879552788917)
                    ·
                      refine ⟨2549981387354144958073961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27199801465110879552788917 2549981387354144958073961)
                      ·
                        rfl

theorem cell23_4966071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 2, 5].length) (baseStart_4966071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966071 prefixEnd_4966071 := by exact prefixLift 4966071
  have htrace : WordTrace (prefixWord ++ tailWord_4966071) baseStart_4966071 baseEnd_4966071 := by
    simpa [prefixWord, tailWord_4966071, baseEnd_4966071] using wordTrace_append hprefix tailTrace_4966071
  have hstable : (prefixWord ++ tailWord_4966071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966071).length < 2 ^ (prefixWord ++ tailWord_4966071).sum := by decide
  have hdescent : baseEnd_4966071 < baseStart_4966071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966082 : List Nat := [3, 5, 1, 2, 1, 1, 1, 2, 7]
def baseStart_4966082 : Nat := 118140960795 + 4966082 * 2 ^ 59
def prefixEnd_4966082 : Nat := 4983230072969 + 3 ^ 40 * 4966082 * 2
def baseEnd_4966082 : Nat := 283331892849038268337379

theorem tailTrace_4966082 : CollatzResearch.WordTrace tailWord_4966082 prefixEnd_4966082 283331892849038268337379 := by
  unfold tailWord_4966082
  simp only [CollatzResearch.WordTrace]
  refine ⟨45281972698685132031723125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120751927196493685417928333 45281972698685132031723125)
  ·
    refine ⟨4245184940501731127974043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45281972698685132031723125 4245184940501731127974043)
    ·
      refine ⟨6367777410752596691961065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4245184940501731127974043 6367777410752596691961065)
      ·
        refine ⟨4775833058064447518970799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6367777410752596691961065 4775833058064447518970799)
        ·
          refine ⟨7163749587096671278456199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4775833058064447518970799 7163749587096671278456199)
          ·
            refine ⟨10745624380645006917684299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7163749587096671278456199 10745624380645006917684299)
            ·
              refine ⟨16118436570967510376526449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10745624380645006917684299 16118436570967510376526449)
              ·
                refine ⟨12088827428225632782394837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16118436570967510376526449 12088827428225632782394837)
                ·
                  refine ⟨283331892849038268337379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12088827428225632782394837 283331892849038268337379)
                  ·
                    rfl

theorem cell23_4966082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_4966082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966082 prefixEnd_4966082 := by exact prefixLift 4966082
  have htrace : WordTrace (prefixWord ++ tailWord_4966082) baseStart_4966082 baseEnd_4966082 := by
    simpa [prefixWord, tailWord_4966082, baseEnd_4966082] using wordTrace_append hprefix tailTrace_4966082
  have hstable : (prefixWord ++ tailWord_4966082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966082).length < 2 ^ (prefixWord ++ tailWord_4966082).sum := by decide
  have hdescent : baseEnd_4966082 < baseStart_4966082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966098 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 1, 3, 4]
def baseStart_4966098 : Nat := 118140960795 + 4966098 * 2 ^ 59
def prefixEnd_4966098 : Nat := 4983230072969 + 3 ^ 40 * 4966098 * 2
def baseEnd_4966098 : Nat := 2549995251331816352436337

theorem tailTrace_4966098 : CollatzResearch.WordTrace tailWord_4966098 prefixEnd_4966098 2549995251331816352436337 := by
  unfold tailWord_4966098
  simp only [CollatzResearch.WordTrace]
  refine ⟨45282118590670640714868737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120752316241788375239649965 45282118590670640714868737)
  ·
    refine ⟨33961588943002980536151553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45282118590670640714868737 33961588943002980536151553)
    ·
      refine ⟨25471191707252235402113665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33961588943002980536151553 25471191707252235402113665)
      ·
        refine ⟨19103393780439176551585249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25471191707252235402113665 19103393780439176551585249)
        ·
          refine ⟨14327545335329382413688937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19103393780439176551585249 14327545335329382413688937)
          ·
            refine ⟨10745659001497036810266703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14327545335329382413688937 10745659001497036810266703)
            ·
              refine ⟨16118488502245555215400055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10745659001497036810266703 16118488502245555215400055)
              ·
                refine ⟨24177732753368332823100083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16118488502245555215400055 24177732753368332823100083)
                ·
                  refine ⟨36266599130052499234650125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24177732753368332823100083 36266599130052499234650125)
                  ·
                    refine ⟨13599974673769687212993797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36266599130052499234650125 13599974673769687212993797)
                    ·
                      refine ⟨2549995251331816352436337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13599974673769687212993797 2549995251331816352436337)
                      ·
                        rfl

theorem cell23_4966098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_4966098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966098 prefixEnd_4966098 := by exact prefixLift 4966098
  have htrace : WordTrace (prefixWord ++ tailWord_4966098) baseStart_4966098 baseEnd_4966098 := by
    simpa [prefixWord, tailWord_4966098, baseEnd_4966098] using wordTrace_append hprefix tailTrace_4966098
  have hstable : (prefixWord ++ tailWord_4966098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966098).length < 2 ^ (prefixWord ++ tailWord_4966098).sum := by decide
  have hdescent : baseEnd_4966098 < baseStart_4966098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966125 : List Nat := [1, 5, 1, 2, 1, 3, 2, 1, 3, 4]
def baseStart_4966125 : Nat := 118140960795 + 4966125 * 2 ^ 59
def prefixEnd_4966125 : Nat := 4983230072969 + 3 ^ 40 * 4966125 * 2
def baseEnd_4966125 : Nat := 850003038436495915599571

theorem tailTrace_4966125 : CollatzResearch.WordTrace tailWord_4966125 prefixEnd_4966125 850003038436495915599571 := by
  unfold tailWord_4966125
  simp only [CollatzResearch.WordTrace]
  refine ⟨181129459133584746470707829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120752972755723164313805219 181129459133584746470707829)
  ·
    refine ⟨16980886793773569981628859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 181129459133584746470707829 16980886793773569981628859)
    ·
      refine ⟨25471330190660354972443289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16980886793773569981628859 25471330190660354972443289)
      ·
        refine ⟨19103497642995266229332467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25471330190660354972443289 19103497642995266229332467)
        ·
          refine ⟨28655246464492899343998701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19103497642995266229332467 28655246464492899343998701)
          ·
            refine ⟨10745717424184837253999513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28655246464492899343998701 10745717424184837253999513)
            ·
              refine ⟨8059288068138627940499635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10745717424184837253999513 8059288068138627940499635)
              ·
                refine ⟨12088932102207941910749453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8059288068138627940499635 12088932102207941910749453)
                ·
                  refine ⟨4533349538327978216531045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12088932102207941910749453 4533349538327978216531045)
                  ·
                    refine ⟨850003038436495915599571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4533349538327978216531045 850003038436495915599571)
                    ·
                      rfl

theorem cell23_4966125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_4966125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966125 prefixEnd_4966125 := by exact prefixLift 4966125
  have htrace : WordTrace (prefixWord ++ tailWord_4966125) baseStart_4966125 baseEnd_4966125 := by
    simpa [prefixWord, tailWord_4966125, baseEnd_4966125] using wordTrace_append hprefix tailTrace_4966125
  have hstable : (prefixWord ++ tailWord_4966125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966125).length < 2 ^ (prefixWord ++ tailWord_4966125).sum := by decide
  have hdescent : baseEnd_4966125 < baseStart_4966125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966150 : List Nat := [6, 2, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4966150 : Nat := 118140960795 + 4966150 * 2 ^ 59
def prefixEnd_4966150 : Nat := 4983230072969 + 3 ^ 40 * 4966150 * 2
def baseEnd_4966150 : Nat := 283335772480650016554011

theorem tailTrace_4966150 : CollatzResearch.WordTrace tailWord_4966150 prefixEnd_4966150 283335772480650016554011 := by
  unfold tailWord_4966150
  simp only [CollatzResearch.WordTrace]
  refine ⟨5660324092452942991886497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 120753580638996117160245269 5660324092452942991886497)
  ·
    refine ⟨4245243069339707243914873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5660324092452942991886497 4245243069339707243914873)
    ·
      refine ⟨3183932302004780432936155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4245243069339707243914873 3183932302004780432936155)
      ·
        refine ⟨4775898453007170649404233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3183932302004780432936155 4775898453007170649404233)
        ·
          refine ⟨3581923839755377987053175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4775898453007170649404233 3581923839755377987053175)
          ·
            refine ⟨5372885759633066980579763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3581923839755377987053175 5372885759633066980579763)
            ·
              refine ⟨8059328639449600470869645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5372885759633066980579763 8059328639449600470869645)
              ·
                refine ⟨3022248239793600176576117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8059328639449600470869645 3022248239793600176576117)
                ·
                  refine ⟨283335772480650016554011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3022248239793600176576117 283335772480650016554011)
                  ·
                    rfl

theorem cell23_4966150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4966150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966150 prefixEnd_4966150 := by exact prefixLift 4966150
  have htrace : WordTrace (prefixWord ++ tailWord_4966150) baseStart_4966150 baseEnd_4966150 := by
    simpa [prefixWord, tailWord_4966150, baseEnd_4966150] using wordTrace_append hprefix tailTrace_4966150
  have hstable : (prefixWord ++ tailWord_4966150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966150).length < 2 ^ (prefixWord ++ tailWord_4966150).sum := by decide
  have hdescent : baseEnd_4966150 < baseStart_4966150 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966168 : List Nat := [2, 1, 2, 3, 1, 1, 4, 3, 1, 5]
def baseStart_4966168 : Nat := 118140960795 + 4966168 * 2 ^ 59
def prefixEnd_4966168 : Nat := 4983230072969 + 3 ^ 40 * 4966168 * 2
def baseEnd_4966168 : Nat := 850010398325877026187005

theorem tailTrace_4966168 : CollatzResearch.WordTrace tailWord_4966168 prefixEnd_4966168 850010398325877026187005 := by
  unfold tailWord_4966168
  simp only [CollatzResearch.WordTrace]
  refine ⟨90565513736214482407261579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120754018314952643209682105 90565513736214482407261579)
  ·
    refine ⟨135848270604321723610892369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90565513736214482407261579 135848270604321723610892369)
    ·
      refine ⟨101886202953241292708169277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135848270604321723610892369 101886202953241292708169277)
      ·
        refine ⟨38207326107465484765563479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101886202953241292708169277 38207326107465484765563479)
        ·
          refine ⟨57310989161198227148345219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38207326107465484765563479 57310989161198227148345219)
          ·
            refine ⟨85966483741797340722517829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57310989161198227148345219 85966483741797340722517829)
            ·
              refine ⟨16118715701587001385472093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85966483741797340722517829 16118715701587001385472093)
              ·
                refine ⟨6044518388095125519552035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16118715701587001385472093 6044518388095125519552035)
                ·
                  refine ⟨9066777582142688279328053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6044518388095125519552035 9066777582142688279328053)
                  ·
                    refine ⟨850010398325877026187005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9066777582142688279328053 850010398325877026187005)
                    ·
                      rfl

theorem cell23_4966168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 1, 5].length) (baseStart_4966168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966168 prefixEnd_4966168 := by exact prefixLift 4966168
  have htrace : WordTrace (prefixWord ++ tailWord_4966168) baseStart_4966168 baseEnd_4966168 := by
    simpa [prefixWord, tailWord_4966168, baseEnd_4966168] using wordTrace_append hprefix tailTrace_4966168
  have hstable : (prefixWord ++ tailWord_4966168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966168).length < 2 ^ (prefixWord ++ tailWord_4966168).sum := by decide
  have hdescent : baseEnd_4966168 < baseStart_4966168 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966175 : List Nat := [1, 1, 2, 4, 2, 1, 3, 2, 2, 3, 2]
def baseStart_4966175 : Nat := 118140960795 + 4966175 * 2 ^ 59
def prefixEnd_4966175 : Nat := 4983230072969 + 3 ^ 40 * 4966175 * 2
def baseEnd_4966175 : Nat := 2550034789342212551173483

theorem tailTrace_4966175 : CollatzResearch.WordTrace tailWord_4966175 prefixEnd_4966175 2550034789342212551173483 := by
  unfold tailWord_4966175
  simp only [CollatzResearch.WordTrace]
  refine ⟨181131282783403605010027979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120754188522269070006685319 181131282783403605010027979)
  ·
    refine ⟨271696924175105407515041969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181131282783403605010027979 271696924175105407515041969)
    ·
      refine ⟨203772693131329055636281477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271696924175105407515041969 203772693131329055636281477)
      ·
        refine ⟨38207379962124197931802777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203772693131329055636281477 38207379962124197931802777)
        ·
          refine ⟨28655534971593148448852083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38207379962124197931802777 28655534971593148448852083)
          ·
            refine ⟨42983302457389722673278125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28655534971593148448852083 42983302457389722673278125)
            ·
              refine ⟨16118738421521146002479297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42983302457389722673278125 16118738421521146002479297)
              ·
                refine ⟨12089053816140859501859473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16118738421521146002479297 12089053816140859501859473)
                ·
                  refine ⟨9066790362105644626394605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12089053816140859501859473 9066790362105644626394605)
                  ·
                    refine ⟨3400046385789616734897977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9066790362105644626394605 3400046385789616734897977)
                    ·
                      refine ⟨2550034789342212551173483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400046385789616734897977 2550034789342212551173483)
                      ·
                        rfl

theorem cell23_4966175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_4966175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966175 prefixEnd_4966175 := by exact prefixLift 4966175
  have htrace : WordTrace (prefixWord ++ tailWord_4966175) baseStart_4966175 baseEnd_4966175 := by
    simpa [prefixWord, tailWord_4966175, baseEnd_4966175] using wordTrace_append hprefix tailTrace_4966175
  have hstable : (prefixWord ++ tailWord_4966175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966175).length < 2 ^ (prefixWord ++ tailWord_4966175).sum := by decide
  have hdescent : baseEnd_4966175 < baseStart_4966175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966205 : List Nat := [1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4966205 : Nat := 118140960795 + 4966205 * 2 ^ 59
def prefixEnd_4966205 : Nat := 4983230072969 + 3 ^ 40 * 4966205 * 2
def baseEnd_4966205 : Nat := 2550050193761847433798345

theorem tailTrace_4966205 : CollatzResearch.WordTrace tailWord_4966205 prefixEnd_4966205 2550050193761847433798345 := by
  unfold tailWord_4966205
  simp only [CollatzResearch.WordTrace]
  refine ⟨181132376973294920133620069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120754917982196613422413379 181132376973294920133620069)
  ·
    refine ⟨33962320682492797525053763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181132376973294920133620069 33962320682492797525053763)
    ·
      refine ⟨50943481023739196287580645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33962320682492797525053763 50943481023739196287580645)
      ·
        refine ⟨9551902691951099303921371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50943481023739196287580645 9551902691951099303921371)
        ·
          refine ⟨14327854037926648955882057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9551902691951099303921371 14327854037926648955882057)
          ·
            refine ⟨10745890528444986716911543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14327854037926648955882057 10745890528444986716911543)
            ·
              refine ⟨16118835792667480075367315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10745890528444986716911543 16118835792667480075367315)
              ·
                refine ⟨24178253689001220113050973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16118835792667480075367315 24178253689001220113050973)
                ·
                  refine ⟨9066845133375457542394115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24178253689001220113050973 9066845133375457542394115)
                  ·
                    refine ⟨13600267700063186313591173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9066845133375457542394115 13600267700063186313591173)
                    ·
                      refine ⟨2550050193761847433798345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13600267700063186313591173 2550050193761847433798345)
                      ·
                        rfl

theorem cell23_4966205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4966205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966205 prefixEnd_4966205 := by exact prefixLift 4966205
  have htrace : WordTrace (prefixWord ++ tailWord_4966205) baseStart_4966205 baseEnd_4966205 := by
    simpa [prefixWord, tailWord_4966205, baseEnd_4966205] using wordTrace_append hprefix tailTrace_4966205
  have hstable : (prefixWord ++ tailWord_4966205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966205).length < 2 ^ (prefixWord ++ tailWord_4966205).sum := by decide
  have hdescent : baseEnd_4966205 < baseStart_4966205 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966211 : List Nat := [1, 1, 1, 3, 1, 5, 2, 9]
def baseStart_4966211 : Nat := 118140960795 + 4966211 * 2 ^ 59
def prefixEnd_4966211 : Nat := 4983230072969 + 3 ^ 40 * 4966211 * 2
def baseEnd_4966211 : Nat := 94446417579473126308271

theorem tailTrace_4966211 : CollatzResearch.WordTrace tailWord_4966211 prefixEnd_4966211 94446417579473126308271 := by
  unfold tailWord_4966211
  simp only [CollatzResearch.WordTrace]
  refine ⟨181132595811273183158338487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120755063874182122105558991 181132595811273183158338487)
  ·
    refine ⟨271698893716909774737507731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181132595811273183158338487 271698893716909774737507731)
    ·
      refine ⟨407548340575364662106261597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271698893716909774737507731 407548340575364662106261597)
      ·
        refine ⟨152830627715761748289848099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407548340575364662106261597 152830627715761748289848099)
        ·
          refine ⟨229245941573642622434772149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152830627715761748289848099 229245941573642622434772149)
          ·
            refine ⟨21491807022528995853259889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229245941573642622434772149 21491807022528995853259889)
            ·
              refine ⟨16118855266896746889944917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21491807022528995853259889 16118855266896746889944917)
              ·
                refine ⟨94446417579473126308271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16118855266896746889944917 94446417579473126308271)
                ·
                  rfl

theorem cell23_4966211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 9].length) (baseStart_4966211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966211 prefixEnd_4966211 := by exact prefixLift 4966211
  have htrace : WordTrace (prefixWord ++ tailWord_4966211) baseStart_4966211 baseEnd_4966211 := by
    simpa [prefixWord, tailWord_4966211, baseEnd_4966211] using wordTrace_append hprefix tailTrace_4966211
  have hstable : (prefixWord ++ tailWord_4966211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966211).length < 2 ^ (prefixWord ++ tailWord_4966211).sum := by decide
  have hdescent : baseEnd_4966211 < baseStart_4966211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966218 : List Nat := [3, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4]
def baseStart_4966218 : Nat := 118140960795 + 4966218 * 2 ^ 59
def prefixEnd_4966218 : Nat := 4983230072969 + 3 ^ 40 * 4966218 * 2
def baseEnd_4966218 : Nat := 2550056869010355882935785

theorem tailTrace_4966218 : CollatzResearch.WordTrace tailWord_4966218 prefixEnd_4966218 2550056869010355882935785 := by
  unfold tailWord_4966218
  simp only [CollatzResearch.WordTrace]
  refine ⟨45283212780561955838460827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120755234081498548902562205 45283212780561955838460827)
  ·
    refine ⟨67924819170842933757691241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45283212780561955838460827 67924819170842933757691241)
    ·
      refine ⟨50943614378132200318268431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67924819170842933757691241 50943614378132200318268431)
      ·
        refine ⟨76415421567198300477402647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50943614378132200318268431 76415421567198300477402647)
        ·
          refine ⟨114623132350797450716103971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76415421567198300477402647 114623132350797450716103971)
          ·
            refine ⟨171934698526196176074155957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114623132350797450716103971 171934698526196176074155957)
            ·
              refine ⟨16118877986830891506952121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171934698526196176074155957 16118877986830891506952121)
              ·
                refine ⟨12089158490123168630214091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16118877986830891506952121 12089158490123168630214091)
                ·
                  refine ⟨18133737735184752945321137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12089158490123168630214091 18133737735184752945321137)
                  ·
                    refine ⟨13600303301388564708990853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18133737735184752945321137 13600303301388564708990853)
                    ·
                      refine ⟨2550056869010355882935785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13600303301388564708990853 2550056869010355882935785)
                      ·
                        rfl

theorem cell23_4966218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 2, 1, 2, 4].length) (baseStart_4966218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966218 prefixEnd_4966218 := by exact prefixLift 4966218
  have htrace : WordTrace (prefixWord ++ tailWord_4966218) baseStart_4966218 baseEnd_4966218 := by
    simpa [prefixWord, tailWord_4966218, baseEnd_4966218] using wordTrace_append hprefix tailTrace_4966218
  have hstable : (prefixWord ++ tailWord_4966218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966218).length < 2 ^ (prefixWord ++ tailWord_4966218).sum := by decide
  have hdescent : baseEnd_4966218 < baseStart_4966218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966225 : List Nat := [1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 5]
def baseStart_4966225 : Nat := 118140960795 + 4966225 * 2 ^ 59
def prefixEnd_4966225 : Nat := 4983230072969 + 3 ^ 40 * 4966225 * 2
def baseEnd_4966225 : Nat := 2550060463374937355548253

theorem tailTrace_4966225 : CollatzResearch.WordTrace tailWord_4966225 prefixEnd_4966225 2550060463374937355548253 := by
  unfold tailWord_4966225
  simp only [CollatzResearch.WordTrace]
  refine ⟨181133106433222463549348129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120755404288814975699565419 181133106433222463549348129)
  ·
    refine ⟨135849829824916847662011097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181133106433222463549348129 135849829824916847662011097)
    ·
      refine ⟨101887372368687635746508323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135849829824916847662011097 101887372368687635746508323)
      ·
        refine ⟨152831058553031453619762485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101887372368687635746508323 152831058553031453619762485)
        ·
          refine ⟨14327911739346698776852733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152831058553031453619762485 14327911739346698776852733)
          ·
            refine ⟨5372966902255012041319775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14327911739346698776852733 5372966902255012041319775)
            ·
              refine ⟨8059450353382518061979663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5372966902255012041319775 8059450353382518061979663)
              ·
                refine ⟨12089175530073777092969495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8059450353382518061979663 12089175530073777092969495)
                ·
                  refine ⟨18133763295110665639454243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12089175530073777092969495 18133763295110665639454243)
                  ·
                    refine ⟨27200644942665998459181365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18133763295110665639454243 27200644942665998459181365)
                    ·
                      refine ⟨2550060463374937355548253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27200644942665998459181365 2550060463374937355548253)
                      ·
                        rfl

theorem cell23_4966225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 1, 5].length) (baseStart_4966225 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966225 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966225 prefixEnd_4966225 := by exact prefixLift 4966225
  have htrace : WordTrace (prefixWord ++ tailWord_4966225) baseStart_4966225 baseEnd_4966225 := by
    simpa [prefixWord, tailWord_4966225, baseEnd_4966225] using wordTrace_append hprefix tailTrace_4966225
  have hstable : (prefixWord ++ tailWord_4966225).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966225).length < 2 ^ (prefixWord ++ tailWord_4966225).sum := by decide
  have hdescent : baseEnd_4966225 < baseStart_4966225 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966239 : List Nat := [1, 1, 2, 3, 1, 5, 1, 4, 1, 2, 2]
def baseStart_4966239 : Nat := 118140960795 + 4966239 * 2 ^ 59
def prefixEnd_4966239 : Nat := 4983230072969 + 3 ^ 40 * 4966239 * 2
def baseEnd_4966239 : Nat := 2550067652104100300773189

theorem tailTrace_4966239 : CollatzResearch.WordTrace tailWord_4966239 prefixEnd_4966239 2550067652104100300773189 := by
  unfold tailWord_4966239
  simp only [CollatzResearch.WordTrace]
  refine ⟨181133617055171743940357771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120755744703447829293571847 181133617055171743940357771)
  ·
    refine ⟨271700425582757615910536657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181133617055171743940357771 271700425582757615910536657)
    ·
      refine ⟨203775319187068211932902493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271700425582757615910536657 203775319187068211932902493)
      ·
        refine ⟨76415744695150579474838435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203775319187068211932902493 76415744695150579474838435)
        ·
          refine ⟨114623617042725869212257653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76415744695150579474838435 114623617042725869212257653)
          ·
            refine ⟨10745964097755550238649155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114623617042725869212257653 10745964097755550238649155)
            ·
              refine ⟨16118946146633325357973733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10745964097755550238649155 16118946146633325357973733)
              ·
                refine ⟨3022302402493748504620075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16118946146633325357973733 3022302402493748504620075)
                ·
                  refine ⟨4533453603740622756930113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022302402493748504620075 4533453603740622756930113)
                  ·
                    refine ⟨3400090202805467067697585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4533453603740622756930113 3400090202805467067697585)
                    ·
                      refine ⟨2550067652104100300773189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400090202805467067697585 2550067652104100300773189)
                      ·
                        rfl

theorem cell23_4966239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_4966239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966239 prefixEnd_4966239 := by exact prefixLift 4966239
  have htrace : WordTrace (prefixWord ++ tailWord_4966239) baseStart_4966239 baseEnd_4966239 := by
    simpa [prefixWord, tailWord_4966239, baseEnd_4966239] using wordTrace_append hprefix tailTrace_4966239
  have hstable : (prefixWord ++ tailWord_4966239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966239).length < 2 ^ (prefixWord ++ tailWord_4966239).sum := by decide
  have hdescent : baseEnd_4966239 < baseStart_4966239 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966241 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 1, 9]
def baseStart_4966241 : Nat := 118140960795 + 4966241 * 2 ^ 59
def prefixEnd_4966241 : Nat := 4983230072969 + 3 ^ 40 * 4966241 * 2
def baseEnd_4966241 : Nat := 850022893021803097649393

theorem tailTrace_4966241 : CollatzResearch.WordTrace tailWord_4966241 prefixEnd_4966241 850022893021803097649393 := by
  unfold tailWord_4966241
  simp only [CollatzResearch.WordTrace]
  refine ⟨181133690001164498281930577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120755793334109665521287051 181133690001164498281930577)
  ·
    refine ⟨135850267500873373711447933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181133690001164498281930577 135850267500873373711447933)
    ·
      refine ⟨50943850312827515141792975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135850267500873373711447933 50943850312827515141792975)
      ·
        refine ⟨76415775469241272712689463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50943850312827515141792975 76415775469241272712689463)
        ·
          refine ⟨114623663203861909069034195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76415775469241272712689463 114623663203861909069034195)
          ·
            refine ⟨171935494805792863603551293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114623663203861909069034195 171935494805792863603551293)
            ·
              refine ⟨64475810552172323851331735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171935494805792863603551293 64475810552172323851331735)
              ·
                refine ⟨96713715828258485776997603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64475810552172323851331735 96713715828258485776997603)
                ·
                  refine ⟨145070573742387728665496405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96713715828258485776997603 145070573742387728665496405)
                  ·
                    refine ⟨850022893021803097649393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 145070573742387728665496405 850022893021803097649393)
                    ·
                      rfl

theorem cell23_4966241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 1, 9].length) (baseStart_4966241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966241 prefixEnd_4966241 := by exact prefixLift 4966241
  have htrace : WordTrace (prefixWord ++ tailWord_4966241) baseStart_4966241 baseEnd_4966241 := by
    simpa [prefixWord, tailWord_4966241, baseEnd_4966241] using wordTrace_append hprefix tailTrace_4966241
  have hstable : (prefixWord ++ tailWord_4966241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966241).length < 2 ^ (prefixWord ++ tailWord_4966241).sum := by decide
  have hdescent : baseEnd_4966241 < baseStart_4966241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966251 : List Nat := [1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5]
def baseStart_4966251 : Nat := 118140960795 + 4966251 * 2 ^ 59
def prefixEnd_4966251 : Nat := 4983230072969 + 3 ^ 40 * 4966251 * 2
def baseEnd_4966251 : Nat := 2550073813871954253823133

theorem tailTrace_4966251 : CollatzResearch.WordTrace tailWord_4966251 prefixEnd_4966251 2550073813871954253823133 := by
  unfold tailWord_4966251
  simp only [CollatzResearch.WordTrace]
  refine ⟨181134054731128269989794607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120756036487418846659863071 181134054731128269989794607)
  ·
    refine ⟨271701082096692404984691911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181134054731128269989794607 271701082096692404984691911)
    ·
      refine ⟨407551623145038607477037867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271701082096692404984691911 407551623145038607477037867)
      ·
        refine ⟨611327434717557911215556801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407551623145038607477037867 611327434717557911215556801)
        ·
          refine ⟨458495576038168433411667601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611327434717557911215556801 458495576038168433411667601)
          ·
            refine ⟨343871682028626325058750701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458495576038168433411667601 343871682028626325058750701)
            ·
              refine ⟨128951880760734871897031513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343871682028626325058750701 128951880760734871897031513)
              ·
                refine ⟨96713910570551153922773635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128951880760734871897031513 96713910570551153922773635)
                ·
                  refine ⟨145070865855826730884160453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96713910570551153922773635 145070865855826730884160453)
                  ·
                    refine ⟨27200787347967512040780085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145070865855826730884160453 27200787347967512040780085)
                    ·
                      refine ⟨2550073813871954253823133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27200787347967512040780085 2550073813871954253823133)
                      ·
                        rfl

theorem cell23_4966251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 5].length) (baseStart_4966251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966251 prefixEnd_4966251 := by exact prefixLift 4966251
  have htrace : WordTrace (prefixWord ++ tailWord_4966251) baseStart_4966251 baseEnd_4966251 := by
    simpa [prefixWord, tailWord_4966251, baseEnd_4966251] using wordTrace_append hprefix tailTrace_4966251
  have hstable : (prefixWord ++ tailWord_4966251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966251).length < 2 ^ (prefixWord ++ tailWord_4966251).sum := by decide
  have hdescent : baseEnd_4966251 < baseStart_4966251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966262 : List Nat := [5, 1, 1, 3, 2, 1, 3, 7]
def baseStart_4966262 : Nat := 118140960795 + 4966262 * 2 ^ 59
def prefixEnd_4966262 : Nat := 4983230072969 + 3 ^ 40 * 4966262 * 2
def baseEnd_4966262 : Nat := 94447387487376063362429

theorem tailTrace_4966262 : CollatzResearch.WordTrace tailWord_4966262 prefixEnd_4966262 94447387487376063362429 := by
  unfold tailWord_4966262
  simp only [CollatzResearch.WordTrace]
  refine ⟨11320903495880526179277815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120756303956058945912296693 11320903495880526179277815)
  ·
    refine ⟨16981355243820789268916723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11320903495880526179277815 16981355243820789268916723)
    ·
      refine ⟨25472032865731183903375085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16981355243820789268916723 25472032865731183903375085)
      ·
        refine ⟨9552012324649193963765657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25472032865731183903375085 9552012324649193963765657)
        ·
          refine ⟨7164009243486895472824243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9552012324649193963765657 7164009243486895472824243)
          ·
            refine ⟨10746013865230343209236365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164009243486895472824243 10746013865230343209236365)
            ·
              refine ⟨4029755199461378703463637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10746013865230343209236365 4029755199461378703463637)
              ·
                refine ⟨94447387487376063362429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4029755199461378703463637 94447387487376063362429)
                ·
                  rfl

theorem cell23_4966262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 3, 7].length) (baseStart_4966262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966262 prefixEnd_4966262 := by exact prefixLift 4966262
  have htrace : WordTrace (prefixWord ++ tailWord_4966262) baseStart_4966262 baseEnd_4966262 := by
    simpa [prefixWord, tailWord_4966262, baseEnd_4966262] using wordTrace_append hprefix tailTrace_4966262
  have hstable : (prefixWord ++ tailWord_4966262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966262).length < 2 ^ (prefixWord ++ tailWord_4966262).sum := by decide
  have hdescent : baseEnd_4966262 < baseStart_4966262 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966265 : List Nat := [1, 2, 1, 3, 2, 2, 1, 3, 3, 3, 2]
def baseStart_4966265 : Nat := 118140960795 + 4966265 * 2 ^ 59
def prefixEnd_4966265 : Nat := 4983230072969 + 3 ^ 40 * 4966265 * 2
def baseEnd_4966265 : Nat := 2550081002601117199048069

theorem tailTrace_4966265 : CollatzResearch.WordTrace tailWord_4966265 prefixEnd_4966265 2550081002601117199048069 := by
  unfold tailWord_4966265
  simp only [CollatzResearch.WordTrace]
  refine ⟨181134565353077550380804249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120756376902051700253869499 181134565353077550380804249)
  ·
    refine ⟨135850924014808162785603187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181134565353077550380804249 135850924014808162785603187)
    ·
      refine ⟨203776386022212244178404781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135850924014808162785603187 203776386022212244178404781)
      ·
        refine ⟨76416144758329591566901793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203776386022212244178404781 76416144758329591566901793)
        ·
          refine ⟨57312108568747193675176345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76416144758329591566901793 57312108568747193675176345)
          ·
            refine ⟨42984081426560395256382259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57312108568747193675176345 42984081426560395256382259)
            ·
              refine ⟨64476122139840592884573389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42984081426560395256382259 64476122139840592884573389)
              ·
                refine ⟨24178545802440222331715021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64476122139840592884573389 24178545802440222331715021)
                ·
                  refine ⟨9066954675915083374393133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24178545802440222331715021 9066954675915083374393133)
                  ·
                    refine ⟨3400108003468156265397425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9066954675915083374393133 3400108003468156265397425)
                    ·
                      refine ⟨2550081002601117199048069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400108003468156265397425 2550081002601117199048069)
                      ·
                        rfl

theorem cell23_4966265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 1, 3, 3, 3, 2].length) (baseStart_4966265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966265 prefixEnd_4966265 := by exact prefixLift 4966265
  have htrace : WordTrace (prefixWord ++ tailWord_4966265) baseStart_4966265 baseEnd_4966265 := by
    simpa [prefixWord, tailWord_4966265, baseEnd_4966265] using wordTrace_append hprefix tailTrace_4966265
  have hstable : (prefixWord ++ tailWord_4966265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966265).length < 2 ^ (prefixWord ++ tailWord_4966265).sum := by decide
  have hdescent : baseEnd_4966265 < baseStart_4966265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966271 : List Nat := [1, 1, 2, 2, 1, 1, 3, 1, 3, 8]
def baseStart_4966271 : Nat := 118140960795 + 4966271 * 2 ^ 59
def prefixEnd_4966271 : Nat := 4983230072969 + 3 ^ 40 * 4966271 * 2
def baseEnd_4966271 : Nat := 850028027828348058524347

theorem tailTrace_4966271 : CollatzResearch.WordTrace tailWord_4966271 prefixEnd_4966271 850028027828348058524347 := by
  unfold tailWord_4966271
  simp only [CollatzResearch.WordTrace]
  refine ⟨181134784191055813405522667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120756522794037208937015111 181134784191055813405522667)
  ·
    refine ⟨271702176286583720108284001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181134784191055813405522667 271702176286583720108284001)
    ·
      refine ⟨203776632214937790081213001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271702176286583720108284001 203776632214937790081213001)
      ·
        refine ⟨152832474161203342560909751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203776632214937790081213001 152832474161203342560909751)
        ·
          refine ⟨229248711241805013841364627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152832474161203342560909751 229248711241805013841364627)
          ·
            refine ⟨343873066862707520762046941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229248711241805013841364627 343873066862707520762046941)
            ·
              refine ⟨128952400073515320285767603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343873066862707520762046941 128952400073515320285767603)
              ·
                refine ⟨193428600110272980428651405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128952400073515320285767603 193428600110272980428651405)
                ·
                  refine ⟨72535725041352367660744277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193428600110272980428651405 72535725041352367660744277)
                  ·
                    refine ⟨850028027828348058524347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72535725041352367660744277 850028027828348058524347)
                    ·
                      rfl

theorem cell23_4966271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 3, 1, 3, 8].length) (baseStart_4966271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966271 prefixEnd_4966271 := by exact prefixLift 4966271
  have htrace : WordTrace (prefixWord ++ tailWord_4966271) baseStart_4966271 baseEnd_4966271 := by
    simpa [prefixWord, tailWord_4966271, baseEnd_4966271] using wordTrace_append hprefix tailTrace_4966271
  have hstable : (prefixWord ++ tailWord_4966271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966271).length < 2 ^ (prefixWord ++ tailWord_4966271).sum := by decide
  have hdescent : baseEnd_4966271 < baseStart_4966271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966273 : List Nat := [1, 2, 4, 4, 1, 1, 2, 3, 1, 2, 2]
def baseStart_4966273 : Nat := 118140960795 + 4966273 * 2 ^ 59
def prefixEnd_4966273 : Nat := 4983230072969 + 3 ^ 40 * 4966273 * 2
def baseEnd_4966273 : Nat := 2550085110446353167748033

theorem tailTrace_4966273 : CollatzResearch.WordTrace tailWord_4966273 prefixEnd_4966273 2550085110446353167748033 := by
  unfold tailWord_4966273
  simp only [CollatzResearch.WordTrace]
  refine ⟨181134857137048567747095473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120756571424699045164730315 181134857137048567747095473)
  ·
    refine ⟨135851142852786425810321605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181134857137048567747095473 135851142852786425810321605)
    ·
      refine ⟨25472089284897454839435301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135851142852786425810321605 25472089284897454839435301)
      ·
        refine ⟨4776016740918272782394119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25472089284897454839435301 4776016740918272782394119)
        ·
          refine ⟨7164025111377409173591179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776016740918272782394119 7164025111377409173591179)
          ·
            refine ⟨10746037667066113760386769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164025111377409173591179 10746037667066113760386769)
            ·
              refine ⟨8059528250299585320290077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10746037667066113760386769 8059528250299585320290077)
              ·
                refine ⟨3022323093862344495108779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8059528250299585320290077 3022323093862344495108779)
                ·
                  refine ⟨4533484640793516742663169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022323093862344495108779 4533484640793516742663169)
                  ·
                    refine ⟨3400113480595137556997377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4533484640793516742663169 3400113480595137556997377)
                    ·
                      refine ⟨2550085110446353167748033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400113480595137556997377 2550085110446353167748033)
                      ·
                        rfl

theorem cell23_4966273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_4966273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966273 prefixEnd_4966273 := by exact prefixLift 4966273
  have htrace : WordTrace (prefixWord ++ tailWord_4966273) baseStart_4966273 baseEnd_4966273 := by
    simpa [prefixWord, tailWord_4966273, baseEnd_4966273] using wordTrace_append hprefix tailTrace_4966273
  have hstable : (prefixWord ++ tailWord_4966273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966273).length < 2 ^ (prefixWord ++ tailWord_4966273).sum := by decide
  have hdescent : baseEnd_4966273 < baseStart_4966273 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966306 : List Nat := [3, 3, 1, 2, 3, 1, 3, 1, 2, 1, 3]
def baseStart_4966306 : Nat := 118140960795 + 4966306 * 2 ^ 59
def prefixEnd_4966306 : Nat := 4983230072969 + 3 ^ 40 * 4966306 * 2
def baseEnd_4966306 : Nat := 2550102055307951538635381

theorem tailTrace_4966306 : CollatzResearch.WordTrace tailWord_4966306 prefixEnd_4966306 2550102055307951538635381 := by
  unfold tailWord_4966306
  simp only [CollatzResearch.WordTrace]
  refine ⟨45284015186482253595761693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120757373830619342922031181 45284015186482253595761693)
  ·
    refine ⟨16981505694930845098410635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45284015186482253595761693 16981505694930845098410635)
    ·
      refine ⟨25472258542396267647615953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16981505694930845098410635 25472258542396267647615953)
      ·
        refine ⟨19104193906797200735711965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25472258542396267647615953 19104193906797200735711965)
        ·
          refine ⟨7164072715048950275891987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19104193906797200735711965 7164072715048950275891987)
          ·
            refine ⟨10746109072573425413837981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164072715048950275891987 10746109072573425413837981)
            ·
              refine ⟨4029790902215034530189243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10746109072573425413837981 4029790902215034530189243)
              ·
                refine ⟨6044686353322551795283865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029790902215034530189243 6044686353322551795283865)
                ·
                  refine ⟨4533514764991913846462899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6044686353322551795283865 4533514764991913846462899)
                  ·
                    refine ⟨6800272147487870769694349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533514764991913846462899 6800272147487870769694349)
                    ·
                      refine ⟨2550102055307951538635381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800272147487870769694349 2550102055307951538635381)
                      ·
                        rfl

theorem cell23_4966306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_4966306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966306 prefixEnd_4966306 := by exact prefixLift 4966306
  have htrace : WordTrace (prefixWord ++ tailWord_4966306) baseStart_4966306 baseEnd_4966306 := by
    simpa [prefixWord, tailWord_4966306, baseEnd_4966306] using wordTrace_append hprefix tailTrace_4966306
  have hstable : (prefixWord ++ tailWord_4966306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966306).length < 2 ^ (prefixWord ++ tailWord_4966306).sum := by decide
  have hdescent : baseEnd_4966306 < baseStart_4966306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966332 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 2, 1, 5]
def baseStart_4966332 : Nat := 118140960795 + 4966332 * 2 ^ 59
def prefixEnd_4966332 : Nat := 4983230072969 + 3 ^ 40 * 4966332 * 2
def baseEnd_4966332 : Nat := 2550115405804968436910261

theorem tailTrace_4966332 : CollatzResearch.WordTrace tailWord_4966332 prefixEnd_4966332 2550115405804968436910261 := by
  unfold tailWord_4966332
  simp only [CollatzResearch.WordTrace]
  refine ⟨90568504521917410411746625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120758006029223213882328833 90568504521917410411746625)
  ·
    refine ⟨67926378391438057808809969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90568504521917410411746625 67926378391438057808809969)
    ·
      refine ⟨50944783793578543356607477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67926378391438057808809969 50944783793578543356607477)
      ·
        refine ⟨4776073480647988439681951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50944783793578543356607477 4776073480647988439681951)
        ·
          refine ⟨7164110220971982659522927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776073480647988439681951 7164110220971982659522927)
          ·
            refine ⟨10746165331457973989284391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164110220971982659522927 10746165331457973989284391)
            ·
              refine ⟨16119247997186960983926587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746165331457973989284391 16119247997186960983926587)
              ·
                refine ⟨24178871995780441475889881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16119247997186960983926587 24178871995780441475889881)
                ·
                  refine ⟨18134153996835331106917411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24178871995780441475889881 18134153996835331106917411)
                  ·
                    refine ⟨27201230995252996660376117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18134153996835331106917411 27201230995252996660376117)
                    ·
                      refine ⟨2550115405804968436910261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27201230995252996660376117 2550115405804968436910261)
                      ·
                        rfl

theorem cell23_4966332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 2, 1, 5].length) (baseStart_4966332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966332 prefixEnd_4966332 := by exact prefixLift 4966332
  have htrace : WordTrace (prefixWord ++ tailWord_4966332) baseStart_4966332 baseEnd_4966332 := by
    simpa [prefixWord, tailWord_4966332, baseEnd_4966332] using wordTrace_append hprefix tailTrace_4966332
  have hstable : (prefixWord ++ tailWord_4966332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966332).length < 2 ^ (prefixWord ++ tailWord_4966332).sum := by decide
  have hdescent : baseEnd_4966332 < baseStart_4966332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966368 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4]
def baseStart_4966368 : Nat := 118140960795 + 4966368 * 2 ^ 59
def prefixEnd_4966368 : Nat := 4983230072969 + 3 ^ 40 * 4966368 * 2
def baseEnd_4966368 : Nat := 2550133891108530296060095

theorem tailTrace_4966368 : CollatzResearch.WordTrace tailWord_4966368 prefixEnd_4966368 2550133891108530296060095 := by
  unfold tailWord_4966368
  simp only [CollatzResearch.WordTrace]
  refine ⟨90569161035852199485901879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120758881381136265981202505 90569161035852199485901879)
  ·
    refine ⟨135853741553778299228852819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90569161035852199485901879 135853741553778299228852819)
    ·
      refine ⟨203780612330667448843279229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135853741553778299228852819 203780612330667448843279229)
      ·
        refine ⟨76417729624000293316229711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203780612330667448843279229 76417729624000293316229711)
        ·
          refine ⟨114626594436000439974344567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76417729624000293316229711 114626594436000439974344567)
          ·
            refine ⟨171939891654000659961516851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114626594436000439974344567 171939891654000659961516851)
            ·
              refine ⟨257909837481000989942275277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171939891654000659961516851 257909837481000989942275277)
              ·
                refine ⟨96716189055375371228353229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257909837481000989942275277 96716189055375371228353229)
                ·
                  refine ⟨36268570895765764210632461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96716189055375371228353229 36268570895765764210632461)
                  ·
                    refine ⟨13600714085912161578987173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36268570895765764210632461 13600714085912161578987173)
                    ·
                      refine ⟨2550133891108530296060095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13600714085912161578987173 2550133891108530296060095)
                      ·
                        rfl

theorem cell23_4966368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_4966368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966368 prefixEnd_4966368 := by exact prefixLift 4966368
  have htrace : WordTrace (prefixWord ++ tailWord_4966368) baseStart_4966368 baseEnd_4966368 := by
    simpa [prefixWord, tailWord_4966368, baseEnd_4966368] using wordTrace_append hprefix tailTrace_4966368
  have hstable : (prefixWord ++ tailWord_4966368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966368).length < 2 ^ (prefixWord ++ tailWord_4966368).sum := by decide
  have hdescent : baseEnd_4966368 < baseStart_4966368 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966382 : List Nat := [4, 1, 2, 1, 3, 2, 2, 1, 2, 5]
def baseStart_4966382 : Nat := 118140960795 + 4966382 * 2 ^ 59
def prefixEnd_4966382 : Nat := 4983230072969 + 3 ^ 40 * 4966382 * 2
def baseEnd_4966382 : Nat := 850047026612564413761677

theorem tailTrace_4966382 : CollatzResearch.WordTrace tailWord_4966382 prefixEnd_4966382 850047026612564413761677 := by
  unfold tailWord_4966382
  simp only [CollatzResearch.WordTrace]
  refine ⟨22642354086706709920351675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120759221795769119575208933 22642354086706709920351675)
  ·
    refine ⟨33963531130060064880527513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22642354086706709920351675 33963531130060064880527513)
    ·
      refine ⟨25472648347545048660395635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33963531130060064880527513 25472648347545048660395635)
      ·
        refine ⟨38208972521317572990593453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25472648347545048660395635 38208972521317572990593453)
        ·
          refine ⟨14328364695494089871472545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38208972521317572990593453 14328364695494089871472545)
          ·
            refine ⟨10746273521620567403604409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14328364695494089871472545 10746273521620567403604409)
            ·
              refine ⟨8059705141215425552703307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10746273521620567403604409 8059705141215425552703307)
              ·
                refine ⟨12089557711823138329054961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8059705141215425552703307 12089557711823138329054961)
                ·
                  refine ⟨9067168283867353746791221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12089557711823138329054961 9067168283867353746791221)
                  ·
                    refine ⟨850047026612564413761677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9067168283867353746791221 850047026612564413761677)
                    ·
                      rfl

theorem cell23_4966382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 1, 2, 5].length) (baseStart_4966382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966382 prefixEnd_4966382 := by exact prefixLift 4966382
  have htrace : WordTrace (prefixWord ++ tailWord_4966382) baseStart_4966382 baseEnd_4966382 := by
    simpa [prefixWord, tailWord_4966382, baseEnd_4966382] using wordTrace_append hprefix tailTrace_4966382
  have hstable : (prefixWord ++ tailWord_4966382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966382).length < 2 ^ (prefixWord ++ tailWord_4966382).sum := by decide
  have hdescent : baseEnd_4966382 < baseStart_4966382 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966436 : List Nat := [2, 3, 1, 4, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4966436 : Nat := 118140960795 + 4966436 * 2 ^ 59
def prefixEnd_4966436 : Nat := 4983230072969 + 3 ^ 40 * 4966436 * 2
def baseEnd_4966436 : Nat := 2550168807793036030009783

theorem tailTrace_4966436 : CollatzResearch.WordTrace tailWord_4966436 prefixEnd_4966436 2550168807793036030009783 := by
  unfold tailWord_4966436
  simp only [CollatzResearch.WordTrace]
  refine ⟨90570401117729023292639581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120760534823638697723519441 90570401117729023292639581)
  ·
    refine ⟨33963900419148383734739843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90570401117729023292639581 33963900419148383734739843)
    ·
      refine ⟨50945850628722575602109765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33963900419148383734739843 50945850628722575602109765)
      ·
        refine ⟨9552346992885482925395581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50945850628722575602109765 9552346992885482925395581)
        ·
          refine ⟨3582130122332056097023343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9552346992885482925395581 3582130122332056097023343)
          ·
            refine ⟨5373195183498084145535015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582130122332056097023343 5373195183498084145535015)
            ·
              refine ⟨8059792775247126218302523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373195183498084145535015 8059792775247126218302523)
              ·
                refine ⟨12089689162870689327453785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8059792775247126218302523 12089689162870689327453785)
                ·
                  refine ⟨9067266872153016995590339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12089689162870689327453785 9067266872153016995590339)
                  ·
                    refine ⟨13600900308229525493385509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9067266872153016995590339 13600900308229525493385509)
                    ·
                      refine ⟨2550168807793036030009783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13600900308229525493385509 2550168807793036030009783)
                      ·
                        rfl

theorem cell23_4966436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4966436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966436 prefixEnd_4966436 := by exact prefixLift 4966436
  have htrace : WordTrace (prefixWord ++ tailWord_4966436) baseStart_4966436 baseEnd_4966436 := by
    simpa [prefixWord, tailWord_4966436, baseEnd_4966436] using wordTrace_append hprefix tailTrace_4966436
  have hstable : (prefixWord ++ tailWord_4966436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966436).length < 2 ^ (prefixWord ++ tailWord_4966436).sum := by decide
  have hdescent : baseEnd_4966436 < baseStart_4966436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966439 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4966439 : Nat := 118140960795 + 4966439 * 2 ^ 59
def prefixEnd_4966439 : Nat := 4983230072969 + 3 ^ 40 * 4966439 * 2
def baseEnd_4966439 : Nat := 2550170348234999518272269

theorem tailTrace_4966439 : CollatzResearch.WordTrace tailWord_4966439 prefixEnd_4966439 2550170348234999518272269 := by
  unfold tailWord_4966439
  simp only [CollatzResearch.WordTrace]
  refine ⟨181140911654447178097638371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120760607769631452065092247 181140911654447178097638371)
  ·
    refine ⟨271711367481670767146457557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181140911654447178097638371 271711367481670767146457557)
    ·
      refine ⟨6368235175351658604995099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 271711367481670767146457557 6368235175351658604995099)
      ·
        refine ⟨9552352763027487907492649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368235175351658604995099 9552352763027487907492649)
        ·
          refine ⟨7164264572270615930619487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9552352763027487907492649 7164264572270615930619487)
          ·
            refine ⟨10746396858405923895929231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164264572270615930619487 10746396858405923895929231)
            ·
              refine ⟨16119595287608885843893847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746396858405923895929231 16119595287608885843893847)
              ·
                refine ⟨24179392931413328765840771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16119595287608885843893847 24179392931413328765840771)
                ·
                  refine ⟨36269089397119993148761157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24179392931413328765840771 36269089397119993148761157)
                  ·
                    refine ⟨6800454261959998715392717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36269089397119993148761157 6800454261959998715392717)
                    ·
                      refine ⟨2550170348234999518272269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800454261959998715392717 2550170348234999518272269)
                      ·
                        rfl

theorem cell23_4966439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4966439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966439 prefixEnd_4966439 := by exact prefixLift 4966439
  have htrace : WordTrace (prefixWord ++ tailWord_4966439) baseStart_4966439 baseEnd_4966439 := by
    simpa [prefixWord, tailWord_4966439, baseEnd_4966439] using wordTrace_append hprefix tailTrace_4966439
  have hstable : (prefixWord ++ tailWord_4966439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966439).length < 2 ^ (prefixWord ++ tailWord_4966439).sum := by decide
  have hdescent : baseEnd_4966439 < baseStart_4966439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966446 : List Nat := [4, 1, 3, 1, 1, 3, 2, 3, 1, 4]
def baseStart_4966446 : Nat := 118140960795 + 4966446 * 2 ^ 59
def prefixEnd_4966446 : Nat := 4983230072969 + 3 ^ 40 * 4966446 * 2
def baseEnd_4966446 : Nat := 850057980866526996961579

theorem tailTrace_4966446 : CollatzResearch.WordTrace tailWord_4966446 prefixEnd_4966446 850057980866526996961579 := by
  unfold tailWord_4966446
  simp only [CollatzResearch.WordTrace]
  refine ⟨22642645870677727286642899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120760777976947878862095461 22642645870677727286642899)
  ·
    refine ⟨33963968806016590929964349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22642645870677727286642899 33963968806016590929964349)
    ·
      refine ⟨12736488302256221598736631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33963968806016590929964349 12736488302256221598736631)
      ·
        refine ⟨19104732453384332398104947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12736488302256221598736631 19104732453384332398104947)
        ·
          refine ⟨28657098680076498597157421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19104732453384332398104947 28657098680076498597157421)
          ·
            refine ⟨10746412005028686973934033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28657098680076498597157421 10746412005028686973934033)
            ·
              refine ⟨8059809003771515230450525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10746412005028686973934033 8059809003771515230450525)
              ·
                refine ⟨3022428376414318211418947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8059809003771515230450525 3022428376414318211418947)
                ·
                  refine ⟨4533642564621477317128421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022428376414318211418947 4533642564621477317128421)
                  ·
                    refine ⟨850057980866526996961579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4533642564621477317128421 850057980866526996961579)
                    ·
                      rfl

theorem cell23_4966446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_4966446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966446 prefixEnd_4966446 := by exact prefixLift 4966446
  have htrace : WordTrace (prefixWord ++ tailWord_4966446) baseStart_4966446 baseEnd_4966446 := by
    simpa [prefixWord, tailWord_4966446, baseEnd_4966446] using wordTrace_append hprefix tailTrace_4966446
  have hstable : (prefixWord ++ tailWord_4966446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966446).length < 2 ^ (prefixWord ++ tailWord_4966446).sum := by decide
  have hdescent : baseEnd_4966446 < baseStart_4966446 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966505 : List Nat := [1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 4]
def baseStart_4966505 : Nat := 118140960795 + 4966505 * 2 ^ 59
def prefixEnd_4966505 : Nat := 4983230072969 + 3 ^ 40 * 4966505 * 2
def baseEnd_4966505 : Nat := 2550204237958196260046965

theorem tailTrace_4966505 : CollatzResearch.WordTrace tailWord_4966505 prefixEnd_4966505 2550204237958196260046965 := by
  unfold tailWord_4966505
  simp only [CollatzResearch.WordTrace]
  refine ⟨181143318872208071369540969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120762212581472047579693979 181143318872208071369540969)
  ·
    refine ⟨135857489154156053527155727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181143318872208071369540969 135857489154156053527155727)
    ·
      refine ⟨203786233731234080290733591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135857489154156053527155727 203786233731234080290733591)
      ·
        refine ⟨305679350596851120436100387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203786233731234080290733591 305679350596851120436100387)
        ·
          refine ⟨458519025895276680654150581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305679350596851120436100387 458519025895276680654150581)
          ·
            refine ⟨42986158677682188811326617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 458519025895276680654150581 42986158677682188811326617)
            ·
              refine ⟨32239619008261641608494963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42986158677682188811326617 32239619008261641608494963)
              ·
                refine ⟨48359428512392462412742445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32239619008261641608494963 48359428512392462412742445)
                ·
                  refine ⟨18134785692147173404778417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48359428512392462412742445 18134785692147173404778417)
                  ·
                    refine ⟨13601089269110380053583813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18134785692147173404778417 13601089269110380053583813)
                    ·
                      refine ⟨2550204237958196260046965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13601089269110380053583813 2550204237958196260046965)
                      ·
                        rfl

theorem cell23_4966505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 1, 3, 2, 4].length) (baseStart_4966505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966505 prefixEnd_4966505 := by exact prefixLift 4966505
  have htrace : WordTrace (prefixWord ++ tailWord_4966505) baseStart_4966505 baseEnd_4966505 := by
    simpa [prefixWord, tailWord_4966505, baseEnd_4966505] using wordTrace_append hprefix tailTrace_4966505
  have hstable : (prefixWord ++ tailWord_4966505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966505).length < 2 ^ (prefixWord ++ tailWord_4966505).sum := by decide
  have hdescent : baseEnd_4966505 < baseStart_4966505 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966512 : List Nat := [2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5]
def baseStart_4966512 : Nat := 118140960795 + 4966512 * 2 ^ 59
def prefixEnd_4966512 : Nat := 4983230072969 + 3 ^ 40 * 4966512 * 2
def baseEnd_4966512 : Nat := 2550207832322777732659433

theorem tailTrace_4966512 : CollatzResearch.WordTrace tailWord_4966512 prefixEnd_4966512 2550207832322777732659433 := by
  unfold tailWord_4966512
  simp only [CollatzResearch.WordTrace]
  refine ⟨90571787091591355782522895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120762382788788474376697193 90571787091591355782522895)
  ·
    refine ⟨135857680637387033673784343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90571787091591355782522895 135857680637387033673784343)
    ·
      refine ⟨203786520956080550510676515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135857680637387033673784343 203786520956080550510676515)
      ·
        refine ⟨305679781434120825766014773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203786520956080550510676515 305679781434120825766014773)
        ·
          refine ⟨28657479509448827415563885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 305679781434120825766014773 28657479509448827415563885)
          ·
            refine ⟨10746554816043310280836457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28657479509448827415563885 10746554816043310280836457)
            ·
              refine ⟨8059916112032482710627343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10746554816043310280836457 8059916112032482710627343)
              ·
                refine ⟨12089874168048724065941015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8059916112032482710627343 12089874168048724065941015)
                ·
                  refine ⟨18134811252073086098911523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12089874168048724065941015 18134811252073086098911523)
                  ·
                    refine ⟨27202216878109629148367285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18134811252073086098911523 27202216878109629148367285)
                    ·
                      refine ⟨2550207832322777732659433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27202216878109629148367285 2550207832322777732659433)
                      ·
                        rfl

theorem cell23_4966512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 5].length) (baseStart_4966512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966512 prefixEnd_4966512 := by exact prefixLift 4966512
  have htrace : WordTrace (prefixWord ++ tailWord_4966512) baseStart_4966512 baseEnd_4966512 := by
    simpa [prefixWord, tailWord_4966512, baseEnd_4966512] using wordTrace_append hprefix tailTrace_4966512
  have hstable : (prefixWord ++ tailWord_4966512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966512).length < 2 ^ (prefixWord ++ tailWord_4966512).sum := by decide
  have hdescent : baseEnd_4966512 < baseStart_4966512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966536 : List Nat := [2, 1, 3, 4, 1, 1, 4, 1, 2, 4]
def baseStart_4966536 : Nat := 118140960795 + 4966536 * 2 ^ 59
def prefixEnd_4966536 : Nat := 4983230072969 + 3 ^ 40 * 4966536 * 2
def baseEnd_4966536 : Nat := 850073385286161879586441

theorem tailTrace_4966536 : CollatzResearch.WordTrace tailWord_4966536 prefixEnd_4966536 850073385286161879586441 := by
  unfold tailWord_4966536
  simp only [CollatzResearch.WordTrace]
  refine ⟨90572224767547881831959731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120762966356730509109279641 90572224767547881831959731)
  ·
    refine ⟨135858337151321822747939597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90572224767547881831959731 135858337151321822747939597)
    ·
      refine ⟨50946876431745683530477349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135858337151321822747939597 50946876431745683530477349)
      ·
        refine ⟨9552539330952315661964503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50946876431745683530477349 9552539330952315661964503)
        ·
          refine ⟨14328808996428473492946755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9552539330952315661964503 14328808996428473492946755)
          ·
            refine ⟨21493213494642710239420133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14328808996428473492946755 21493213494642710239420133)
            ·
              refine ⟨4029977530245508169891275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21493213494642710239420133 4029977530245508169891275)
              ·
                refine ⟨6044966295368262254836913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4029977530245508169891275 6044966295368262254836913)
                ·
                  refine ⟨4533724721526196691127685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6044966295368262254836913 4533724721526196691127685)
                  ·
                    refine ⟨850073385286161879586441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4533724721526196691127685 850073385286161879586441)
                    ·
                      rfl

theorem cell23_4966536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 4, 1, 2, 4].length) (baseStart_4966536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966536 prefixEnd_4966536 := by exact prefixLift 4966536
  have htrace : WordTrace (prefixWord ++ tailWord_4966536) baseStart_4966536 baseEnd_4966536 := by
    simpa [prefixWord, tailWord_4966536, baseEnd_4966536] using wordTrace_append hprefix tailTrace_4966536
  have hstable : (prefixWord ++ tailWord_4966536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966536).length < 2 ^ (prefixWord ++ tailWord_4966536).sum := by decide
  have hdescent : baseEnd_4966536 < baseStart_4966536 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966559 : List Nat := [1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 3]
def baseStart_4966559 : Nat := 118140960795 + 4966559 * 2 ^ 59
def prefixEnd_4966559 : Nat := 4983230072969 + 3 ^ 40 * 4966559 * 2
def baseEnd_4966559 : Nat := 2550231965913539048771717

theorem tailTrace_4966559 : CollatzResearch.WordTrace tailWord_4966559 prefixEnd_4966559 2550231965913539048771717 := by
  unfold tailWord_4966559
  simp only [CollatzResearch.WordTrace]
  refine ⟨181145288414012438592006731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120763525609341625728004487 181145288414012438592006731)
  ·
    refine ⟨271717932621018657888010097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181145288414012438592006731 271717932621018657888010097)
    ·
      refine ⟨203788449465763993416007573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271717932621018657888010097 203788449465763993416007573)
      ·
        refine ⟨9552583568707687191375355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 203788449465763993416007573 9552583568707687191375355)
        ·
          refine ⟨14328875353061530787063033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9552583568707687191375355 14328875353061530787063033)
          ·
            refine ⟨10746656514796148090297275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14328875353061530787063033 10746656514796148090297275)
            ·
              refine ⟨16119984772194222135445913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746656514796148090297275 16119984772194222135445913)
              ·
                refine ⟨12089988579145666601584435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16119984772194222135445913 12089988579145666601584435)
                ·
                  refine ⟨18134982868718499902376653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12089988579145666601584435 18134982868718499902376653)
                  ·
                    refine ⟨6800618575769437463391245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18134982868718499902376653 6800618575769437463391245)
                    ·
                      refine ⟨2550231965913539048771717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800618575769437463391245 2550231965913539048771717)
                      ·
                        rfl

theorem cell23_4966559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_4966559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966559 prefixEnd_4966559 := by exact prefixLift 4966559
  have htrace : WordTrace (prefixWord ++ tailWord_4966559) baseStart_4966559 baseEnd_4966559 := by
    simpa [prefixWord, tailWord_4966559, baseEnd_4966559] using wordTrace_append hprefix tailTrace_4966559
  have hstable : (prefixWord ++ tailWord_4966559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966559).length < 2 ^ (prefixWord ++ tailWord_4966559).sum := by decide
  have hdescent : baseEnd_4966559 < baseStart_4966559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966575 : List Nat := [1, 1, 2, 1, 2, 3, 1, 4, 2, 6]
def baseStart_4966575 : Nat := 118140960795 + 4966575 * 2 ^ 59
def prefixEnd_4966575 : Nat := 4983230072969 + 3 ^ 40 * 4966575 * 2
def baseEnd_4966575 : Nat := 850080060534670328723881

theorem tailTrace_4966575 : CollatzResearch.WordTrace tailWord_4966575 prefixEnd_4966575 850080060534670328723881 := by
  unfold tailWord_4966575
  simp only [CollatzResearch.WordTrace]
  refine ⟨181145871981954473324589179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120763914654636315549726119 181145871981954473324589179)
  ·
    refine ⟨271718807972931709986883769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181145871981954473324589179 271718807972931709986883769)
    ·
      refine ⟨203789105979698782490162827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271718807972931709986883769 203789105979698782490162827)
      ·
        refine ⟨305683658969548173735244241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203789105979698782490162827 305683658969548173735244241)
        ·
          refine ⟨229262744227161130301433181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305683658969548173735244241 229262744227161130301433181)
          ·
            refine ⟨85973529085185423863037443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229262744227161130301433181 85973529085185423863037443)
            ·
              refine ⟨128960293627778135794556165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85973529085185423863037443 128960293627778135794556165)
              ·
                refine ⟨24180055055208400461479281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128960293627778135794556165 24180055055208400461479281)
                ·
                  refine ⟨18135041291406300346109461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24180055055208400461479281 18135041291406300346109461)
                  ·
                    refine ⟨850080060534670328723881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18135041291406300346109461 850080060534670328723881)
                    ·
                      rfl

theorem cell23_4966575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 4, 2, 6].length) (baseStart_4966575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966575 prefixEnd_4966575 := by exact prefixLift 4966575
  have htrace : WordTrace (prefixWord ++ tailWord_4966575) baseStart_4966575 baseEnd_4966575 := by
    simpa [prefixWord, tailWord_4966575, baseEnd_4966575] using wordTrace_append hprefix tailTrace_4966575
  have hstable : (prefixWord ++ tailWord_4966575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966575).length < 2 ^ (prefixWord ++ tailWord_4966575).sum := by decide
  have hdescent : baseEnd_4966575 < baseStart_4966575 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966577 : List Nat := [1, 2, 2, 5, 2, 2, 2, 2, 1, 2, 2]
def baseStart_4966577 : Nat := 118140960795 + 4966577 * 2 ^ 59
def prefixEnd_4966577 : Nat := 4983230072969 + 3 ^ 40 * 4966577 * 2
def baseEnd_4966577 : Nat := 2550241208565319978346635

theorem tailTrace_4966577 : CollatzResearch.WordTrace tailWord_4966577 prefixEnd_4966577 2550241208565319978346635 := by
  unfold tailWord_4966577
  simp only [CollatzResearch.WordTrace]
  refine ⟨181145944927947227666161985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120763963285298151777441323 181145944927947227666161985)
  ·
    refine ⟨135859458695960420749621489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181145944927947227666161985 135859458695960420749621489)
    ·
      refine ⟨101894594021970315562216117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135859458695960420749621489 101894594021970315562216117)
      ·
        refine ⟨9552618189559717083957761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101894594021970315562216117 9552618189559717083957761)
        ·
          refine ⟨7164463642169787812968321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9552618189559717083957761 7164463642169787812968321)
          ·
            refine ⟨5373347731627340859726241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7164463642169787812968321 5373347731627340859726241)
            ·
              refine ⟨4030010798720505644794681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5373347731627340859726241 4030010798720505644794681)
              ·
                refine ⟨3022508099040379233596011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4030010798720505644794681 3022508099040379233596011)
                ·
                  refine ⟨4533762148560568850394017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022508099040379233596011 4533762148560568850394017)
                  ·
                    refine ⟨3400321611420426637795513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4533762148560568850394017 3400321611420426637795513)
                    ·
                      refine ⟨2550241208565319978346635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400321611420426637795513 2550241208565319978346635)
                      ·
                        rfl

theorem cell23_4966577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 2, 2, 1, 2, 2].length) (baseStart_4966577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966577 prefixEnd_4966577 := by exact prefixLift 4966577
  have htrace : WordTrace (prefixWord ++ tailWord_4966577) baseStart_4966577 baseEnd_4966577 := by
    simpa [prefixWord, tailWord_4966577, baseEnd_4966577] using wordTrace_append hprefix tailTrace_4966577
  have hstable : (prefixWord ++ tailWord_4966577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966577).length < 2 ^ (prefixWord ++ tailWord_4966577).sum := by decide
  have hdescent : baseEnd_4966577 < baseStart_4966577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966592 : List Nat := [2, 1, 1, 2, 5, 2, 1, 1, 2, 6]
def baseStart_4966592 : Nat := 118140960795 + 4966592 * 2 ^ 59
def prefixEnd_4966592 : Nat := 4983230072969 + 3 ^ 40 * 4966592 * 2
def baseEnd_4966592 : Nat := 850082970258379139886355

theorem tailTrace_4966592 : CollatzResearch.WordTrace tailWord_4966592 prefixEnd_4966592 850082970258379139886355 := by
  unfold tailWord_4966592
  simp only [CollatzResearch.WordTrace]
  refine ⟨90573246011446442613979015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120764328015261923485305353 90573246011446442613979015)
  ·
    refine ⟨135859869017169663920968523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90573246011446442613979015 135859869017169663920968523)
    ·
      refine ⟨203789803525754495881452785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135859869017169663920968523 203789803525754495881452785)
      ·
        refine ⟨152842352644315871911089589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203789803525754495881452785 152842352644315871911089589)
        ·
          refine ⟨14328970560404612991664649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152842352644315871911089589 14328970560404612991664649)
          ·
            refine ⟨10746727920303459743748487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14328970560404612991664649 10746727920303459743748487)
            ·
              refine ⟨16120091880455189615622731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746727920303459743748487 16120091880455189615622731)
              ·
                refine ⟨24180137820682784423434097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16120091880455189615622731 24180137820682784423434097)
                ·
                  refine ⟨18135103365512088317575573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24180137820682784423434097 18135103365512088317575573)
                  ·
                    refine ⟨850082970258379139886355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18135103365512088317575573 850082970258379139886355)
                    ·
                      rfl

theorem cell23_4966592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 2, 6].length) (baseStart_4966592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966592 prefixEnd_4966592 := by exact prefixLift 4966592
  have htrace : WordTrace (prefixWord ++ tailWord_4966592) baseStart_4966592 baseEnd_4966592 := by
    simpa [prefixWord, tailWord_4966592, baseEnd_4966592] using wordTrace_append hprefix tailTrace_4966592
  have hstable : (prefixWord ++ tailWord_4966592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966592).length < 2 ^ (prefixWord ++ tailWord_4966592).sum := by decide
  have hdescent : baseEnd_4966592 < baseStart_4966592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966599 : List Nat := [1, 1, 4, 1, 1, 1, 1, 1, 8, 2, 2]
def baseStart_4966599 : Nat := 118140960795 + 4966599 * 2 ^ 59
def prefixEnd_4966599 : Nat := 4983230072969 + 3 ^ 40 * 4966599 * 2
def baseEnd_4966599 : Nat := 2550252505139718892271533

theorem tailTrace_4966599 : CollatzResearch.WordTrace tailWord_4966599 prefixEnd_4966599 2550252505139718892271533 := by
  unfold tailWord_4966599
  simp only [CollatzResearch.WordTrace]
  refine ⟨181146747333867525423462851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120764498222578350282308567 181146747333867525423462851)
  ·
    refine ⟨271720121000801288135194277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181146747333867525423462851 271720121000801288135194277)
    ·
      refine ⟨50947522687650241525348927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 271720121000801288135194277 50947522687650241525348927)
      ·
        refine ⟨76421284031475362288023391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50947522687650241525348927 76421284031475362288023391)
        ·
          refine ⟨114631926047213043432035087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76421284031475362288023391 114631926047213043432035087)
          ·
            refine ⟨171947889070819565148052631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114631926047213043432035087 171947889070819565148052631)
            ·
              refine ⟨257921833606229347722078947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171947889070819565148052631 257921833606229347722078947)
              ·
                refine ⟨386882750409344021583118421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 257921833606229347722078947 386882750409344021583118421)
                ·
                  refine ⟨4533782231359500252927169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 386882750409344021583118421 4533782231359500252927169)
                  ·
                    refine ⟨3400336673519625189695377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4533782231359500252927169 3400336673519625189695377)
                    ·
                      refine ⟨2550252505139718892271533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400336673519625189695377 2550252505139718892271533)
                      ·
                        rfl

theorem cell23_4966599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 1, 8, 2, 2].length) (baseStart_4966599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966599 prefixEnd_4966599 := by exact prefixLift 4966599
  have htrace : WordTrace (prefixWord ++ tailWord_4966599) baseStart_4966599 baseEnd_4966599 := by
    simpa [prefixWord, tailWord_4966599, baseEnd_4966599] using wordTrace_append hprefix tailTrace_4966599
  have hstable : (prefixWord ++ tailWord_4966599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966599).length < 2 ^ (prefixWord ++ tailWord_4966599).sum := by decide
  have hdescent : baseEnd_4966599 < baseStart_4966599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966602 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3]
def baseStart_4966602 : Nat := 118140960795 + 4966602 * 2 ^ 59
def prefixEnd_4966602 : Nat := 4983230072969 + 3 ^ 40 * 4966602 * 2
def baseEnd_4966602 : Nat := 2550254045581682380534019

theorem tailTrace_4966602 : CollatzResearch.WordTrace tailWord_4966602 prefixEnd_4966602 2550254045581682380534019 := by
  unfold tailWord_4966602
  simp only [CollatzResearch.WordTrace]
  refine ⟨45286714188214164233955515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120764571168571104623881373 45286714188214164233955515)
  ·
    refine ⟨67930071282321246350933273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45286714188214164233955515 67930071282321246350933273)
    ·
      refine ⟨50947553461740934763199955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67930071282321246350933273 50947553461740934763199955)
      ·
        refine ⟨76421330192611402144799933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50947553461740934763199955 76421330192611402144799933)
        ·
          refine ⟨28657998822229275804299975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76421330192611402144799933 28657998822229275804299975)
          ·
            refine ⟨42986998233343913706449963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28657998822229275804299975 42986998233343913706449963)
            ·
              refine ⟨64480497350015870559674945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42986998233343913706449963 64480497350015870559674945)
              ·
                refine ⟨48360373012511902919756209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64480497350015870559674945 48360373012511902919756209)
                ·
                  refine ⟨36270279759383927189817157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48360373012511902919756209 36270279759383927189817157)
                  ·
                    refine ⟨6800677454884486348090717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36270279759383927189817157 6800677454884486348090717)
                    ·
                      refine ⟨2550254045581682380534019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800677454884486348090717 2550254045581682380534019)
                      ·
                        rfl

theorem cell23_4966602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3].length) (baseStart_4966602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966602 prefixEnd_4966602 := by exact prefixLift 4966602
  have htrace : WordTrace (prefixWord ++ tailWord_4966602) baseStart_4966602 baseEnd_4966602 := by
    simpa [prefixWord, tailWord_4966602, baseEnd_4966602] using wordTrace_append hprefix tailTrace_4966602
  have hstable : (prefixWord ++ tailWord_4966602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966602).length < 2 ^ (prefixWord ++ tailWord_4966602).sum := by decide
  have hdescent : baseEnd_4966602 < baseStart_4966602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966615 : List Nat := [1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 7]
def baseStart_4966615 : Nat := 118140960795 + 4966615 * 2 ^ 59
def prefixEnd_4966615 : Nat := 4983230072969 + 3 ^ 40 * 4966615 * 2
def baseEnd_4966615 : Nat := 2550260720830190829671459

theorem tailTrace_4966615 : CollatzResearch.WordTrace tailWord_4966615 prefixEnd_4966615 2550260720830190829671459 := by
  unfold tailWord_4966615
  simp only [CollatzResearch.WordTrace]
  refine ⟨181147330901809560156045299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120764887267873040104030199 181147330901809560156045299)
  ·
    refine ⟨271720996352714340234067949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181147330901809560156045299 271720996352714340234067949)
    ·
      refine ⟨101895373632267877587775481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271720996352714340234067949 101895373632267877587775481)
      ·
        refine ⟨76421530224200908190831611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101895373632267877587775481 76421530224200908190831611)
        ·
          refine ⟨114632295336301362286247417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76421530224200908190831611 114632295336301362286247417)
          ·
            refine ⟨85974221502226021714685563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114632295336301362286247417 85974221502226021714685563)
            ·
              refine ⟨128961332253339032572028345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85974221502226021714685563 128961332253339032572028345)
              ·
                refine ⟨96720999190004274429021259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128961332253339032572028345 96720999190004274429021259)
                ·
                  refine ⟨145081498785006411643531889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96720999190004274429021259 145081498785006411643531889)
                  ·
                    refine ⟨108811124088754808732648917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 145081498785006411643531889 108811124088754808732648917)
                    ·
                      refine ⟨2550260720830190829671459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108811124088754808732648917 2550260720830190829671459)
                      ·
                        rfl

theorem cell23_4966615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 2, 1, 2, 7].length) (baseStart_4966615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966615 prefixEnd_4966615 := by exact prefixLift 4966615
  have htrace : WordTrace (prefixWord ++ tailWord_4966615) baseStart_4966615 baseEnd_4966615 := by
    simpa [prefixWord, tailWord_4966615, baseEnd_4966615] using wordTrace_append hprefix tailTrace_4966615
  have hstable : (prefixWord ++ tailWord_4966615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966615).length < 2 ^ (prefixWord ++ tailWord_4966615).sum := by decide
  have hdescent : baseEnd_4966615 < baseStart_4966615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966620 : List Nat := [2, 2, 5, 2, 1, 1, 1, 3, 1, 3, 2]
def baseStart_4966620 : Nat := 118140960795 + 4966620 * 2 ^ 59
def prefixEnd_4966620 : Nat := 4983230072969 + 3 ^ 40 * 4966620 * 2
def baseEnd_4966620 : Nat := 2550263288233463310108937

theorem tailTrace_4966620 : CollatzResearch.WordTrace tailWord_4966620 prefixEnd_4966620 2550263288233463310108937 := by
  unfold tailWord_4966620
  simp only [CollatzResearch.WordTrace]
  refine ⟨90573756633395723004988657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120765008844527630673318209 90573756633395723004988657)
  ·
    refine ⟨67930317475046792253741493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90573756633395723004988657 67930317475046792253741493)
    ·
      refine ⟨6368467263285636773788265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67930317475046792253741493 6368467263285636773788265)
      ·
        refine ⟨4776350447464227580341199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6368467263285636773788265 4776350447464227580341199)
        ·
          refine ⟨7164525671196341370511799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4776350447464227580341199 7164525671196341370511799)
          ·
            refine ⟨10746788506794512055767699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7164525671196341370511799 10746788506794512055767699)
            ·
              refine ⟨16120182760191768083651549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10746788506794512055767699 16120182760191768083651549)
              ·
                refine ⟨6045068535071913031369331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16120182760191768083651549 6045068535071913031369331)
                ·
                  refine ⟨9067602802607869547053997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045068535071913031369331 9067602802607869547053997)
                  ·
                    refine ⟨3400351050977951080145249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9067602802607869547053997 3400351050977951080145249)
                    ·
                      refine ⟨2550263288233463310108937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400351050977951080145249 2550263288233463310108937)
                      ·
                        rfl

theorem cell23_4966620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 3, 1, 3, 2].length) (baseStart_4966620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966620 prefixEnd_4966620 := by exact prefixLift 4966620
  have htrace : WordTrace (prefixWord ++ tailWord_4966620) baseStart_4966620 baseEnd_4966620 := by
    simpa [prefixWord, tailWord_4966620, baseEnd_4966620] using wordTrace_append hprefix tailTrace_4966620
  have hstable : (prefixWord ++ tailWord_4966620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966620).length < 2 ^ (prefixWord ++ tailWord_4966620).sum := by decide
  have hdescent : baseEnd_4966620 < baseStart_4966620 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966639 : List Nat := [1, 1, 2, 1, 6, 1, 2, 4, 5]
def baseStart_4966639 : Nat := 118140960795 + 4966639 * 2 ^ 59
def prefixEnd_4966639 : Nat := 4983230072969 + 3 ^ 40 * 4966639 * 2
def baseEnd_4966639 : Nat := 283363671596210970641261

theorem tailTrace_4966639 : CollatzResearch.WordTrace tailWord_4966639 prefixEnd_4966639 283363671596210970641261 := by
  unfold tailWord_4966639
  simp only [CollatzResearch.WordTrace]
  refine ⟨181148206253722612254918971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120765470835815074836612647 181148206253722612254918971)
  ·
    refine ⟨271722309380583918382378457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181148206253722612254918971 271722309380583918382378457)
    ·
      refine ⟨203791732035437938786783843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271722309380583918382378457 203791732035437938786783843)
      ·
        refine ⟨305687598053156908180175765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203791732035437938786783843 305687598053156908180175765)
        ·
          refine ⟨14329106158741730070945739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 305687598053156908180175765 14329106158741730070945739)
          ·
            refine ⟨21493659238112595106418609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14329106158741730070945739 21493659238112595106418609)
            ·
              refine ⟨16120244428584446329813957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21493659238112595106418609 16120244428584446329813957)
              ·
                refine ⟨3022545830359583686840117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16120244428584446329813957 3022545830359583686840117)
                ·
                  refine ⟨283363671596210970641261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3022545830359583686840117 283363671596210970641261)
                  ·
                    rfl

theorem cell23_4966639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 2, 4, 5].length) (baseStart_4966639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966639 prefixEnd_4966639 := by exact prefixLift 4966639
  have htrace : WordTrace (prefixWord ++ tailWord_4966639) baseStart_4966639 baseEnd_4966639 := by
    simpa [prefixWord, tailWord_4966639, baseEnd_4966639] using wordTrace_append hprefix tailTrace_4966639
  have hstable : (prefixWord ++ tailWord_4966639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966639).length < 2 ^ (prefixWord ++ tailWord_4966639).sum := by decide
  have hdescent : baseEnd_4966639 < baseStart_4966639 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966652 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 1, 7]
def baseStart_4966652 : Nat := 118140960795 + 4966652 * 2 ^ 59
def prefixEnd_4966652 : Nat := 4983230072969 + 3 ^ 40 * 4966652 * 2
def baseEnd_4966652 : Nat := 850093239871469061636263

theorem tailTrace_4966652 : CollatzResearch.WordTrace tailWord_4966652 prefixEnd_4966652 850093239871469061636263 := by
  unfold tailWord_4966652
  simp only [CollatzResearch.WordTrace]
  refine ⟨90574340201337757737571105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120765786935117010316761473 90574340201337757737571105)
  ·
    refine ⟨67930755151003318303178329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90574340201337757737571105 67930755151003318303178329)
    ·
      refine ⟨50948066363252488727383747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67930755151003318303178329 50948066363252488727383747)
      ·
        refine ⟨76422099544878733091075621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50948066363252488727383747 76422099544878733091075621)
        ·
          refine ⟨14329143664664762454576679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76422099544878733091075621 14329143664664762454576679)
          ·
            refine ⟨21493715496997143681865019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14329143664664762454576679 21493715496997143681865019)
            ·
              refine ⟨32240573245495715522797529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21493715496997143681865019 32240573245495715522797529)
              ·
                refine ⟨24180429934121786642098147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32240573245495715522797529 24180429934121786642098147)
                ·
                  refine ⟨36270644901182679963147221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24180429934121786642098147 36270644901182679963147221)
                  ·
                    refine ⟨850093239871469061636263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36270644901182679963147221 850093239871469061636263)
                    ·
                      rfl

theorem cell23_4966652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 1, 7].length) (baseStart_4966652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966652 prefixEnd_4966652 := by exact prefixLift 4966652
  have htrace : WordTrace (prefixWord ++ tailWord_4966652) baseStart_4966652 baseEnd_4966652 := by
    simpa [prefixWord, tailWord_4966652, baseEnd_4966652] using wordTrace_append hprefix tailTrace_4966652
  have hstable : (prefixWord ++ tailWord_4966652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966652).length < 2 ^ (prefixWord ++ tailWord_4966652).sum := by decide
  have hdescent : baseEnd_4966652 < baseStart_4966652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966686 : List Nat := [4, 3, 2, 1, 1, 1, 1, 1, 4, 5]
def baseStart_4966686 : Nat := 118140960795 + 4966686 * 2 ^ 59
def prefixEnd_4966686 : Nat := 4983230072969 + 3 ^ 40 * 4966686 * 2
def baseEnd_4966686 : Nat := 850099059318886683961211

theorem tailTrace_4966686 : CollatzResearch.WordTrace tailWord_4966686 prefixEnd_4966686 850099059318886683961211 := by
  unfold tailWord_4966686
  simp only [CollatzResearch.WordTrace]
  refine ⟨22643740060569042410234989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120766613656368226187919941 22643740060569042410234989)
  ·
    refine ⟨8491402522713390903838121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22643740060569042410234989 8491402522713390903838121)
    ·
      refine ⟨6368551892035043177878591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8491402522713390903838121 6368551892035043177878591)
      ·
        refine ⟨9552827838052564766817887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6368551892035043177878591 9552827838052564766817887)
        ·
          refine ⟨14329241757078847150226831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9552827838052564766817887 14329241757078847150226831)
          ·
            refine ⟨21493862635618270725340247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14329241757078847150226831 21493862635618270725340247)
            ·
              refine ⟨32240793953427406088010371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21493862635618270725340247 32240793953427406088010371)
              ·
                refine ⟨48361190930141109132015557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32240793953427406088010371 48361190930141109132015557)
                ·
                  refine ⟨9067723299401457962252917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48361190930141109132015557 9067723299401457962252917)
                  ·
                    refine ⟨850099059318886683961211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9067723299401457962252917 850099059318886683961211)
                    ·
                      rfl

theorem cell23_4966686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_4966686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966686 prefixEnd_4966686 := by exact prefixLift 4966686
  have htrace : WordTrace (prefixWord ++ tailWord_4966686) baseStart_4966686 baseEnd_4966686 := by
    simpa [prefixWord, tailWord_4966686, baseEnd_4966686] using wordTrace_append hprefix tailTrace_4966686
  have hstable : (prefixWord ++ tailWord_4966686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966686).length < 2 ^ (prefixWord ++ tailWord_4966686).sum := by decide
  have hdescent : baseEnd_4966686 < baseStart_4966686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966689 : List Nat := [1, 2, 3, 2, 1, 1, 2, 1, 4, 4, 2]
def baseStart_4966689 : Nat := 118140960795 + 4966689 * 2 ^ 59
def prefixEnd_4966689 : Nat := 4983230072969 + 3 ^ 40 * 4966689 * 2
def baseEnd_4966689 : Nat := 2550298718398623540146119

theorem tailTrace_4966689 : CollatzResearch.WordTrace tailWord_4966689 prefixEnd_4966689 2550298718398623540146119 := by
  unfold tailWord_4966689
  simp only [CollatzResearch.WordTrace]
  refine ⟨181150029903541470794239121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120766686602360980529492747 181150029903541470794239121)
  ·
    refine ⟨135862522427656103095679341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181150029903541470794239121 135862522427656103095679341)
    ·
      refine ⟨50948445910371038660879753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135862522427656103095679341 50948445910371038660879753)
      ·
        refine ⟨38211334432778278995659815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50948445910371038660879753 38211334432778278995659815)
        ·
          refine ⟨57317001649167418493489723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38211334432778278995659815 57317001649167418493489723)
          ·
            refine ⟨85975502473751127740234585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57317001649167418493489723 85975502473751127740234585)
            ·
              refine ⟨64481626855313345805175939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85975502473751127740234585 64481626855313345805175939)
              ·
                refine ⟨96722440282970018707763909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64481626855313345805175939 96722440282970018707763909)
                ·
                  refine ⟨18135457553056878507705733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96722440282970018707763909 18135457553056878507705733)
                  ·
                    refine ⟨3400398291198164720194825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18135457553056878507705733 3400398291198164720194825)
                    ·
                      refine ⟨2550298718398623540146119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400398291198164720194825 2550298718398623540146119)
                      ·
                        rfl

theorem cell23_4966689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 4, 4, 2].length) (baseStart_4966689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966689 prefixEnd_4966689 := by exact prefixLift 4966689
  have htrace : WordTrace (prefixWord ++ tailWord_4966689) baseStart_4966689 baseEnd_4966689 := by
    simpa [prefixWord, tailWord_4966689, baseEnd_4966689] using wordTrace_append hprefix tailTrace_4966689
  have hstable : (prefixWord ++ tailWord_4966689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966689).length < 2 ^ (prefixWord ++ tailWord_4966689).sum := by decide
  have hdescent : baseEnd_4966689 < baseStart_4966689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966709 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 3]
def baseStart_4966709 : Nat := 118140960795 + 4966709 * 2 ^ 59
def prefixEnd_4966709 : Nat := 4983230072969 + 3 ^ 40 * 4966709 * 2
def baseEnd_4966709 : Nat := 2550308988011713461896027

theorem tailTrace_4966709 : CollatzResearch.WordTrace tailWord_4966709 prefixEnd_4966709 2550308988011713461896027 := by
  unfold tailWord_4966709
  simp only [CollatzResearch.WordTrace]
  refine ⟨181150759363469014209967181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120767172908979342806644787 181150759363469014209967181)
  ·
    refine ⟨67931534761300880328737693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181150759363469014209967181 67931534761300880328737693)
    ·
      refine ⟨25474325535487830123276635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67931534761300880328737693 25474325535487830123276635)
      ·
        refine ⟨38211488303231745184914953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25474325535487830123276635 38211488303231745184914953)
        ·
          refine ⟨28658616227423808888686215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38211488303231745184914953 28658616227423808888686215)
          ·
            refine ⟨42987924341135713333029323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28658616227423808888686215 42987924341135713333029323)
            ·
              refine ⟨64481886511703569999543985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42987924341135713333029323 64481886511703569999543985)
              ·
                refine ⟨48361414883777677499657989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64481886511703569999543985 48361414883777677499657989)
                ·
                  refine ⟨9067765290708314531185873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48361414883777677499657989 9067765290708314531185873)
                  ·
                    refine ⟨6800823968031235898389405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9067765290708314531185873 6800823968031235898389405)
                    ·
                      refine ⟨2550308988011713461896027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800823968031235898389405 2550308988011713461896027)
                      ·
                        rfl

theorem cell23_4966709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_4966709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966709 prefixEnd_4966709 := by exact prefixLift 4966709
  have htrace : WordTrace (prefixWord ++ tailWord_4966709) baseStart_4966709 baseEnd_4966709 := by
    simpa [prefixWord, tailWord_4966709, baseEnd_4966709] using wordTrace_append hprefix tailTrace_4966709
  have hstable : (prefixWord ++ tailWord_4966709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966709).length < 2 ^ (prefixWord ++ tailWord_4966709).sum := by decide
  have hdescent : baseEnd_4966709 < baseStart_4966709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966739 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 3]
def baseStart_4966739 : Nat := 118140960795 + 4966739 * 2 ^ 59
def prefixEnd_4966739 : Nat := 4983230072969 + 3 ^ 40 * 4966739 * 2
def baseEnd_4966739 : Nat := 2550324392431348344520889

theorem tailTrace_4966739 : CollatzResearch.WordTrace tailWord_4966739 prefixEnd_4966739 2550324392431348344520889 := by
  unfold tailWord_4966739
  simp only [CollatzResearch.WordTrace]
  refine ⟨181151853553360329333559271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120767902368906886222372847 181151853553360329333559271)
  ·
    refine ⟨271727780330040494000338907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181151853553360329333559271 271727780330040494000338907)
    ·
      refine ⟨407591670495060741000508361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271727780330040494000338907 407591670495060741000508361)
      ·
        refine ⟨305693752871295555750381271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407591670495060741000508361 305693752871295555750381271)
        ·
          refine ⟨458540629306943333625571907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305693752871295555750381271 458540629306943333625571907)
          ·
            refine ⟨687810943960415000438357861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458540629306943333625571907 687810943960415000438357861)
            ·
              refine ⟨128964551992577812582192099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 687810943960415000438357861 128964551992577812582192099)
              ·
                refine ⟨193446827988866718873288149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128964551992577812582192099 193446827988866718873288149)
                ·
                  refine ⟨4533910030989063723592691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 193446827988866718873288149 4533910030989063723592691)
                  ·
                    refine ⟨6800865046483595585389037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533910030989063723592691 6800865046483595585389037)
                    ·
                      refine ⟨2550324392431348344520889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800865046483595585389037 2550324392431348344520889)
                      ·
                        rfl

theorem cell23_4966739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 7, 1, 3].length) (baseStart_4966739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966739 prefixEnd_4966739 := by exact prefixLift 4966739
  have htrace : WordTrace (prefixWord ++ tailWord_4966739) baseStart_4966739 baseEnd_4966739 := by
    simpa [prefixWord, tailWord_4966739, baseEnd_4966739] using wordTrace_append hprefix tailTrace_4966739
  have hstable : (prefixWord ++ tailWord_4966739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966739).length < 2 ^ (prefixWord ++ tailWord_4966739).sum := by decide
  have hdescent : baseEnd_4966739 < baseStart_4966739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966756 : List Nat := [2, 3, 1, 1, 3, 1, 2, 3, 3, 1, 3]
def baseStart_4966756 : Nat := 118140960795 + 4966756 * 2 ^ 59
def prefixEnd_4966756 : Nat := 4983230072969 + 3 ^ 40 * 4966756 * 2
def baseEnd_4966756 : Nat := 2550333121602474778008311

theorem tailTrace_4966756 : CollatzResearch.WordTrace tailWord_4966756 prefixEnd_4966756 2550333121602474778008311 := by
  unfold tailWord_4966756
  simp only [CollatzResearch.WordTrace]
  refine ⟨90576236797149370618464061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120768315729532494157952081 90576236797149370618464061)
  ·
    refine ⟨33966088798931013981924023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90576236797149370618464061 33966088798931013981924023)
    ·
      refine ⟨50949133198396520972886035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33966088798931013981924023 50949133198396520972886035)
      ·
        refine ⟨76423699797594781459329053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50949133198396520972886035 76423699797594781459329053)
        ·
          refine ⟨28658887424098043047248395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76423699797594781459329053 28658887424098043047248395)
          ·
            refine ⟨42988331136147064570872593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28658887424098043047248395 42988331136147064570872593)
            ·
              refine ⟨32241248352110298428154445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42988331136147064570872593 32241248352110298428154445)
              ·
                refine ⟨12090468132041361910557917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32241248352110298428154445 12090468132041361910557917)
                ·
                  refine ⟨4533925549515510716459219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12090468132041361910557917 4533925549515510716459219)
                  ·
                    refine ⟨6800888324273266074688829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533925549515510716459219 6800888324273266074688829)
                    ·
                      refine ⟨2550333121602474778008311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800888324273266074688829 2550333121602474778008311)
                      ·
                        rfl

theorem cell23_4966756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 3, 3, 1, 3].length) (baseStart_4966756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966756 prefixEnd_4966756 := by exact prefixLift 4966756
  have htrace : WordTrace (prefixWord ++ tailWord_4966756) baseStart_4966756 baseEnd_4966756 := by
    simpa [prefixWord, tailWord_4966756, baseEnd_4966756] using wordTrace_append hprefix tailTrace_4966756
  have hstable : (prefixWord ++ tailWord_4966756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966756).length < 2 ^ (prefixWord ++ tailWord_4966756).sum := by decide
  have hdescent : baseEnd_4966756 < baseStart_4966756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966759 : List Nat := [1, 1, 5, 1, 3, 1, 1, 2, 3, 5]
def baseStart_4966759 : Nat := 118140960795 + 4966759 * 2 ^ 59
def prefixEnd_4966759 : Nat := 4983230072969 + 3 ^ 40 * 4966759 * 2
def baseEnd_4966759 : Nat := 850111554014812755423599

theorem tailTrace_4966759 : CollatzResearch.WordTrace tailWord_4966759 prefixEnd_4966759 850111554014812755423599 := by
  unfold tailWord_4966759
  simp only [CollatzResearch.WordTrace]
  refine ⟨181152583013287872749287331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120768388675525248499524887 181152583013287872749287331)
  ·
    refine ⟨271728874519931809123930997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181152583013287872749287331 271728874519931809123930997)
    ·
      refine ⟨25474581986243607105368531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271728874519931809123930997 25474581986243607105368531)
      ·
        refine ⟨38211872979365410658052797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25474581986243607105368531 38211872979365410658052797)
        ·
          refine ⟨14329452367262028996769799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38211872979365410658052797 14329452367262028996769799)
          ·
            refine ⟨21494178550893043495154699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14329452367262028996769799 21494178550893043495154699)
            ·
              refine ⟨32241267826339565242732049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21494178550893043495154699 32241267826339565242732049)
              ·
                refine ⟨24180950869754673932049037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32241267826339565242732049 24180950869754673932049037)
                ·
                  refine ⟨9067856576158002724518389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24180950869754673932049037 9067856576158002724518389)
                  ·
                    refine ⟨850111554014812755423599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9067856576158002724518389 850111554014812755423599)
                    ·
                      rfl

theorem cell23_4966759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_4966759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966759 prefixEnd_4966759 := by exact prefixLift 4966759
  have htrace : WordTrace (prefixWord ++ tailWord_4966759) baseStart_4966759 baseEnd_4966759 := by
    simpa [prefixWord, tailWord_4966759, baseEnd_4966759] using wordTrace_append hprefix tailTrace_4966759
  have hstable : (prefixWord ++ tailWord_4966759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966759).length < 2 ^ (prefixWord ++ tailWord_4966759).sum := by decide
  have hdescent : baseEnd_4966759 < baseStart_4966759 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966773 : List Nat := [1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 3]
def baseStart_4966773 : Nat := 118140960795 + 4966773 * 2 ^ 59
def prefixEnd_4966773 : Nat := 4983230072969 + 3 ^ 40 * 4966773 * 2
def baseEnd_4966773 : Nat := 2550341850773601211495733

theorem tailTrace_4966773 : CollatzResearch.WordTrace tailWord_4966773 prefixEnd_4966773 2550341850773601211495733 := by
  unfold tailWord_4966773
  simp only [CollatzResearch.WordTrace]
  refine ⟨181153093635237153140296973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120768729090158102093531315 181153093635237153140296973)
  ·
    refine ⟨67932410113213932427611365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181153093635237153140296973 67932410113213932427611365)
    ·
      refine ⟨12737326896227612330177131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67932410113213932427611365 12737326896227612330177131)
      ·
        refine ⟨19105990344341418495265697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12737326896227612330177131 19105990344341418495265697)
        ·
          refine ⟨14329492758256063871449273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19105990344341418495265697 14329492758256063871449273)
          ·
            refine ⟨10747119568692047903586955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14329492758256063871449273 10747119568692047903586955)
            ·
              refine ⟨16120679353038071855380433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10747119568692047903586955 16120679353038071855380433)
              ·
                refine ⟨12090509514778553891535325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16120679353038071855380433 12090509514778553891535325)
                ·
                  refine ⟨4533941068041957709325747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12090509514778553891535325 4533941068041957709325747)
                  ·
                    refine ⟨6800911602062936563988621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4533941068041957709325747 6800911602062936563988621)
                    ·
                      refine ⟨2550341850773601211495733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800911602062936563988621 2550341850773601211495733)
                      ·
                        rfl

theorem cell23_4966773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_4966773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966773 prefixEnd_4966773 := by exact prefixLift 4966773
  have htrace : WordTrace (prefixWord ++ tailWord_4966773) baseStart_4966773 baseEnd_4966773 := by
    simpa [prefixWord, tailWord_4966773, baseEnd_4966773] using wordTrace_append hprefix tailTrace_4966773
  have hstable : (prefixWord ++ tailWord_4966773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966773).length < 2 ^ (prefixWord ++ tailWord_4966773).sum := by decide
  have hdescent : baseEnd_4966773 < baseStart_4966773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966779 : List Nat := [1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 4]
def baseStart_4966779 : Nat := 118140960795 + 4966779 * 2 ^ 59
def prefixEnd_4966779 : Nat := 4983230072969 + 3 ^ 40 * 4966779 * 2
def baseEnd_4966779 : Nat := 2550344931657528188020705

theorem tailTrace_4966779 : CollatzResearch.WordTrace tailWord_4966779 prefixEnd_4966779 2550344931657528188020705 := by
  unfold tailWord_4966779
  simp only [CollatzResearch.WordTrace]
  refine ⟨181153312473215416165015391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120768874982143610776676927 181153312473215416165015391)
  ·
    refine ⟨271729968709823124247523087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181153312473215416165015391 271729968709823124247523087)
    ·
      refine ⟨407594953064734686371284631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271729968709823124247523087 407594953064734686371284631)
      ·
        refine ⟨611392429597102029556926947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407594953064734686371284631 611392429597102029556926947)
        ·
          refine ⟨917088644395653044335390421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611392429597102029556926947 917088644395653044335390421)
          ·
            refine ⟨21494265103023118226610713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 917088644395653044335390421 21494265103023118226610713)
            ·
              refine ⟨16120698827267338669958035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21494265103023118226610713 16120698827267338669958035)
              ·
                refine ⟨24181048240901008004937053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16120698827267338669958035 24181048240901008004937053)
                ·
                  refine ⟨9067893090337878001851395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24181048240901008004937053 9067893090337878001851395)
                  ·
                    refine ⟨13601839635506817002777093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9067893090337878001851395 13601839635506817002777093)
                    ·
                      refine ⟨2550344931657528188020705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13601839635506817002777093 2550344931657528188020705)
                      ·
                        rfl

theorem cell23_4966779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 2, 1, 3, 1, 4].length) (baseStart_4966779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966779 prefixEnd_4966779 := by exact prefixLift 4966779
  have htrace : WordTrace (prefixWord ++ tailWord_4966779) baseStart_4966779 baseEnd_4966779 := by
    simpa [prefixWord, tailWord_4966779, baseEnd_4966779] using wordTrace_append hprefix tailTrace_4966779
  have hstable : (prefixWord ++ tailWord_4966779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966779).length < 2 ^ (prefixWord ++ tailWord_4966779).sum := by decide
  have hdescent : baseEnd_4966779 < baseStart_4966779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966789 : List Nat := [1, 3, 1, 1, 3, 1, 1, 4, 4, 4]
def baseStart_4966789 : Nat := 118140960795 + 4966789 * 2 ^ 59
def prefixEnd_4966789 : Nat := 4983230072969 + 3 ^ 40 * 4966789 * 2
def baseEnd_4966789 : Nat := 850116688821357716298553

theorem tailTrace_4966789 : CollatzResearch.WordTrace tailWord_4966789 prefixEnd_4966789 850116688821357716298553 := by
  unfold tailWord_4966789
  simp only [CollatzResearch.WordTrace]
  refine ⟨181153677203179187872879421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120769118135452791915252947 181153677203179187872879421)
  ·
    refine ⟨67932628951192195452329783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181153677203179187872879421 67932628951192195452329783)
    ·
      refine ⟨101898943426788293178494675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67932628951192195452329783 101898943426788293178494675)
      ·
        refine ⟨152848415140182439767742013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101898943426788293178494675 152848415140182439767742013)
        ·
          refine ⟨57318155677568414912903255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152848415140182439767742013 57318155677568414912903255)
          ·
            refine ⟨85977233516352622369354883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57318155677568414912903255 85977233516352622369354883)
            ·
              refine ⟨128965850274528933554032325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85977233516352622369354883 128965850274528933554032325)
              ·
                refine ⟨24181096926474175041381061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 128965850274528933554032325 24181096926474175041381061)
                ·
                  refine ⟨4533955673713907820258949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24181096926474175041381061 4533955673713907820258949)
                  ·
                    refine ⟨850116688821357716298553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4533955673713907820258949 850116688821357716298553)
                    ·
                      rfl

theorem cell23_4966789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 4, 4, 4].length) (baseStart_4966789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966789 prefixEnd_4966789 := by exact prefixLift 4966789
  have htrace : WordTrace (prefixWord ++ tailWord_4966789) baseStart_4966789 baseEnd_4966789 := by
    simpa [prefixWord, tailWord_4966789, baseEnd_4966789] using wordTrace_append hprefix tailTrace_4966789
  have hstable : (prefixWord ++ tailWord_4966789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966789).length < 2 ^ (prefixWord ++ tailWord_4966789).sum := by decide
  have hdescent : baseEnd_4966789 < baseStart_4966789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966793 : List Nat := [1, 2, 1, 1, 6, 3, 2, 1, 1, 5]
def baseStart_4966793 : Nat := 118140960795 + 4966793 * 2 ^ 59
def prefixEnd_4966793 : Nat := 4983230072969 + 3 ^ 40 * 4966793 * 2
def baseEnd_4966793 : Nat := 850117373462230377748547

theorem tailTrace_4966793 : CollatzResearch.WordTrace tailWord_4966793 prefixEnd_4966793 850117373462230377748547 := by
  unfold tailWord_4966793
  simp only [CollatzResearch.WordTrace]
  refine ⟨181153823095164696556025033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120769215396776464370683355 181153823095164696556025033)
  ·
    refine ⟨135865367321373522417018775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181153823095164696556025033 135865367321373522417018775)
    ·
      refine ⟨203798050982060283625528163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135865367321373522417018775 203798050982060283625528163)
      ·
        refine ⟨305697076473090425438292245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203798050982060283625528163 305697076473090425438292245)
        ·
          refine ⟨14329550459676113692419949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 305697076473090425438292245 14329550459676113692419949)
          ·
            refine ⟨5373581422378542634657481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14329550459676113692419949 5373581422378542634657481)
            ·
              refine ⟨4030186066783906975993111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5373581422378542634657481 4030186066783906975993111)
              ·
                refine ⟨6045279100175860463989667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030186066783906975993111 6045279100175860463989667)
                ·
                  refine ⟨9067918650263790695984501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045279100175860463989667 9067918650263790695984501)
                  ·
                    refine ⟨850117373462230377748547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9067918650263790695984501 850117373462230377748547)
                    ·
                      rfl

theorem cell23_4966793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 2, 1, 1, 5].length) (baseStart_4966793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966793 prefixEnd_4966793 := by exact prefixLift 4966793
  have htrace : WordTrace (prefixWord ++ tailWord_4966793) baseStart_4966793 baseEnd_4966793 := by
    simpa [prefixWord, tailWord_4966793, baseEnd_4966793] using wordTrace_append hprefix tailTrace_4966793
  have hstable : (prefixWord ++ tailWord_4966793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966793).length < 2 ^ (prefixWord ++ tailWord_4966793).sum := by decide
  have hdescent : baseEnd_4966793 < baseStart_4966793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966796 : List Nat := [2, 2, 1, 2, 1, 5, 1, 3, 1, 1, 4]
def baseStart_4966796 : Nat := 118140960795 + 4966796 * 2 ^ 59
def prefixEnd_4966796 : Nat := 4983230072969 + 3 ^ 40 * 4966796 * 2
def baseEnd_4966796 : Nat := 2550353660828654621508127

theorem tailTrace_4966796 : CollatzResearch.WordTrace tailWord_4966796 prefixEnd_4966796 2550353660828654621508127 := by
  unfold tailWord_4966796
  simp only [CollatzResearch.WordTrace]
  refine ⟨90576966257076914034192121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120769288342769218712256161 90576966257076914034192121)
  ·
    refine ⟨67932724692807685525644091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90576966257076914034192121 67932724692807685525644091)
    ·
      refine ⟨101899087039211528288466137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67932724692807685525644091 101899087039211528288466137)
      ·
        refine ⟨76424315279408646216349603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101899087039211528288466137 76424315279408646216349603)
        ·
          refine ⟨114636472919112969324524405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76424315279408646216349603 114636472919112969324524405)
          ·
            refine ⟨10747169336166840874174163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114636472919112969324524405 10747169336166840874174163)
            ·
              refine ⟨16120754004250261311261245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10747169336166840874174163 16120754004250261311261245)
              ·
                refine ⟨6045282751593847991722967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16120754004250261311261245 6045282751593847991722967)
                ·
                  refine ⟨9067924127390771987584451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045282751593847991722967 9067924127390771987584451)
                  ·
                    refine ⟨13601886191086157981376677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9067924127390771987584451 13601886191086157981376677)
                    ·
                      refine ⟨2550353660828654621508127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13601886191086157981376677 2550353660828654621508127)
                      ·
                        rfl

theorem cell23_4966796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 3, 1, 1, 4].length) (baseStart_4966796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966796 prefixEnd_4966796 := by exact prefixLift 4966796
  have htrace : WordTrace (prefixWord ++ tailWord_4966796) baseStart_4966796 baseEnd_4966796 := by
    simpa [prefixWord, tailWord_4966796, baseEnd_4966796] using wordTrace_append hprefix tailTrace_4966796
  have hstable : (prefixWord ++ tailWord_4966796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966796).length < 2 ^ (prefixWord ++ tailWord_4966796).sum := by decide
  have hdescent : baseEnd_4966796 < baseStart_4966796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966832 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 3, 9]
def baseStart_4966832 : Nat := 118140960795 + 4966832 * 2 ^ 59
def prefixEnd_4966832 : Nat := 4983230072969 + 3 ^ 40 * 4966832 * 2
def baseEnd_4966832 : Nat := 850124048710738826885987

theorem tailTrace_4966832 : CollatzResearch.WordTrace tailWord_4966832 prefixEnd_4966832 850124048710738826885987 := by
  unfold tailWord_4966832
  simp only [CollatzResearch.WordTrace]
  refine ⟨90577622771011703108347375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120770163694682270811129833 90577622771011703108347375)
  ·
    refine ⟨135866434156517554662521063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90577622771011703108347375 135866434156517554662521063)
    ·
      refine ⟨203799651234776331993781595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135866434156517554662521063 203799651234776331993781595)
      ·
        refine ⟨305699476852164497990672393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203799651234776331993781595 305699476852164497990672393)
        ·
          refine ⟨229274607639123373493004295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305699476852164497990672393 229274607639123373493004295)
          ·
            refine ⟨343911911458685060239506443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229274607639123373493004295 343911911458685060239506443)
            ·
              refine ⟨515867867188027590359259665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343911911458685060239506443 515867867188027590359259665)
              ·
                refine ⟨386900900391020692769444749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 515867867188027590359259665 386900900391020692769444749)
                ·
                  refine ⟨145087837646632759788541781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 386900900391020692769444749 145087837646632759788541781)
                  ·
                    refine ⟨850124048710738826885987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 145087837646632759788541781 850124048710738826885987)
                    ·
                      rfl

theorem cell23_4966832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 3, 9].length) (baseStart_4966832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966832 prefixEnd_4966832 := by exact prefixLift 4966832
  have htrace : WordTrace (prefixWord ++ tailWord_4966832) baseStart_4966832 baseEnd_4966832 := by
    simpa [prefixWord, tailWord_4966832, baseEnd_4966832] using wordTrace_append hprefix tailTrace_4966832
  have hstable : (prefixWord ++ tailWord_4966832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966832).length < 2 ^ (prefixWord ++ tailWord_4966832).sum := by decide
  have hdescent : baseEnd_4966832 < baseStart_4966832 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966833 : List Nat := [1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 3]
def baseStart_4966833 : Nat := 118140960795 + 4966833 * 2 ^ 59
def prefixEnd_4966833 : Nat := 4983230072969 + 3 ^ 40 * 4966833 * 2
def baseEnd_4966833 : Nat := 2550372659612870976745457

theorem tailTrace_4966833 : CollatzResearch.WordTrace tailWord_4966833 prefixEnd_4966833 2550372659612870976745457 := by
  unfold tailWord_4966833
  simp only [CollatzResearch.WordTrace]
  refine ⟨181155282015019783387481153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120770188010013188924987435 181155282015019783387481153)
  ·
    refine ⟨135866461511264837540610865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181155282015019783387481153 135866461511264837540610865)
    ·
      refine ⟨101899846133448628155458149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135866461511264837540610865 101899846133448628155458149)
      ·
        refine ⟨19106221150021617779148403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101899846133448628155458149 19106221150021617779148403)
        ·
          refine ⟨28659331725032426668722605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19106221150021617779148403 28659331725032426668722605)
          ·
            refine ⟨10747249396887160000770977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28659331725032426668722605 10747249396887160000770977)
            ·
              refine ⟨8060437047665370000578233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10747249396887160000770977 8060437047665370000578233)
              ·
                refine ⟨6045327785749027500433675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8060437047665370000578233 6045327785749027500433675)
                ·
                  refine ⟨9067991678623541250650513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045327785749027500433675 9067991678623541250650513)
                  ·
                    refine ⟨6800993758967655937987885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9067991678623541250650513 6800993758967655937987885)
                    ·
                      refine ⟨2550372659612870976745457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6800993758967655937987885 2550372659612870976745457)
                      ·
                        rfl

theorem cell23_4966833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 1, 2, 3].length) (baseStart_4966833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966833 prefixEnd_4966833 := by exact prefixLift 4966833
  have htrace : WordTrace (prefixWord ++ tailWord_4966833) baseStart_4966833 baseEnd_4966833 := by
    simpa [prefixWord, tailWord_4966833, baseEnd_4966833] using wordTrace_append hprefix tailTrace_4966833
  have hstable : (prefixWord ++ tailWord_4966833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966833).length < 2 ^ (prefixWord ++ tailWord_4966833).sum := by decide
  have hdescent : baseEnd_4966833 < baseStart_4966833 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966846 : List Nat := [4, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3]
def baseStart_4966846 : Nat := 118140960795 + 4966846 * 2 ^ 59
def prefixEnd_4966846 : Nat := 4983230072969 + 3 ^ 40 * 4966846 * 2
def baseEnd_4966846 : Nat := 2550379334861379425882897

theorem tailTrace_4966846 : CollatzResearch.WordTrace tailWord_4966846 prefixEnd_4966846 2550379334861379425882897 := by
  unfold tailWord_4966846
  simp only [CollatzResearch.WordTrace]
  refine ⟨22644469520496585825963049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120770504109315124405136261 22644469520496585825963049)
  ·
    refine ⟨16983352140372439369472287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22644469520496585825963049 16983352140372439369472287)
    ·
      refine ⟨25475028210558659054208431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16983352140372439369472287 25475028210558659054208431)
      ·
        refine ⟨38212542315837988581312647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25475028210558659054208431 38212542315837988581312647)
        ·
          refine ⟨57318813473756982871968971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38212542315837988581312647 57318813473756982871968971)
          ·
            refine ⟨85978220210635474307953457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57318813473756982871968971 85978220210635474307953457)
            ·
              refine ⟨64483665157976605730965093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85978220210635474307953457 64483665157976605730965093)
              ·
                refine ⟨12090687217120613574555955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64483665157976605730965093 12090687217120613574555955)
                ·
                  refine ⟨18136030825680920361833933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12090687217120613574555955 18136030825680920361833933)
                  ·
                    refine ⟨6801011559630345135687725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18136030825680920361833933 6801011559630345135687725)
                    ·
                      refine ⟨2550379334861379425882897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6801011559630345135687725 2550379334861379425882897)
                      ·
                        rfl

theorem cell23_4966846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_4966846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966846 prefixEnd_4966846 := by exact prefixLift 4966846
  have htrace : WordTrace (prefixWord ++ tailWord_4966846) baseStart_4966846 baseEnd_4966846 := by
    simpa [prefixWord, tailWord_4966846, baseEnd_4966846] using wordTrace_append hprefix tailTrace_4966846
  have hstable : (prefixWord ++ tailWord_4966846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966846).length < 2 ^ (prefixWord ++ tailWord_4966846).sum := by decide
  have hdescent : baseEnd_4966846 < baseStart_4966846 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966889 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 3]
def baseStart_4966889 : Nat := 118140960795 + 4966889 * 2 ^ 59
def prefixEnd_4966889 : Nat := 4983230072969 + 3 ^ 40 * 4966889 * 2
def baseEnd_4966889 : Nat := 2550401414529522757645199

theorem tailTrace_4966889 : CollatzResearch.WordTrace tailWord_4966889 prefixEnd_4966889 2550401414529522757645199 := by
  unfold tailWord_4966889
  simp only [CollatzResearch.WordTrace]
  refine ⟨181157324502816904951519721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120771549668544603301013147 181157324502816904951519721)
  ·
    refine ⟨135867993377112678713639791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181157324502816904951519721 135867993377112678713639791)
    ·
      refine ⟨203801990065669018070459687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135867993377112678713639791 203801990065669018070459687)
      ·
        refine ⟨305702985098503527105689531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203801990065669018070459687 305702985098503527105689531)
        ·
          refine ⟨458554477647755290658534297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305702985098503527105689531 458554477647755290658534297)
          ·
            refine ⟨343915858235816467993900723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458554477647755290658534297 343915858235816467993900723)
            ·
              refine ⟨515873787353724701990851085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343915858235816467993900723 515873787353724701990851085)
              ·
                refine ⟨193452670257646763246569157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 515873787353724701990851085 193452670257646763246569157)
                ·
                  refine ⟨36272375673308768108731717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193452670257646763246569157 36272375673308768108731717)
                  ·
                    refine ⟨6801070438745394020387197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36272375673308768108731717 6801070438745394020387197)
                    ·
                      refine ⟨2550401414529522757645199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6801070438745394020387197 2550401414529522757645199)
                      ·
                        rfl

theorem cell23_4966889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 4, 4, 3].length) (baseStart_4966889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966889 prefixEnd_4966889 := by exact prefixLift 4966889
  have htrace : WordTrace (prefixWord ++ tailWord_4966889) baseStart_4966889 baseEnd_4966889 := by
    simpa [prefixWord, tailWord_4966889, baseEnd_4966889] using wordTrace_append hprefix tailTrace_4966889
  have hstable : (prefixWord ++ tailWord_4966889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966889).length < 2 ^ (prefixWord ++ tailWord_4966889).sum := by decide
  have hdescent : baseEnd_4966889 < baseStart_4966889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966890 : List Nat := [3, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2]
def baseStart_4966890 : Nat := 118140960795 + 4966890 * 2 ^ 59
def prefixEnd_4966890 : Nat := 4983230072969 + 3 ^ 40 * 4966890 * 2
def baseEnd_4966890 : Nat := 2550401928010177253732695

theorem tailTrace_4966890 : CollatzResearch.WordTrace tailWord_4966890 prefixEnd_4966890 2550401928010177253732695 := by
  unfold tailWord_4966890
  simp only [CollatzResearch.WordTrace]
  refine ⟨45289340243953320530576531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120771573983875521414870749 45289340243953320530576531)
  ·
    refine ⟨67934010365929980795864797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45289340243953320530576531 67934010365929980795864797)
    ·
      refine ⟨25475253887223742798449299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67934010365929980795864797 25475253887223742798449299)
      ·
        refine ⟨38212880830835614197673949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25475253887223742798449299 38212880830835614197673949)
        ·
          refine ⟨14329830311563355324127731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38212880830835614197673949 14329830311563355324127731)
          ·
            refine ⟨21494745467345032986191597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14329830311563355324127731 21494745467345032986191597)
            ·
              refine ⟨8060529550254387369821849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21494745467345032986191597 8060529550254387369821849)
              ·
                refine ⟨6045397162690790527366387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8060529550254387369821849 6045397162690790527366387)
                ·
                  refine ⟨9068095744036185791049581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045397162690790527366387 9068095744036185791049581)
                  ·
                    refine ⟨3400535904013569671643593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9068095744036185791049581 3400535904013569671643593)
                    ·
                      refine ⟨2550401928010177253732695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400535904013569671643593 2550401928010177253732695)
                      ·
                        rfl

theorem cell23_4966890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_4966890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966890 prefixEnd_4966890 := by exact prefixLift 4966890
  have htrace : WordTrace (prefixWord ++ tailWord_4966890) baseStart_4966890 baseEnd_4966890 := by
    simpa [prefixWord, tailWord_4966890, baseEnd_4966890] using wordTrace_append hprefix tailTrace_4966890
  have hstable : (prefixWord ++ tailWord_4966890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966890).length < 2 ^ (prefixWord ++ tailWord_4966890).sum := by decide
  have hdescent : baseEnd_4966890 < baseStart_4966890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966936 : List Nat := [2, 1, 2, 3, 3, 1, 1, 1, 1, 5, 3]
def baseStart_4966936 : Nat := 118140960795 + 4966936 * 2 ^ 59
def prefixEnd_4966936 : Nat := 4983230072969 + 3 ^ 40 * 4966936 * 2
def baseEnd_4966936 : Nat := 2550425548120284073757483

theorem tailTrace_4966936 : CollatzResearch.WordTrace tailWord_4966936 prefixEnd_4966936 2550425548120284073757483 := by
  unfold tailWord_4966936
  simp only [CollatzResearch.WordTrace]
  refine ⟨90579519366823315989240331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120772692489097754652320441 90579519366823315989240331)
  ·
    refine ⟨135869279050234973983860497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90579519366823315989240331 135869279050234973983860497)
    ·
      refine ⟨101901959287676230487895373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135869279050234973983860497 101901959287676230487895373)
      ·
        refine ⟨38213234732878586432960765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101901959287676230487895373 38213234732878586432960765)
        ·
          refine ⟨14329963024829469912360287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38213234732878586432960765 14329963024829469912360287)
          ·
            refine ⟨21494944537244204868540431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14329963024829469912360287 21494944537244204868540431)
            ·
              refine ⟨32242416805866307302810647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21494944537244204868540431 32242416805866307302810647)
              ·
                refine ⟨48363625208799460954215971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32242416805866307302810647 48363625208799460954215971)
                ·
                  refine ⟨72545437813199191431323957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48363625208799460954215971 72545437813199191431323957)
                  ·
                    refine ⟨6801134794987424196686621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72545437813199191431323957 6801134794987424196686621)
                    ·
                      refine ⟨2550425548120284073757483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6801134794987424196686621 2550425548120284073757483)
                      ·
                        rfl

theorem cell23_4966936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 1, 1, 1, 5, 3].length) (baseStart_4966936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966936 prefixEnd_4966936 := by exact prefixLift 4966936
  have htrace : WordTrace (prefixWord ++ tailWord_4966936) baseStart_4966936 baseEnd_4966936 := by
    simpa [prefixWord, tailWord_4966936, baseEnd_4966936] using wordTrace_append hprefix tailTrace_4966936
  have hstable : (prefixWord ++ tailWord_4966936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966936).length < 2 ^ (prefixWord ++ tailWord_4966936).sum := by decide
  have hdescent : baseEnd_4966936 < baseStart_4966936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966949 : List Nat := [1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 7]
def baseStart_4966949 : Nat := 118140960795 + 4966949 * 2 ^ 59
def prefixEnd_4966949 : Nat := 4983230072969 + 3 ^ 40 * 4966949 * 2
def baseEnd_4966949 : Nat := 2550432223368792522894923

theorem tailTrace_4966949 : CollatzResearch.WordTrace tailWord_4966949 prefixEnd_4966949 2550432223368792522894923 := by
  unfold tailWord_4966949
  simp only [CollatzResearch.WordTrace]
  refine ⟨181159512882599535198703901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120773008588399690132469267 181159512882599535198703901)
  ·
    refine ⟨67934817330974825699513963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181159512882599535198703901 67934817330974825699513963)
    ·
      refine ⟨101902225996462238549270945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67934817330974825699513963 101902225996462238549270945)
      ·
        refine ⟨76426669497346678911953209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101902225996462238549270945 76426669497346678911953209)
        ·
          refine ⟨57320002123010009183964907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76426669497346678911953209 57320002123010009183964907)
          ·
            refine ⟨85980003184515013775947361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57320002123010009183964907 85980003184515013775947361)
            ·
              refine ⟨64485002388386260331960521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85980003184515013775947361 64485002388386260331960521)
              ·
                refine ⟨48363751791289695248970391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64485002388386260331960521 48363751791289695248970391)
                ·
                  refine ⟨72545627686934542873455587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48363751791289695248970391 72545627686934542873455587)
                  ·
                    refine ⟨108818441530401814310183381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72545627686934542873455587 108818441530401814310183381)
                    ·
                      refine ⟨2550432223368792522894923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108818441530401814310183381 2550432223368792522894923)
                      ·
                        rfl

theorem cell23_4966949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 2, 1, 1, 7].length) (baseStart_4966949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966949 prefixEnd_4966949 := by exact prefixLift 4966949
  have htrace : WordTrace (prefixWord ++ tailWord_4966949) baseStart_4966949 baseEnd_4966949 := by
    simpa [prefixWord, tailWord_4966949, baseEnd_4966949] using wordTrace_append hprefix tailTrace_4966949
  have hstable : (prefixWord ++ tailWord_4966949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966949).length < 2 ^ (prefixWord ++ tailWord_4966949).sum := by decide
  have hdescent : baseEnd_4966949 < baseStart_4966949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966976 : List Nat := [2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4]
def baseStart_4966976 : Nat := 118140960795 + 4966976 * 2 ^ 59
def prefixEnd_4966976 : Nat := 4983230072969 + 3 ^ 40 * 4966976 * 2
def baseEnd_4966976 : Nat := 2550446087346463917257299

theorem tailTrace_4966976 : CollatzResearch.WordTrace tailWord_4966976 prefixEnd_4966976 2550446087346463917257299 := by
  unfold tailWord_4966976
  simp only [CollatzResearch.WordTrace]
  refine ⟨90580248826750859404968391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120773665102334479206624521 90580248826750859404968391)
  ·
    refine ⟨135870373240126289107452587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90580248826750859404968391 135870373240126289107452587)
    ·
      refine ⟨203805559860189433661178881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135870373240126289107452587 203805559860189433661178881)
      ·
        refine ⟨152854169895142075245884161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203805559860189433661178881 152854169895142075245884161)
        ·
          refine ⟨114640627421356556434413121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152854169895142075245884161 114640627421356556434413121)
          ·
            refine ⟨85980470566017417325809841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114640627421356556434413121 85980470566017417325809841)
            ·
              refine ⟨64485352924513062994357381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85980470566017417325809841 64485352924513062994357381)
              ·
                refine ⟨12091003673346199311442009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64485352924513062994357381 12091003673346199311442009)
                ·
                  refine ⟨9068252755009649483581507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12091003673346199311442009 9068252755009649483581507)
                  ·
                    refine ⟨13602379132514474225372261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9068252755009649483581507 13602379132514474225372261)
                    ·
                      refine ⟨2550446087346463917257299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13602379132514474225372261 2550446087346463917257299)
                      ·
                        rfl

theorem cell23_4966976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 4].length) (baseStart_4966976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966976 prefixEnd_4966976 := by exact prefixLift 4966976
  have htrace : WordTrace (prefixWord ++ tailWord_4966976) baseStart_4966976 baseEnd_4966976 := by
    simpa [prefixWord, tailWord_4966976, baseEnd_4966976] using wordTrace_append hprefix tailTrace_4966976
  have hstable : (prefixWord ++ tailWord_4966976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966976).length < 2 ^ (prefixWord ++ tailWord_4966976).sum := by decide
  have hdescent : baseEnd_4966976 < baseStart_4966976 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966979 : List Nat := [1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5]
def baseStart_4966979 : Nat := 118140960795 + 4966979 * 2 ^ 59
def prefixEnd_4966979 : Nat := 4983230072969 + 3 ^ 40 * 4966979 * 2
def baseEnd_4966979 : Nat := 2550447627788427405519785

theorem tailTrace_4966979 : CollatzResearch.WordTrace tailWord_4966979 prefixEnd_4966979 2550447627788427405519785 := by
  unfold tailWord_4966979
  simp only [CollatzResearch.WordTrace]
  refine ⟨181160607072490850322295991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120773738048327233548197327 181160607072490850322295991)
  ·
    refine ⟨271740910608736275483443987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181160607072490850322295991 271740910608736275483443987)
    ·
      refine ⟨407611365913104413225165981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271740910608736275483443987 407611365913104413225165981)
      ·
        refine ⟨152854262217414154959437243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407611365913104413225165981 152854262217414154959437243)
        ·
          refine ⟨229281393326121232439155865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152854262217414154959437243 229281393326121232439155865)
          ·
            refine ⟨171961044994590924329366899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229281393326121232439155865 171961044994590924329366899)
            ·
              refine ⟨257941567491886386494050349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171961044994590924329366899 257941567491886386494050349)
              ·
                refine ⟨96728087809457394935268881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257941567491886386494050349 96728087809457394935268881)
                ·
                  refine ⟨72546065857093046201451661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96728087809457394935268881 72546065857093046201451661)
                  ·
                    refine ⟨27204774696409892325544373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 72546065857093046201451661 27204774696409892325544373)
                    ·
                      refine ⟨2550447627788427405519785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27204774696409892325544373 2550447627788427405519785)
                      ·
                        rfl

theorem cell23_4966979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 3, 5].length) (baseStart_4966979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966979 prefixEnd_4966979 := by exact prefixLift 4966979
  have htrace : WordTrace (prefixWord ++ tailWord_4966979) baseStart_4966979 baseEnd_4966979 := by
    simpa [prefixWord, tailWord_4966979, baseEnd_4966979] using wordTrace_append hprefix tailTrace_4966979
  have hstable : (prefixWord ++ tailWord_4966979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966979).length < 2 ^ (prefixWord ++ tailWord_4966979).sum := by decide
  have hdescent : baseEnd_4966979 < baseStart_4966979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4966993 : List Nat := [1, 2, 2, 1, 3, 3, 2, 1, 2, 4, 2]
def baseStart_4966993 : Nat := 118140960795 + 4966993 * 2 ^ 59
def prefixEnd_4966993 : Nat := 4983230072969 + 3 ^ 40 * 4966993 * 2
def baseEnd_4966993 : Nat := 2550454816517590350744721

theorem tailTrace_4966993 : CollatzResearch.WordTrace tailWord_4966993 prefixEnd_4966993 2550454816517590350744721 := by
  unfold tailWord_4966993
  simp only [CollatzResearch.WordTrace]
  refine ⟨181161117694440130713305633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120774078462960087142203755 181161117694440130713305633)
  ·
    refine ⟨135870838270830098034979225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181161117694440130713305633 135870838270830098034979225)
    ·
      refine ⟨101903128703122573526234419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135870838270830098034979225 101903128703122573526234419)
      ·
        refine ⟨152854693054683860289351629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101903128703122573526234419 152854693054683860289351629)
        ·
          refine ⟨57320509895506447608506861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152854693054683860289351629 57320509895506447608506861)
          ·
            refine ⟨21495191210814917853190073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57320509895506447608506861 21495191210814917853190073)
            ·
              refine ⟨16121393408111188389892555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21495191210814917853190073 16121393408111188389892555)
              ·
                refine ⟨24182090112166782584838833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16121393408111188389892555 24182090112166782584838833)
                ·
                  refine ⟨18136567584125086938629125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24182090112166782584838833 18136567584125086938629125)
                  ·
                    refine ⟨3400606422023453800992961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18136567584125086938629125 3400606422023453800992961)
                    ·
                      refine ⟨2550454816517590350744721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400606422023453800992961 2550454816517590350744721)
                      ·
                        rfl

theorem cell23_4966993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 2, 1, 2, 4, 2].length) (baseStart_4966993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4966993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4966993 prefixEnd_4966993 := by exact prefixLift 4966993
  have htrace : WordTrace (prefixWord ++ tailWord_4966993) baseStart_4966993 baseEnd_4966993 := by
    simpa [prefixWord, tailWord_4966993, baseEnd_4966993] using wordTrace_append hprefix tailTrace_4966993
  have hstable : (prefixWord ++ tailWord_4966993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4966993).length < 2 ^ (prefixWord ++ tailWord_4966993).sum := by decide
  have hdescent : baseEnd_4966993 < baseStart_4966993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4966993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967019 : List Nat := [1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8]
def baseStart_4967019 : Nat := 118140960795 + 4967019 * 2 ^ 59
def prefixEnd_4967019 : Nat := 4983230072969 + 3 ^ 40 * 4967019 * 2
def baseEnd_4967019 : Nat := 2550468167014607249019601

theorem tailTrace_4967019 : CollatzResearch.WordTrace tailWord_4967019 prefixEnd_4967019 2550468167014607249019601 := by
  unfold tailWord_4967019
  simp only [CollatzResearch.WordTrace]
  refine ⟨181162065992345937153752111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120774710661563958102501407 181162065992345937153752111)
  ·
    refine ⟨271743098988518905730628167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181162065992345937153752111 271743098988518905730628167)
    ·
      refine ⟨407614648482778358595942251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271743098988518905730628167 407614648482778358595942251)
      ·
        refine ⟨611421972724167537893913377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407614648482778358595942251 611421972724167537893913377)
        ·
          refine ⟨458566479543125653420435033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 611421972724167537893913377 458566479543125653420435033)
          ·
            refine ⟨343924859657344240065326275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458566479543125653420435033 343924859657344240065326275)
            ·
              refine ⟨515887289486016360097989413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 343924859657344240065326275 515887289486016360097989413)
              ·
                refine ⟨96728866778628067518373015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 515887289486016360097989413 96728866778628067518373015)
                ·
                  refine ⟨145093300167942101277559523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96728866778628067518373015 145093300167942101277559523)
                  ·
                    refine ⟨217639950251913151916339285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 145093300167942101277559523 217639950251913151916339285)
                    ·
                      refine ⟨2550468167014607249019601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 217639950251913151916339285 2550468167014607249019601)
                      ·
                        rfl

theorem cell23_4967019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 1, 8].length) (baseStart_4967019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967019 prefixEnd_4967019 := by exact prefixLift 4967019
  have htrace : WordTrace (prefixWord ++ tailWord_4967019) baseStart_4967019 baseEnd_4967019 := by
    simpa [prefixWord, tailWord_4967019, baseEnd_4967019] using wordTrace_append hprefix tailTrace_4967019
  have hstable : (prefixWord ++ tailWord_4967019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967019).length < 2 ^ (prefixWord ++ tailWord_4967019).sum := by decide
  have hdescent : baseEnd_4967019 < baseStart_4967019 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967020 : List Nat := [2, 2, 1, 1, 3, 1, 5, 3, 1, 4]
def baseStart_4967020 : Nat := 118140960795 + 4967020 * 2 ^ 59
def prefixEnd_4967020 : Nat := 4983230072969 + 3 ^ 40 * 4967020 * 2
def baseEnd_4967020 : Nat := 850156226831753915035699

theorem tailTrace_4967020 : CollatzResearch.WordTrace tailWord_4967020 prefixEnd_4967020 850156226831753915035699 := by
  unfold tailWord_4967020
  simp only [CollatzResearch.WordTrace]
  refine ⟨90581051232671157162269257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120774734976894876216359009 90581051232671157162269257)
  ·
    refine ⟨67935788424503367871701943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90581051232671157162269257 67935788424503367871701943)
    ·
      refine ⟨101903682636755051807552915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67935788424503367871701943 101903682636755051807552915)
      ·
        refine ⟨152855523955132577711329373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101903682636755051807552915 152855523955132577711329373)
        ·
          refine ⟨57320821483174716641748515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152855523955132577711329373 57320821483174716641748515)
          ·
            refine ⟨85981232224762074962622773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57320821483174716641748515 85981232224762074962622773)
            ·
              refine ⟨8060740521071444527745885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 85981232224762074962622773 8060740521071444527745885)
              ·
                refine ⟨3022777695401791697904707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8060740521071444527745885 3022777695401791697904707)
                ·
                  refine ⟨4534166543102687546857061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022777695401791697904707 4534166543102687546857061)
                  ·
                    refine ⟨850156226831753915035699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534166543102687546857061 850156226831753915035699)
                    ·
                      rfl

theorem cell23_4967020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 3, 1, 4].length) (baseStart_4967020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967020 prefixEnd_4967020 := by exact prefixLift 4967020
  have htrace : WordTrace (prefixWord ++ tailWord_4967020) baseStart_4967020 baseEnd_4967020 := by
    simpa [prefixWord, tailWord_4967020, baseEnd_4967020] using wordTrace_append hprefix tailTrace_4967020
  have hstable : (prefixWord ++ tailWord_4967020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967020).length < 2 ^ (prefixWord ++ tailWord_4967020).sum := by decide
  have hdescent : baseEnd_4967020 < baseStart_4967020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967037 : List Nat := [1, 4, 1, 1, 6, 1, 1, 1, 3, 4]
def baseStart_4967037 : Nat := 118140960795 + 4967037 * 2 ^ 59
def prefixEnd_4967037 : Nat := 4983230072969 + 3 ^ 40 * 4967037 * 2
def baseEnd_4967037 : Nat := 850159136555462726198173

theorem tailTrace_4967037 : CollatzResearch.WordTrace tailWord_4967037 prefixEnd_4967037 850159136555462726198173 := by
  unfold tailWord_4967037
  simp only [CollatzResearch.WordTrace]
  refine ⟨181162722506280726227907365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120775148337520484151938243 181162722506280726227907365)
  ·
    refine ⟨33968010469927636167732631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181162722506280726227907365 33968010469927636167732631)
    ·
      refine ⟨50952015704891454251598947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33968010469927636167732631 50952015704891454251598947)
      ·
        refine ⟨76428023557337181377398421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50952015704891454251598947 76428023557337181377398421)
        ·
          refine ⟨3582563604250180377065551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76428023557337181377398421 3582563604250180377065551)
          ·
            refine ⟨5373845406375270565598327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582563604250180377065551 5373845406375270565598327)
            ·
              refine ⟨8060768109562905848397491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373845406375270565598327 8060768109562905848397491)
              ·
                refine ⟨12091152164344358772596237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8060768109562905848397491 12091152164344358772596237)
                ·
                  refine ⟨4534182061629134539723589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12091152164344358772596237 4534182061629134539723589)
                  ·
                    refine ⟨850159136555462726198173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534182061629134539723589 850159136555462726198173)
                    ·
                      rfl

theorem cell23_4967037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 1, 3, 4].length) (baseStart_4967037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967037 prefixEnd_4967037 := by exact prefixLift 4967037
  have htrace : WordTrace (prefixWord ++ tailWord_4967037) baseStart_4967037 baseEnd_4967037 := by
    simpa [prefixWord, tailWord_4967037, baseEnd_4967037] using wordTrace_append hprefix tailTrace_4967037
  have hstable : (prefixWord ++ tailWord_4967037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967037).length < 2 ^ (prefixWord ++ tailWord_4967037).sum := by decide
  have hdescent : baseEnd_4967037 < baseStart_4967037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967103 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 3]
def baseStart_4967103 : Nat := 118140960795 + 4967103 * 2 ^ 59
def prefixEnd_4967103 : Nat := 4983230072969 + 3 ^ 40 * 4967103 * 2
def baseEnd_4967103 : Nat := 2550511299389584920369215

theorem tailTrace_4967103 : CollatzResearch.WordTrace tailWord_4967103 prefixEnd_4967103 2550511299389584920369215 := by
  unfold tailWord_4967103
  simp only [CollatzResearch.WordTrace]
  refine ⟨181165129724041619499809963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120776753149361079666539975 181165129724041619499809963)
  ·
    refine ⟨271747694586062429249714945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181165129724041619499809963 271747694586062429249714945)
    ·
      refine ⟨203810770939546821937286209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271747694586062429249714945 203810770939546821937286209)
      ·
        refine ⟨152858078204660116452964657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203810770939546821937286209 152858078204660116452964657)
        ·
          refine ⟨114643558653495087339723493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152858078204660116452964657 114643558653495087339723493)
          ·
            refine ⟨21495667247530328876198155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 114643558653495087339723493 21495667247530328876198155)
            ·
              refine ⟨32243500871295493314297233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21495667247530328876198155 32243500871295493314297233)
              ·
                refine ⟨24182625653471619985722925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32243500871295493314297233 24182625653471619985722925)
                ·
                  refine ⟨9068484620051857494646097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24182625653471619985722925 9068484620051857494646097)
                  ·
                    refine ⟨6801363465038893120984573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9068484620051857494646097 6801363465038893120984573)
                    ·
                      refine ⟨2550511299389584920369215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6801363465038893120984573 2550511299389584920369215)
                      ·
                        rfl

theorem cell23_4967103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 3, 2, 3].length) (baseStart_4967103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967103 prefixEnd_4967103 := by exact prefixLift 4967103
  have htrace : WordTrace (prefixWord ++ tailWord_4967103) baseStart_4967103 baseEnd_4967103 := by
    simpa [prefixWord, tailWord_4967103, baseEnd_4967103] using wordTrace_append hprefix tailTrace_4967103
  have hstable : (prefixWord ++ tailWord_4967103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967103).length < 2 ^ (prefixWord ++ tailWord_4967103).sum := by decide
  have hdescent : baseEnd_4967103 < baseStart_4967103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967137 : List Nat := [1, 2, 3, 1, 4, 1, 4, 1, 1, 2, 3]
def baseStart_4967137 : Nat := 118140960795 + 4967137 * 2 ^ 59
def prefixEnd_4967137 : Nat := 4983230072969 + 3 ^ 40 * 4967137 * 2
def baseEnd_4967137 : Nat := 2550528757731837787344059

theorem tailTrace_4967137 : CollatzResearch.WordTrace tailWord_4967137 prefixEnd_4967137 2550528757731837787344059 := by
  unfold tailWord_4967137
  simp only [CollatzResearch.WordTrace]
  refine ⟨181166369805918443306547665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120777579870612295537698443 181166369805918443306547665)
  ·
    refine ⟨135874777354438832479910749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181166369805918443306547665 135874777354438832479910749)
    ·
      refine ⟨50953041507914562179966531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135874777354438832479910749 50953041507914562179966531)
      ·
        refine ⟨76429562261871843269949797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50953041507914562179966531 76429562261871843269949797)
        ·
          refine ⟨14330542924100970613115587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76429562261871843269949797 14330542924100970613115587)
          ·
            refine ⟨21495814386151455919673381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14330542924100970613115587 21495814386151455919673381)
            ·
              refine ⟨4030465197403397984938759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21495814386151455919673381 4030465197403397984938759)
              ·
                refine ⟨6045697796105096977408139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4030465197403397984938759 6045697796105096977408139)
                ·
                  refine ⟨9068546694157645466112209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6045697796105096977408139 9068546694157645466112209)
                  ·
                    refine ⟨6801410020618234099584157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9068546694157645466112209 6801410020618234099584157)
                    ·
                      refine ⟨2550528757731837787344059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6801410020618234099584157 2550528757731837787344059)
                      ·
                        rfl

theorem cell23_4967137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 4, 1, 1, 2, 3].length) (baseStart_4967137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967137 prefixEnd_4967137 := by exact prefixLift 4967137
  have htrace : WordTrace (prefixWord ++ tailWord_4967137) baseStart_4967137 baseEnd_4967137 := by
    simpa [prefixWord, tailWord_4967137, baseEnd_4967137] using wordTrace_append hprefix tailTrace_4967137
  have hstable : (prefixWord ++ tailWord_4967137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967137).length < 2 ^ (prefixWord ++ tailWord_4967137).sum := by decide
  have hdescent : baseEnd_4967137 < baseStart_4967137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967144 : List Nat := [2, 1, 4, 1, 5, 1, 1, 2, 2, 4]
def baseStart_4967144 : Nat := 118140960795 + 4967144 * 2 ^ 59
def prefixEnd_4967144 : Nat := 4983230072969 + 3 ^ 40 * 4967144 * 2
def baseEnd_4967144 : Nat := 850177450698806419985509

theorem tailTrace_4967144 : CollatzResearch.WordTrace tailWord_4967144 prefixEnd_4967144 850177450698806419985509 := by
  unfold tailWord_4967144
  simp only [CollatzResearch.WordTrace]
  refine ⟨90583312558446541751026243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120777750077928722334701657 90583312558446541751026243)
  ·
    refine ⟨135874968837669812626539365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90583312558446541751026243 135874968837669812626539365)
    ·
      refine ⟨25476556657063089867476131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135874968837669812626539365 25476556657063089867476131)
      ·
        refine ⟨38214834985594634801214197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25476556657063089867476131 38214834985594634801214197)
        ·
          refine ⟨3582640779899497012613831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38214834985594634801214197 3582640779899497012613831)
          ·
            refine ⟨5373961169849245518920747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3582640779899497012613831 5373961169849245518920747)
            ·
              refine ⟨8060941754773868278381121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5373961169849245518920747 8060941754773868278381121)
              ·
                refine ⟨6045706316080401208785841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8060941754773868278381121 6045706316080401208785841)
                ·
                  refine ⟨4534279737060300906589381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6045706316080401208785841 4534279737060300906589381)
                  ·
                    refine ⟨850177450698806419985509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534279737060300906589381 850177450698806419985509)
                    ·
                      rfl

theorem cell23_4967144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_4967144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967144 prefixEnd_4967144 := by exact prefixLift 4967144
  have htrace : WordTrace (prefixWord ++ tailWord_4967144) baseStart_4967144 baseEnd_4967144 := by
    simpa [prefixWord, tailWord_4967144, baseEnd_4967144] using wordTrace_append hprefix tailTrace_4967144
  have hstable : (prefixWord ++ tailWord_4967144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967144).length < 2 ^ (prefixWord ++ tailWord_4967144).sum := by decide
  have hdescent : baseEnd_4967144 < baseStart_4967144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967223 : List Nat := [1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 3]
def baseStart_4967223 : Nat := 118140960795 + 4967223 * 2 ^ 59
def prefixEnd_4967223 : Nat := 4983230072969 + 3 ^ 40 * 4967223 * 2
def baseEnd_4967223 : Nat := 2550572917068124450868663

theorem tailTrace_4967223 : CollatzResearch.WordTrace tailWord_4967223 prefixEnd_4967223 2550572917068124450868663 := by
  unfold tailWord_4967223
  simp only [CollatzResearch.WordTrace]
  refine ⟨181169506483606879994178323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120779670989071253329452215 181169506483606879994178323)
  ·
    refine ⟨271754259725410319991267485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181169506483606879994178323 271754259725410319991267485)
    ·
      refine ⟨101907847397028869996725307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271754259725410319991267485 101907847397028869996725307)
      ·
        refine ⟨152861771095543304995087961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101907847397028869996725307 152861771095543304995087961)
        ·
          refine ⟨114646328321657478746315971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152861771095543304995087961 114646328321657478746315971)
          ·
            refine ⟨171969492482486218119473957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114646328321657478746315971 171969492482486218119473957)
            ·
              refine ⟨32244279840466165897401367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 171969492482486218119473957 32244279840466165897401367)
              ·
                refine ⟨48366419760699248846102051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32244279840466165897401367 48366419760699248846102051)
                ·
                  refine ⟨72549629641048873269153077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48366419760699248846102051 72549629641048873269153077)
                  ·
                    refine ⟨6801527778848331868983101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72549629641048873269153077 6801527778848331868983101)
                    ·
                      refine ⟨2550572917068124450868663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6801527778848331868983101 2550572917068124450868663)
                      ·
                        rfl

theorem cell23_4967223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 4, 1, 1, 5, 3].length) (baseStart_4967223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967223 prefixEnd_4967223 := by exact prefixLift 4967223
  have htrace : WordTrace (prefixWord ++ tailWord_4967223) baseStart_4967223 baseEnd_4967223 := by
    simpa [prefixWord, tailWord_4967223, baseEnd_4967223] using wordTrace_append hprefix tailTrace_4967223
  have hstable : (prefixWord ++ tailWord_4967223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967223).length < 2 ^ (prefixWord ++ tailWord_4967223).sum := by decide
  have hdescent : baseEnd_4967223 < baseStart_4967223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967253 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 5]
def baseStart_4967253 : Nat := 118140960795 + 4967253 * 2 ^ 59
def prefixEnd_4967253 : Nat := 4983230072969 + 3 ^ 40 * 4967253 * 2
def baseEnd_4967253 : Nat := 2550588321487759333493525

theorem tailTrace_4967253 : CollatzResearch.WordTrace tailWord_4967253 prefixEnd_4967253 2550588321487759333493525 := by
  unfold tailWord_4967253
  simp only [CollatzResearch.WordTrace]
  refine ⟨181170600673498195117770413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120780400448998796745180275 181170600673498195117770413)
  ·
    refine ⟨67938975252561823169163905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181170600673498195117770413 67938975252561823169163905)
    ·
      refine ⟨50954231439421367376872929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67938975252561823169163905 50954231439421367376872929)
      ·
        refine ⟨38215673579566025532654697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50954231439421367376872929 38215673579566025532654697)
        ·
          refine ⟨28661755184674519149491023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38215673579566025532654697 28661755184674519149491023)
          ·
            refine ⟨42992632777011778724236535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28661755184674519149491023 42992632777011778724236535)
            ·
              refine ⟨64488949165517668086354803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42992632777011778724236535 64488949165517668086354803)
              ·
                refine ⟨96733423748276502129532205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64488949165517668086354803 96733423748276502129532205)
                ·
                  refine ⟨36275033905603688298574577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96733423748276502129532205 36275033905603688298574577)
                  ·
                    refine ⟨27206275429202766223930933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36275033905603688298574577 27206275429202766223930933)
                    ·
                      refine ⟨2550588321487759333493525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27206275429202766223930933 2550588321487759333493525)
                      ·
                        rfl

theorem cell23_4967253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 2, 5].length) (baseStart_4967253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967253 prefixEnd_4967253 := by exact prefixLift 4967253
  have htrace : WordTrace (prefixWord ++ tailWord_4967253) baseStart_4967253 baseEnd_4967253 := by
    simpa [prefixWord, tailWord_4967253, baseEnd_4967253] using wordTrace_append hprefix tailTrace_4967253
  have hstable : (prefixWord ++ tailWord_4967253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967253).length < 2 ^ (prefixWord ++ tailWord_4967253).sum := by decide
  have hdescent : baseEnd_4967253 < baseStart_4967253 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967280 : List Nat := [2, 1, 1, 1, 4, 1, 3, 1, 1, 6, 2]
def baseStart_4967280 : Nat := 118140960795 + 4967280 * 2 ^ 59
def prefixEnd_4967280 : Nat := 4983230072969 + 3 ^ 40 * 4967280 * 2
def baseEnd_4967280 : Nat := 2550602185465430727855901

theorem tailTrace_4967280 : CollatzResearch.WordTrace tailWord_4967280 prefixEnd_4967280 2550602185465430727855901 := by
  unfold tailWord_4967280
  simp only [CollatzResearch.WordTrace]
  refine ⟨90585792722200189364501647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120781056962933585819335529 90585792722200189364501647)
  ·
    refine ⟨135878689083300284046752471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90585792722200189364501647 135878689083300284046752471)
    ·
      refine ⟨203818033624950426070128707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135878689083300284046752471 203818033624950426070128707)
      ·
        refine ⟨305727050437425639105193061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203818033624950426070128707 305727050437425639105193061)
        ·
          refine ⟨57323821957017307332223699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305727050437425639105193061 57323821957017307332223699)
          ·
            refine ⟨85985732935525960998335549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57323821957017307332223699 85985732935525960998335549)
            ·
              refine ⟨32244649850822235374375831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85985732935525960998335549 32244649850822235374375831)
              ·
                refine ⟨48366974776233353061563747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32244649850822235374375831 48366974776233353061563747)
                ·
                  refine ⟨72550462164350029592345621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48366974776233353061563747 72550462164350029592345621)
                  ·
                    refine ⟨3400802913953907637141201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72550462164350029592345621 3400802913953907637141201)
                    ·
                      refine ⟨2550602185465430727855901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400802913953907637141201 2550602185465430727855901)
                      ·
                        rfl

theorem cell23_4967280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 1, 6, 2].length) (baseStart_4967280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967280 prefixEnd_4967280 := by exact prefixLift 4967280
  have htrace : WordTrace (prefixWord ++ tailWord_4967280) baseStart_4967280 baseEnd_4967280 := by
    simpa [prefixWord, tailWord_4967280, baseEnd_4967280] using wordTrace_append hprefix tailTrace_4967280
  have hstable : (prefixWord ++ tailWord_4967280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967280).length < 2 ^ (prefixWord ++ tailWord_4967280).sum := by decide
  have hdescent : baseEnd_4967280 < baseStart_4967280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967307 : List Nat := [1, 1, 1, 1, 4, 2, 3, 5, 1, 4]
def baseStart_4967307 : Nat := 118140960795 + 4967307 * 2 ^ 59
def prefixEnd_4967307 : Nat := 4983230072969 + 3 ^ 40 * 4967307 * 2
def baseEnd_4967307 : Nat := 850205349814367374072759

theorem tailTrace_4967307 : CollatzResearch.WordTrace tailWord_4967307 prefixEnd_4967307 850205349814367374072759 := by
  unfold tailWord_4967307
  simp only [CollatzResearch.WordTrace]
  refine ⟨181172570215302562340236175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120781713476868374893490783 181172570215302562340236175)
  ·
    refine ⟨271758855322953843510354263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181172570215302562340236175 271758855322953843510354263)
    ·
      refine ⟨407638282984430765265531395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271758855322953843510354263 407638282984430765265531395)
      ·
        refine ⟨611457424476646147898297093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407638282984430765265531395 611457424476646147898297093)
        ·
          refine ⟨114648267089371152730930705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 611457424476646147898297093 114648267089371152730930705)
          ·
            refine ⟨85986200317028364548198029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114648267089371152730930705 85986200317028364548198029)
            ·
              refine ⟨32244825118885636705574261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85986200317028364548198029 32244825118885636705574261)
              ·
                refine ⟨3022952354895528441147587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32244825118885636705574261 3022952354895528441147587)
                ·
                  refine ⟨4534428532343292661721381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3022952354895528441147587 4534428532343292661721381)
                  ·
                    refine ⟨850205349814367374072759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534428532343292661721381 850205349814367374072759)
                    ·
                      rfl

theorem cell23_4967307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 5, 1, 4].length) (baseStart_4967307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967307 prefixEnd_4967307 := by exact prefixLift 4967307
  have htrace : WordTrace (prefixWord ++ tailWord_4967307) baseStart_4967307 baseEnd_4967307 := by
    simpa [prefixWord, tailWord_4967307, baseEnd_4967307] using wordTrace_append hprefix tailTrace_4967307
  have hstable : (prefixWord ++ tailWord_4967307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967307).length < 2 ^ (prefixWord ++ tailWord_4967307).sum := by decide
  have hdescent : baseEnd_4967307 < baseStart_4967307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967324 : List Nat := [2, 2, 3, 3, 2, 1, 2, 1, 3, 4]
def baseStart_4967324 : Nat := 118140960795 + 4967324 * 2 ^ 59
def prefixEnd_4967324 : Nat := 4983230072969 + 3 ^ 40 * 4967324 * 2
def baseEnd_4967324 : Nat := 850208259538076185235233

theorem tailTrace_4967324 : CollatzResearch.WordTrace tailWord_4967324 prefixEnd_4967324 850208259538076185235233 := by
  unfold tailWord_4967324
  simp only [CollatzResearch.WordTrace]
  refine ⟨90586595128120487121802513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120782126837493982829070017 90586595128120487121802513)
  ·
    refine ⟨67939946346090365341351885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90586595128120487121802513 67939946346090365341351885)
    ·
      refine ⟨25477479879783887003006957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67939946346090365341351885 25477479879783887003006957)
      ·
        refine ⟨9554054954918957626127609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25477479879783887003006957 9554054954918957626127609)
        ·
          refine ⟨7165541216189218219595707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9554054954918957626127609 7165541216189218219595707)
          ·
            refine ⟨10748311824283827329393561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7165541216189218219595707 10748311824283827329393561)
            ·
              refine ⟨8061233868212870497045171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10748311824283827329393561 8061233868212870497045171)
              ·
                refine ⟨12091850802319305745567757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8061233868212870497045171 12091850802319305745567757)
                ·
                  refine ⟨4534444050869739654587909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12091850802319305745567757 4534444050869739654587909)
                  ·
                    refine ⟨850208259538076185235233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534444050869739654587909 850208259538076185235233)
                    ·
                      rfl

theorem cell23_4967324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 1, 3, 4].length) (baseStart_4967324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967324 prefixEnd_4967324 := by exact prefixLift 4967324
  have htrace : WordTrace (prefixWord ++ tailWord_4967324) baseStart_4967324 baseEnd_4967324 := by
    simpa [prefixWord, tailWord_4967324, baseEnd_4967324] using wordTrace_append hprefix tailTrace_4967324
  have hstable : (prefixWord ++ tailWord_4967324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967324).length < 2 ^ (prefixWord ++ tailWord_4967324).sum := by decide
  have hdescent : baseEnd_4967324 < baseStart_4967324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967370 : List Nat := [3, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4]
def baseStart_4967370 : Nat := 118140960795 + 4967370 * 2 ^ 59
def prefixEnd_4967370 : Nat := 4983230072969 + 3 ^ 40 * 4967370 * 2
def baseEnd_4967370 : Nat := 2550648398724335375730487

theorem tailTrace_4967370 : CollatzResearch.WordTrace tailWord_4967370 prefixEnd_4967370 2550648398724335375730487 := by
  unfold tailWord_4967370
  simp only [CollatzResearch.WordTrace]
  refine ⟨45293717003518581024944891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120783245342716216066519709 45293717003518581024944891)
  ·
    refine ⟨67940575505277871537417337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45293717003518581024944891 67940575505277871537417337)
    ·
      refine ⟨50955431628958403653063003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67940575505277871537417337 50955431628958403653063003)
      ·
        refine ⟨76433147443437605479594505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50955431628958403653063003 76433147443437605479594505)
        ·
          refine ⟨57324860582578204109695879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76433147443437605479594505 57324860582578204109695879)
          ·
            refine ⟨85987290873867306164543819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57324860582578204109695879 85987290873867306164543819)
            ·
              refine ⟨128980936310800959246815729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85987290873867306164543819 128980936310800959246815729)
              ·
                refine ⟨96735702233100719435111797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128980936310800959246815729 96735702233100719435111797)
                ·
                  refine ⟨9068972084353192447041731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 96735702233100719435111797 9068972084353192447041731)
                  ·
                    refine ⟨13603458126529788670562597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9068972084353192447041731 13603458126529788670562597)
                    ·
                      refine ⟨2550648398724335375730487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13603458126529788670562597 2550648398724335375730487)
                      ·
                        rfl

theorem cell23_4967370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 2, 5, 1, 4].length) (baseStart_4967370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967370 prefixEnd_4967370 := by exact prefixLift 4967370
  have htrace : WordTrace (prefixWord ++ tailWord_4967370) baseStart_4967370 baseEnd_4967370 := by
    simpa [prefixWord, tailWord_4967370, baseEnd_4967370] using wordTrace_append hprefix tailTrace_4967370
  have hstable : (prefixWord ++ tailWord_4967370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967370).length < 2 ^ (prefixWord ++ tailWord_4967370).sum := by decide
  have hdescent : baseEnd_4967370 < baseStart_4967370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967374 : List Nat := [4, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2]
def baseStart_4967374 : Nat := 118140960795 + 4967374 * 2 ^ 59
def prefixEnd_4967374 : Nat := 4983230072969 + 3 ^ 40 * 4967374 * 2
def baseEnd_4967374 : Nat := 2550650452646953360080469

theorem tailTrace_4967374 : CollatzResearch.WordTrace tailWord_4967374 prefixEnd_4967374 2550650452646953360080469 := by
  unfold tailWord_4967374
  simp only [CollatzResearch.WordTrace]
  refine ⟨22646876738257479097865647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120783342604039888521950117 22646876738257479097865647)
  ·
    refine ⟨33970315107386218646798471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22646876738257479097865647 33970315107386218646798471)
    ·
      refine ⟨50955472661079327970197707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33970315107386218646798471 50955472661079327970197707)
      ·
        refine ⟨76433208991618991955296561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50955472661079327970197707 76433208991618991955296561)
        ·
          refine ⟨57324906743714243966472421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76433208991618991955296561 57324906743714243966472421)
          ·
            refine ⟨10748420014446420743713579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57324906743714243966472421 10748420014446420743713579)
            ·
              refine ⟨16122630021669631115570369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10748420014446420743713579 16122630021669631115570369)
              ·
                refine ⟨12091972516252223336677777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16122630021669631115570369 12091972516252223336677777)
                ·
                  refine ⟨9068979387189167502508333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12091972516252223336677777 9068979387189167502508333)
                  ·
                    refine ⟨3400867270195937813440625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9068979387189167502508333 3400867270195937813440625)
                    ·
                      refine ⟨2550650452646953360080469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400867270195937813440625 2550650452646953360080469)
                      ·
                        rfl

theorem cell23_4967374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 2, 3, 2].length) (baseStart_4967374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967374 prefixEnd_4967374 := by exact prefixLift 4967374
  have htrace : WordTrace (prefixWord ++ tailWord_4967374) baseStart_4967374 baseEnd_4967374 := by
    simpa [prefixWord, tailWord_4967374, baseEnd_4967374] using wordTrace_append hprefix tailTrace_4967374
  have hstable : (prefixWord ++ tailWord_4967374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967374).length < 2 ^ (prefixWord ++ tailWord_4967374).sum := by decide
  have hdescent : baseEnd_4967374 < baseStart_4967374 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967381 : List Nat := [1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 3]
def baseStart_4967381 : Nat := 118140960795 + 4967381 * 2 ^ 59
def prefixEnd_4967381 : Nat := 4983230072969 + 3 ^ 40 * 4967381 * 2
def baseEnd_4967381 : Nat := 2550654047011534832692937

theorem tailTrace_4967381 : CollatzResearch.WordTrace tailWord_4967381 prefixEnd_4967381 2550654047011534832692937 := by
  unfold tailWord_4967381
  simp only [CollatzResearch.WordTrace]
  refine ⟨181175269217034472978429997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120783512811356315318953331 181175269217034472978429997)
  ·
    refine ⟨67940725956387927366911249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181175269217034472978429997 67940725956387927366911249)
    ·
      refine ⟨50955544467290945525183437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67940725956387927366911249 50955544467290945525183437)
      ·
        refine ⟨19108329175234104571943789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50955544467290945525183437 19108329175234104571943789)
        ·
          refine ⟨7165623440712789214478921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19108329175234104571943789 7165623440712789214478921)
          ·
            refine ⟨5374217580534591910859191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7165623440712789214478921 5374217580534591910859191)
            ·
              refine ⟨8061326370801887866288787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5374217580534591910859191 8061326370801887866288787)
              ·
                refine ⟨12091989556202831799433181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8061326370801887866288787 12091989556202831799433181)
                ·
                  refine ⟨4534496083576061924787443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12091989556202831799433181 4534496083576061924787443)
                  ·
                    refine ⟨6801744125364092887181165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4534496083576061924787443 6801744125364092887181165)
                    ·
                      refine ⟨2550654047011534832692937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6801744125364092887181165 2550654047011534832692937)
                      ·
                        rfl

theorem cell23_4967381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_4967381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967381 prefixEnd_4967381 := by exact prefixLift 4967381
  have htrace : WordTrace (prefixWord ++ tailWord_4967381) baseStart_4967381 baseEnd_4967381 := by
    simpa [prefixWord, tailWord_4967381, baseEnd_4967381] using wordTrace_append hprefix tailTrace_4967381
  have hstable : (prefixWord ++ tailWord_4967381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967381).length < 2 ^ (prefixWord ++ tailWord_4967381).sum := by decide
  have hdescent : baseEnd_4967381 < baseStart_4967381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967400 : List Nat := [2, 1, 4, 1, 1, 1, 4, 1, 1, 1, 6]
def baseStart_4967400 : Nat := 118140960795 + 4967400 * 2 ^ 59
def prefixEnd_4967400 : Nat := 4983230072969 + 3 ^ 40 * 4967400 * 2
def baseEnd_4967400 : Nat := 2550663803143970258355349

theorem tailTrace_4967400 : CollatzResearch.WordTrace tailWord_4967400 prefixEnd_4967400 2550663803143970258355349 := by
  unfold tailWord_4967400
  simp only [CollatzResearch.WordTrace]
  refine ⟨90587981101982819611685827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120783974802643759482247769 90587981101982819611685827)
  ·
    refine ⟨135881971652974229417528741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90587981101982819611685827 135881971652974229417528741)
    ·
      refine ⟨25477869684932668015786639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135881971652974229417528741 25477869684932668015786639)
      ·
        refine ⟨38216804527399002023679959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25477869684932668015786639 38216804527399002023679959)
        ·
          refine ⟨57325206791098503035519939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38216804527399002023679959 57325206791098503035519939)
          ·
            refine ⟨85987810186647754553279909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57325206791098503035519939 85987810186647754553279909)
            ·
              refine ⟨16122714409996453978739983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 85987810186647754553279909 16122714409996453978739983)
              ·
                refine ⟨24184071614994680968109975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16122714409996453978739983 24184071614994680968109975)
                ·
                  refine ⟨36276107422492021452164963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24184071614994680968109975 36276107422492021452164963)
                  ·
                    refine ⟨54414161133738032178247445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36276107422492021452164963 54414161133738032178247445)
                    ·
                      refine ⟨2550663803143970258355349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54414161133738032178247445 2550663803143970258355349)
                      ·
                        rfl

theorem cell23_4967400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_4967400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967400 prefixEnd_4967400 := by exact prefixLift 4967400
  have htrace : WordTrace (prefixWord ++ tailWord_4967400) baseStart_4967400 baseEnd_4967400 := by
    simpa [prefixWord, tailWord_4967400, baseEnd_4967400] using wordTrace_append hprefix tailTrace_4967400
  have hstable : (prefixWord ++ tailWord_4967400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967400).length < 2 ^ (prefixWord ++ tailWord_4967400).sum := by decide
  have hdescent : baseEnd_4967400 < baseStart_4967400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967407 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 3]
def baseStart_4967407 : Nat := 118140960795 + 4967407 * 2 ^ 59
def prefixEnd_4967407 : Nat := 4983230072969 + 3 ^ 40 * 4967407 * 2
def baseEnd_4967407 : Nat := 2550667397508551730967817

theorem tailTrace_4967407 : CollatzResearch.WordTrace tailWord_4967407 prefixEnd_4967407 2550667397508551730967817 := by
  unfold tailWord_4967407
  simp only [CollatzResearch.WordTrace]
  refine ⟨181176217514940279418876475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120784145009960186279250983 181176217514940279418876475)
  ·
    refine ⟨271764326272410419128314713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181176217514940279418876475 271764326272410419128314713)
    ·
      refine ⟨203823244704307814346236035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271764326272410419128314713 203823244704307814346236035)
      ·
        refine ⟨305734867056461721519354053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203823244704307814346236035 305734867056461721519354053)
        ·
          refine ⟨57325287573086572784878885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305734867056461721519354053 57325287573086572784878885)
          ·
            refine ⟨10748491419953732397164791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57325287573086572784878885 10748491419953732397164791)
            ·
              refine ⟨16122737129930598595747187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10748491419953732397164791 16122737129930598595747187)
              ·
                refine ⟨24184105694895897893620781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16122737129930598595747187 24184105694895897893620781)
                ·
                  refine ⟨9069039635585961710107793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24184105694895897893620781 9069039635585961710107793)
                  ·
                    refine ⟨6801779726689471282580845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9069039635585961710107793 6801779726689471282580845)
                    ·
                      refine ⟨2550667397508551730967817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6801779726689471282580845 2550667397508551730967817)
                      ·
                        rfl

theorem cell23_4967407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 3, 2, 3].length) (baseStart_4967407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967407 prefixEnd_4967407 := by exact prefixLift 4967407
  have htrace : WordTrace (prefixWord ++ tailWord_4967407) baseStart_4967407 baseEnd_4967407 := by
    simpa [prefixWord, tailWord_4967407, baseEnd_4967407] using wordTrace_append hprefix tailTrace_4967407
  have hstable : (prefixWord ++ tailWord_4967407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967407).length < 2 ^ (prefixWord ++ tailWord_4967407).sum := by decide
  have hdescent : baseEnd_4967407 < baseStart_4967407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967421 : List Nat := [1, 4, 1, 1, 1, 2, 1, 7, 1, 2, 2]
def baseStart_4967421 : Nat := 118140960795 + 4967421 * 2 ^ 59
def prefixEnd_4967421 : Nat := 4983230072969 + 3 ^ 40 * 4967421 * 2
def baseEnd_4967421 : Nat := 2550674586237714676192753

theorem tailTrace_4967421 : CollatzResearch.WordTrace tailWord_4967421 prefixEnd_4967421 2550674586237714676192753 := by
  unfold tailWord_4967421
  simp only [CollatzResearch.WordTrace]
  refine ⟨181176728136889559809886117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120784485424593039873257411 181176728136889559809886117)
  ·
    refine ⟨33970636525666792464353647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181176728136889559809886117 33970636525666792464353647)
    ·
      refine ⟨50955954788500188696530471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33970636525666792464353647 50955954788500188696530471)
      ·
        refine ⟨76433932182750283044795707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50955954788500188696530471 76433932182750283044795707)
        ·
          refine ⟨114650898274125424567193561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76433932182750283044795707 114650898274125424567193561)
          ·
            refine ⟨85988173705594068425395171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114650898274125424567193561 85988173705594068425395171)
            ·
              refine ⟨128982260558391102638092757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85988173705594068425395171 128982260558391102638092757)
              ·
                refine ⟨3023021731837291468080299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 128982260558391102638092757 3023021731837291468080299)
                ·
                  refine ⟨4534532597755937202120449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023021731837291468080299 4534532597755937202120449)
                  ·
                    refine ⟨3400899448316952901590337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4534532597755937202120449 3400899448316952901590337)
                    ·
                      refine ⟨2550674586237714676192753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400899448316952901590337 2550674586237714676192753)
                      ·
                        rfl

theorem cell23_4967421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 1, 2, 2].length) (baseStart_4967421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967421 prefixEnd_4967421 := by exact prefixLift 4967421
  have htrace : WordTrace (prefixWord ++ tailWord_4967421) baseStart_4967421 baseEnd_4967421 := by
    simpa [prefixWord, tailWord_4967421, baseEnd_4967421] using wordTrace_append hprefix tailTrace_4967421
  have hstable : (prefixWord ++ tailWord_4967421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967421).length < 2 ^ (prefixWord ++ tailWord_4967421).sum := by decide
  have hdescent : baseEnd_4967421 < baseStart_4967421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967438 : List Nat := [4, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2]
def baseStart_4967438 : Nat := 118140960795 + 4967438 * 2 ^ 59
def prefixEnd_4967438 : Nat := 4983230072969 + 3 ^ 40 * 4967438 * 2
def baseEnd_4967438 : Nat := 2550683315408841109680175

theorem tailTrace_4967438 : CollatzResearch.WordTrace tailWord_4967438 prefixEnd_4967438 2550683315408841109680175 := by
  unfold tailWord_4967438
  simp only [CollatzResearch.WordTrace]
  refine ⟨22647168522228496464156871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120784898785218647808836645 22647168522228496464156871)
  ·
    refine ⟨33970752783342744696235307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22647168522228496464156871 33970752783342744696235307)
    ·
      refine ⟨50956129175014117044352961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33970752783342744696235307 50956129175014117044352961)
      ·
        refine ⟨38217096881260587783264721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50956129175014117044352961 38217096881260587783264721)
        ·
          refine ⟨28662822660945440837448541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38217096881260587783264721 28662822660945440837448541)
          ·
            refine ⟨10748558497854540314043203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28662822660945440837448541 10748558497854540314043203)
            ·
              refine ⟨16122837746781810471064805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10748558497854540314043203 16122837746781810471064805)
              ·
                refine ⟨3023032077521589463324651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16122837746781810471064805 3023032077521589463324651)
                ·
                  refine ⟨4534548116282384194986977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023032077521589463324651 4534548116282384194986977)
                  ·
                    refine ⟨3400911087211788146240233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4534548116282384194986977 3400911087211788146240233)
                    ·
                      refine ⟨2550683315408841109680175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400911087211788146240233 2550683315408841109680175)
                      ·
                        rfl

theorem cell23_4967438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2].length) (baseStart_4967438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967438 prefixEnd_4967438 := by exact prefixLift 4967438
  have htrace : WordTrace (prefixWord ++ tailWord_4967438) baseStart_4967438 baseEnd_4967438 := by
    simpa [prefixWord, tailWord_4967438, baseEnd_4967438] using wordTrace_append hprefix tailTrace_4967438
  have hstable : (prefixWord ++ tailWord_4967438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967438).length < 2 ^ (prefixWord ++ tailWord_4967438).sum := by decide
  have hdescent : baseEnd_4967438 < baseStart_4967438 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967481 : List Nat := [1, 2, 1, 5, 2, 2, 1, 3, 1, 3, 2]
def baseStart_4967481 : Nat := 118140960795 + 4967481 * 2 ^ 59
def prefixEnd_4967481 : Nat := 4983230072969 + 3 ^ 40 * 4967481 * 2
def baseEnd_4967481 : Nat := 2550705395076984441442477

theorem tailTrace_4967481 : CollatzResearch.WordTrace tailWord_4967481 prefixEnd_4967481 2550705395076984441442477 := by
  unfold tailWord_4967481
  simp only [CollatzResearch.WordTrace]
  refine ⟨181178916516672190057070297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120785944344448126704713531 181178916516672190057070297)
  ·
    refine ⟨135884187387504142542802723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181178916516672190057070297 135884187387504142542802723)
    ·
      refine ⟨203826281081256213814204085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135884187387504142542802723 203826281081256213814204085)
      ·
        refine ⟨19108713851367770045081633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203826281081256213814204085 19108713851367770045081633)
        ·
          refine ⟨14331535388525827533811225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19108713851367770045081633 14331535388525827533811225)
          ·
            refine ⟨10748651541394370650358419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14331535388525827533811225 10748651541394370650358419)
            ·
              refine ⟨16122977312091555975537629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10748651541394370650358419 16122977312091555975537629)
              ·
                refine ⟨6046116492034333490826611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16122977312091555975537629 6046116492034333490826611)
                ·
                  refine ⟨9069174738051500236239917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6046116492034333490826611 9069174738051500236239917)
                  ·
                    refine ⟨3400940526769312588589969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9069174738051500236239917 3400940526769312588589969)
                    ·
                      refine ⟨2550705395076984441442477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3400940526769312588589969 2550705395076984441442477)
                      ·
                        rfl

theorem cell23_4967481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 2, 1, 3, 1, 3, 2].length) (baseStart_4967481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967481 prefixEnd_4967481 := by exact prefixLift 4967481
  have htrace : WordTrace (prefixWord ++ tailWord_4967481) baseStart_4967481 baseEnd_4967481 := by
    simpa [prefixWord, tailWord_4967481, baseEnd_4967481] using wordTrace_append hprefix tailTrace_4967481
  have hstable : (prefixWord ++ tailWord_4967481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967481).length < 2 ^ (prefixWord ++ tailWord_4967481).sum := by decide
  have hdescent : baseEnd_4967481 < baseStart_4967481 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967584 : List Nat := [2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4]
def baseStart_4967584 : Nat := 118140960795 + 4967584 * 2 ^ 59
def prefixEnd_4967584 : Nat := 4983230072969 + 3 ^ 40 * 4967584 * 2
def baseEnd_4967584 : Nat := 2550758283584397538454503

theorem tailTrace_4967584 : CollatzResearch.WordTrace tailWord_4967584 prefixEnd_4967584 2550758283584397538454503 := by
  unfold tailWord_4967584
  simp only [CollatzResearch.WordTrace]
  refine ⟨90591336617649519324034903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120788448823532692432046537 90591336617649519324034903)
  ·
    refine ⟨135887004926474278986052355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90591336617649519324034903 135887004926474278986052355)
    ·
      refine ⟨203830507389711418479078533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135887004926474278986052355 203830507389711418479078533)
      ·
        refine ⟨38218220135570890964827225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203830507389711418479078533 38218220135570890964827225)
        ·
          refine ⟨28663665101678168223620419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38218220135570890964827225 28663665101678168223620419)
          ·
            refine ⟨42995497652517252335430629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28663665101678168223620419 42995497652517252335430629)
            ·
              refine ⟨8061655809846984812893243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42995497652517252335430629 8061655809846984812893243)
              ·
                refine ⟨12092483714770477219339865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8061655809846984812893243 12092483714770477219339865)
                ·
                  refine ⟨9069362786077857914504899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12092483714770477219339865 9069362786077857914504899)
                  ·
                    refine ⟨13604044179116786871757349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9069362786077857914504899 13604044179116786871757349)
                    ·
                      refine ⟨2550758283584397538454503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13604044179116786871757349 2550758283584397538454503)
                      ·
                        rfl

theorem cell23_4967584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 4].length) (baseStart_4967584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967584 prefixEnd_4967584 := by exact prefixLift 4967584
  have htrace : WordTrace (prefixWord ++ tailWord_4967584) baseStart_4967584 baseEnd_4967584 := by
    simpa [prefixWord, tailWord_4967584, baseEnd_4967584] using wordTrace_append hprefix tailTrace_4967584
  have hstable : (prefixWord ++ tailWord_4967584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967584).length < 2 ^ (prefixWord ++ tailWord_4967584).sum := by decide
  have hdescent : baseEnd_4967584 < baseStart_4967584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967587 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 3]
def baseStart_4967587 : Nat := 118140960795 + 4967587 * 2 ^ 59
def prefixEnd_4967587 : Nat := 4983230072969 + 3 ^ 40 * 4967587 * 2
def baseEnd_4967587 : Nat := 2550759824026361026716989

theorem tailTrace_4967587 : CollatzResearch.WordTrace tailWord_4967587 prefixEnd_4967587 2550759824026361026716989 := by
  unfold tailWord_4967587
  simp only [CollatzResearch.WordTrace]
  refine ⟨181182782654288170160429015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120788521769525446773619343 181182782654288170160429015)
  ·
    refine ⟨271774173981432255240643523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181182782654288170160429015 271774173981432255240643523)
    ·
      refine ⟨407661260972148382860965285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271774173981432255240643523 407661260972148382860965285)
      ·
        refine ⟨76436486432277821786430991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407661260972148382860965285 76436486432277821786430991)
        ·
          refine ⟨114654729648416732679646487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76436486432277821786430991 114654729648416732679646487)
          ·
            refine ⟨171982094472625099019469731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114654729648416732679646487 171982094472625099019469731)
            ·
              refine ⟨257973141708937648529204597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171982094472625099019469731 257973141708937648529204597)
              ·
                refine ⟨24184982035212904549612931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 257973141708937648529204597 24184982035212904549612931)
                ·
                  refine ⟨36277473052819356824419397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24184982035212904549612931 36277473052819356824419397)
                  ·
                    refine ⟨6802026197403629404578637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36277473052819356824419397 6802026197403629404578637)
                    ·
                      refine ⟨2550759824026361026716989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6802026197403629404578637 2550759824026361026716989)
                      ·
                        rfl

theorem cell23_4967587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 4, 3].length) (baseStart_4967587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967587 prefixEnd_4967587 := by exact prefixLift 4967587
  have htrace : WordTrace (prefixWord ++ tailWord_4967587) baseStart_4967587 baseEnd_4967587 := by
    simpa [prefixWord, tailWord_4967587, baseEnd_4967587] using wordTrace_append hprefix tailTrace_4967587
  have hstable : (prefixWord ++ tailWord_4967587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967587).length < 2 ^ (prefixWord ++ tailWord_4967587).sum := by decide
  have hdescent : baseEnd_4967587 < baseStart_4967587 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967638 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 1, 4, 3]
def baseStart_4967638 : Nat := 118140960795 + 4967638 * 2 ^ 59
def prefixEnd_4967638 : Nat := 4983230072969 + 3 ^ 40 * 4967638 * 2
def baseEnd_4967638 : Nat := 2550786011539740327179255

theorem tailTrace_4967638 : CollatzResearch.WordTrace tailWord_4967638 prefixEnd_4967638 2550786011539740327179255 := by
  unfold tailWord_4967638
  simp only [CollatzResearch.WordTrace]
  refine ⟨11324040173568962866908473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120789761851402270580357045 11324040173568962866908473)
  ·
    refine ⟨8493030130176722150181355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11324040173568962866908473 8493030130176722150181355)
    ·
      refine ⟨12739545195265083225272033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8493030130176722150181355 12739545195265083225272033)
      ·
        refine ⟨9554658896448812418954025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12739545195265083225272033 9554658896448812418954025)
        ·
          refine ⟨7165994172336609314215519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9554658896448812418954025 7165994172336609314215519)
          ·
            refine ⟨10748991258504913971323279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7165994172336609314215519 10748991258504913971323279)
            ·
              refine ⟨16123486887757370956984919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10748991258504913971323279 16123486887757370956984919)
              ·
                refine ⟨24185230331636056435477379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16123486887757370956984919 24185230331636056435477379)
                ·
                  refine ⟨36277845497454084653216069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24185230331636056435477379 36277845497454084653216069)
                  ·
                    refine ⟨6802096030772640872478013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36277845497454084653216069 6802096030772640872478013)
                    ·
                      refine ⟨2550786011539740327179255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6802096030772640872478013 2550786011539740327179255)
                      ·
                        rfl

theorem cell23_4967638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_4967638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967638 prefixEnd_4967638 := by exact prefixLift 4967638
  have htrace : WordTrace (prefixWord ++ tailWord_4967638) baseStart_4967638 baseEnd_4967638 := by
    simpa [prefixWord, tailWord_4967638, baseEnd_4967638] using wordTrace_append hprefix tailTrace_4967638
  have hstable : (prefixWord ++ tailWord_4967638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967638).length < 2 ^ (prefixWord ++ tailWord_4967638).sum := by decide
  have hdescent : baseEnd_4967638 < baseStart_4967638 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967645 : List Nat := [1, 4, 3, 2, 2, 1, 2, 3, 1, 4]
def baseStart_4967645 : Nat := 118140960795 + 4967645 * 2 ^ 59
def prefixEnd_4967645 : Nat := 4983230072969 + 3 ^ 40 * 4967645 * 2
def baseEnd_4967645 : Nat := 850263201968107266597241

theorem tailTrace_4967645 : CollatzResearch.WordTrace tailWord_4967645 prefixEnd_4967645 850263201968107266597241 := by
  unfold tailWord_4967645
  simp only [CollatzResearch.WordTrace]
  refine ⟨181184898088078046066040389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120789932058718697377360259 181184898088078046066040389)
  ·
    refine ⟨33972168391514633637382573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181184898088078046066040389 33972168391514633637382573)
    ·
      refine ⟨12739563146817987614018465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33972168391514633637382573 12739563146817987614018465)
      ·
        refine ⟨9554672360113490710513849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12739563146817987614018465 9554672360113490710513849)
        ·
          refine ⟨7166004270085118032885387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9554672360113490710513849 7166004270085118032885387)
          ·
            refine ⟨10749006405127677049328081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166004270085118032885387 10749006405127677049328081)
            ·
              refine ⟨8061754803845757786996061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10749006405127677049328081 8061754803845757786996061)
              ·
                refine ⟨3023158051442159170123523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8061754803845757786996061 3023158051442159170123523)
                ·
                  refine ⟨4534737077163238755185285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023158051442159170123523 4534737077163238755185285)
                  ·
                    refine ⟨850263201968107266597241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534737077163238755185285 850263201968107266597241)
                    ·
                      rfl

theorem cell23_4967645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_4967645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967645 prefixEnd_4967645 := by exact prefixLift 4967645
  have htrace : WordTrace (prefixWord ++ tailWord_4967645) baseStart_4967645 baseEnd_4967645 := by
    simpa [prefixWord, tailWord_4967645, baseEnd_4967645] using wordTrace_append hprefix tailTrace_4967645
  have hstable : (prefixWord ++ tailWord_4967645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967645).length < 2 ^ (prefixWord ++ tailWord_4967645).sum := by decide
  have hdescent : baseEnd_4967645 < baseStart_4967645 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967691 : List Nat := [1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 4]
def baseStart_4967691 : Nat := 118140960795 + 4967691 * 2 ^ 59
def prefixEnd_4967691 : Nat := 4983230072969 + 3 ^ 40 * 4967691 * 2
def baseEnd_4967691 : Nat := 2550813226014428619816511

theorem tailTrace_4967691 : CollatzResearch.WordTrace tailWord_4967691 prefixEnd_4967691 2550813226014428619816511 := by
  unfold tailWord_4967691
  simp only [CollatzResearch.WordTrace]
  refine ⟨181186575845911395922214927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120791050563940930614809951 181186575845911395922214927)
  ·
    refine ⟨271779863768867093883322391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181186575845911395922214927 271779863768867093883322391)
    ·
      refine ⟨407669795653300640824983587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271779863768867093883322391 407669795653300640824983587)
      ·
        refine ⟨611504693479950961237475381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407669795653300640824983587 611504693479950961237475381)
        ·
          refine ⟨57328565013745402616013317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 611504693479950961237475381 57328565013745402616013317)
          ·
            refine ⟨10749105940077262990502497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57328565013745402616013317 10749105940077262990502497)
            ·
              refine ⟨8061829455057947242876873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10749105940077262990502497 8061829455057947242876873)
              ·
                refine ⟨6046372091293460432157655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8061829455057947242876873 6046372091293460432157655)
                ·
                  refine ⟨9069558136940190648236483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6046372091293460432157655 9069558136940190648236483)
                  ·
                    refine ⟨13604337205410285972354725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9069558136940190648236483 13604337205410285972354725)
                    ·
                      refine ⟨2550813226014428619816511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13604337205410285972354725 2550813226014428619816511)
                      ·
                        rfl

theorem cell23_4967691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 2, 2, 1, 1, 4].length) (baseStart_4967691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967691 prefixEnd_4967691 := by exact prefixLift 4967691
  have htrace : WordTrace (prefixWord ++ tailWord_4967691) baseStart_4967691 baseEnd_4967691 := by
    simpa [prefixWord, tailWord_4967691, baseEnd_4967691] using wordTrace_append hprefix tailTrace_4967691
  have hstable : (prefixWord ++ tailWord_4967691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967691).length < 2 ^ (prefixWord ++ tailWord_4967691).sum := by decide
  have hdescent : baseEnd_4967691 < baseStart_4967691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967697 : List Nat := [1, 2, 2, 1, 1, 4, 3, 9]
def baseStart_4967697 : Nat := 118140960795 + 4967697 * 2 ^ 59
def prefixEnd_4967697 : Nat := 4983230072969 + 3 ^ 40 * 4967697 * 2
def baseEnd_4967697 : Nat := 94474678033272429494129

theorem tailTrace_4967697 : CollatzResearch.WordTrace tailWord_4967697 prefixEnd_4967697 94474678033272429494129 := by
  unfold tailWord_4967697
  simp only [CollatzResearch.WordTrace]
  refine ⟨181186794683889658946933345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120791196455926439297955563 181186794683889658946933345)
  ·
    refine ⟨135890096012917244210200009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181186794683889658946933345 135890096012917244210200009)
    ·
      refine ⟨101917572009687933157650007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135890096012917244210200009 101917572009687933157650007)
      ·
        refine ⟨152876358014531899736475011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101917572009687933157650007 152876358014531899736475011)
        ·
          refine ⟨229314537021797849604712517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152876358014531899736475011 229314537021797849604712517)
          ·
            refine ⟨42996475691587096800883597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229314537021797849604712517 42996475691587096800883597)
            ·
              refine ⟨16123678384345161300331349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42996475691587096800883597 16123678384345161300331349)
              ·
                refine ⟨94474678033272429494129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16123678384345161300331349 94474678033272429494129)
                ·
                  rfl

theorem cell23_4967697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 3, 9].length) (baseStart_4967697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967697 prefixEnd_4967697 := by exact prefixLift 4967697
  have htrace : WordTrace (prefixWord ++ tailWord_4967697) baseStart_4967697 baseEnd_4967697 := by
    simpa [prefixWord, tailWord_4967697, baseEnd_4967697] using wordTrace_append hprefix tailTrace_4967697
  have hstable : (prefixWord ++ tailWord_4967697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967697).length < 2 ^ (prefixWord ++ tailWord_4967697).sum := by decide
  have hdescent : baseEnd_4967697 < baseStart_4967697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967711 : List Nat := [1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 5]
def baseStart_4967711 : Nat := 118140960795 + 4967711 * 2 ^ 59
def prefixEnd_4967711 : Nat := 4983230072969 + 3 ^ 40 * 4967711 * 2
def baseEnd_4967711 : Nat := 2550823495627518541566419

theorem tailTrace_4967711 : CollatzResearch.WordTrace tailWord_4967711 prefixEnd_4967711 2550823495627518541566419 := by
  unfold tailWord_4967711
  simp only [CollatzResearch.WordTrace]
  refine ⟨181187305305838939337942987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120791536870559292891961991 181187305305838939337942987)
  ·
    refine ⟨271780957958758409006914481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181187305305838939337942987 271780957958758409006914481)
    ·
      refine ⟨203835718469068806755185861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271780957958758409006914481 203835718469068806755185861)
      ·
        refine ⟨38219197212950401266597349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203835718469068806755185861 38219197212950401266597349)
        ·
          refine ⟨7166099477428200237487003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38219197212950401266597349 7166099477428200237487003)
          ·
            refine ⟨10749149216142300356230505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166099477428200237487003 10749149216142300356230505)
            ·
              refine ⟨8061861912106725267172879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10749149216142300356230505 8061861912106725267172879)
              ·
                refine ⟨12092792868160087900759319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8061861912106725267172879 12092792868160087900759319)
                ·
                  refine ⟨18139189302240131851138979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12092792868160087900759319 18139189302240131851138979)
                  ·
                    refine ⟨27208783953360197776708469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18139189302240131851138979 27208783953360197776708469)
                    ·
                      refine ⟨2550823495627518541566419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27208783953360197776708469 2550823495627518541566419)
                      ·
                        rfl

theorem cell23_4967711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_4967711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967711 prefixEnd_4967711 := by exact prefixLift 4967711
  have htrace : WordTrace (prefixWord ++ tailWord_4967711) baseStart_4967711 baseEnd_4967711 := by
    simpa [prefixWord, tailWord_4967711, baseEnd_4967711] using wordTrace_append hprefix tailTrace_4967711
  have hstable : (prefixWord ++ tailWord_4967711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967711).length < 2 ^ (prefixWord ++ tailWord_4967711).sum := by decide
  have hdescent : baseEnd_4967711 < baseStart_4967711 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967727 : List Nat := [1, 1, 2, 1, 2, 1, 3, 3, 2, 7]
def baseStart_4967727 : Nat := 118140960795 + 4967727 * 2 ^ 59
def prefixEnd_4967727 : Nat := 4983230072969 + 3 ^ 40 * 4967727 * 2
def baseEnd_4967727 : Nat := 850277237105996826322115

theorem tailTrace_4967727 : CollatzResearch.WordTrace tailWord_4967727 prefixEnd_4967727 850277237105996826322115 := by
  unfold tailWord_4967727
  simp only [CollatzResearch.WordTrace]
  refine ⟨181187888873780974070525435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120791925915853982713683623 181187888873780974070525435)
  ·
    refine ⟨271781833310671461105788153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181187888873780974070525435 271781833310671461105788153)
    ·
      refine ⟨203836374983003595829341115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271781833310671461105788153 203836374983003595829341115)
      ·
        refine ⟨305754562474505393744011673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203836374983003595829341115 305754562474505393744011673)
        ·
          refine ⟨229315921855879045308008755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305754562474505393744011673 229315921855879045308008755)
          ·
            refine ⟨343973882783818567962013133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229315921855879045308008755 343973882783818567962013133)
            ·
              refine ⟨128990206043931962985754925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343973882783818567962013133 128990206043931962985754925)
              ·
                refine ⟨48371327266474486119658097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128990206043931962985754925 48371327266474486119658097)
                ·
                  refine ⟨36278495449855864589743573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48371327266474486119658097 36278495449855864589743573)
                  ·
                    refine ⟨850277237105996826322115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36278495449855864589743573 850277237105996826322115)
                    ·
                      rfl

theorem cell23_4967727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 3, 3, 2, 7].length) (baseStart_4967727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967727 prefixEnd_4967727 := by exact prefixLift 4967727
  have htrace : WordTrace (prefixWord ++ tailWord_4967727) baseStart_4967727 baseEnd_4967727 := by
    simpa [prefixWord, tailWord_4967727, baseEnd_4967727] using wordTrace_append hprefix tailTrace_4967727
  have hstable : (prefixWord ++ tailWord_4967727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967727).length < 2 ^ (prefixWord ++ tailWord_4967727).sum := by decide
  have hdescent : baseEnd_4967727 < baseStart_4967727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967745 : List Nat := [1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 3]
def baseStart_4967745 : Nat := 118140960795 + 4967745 * 2 ^ 59
def prefixEnd_4967745 : Nat := 4983230072969 + 3 ^ 40 * 4967745 * 2
def baseEnd_4967745 : Nat := 2550840953969771408541263

theorem tailTrace_4967745 : CollatzResearch.WordTrace tailWord_4967745 prefixEnd_4967745 2550840953969771408541263 := by
  unfold tailWord_4967745
  simp only [CollatzResearch.WordTrace]
  refine ⟨181188545387715763144680689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120792363591810508763120459 181188545387715763144680689)
  ·
    refine ⟨135891409040786822358510517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181188545387715763144680689 135891409040786822358510517)
    ·
      refine ⟨12739819597573764596110361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135891409040786822358510517 12739819597573764596110361)
      ·
        refine ⟨9554864698180323447082771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12739819597573764596110361 9554864698180323447082771)
        ·
          refine ⟨14332297047270485170624157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9554864698180323447082771 14332297047270485170624157)
          ·
            refine ⟨5374611392726431938984059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14332297047270485170624157 5374611392726431938984059)
            ·
              refine ⟨8061917089089647908476089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5374611392726431938984059 8061917089089647908476089)
              ·
                refine ⟨6046437816817235931357067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8061917089089647908476089 6046437816817235931357067)
                ·
                  refine ⟨9069656725225853897035601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6046437816817235931357067 9069656725225853897035601)
                  ·
                    refine ⟨6802242543919390422776701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9069656725225853897035601 6802242543919390422776701)
                    ·
                      refine ⟨2550840953969771408541263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6802242543919390422776701 2550840953969771408541263)
                      ·
                        rfl

theorem cell23_4967745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_4967745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967745 prefixEnd_4967745 := by exact prefixLift 4967745
  have htrace : WordTrace (prefixWord ++ tailWord_4967745) baseStart_4967745 baseEnd_4967745 := by
    simpa [prefixWord, tailWord_4967745, baseEnd_4967745] using wordTrace_append hprefix tailTrace_4967745
  have hstable : (prefixWord ++ tailWord_4967745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967745).length < 2 ^ (prefixWord ++ tailWord_4967745).sum := by decide
  have hdescent : baseEnd_4967745 < baseStart_4967745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967747 : List Nat := [1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8]
def baseStart_4967747 : Nat := 118140960795 + 4967747 * 2 ^ 59
def prefixEnd_4967747 : Nat := 4983230072969 + 3 ^ 40 * 4967747 * 2
def baseEnd_4967747 : Nat := 2550841980931080400716253

theorem tailTrace_4967747 : CollatzResearch.WordTrace tailWord_4967747 prefixEnd_4967747 2550841980931080400716253 := by
  unfold tailWord_4967747
  simp only [CollatzResearch.WordTrace]
  refine ⟨181188618333708517486253495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120792412222472344990835663 181188618333708517486253495)
  ·
    refine ⟨271782927500562776229380243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181188618333708517486253495 271782927500562776229380243)
    ·
      refine ⟨407674391250844164344070365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271782927500562776229380243 407674391250844164344070365)
      ·
        refine ⟨152877896719066561629026387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407674391250844164344070365 152877896719066561629026387)
        ·
          refine ⟨229316845078599842443539581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152877896719066561629026387 229316845078599842443539581)
          ·
            refine ⟨85993816904474940916327343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229316845078599842443539581 85993816904474940916327343)
            ·
              refine ⟨128990725356712411374491015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85993816904474940916327343 128990725356712411374491015)
              ·
                refine ⟨193486088035068617061736523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 128990725356712411374491015 193486088035068617061736523)
                ·
                  refine ⟨290229132052602925592604785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 193486088035068617061736523 290229132052602925592604785)
                  ·
                    refine ⟨217671849039452194194453589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 290229132052602925592604785 217671849039452194194453589)
                    ·
                      refine ⟨2550841980931080400716253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 217671849039452194194453589 2550841980931080400716253)
                      ·
                        rfl

theorem cell23_4967747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 8].length) (baseStart_4967747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967747 prefixEnd_4967747 := by exact prefixLift 4967747
  have htrace : WordTrace (prefixWord ++ tailWord_4967747) baseStart_4967747 baseEnd_4967747 := by
    simpa [prefixWord, tailWord_4967747, baseEnd_4967747] using wordTrace_append hprefix tailTrace_4967747
  have hstable : (prefixWord ++ tailWord_4967747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967747).length < 2 ^ (prefixWord ++ tailWord_4967747).sum := by decide
  have hdescent : baseEnd_4967747 < baseStart_4967747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967781 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 3, 4, 2]
def baseStart_4967781 : Nat := 118140960795 + 4967781 * 2 ^ 59
def prefixEnd_4967781 : Nat := 4983230072969 + 3 ^ 40 * 4967781 * 2
def baseEnd_4967781 : Nat := 2550859439273333267691097

theorem tailTrace_4967781 : CollatzResearch.WordTrace tailWord_4967781 prefixEnd_4967781 2550859439273333267691097 := by
  unfold tailWord_4967781
  simp only [CollatzResearch.WordTrace]
  refine ⟨181189858415585341292991197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120793238943723560861994131 181189858415585341292991197)
  ·
    refine ⟨67946196905844502984871699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181189858415585341292991197 67946196905844502984871699)
    ·
      refine ⟨101919295358766754477307549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67946196905844502984871699 101919295358766754477307549)
      ·
        refine ⟨38219735759537532928990331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101919295358766754477307549 38219735759537532928990331)
        ·
          refine ⟨57329603639306299393485497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38219735759537532928990331 57329603639306299393485497)
          ·
            refine ⟨42997202729479724545114123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57329603639306299393485497 42997202729479724545114123)
            ·
              refine ⟨64495804094219586817671185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42997202729479724545114123 64495804094219586817671185)
              ·
                refine ⟨48371853070664690113253389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64495804094219586817671185 48371853070664690113253389)
                ·
                  refine ⟨18139444901499258792470021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48371853070664690113253389 18139444901499258792470021)
                  ·
                    refine ⟨3401145919031111023588129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18139444901499258792470021 3401145919031111023588129)
                    ·
                      refine ⟨2550859439273333267691097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401145919031111023588129 2550859439273333267691097)
                      ·
                        rfl

theorem cell23_4967781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 3, 4, 2].length) (baseStart_4967781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967781 prefixEnd_4967781 := by exact prefixLift 4967781
  have htrace : WordTrace (prefixWord ++ tailWord_4967781) baseStart_4967781 baseEnd_4967781 := by
    simpa [prefixWord, tailWord_4967781, baseEnd_4967781] using wordTrace_append hprefix tailTrace_4967781
  have hstable : (prefixWord ++ tailWord_4967781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967781).length < 2 ^ (prefixWord ++ tailWord_4967781).sum := by decide
  have hdescent : baseEnd_4967781 < baseStart_4967781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967804 : List Nat := [2, 2, 2, 1, 1, 1, 5, 2, 7]
def baseStart_4967804 : Nat := 118140960795 + 4967804 * 2 ^ 59
def prefixEnd_4967804 : Nat := 4983230072969 + 3 ^ 40 * 4967804 * 2
def baseEnd_4967804 : Nat := 283430138814265186411499

theorem tailTrace_4967804 : CollatzResearch.WordTrace tailWord_4967804 prefixEnd_4967804 283430138814265186411499 := by
  unfold tailWord_4967804
  simp only [CollatzResearch.WordTrace]
  refine ⟨90595348647251008110539233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120793798196334677480718977 90595348647251008110539233)
  ·
    refine ⟨67946511485438256082904425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90595348647251008110539233 67946511485438256082904425)
    ·
      refine ⟨50959883614078692062178319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67946511485438256082904425 50959883614078692062178319)
      ·
        refine ⟨76439825421118038093267479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50959883614078692062178319 76439825421118038093267479)
        ·
          refine ⟨114659738131677057139901219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76439825421118038093267479 114659738131677057139901219)
          ·
            refine ⟨171989607197515585709851829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114659738131677057139901219 171989607197515585709851829)
            ·
              refine ⟨16124025674767086160298609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 171989607197515585709851829 16124025674767086160298609)
              ·
                refine ⟨12093019256075314620223957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16124025674767086160298609 12093019256075314620223957)
                ·
                  refine ⟨283430138814265186411499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12093019256075314620223957 283430138814265186411499)
                  ·
                    rfl

theorem cell23_4967804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 7].length) (baseStart_4967804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967804 prefixEnd_4967804 := by exact prefixLift 4967804
  have htrace : WordTrace (prefixWord ++ tailWord_4967804) baseStart_4967804 baseEnd_4967804 := by
    simpa [prefixWord, tailWord_4967804, baseEnd_4967804] using wordTrace_append hprefix tailTrace_4967804
  have hstable : (prefixWord ++ tailWord_4967804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967804).length < 2 ^ (prefixWord ++ tailWord_4967804).sum := by decide
  have hdescent : baseEnd_4967804 < baseStart_4967804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967844 : List Nat := [2, 3, 1, 2, 1, 1, 1, 3, 1, 1, 7]
def baseStart_4967844 : Nat := 118140960795 + 4967844 * 2 ^ 59
def prefixEnd_4967844 : Nat := 4983230072969 + 3 ^ 40 * 4967844 * 2
def baseEnd_4967844 : Nat := 2550891788554566521203307

theorem tailTrace_4967844 : CollatzResearch.WordTrace tailWord_4967844 prefixEnd_4967844 2550891788554566521203307 := by
  unfold tailWord_4967844
  simp only [CollatzResearch.WordTrace]
  refine ⟨90596078107178551526267293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120794770809571402035023057 90596078107178551526267293)
  ·
    refine ⟨33973529290191956822350235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90596078107178551526267293 33973529290191956822350235)
    ·
      refine ⟨50960293935287935233525353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33973529290191956822350235 50960293935287935233525353)
      ·
        refine ⟨38220220451465951425144015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50960293935287935233525353 38220220451465951425144015)
        ·
          refine ⟨57330330677198927137716023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38220220451465951425144015 57330330677198927137716023)
          ·
            refine ⟨85995496015798390706574035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57330330677198927137716023 85995496015798390706574035)
            ·
              refine ⟨128993244023697586059861053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85995496015798390706574035 128993244023697586059861053)
              ·
                refine ⟨48372466508886594772447895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128993244023697586059861053 48372466508886594772447895)
                ·
                  refine ⟨72558699763329892158671843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48372466508886594772447895 72558699763329892158671843)
                  ·
                    refine ⟨108838049644994838238007765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72558699763329892158671843 108838049644994838238007765)
                    ·
                      refine ⟨2550891788554566521203307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108838049644994838238007765 2550891788554566521203307)
                      ·
                        rfl

theorem cell23_4967844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 3, 1, 1, 7].length) (baseStart_4967844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967844 prefixEnd_4967844 := by exact prefixLift 4967844
  have htrace : WordTrace (prefixWord ++ tailWord_4967844) baseStart_4967844 baseEnd_4967844 := by
    simpa [prefixWord, tailWord_4967844, baseEnd_4967844] using wordTrace_append hprefix tailTrace_4967844
  have hstable : (prefixWord ++ tailWord_4967844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967844).length < 2 ^ (prefixWord ++ tailWord_4967844).sum := by decide
  have hdescent : baseEnd_4967844 < baseStart_4967844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967871 : List Nat := [1, 1, 2, 2, 2, 1, 1, 4, 1, 6, 2]
def baseStart_4967871 : Nat := 118140960795 + 4967871 * 2 ^ 59
def prefixEnd_4967871 : Nat := 4983230072969 + 3 ^ 40 * 4967871 * 2
def baseEnd_4967871 : Nat := 2550905652532237915565683

theorem tailTrace_4967871 : CollatzResearch.WordTrace tailWord_4967871 prefixEnd_4967871 2550905652532237915565683 := by
  unfold tailWord_4967871
  simp only [CollatzResearch.WordTrace]
  refine ⟨181193140985259286663767467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120795427323506191109178311 181193140985259286663767467)
  ·
    refine ⟨271789711477888929995651201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181193140985259286663767467 271789711477888929995651201)
    ·
      refine ⟨203842283608416697496738401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271789711477888929995651201 203842283608416697496738401)
      ·
        refine ⟨152881712706312523122553801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203842283608416697496738401 152881712706312523122553801)
        ·
          refine ⟨114661284529734392341915351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152881712706312523122553801 114661284529734392341915351)
          ·
            refine ⟨171991926794601588512873027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114661284529734392341915351 171991926794601588512873027)
            ·
              refine ⟨257987890191902382769309541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171991926794601588512873027 257987890191902382769309541)
              ·
                refine ⟨48372729410981696769245539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257987890191902382769309541 48372729410981696769245539)
                ·
                  refine ⟨72559094116472545153868309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48372729410981696769245539 72559094116472545153868309)
                  ·
                    refine ⟨3401207536709650554087577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72559094116472545153868309 3401207536709650554087577)
                    ·
                      refine ⟨2550905652532237915565683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401207536709650554087577 2550905652532237915565683)
                      ·
                        rfl

theorem cell23_4967871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 1, 6, 2].length) (baseStart_4967871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967871 prefixEnd_4967871 := by exact prefixLift 4967871
  have htrace : WordTrace (prefixWord ++ tailWord_4967871) baseStart_4967871 baseEnd_4967871 := by
    simpa [prefixWord, tailWord_4967871, baseEnd_4967871] using wordTrace_append hprefix tailTrace_4967871
  have hstable : (prefixWord ++ tailWord_4967871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967871).length < 2 ^ (prefixWord ++ tailWord_4967871).sum := by decide
  have hdescent : baseEnd_4967871 < baseStart_4967871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967898 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 3, 4]
def baseStart_4967898 : Nat := 118140960795 + 4967898 * 2 ^ 59
def prefixEnd_4967898 : Nat := 4983230072969 + 3 ^ 40 * 4967898 * 2
def baseEnd_4967898 : Nat := 850306505503303103309353

theorem tailTrace_4967898 : CollatzResearch.WordTrace tailWord_4967898 prefixEnd_4967898 850306505503303103309353 := by
  unfold tailWord_4967898
  simp only [CollatzResearch.WordTrace]
  refine ⟨45298531439040367568750087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120796083837440980183333565 45298531439040367568750087)
  ·
    refine ⟨67947797158560551353125131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45298531439040367568750087 67947797158560551353125131)
    ·
      refine ⟨101921695737840827029687697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67947797158560551353125131 101921695737840827029687697)
      ·
        refine ⟨76441271803380620272265773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101921695737840827029687697 76441271803380620272265773)
        ·
          refine ⟨28665476926267732602099665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76441271803380620272265773 28665476926267732602099665)
          ·
            refine ⟨21499107694700799451574749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28665476926267732602099665 21499107694700799451574749)
            ·
              refine ⟨8062165385512799794340531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21499107694700799451574749 8062165385512799794340531)
              ·
                refine ⟨12093248078269199691510797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062165385512799794340531 12093248078269199691510797)
                ·
                  refine ⟨4534968029350949884316549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12093248078269199691510797 4534968029350949884316549)
                  ·
                    refine ⟨850306505503303103309353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4534968029350949884316549 850306505503303103309353)
                    ·
                      rfl

theorem cell23_4967898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 3, 4].length) (baseStart_4967898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967898 prefixEnd_4967898 := by exact prefixLift 4967898
  have htrace : WordTrace (prefixWord ++ tailWord_4967898) baseStart_4967898 baseEnd_4967898 := by
    simpa [prefixWord, tailWord_4967898, baseEnd_4967898] using wordTrace_append hprefix tailTrace_4967898
  have hstable : (prefixWord ++ tailWord_4967898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967898).length < 2 ^ (prefixWord ++ tailWord_4967898).sum := by decide
  have hdescent : baseEnd_4967898 < baseStart_4967898 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967925 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 3]
def baseStart_4967925 : Nat := 118140960795 + 4967925 * 2 ^ 59
def prefixEnd_4967925 : Nat := 4983230072969 + 3 ^ 40 * 4967925 * 2
def baseEnd_4967925 : Nat := 2550933380487580704290435

theorem tailTrace_4967925 : CollatzResearch.WordTrace tailWord_4967925 prefixEnd_4967925 2550933380487580704290435 := by
  unfold tailWord_4967925
  simp only [CollatzResearch.WordTrace]
  refine ⟨181195110527063653886233229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120796740351375769257488819 181195110527063653886233229)
  ·
    refine ⟨67948166447648870207337461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181195110527063653886233229 67948166447648870207337461)
    ·
      refine ⟨6370140604467081581937887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67948166447648870207337461 6370140604467081581937887)
      ·
        refine ⟨9555210906700622372906831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6370140604467081581937887 9555210906700622372906831)
        ·
          refine ⟨14332816360050933559360247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9555210906700622372906831 14332816360050933559360247)
          ·
            refine ⟨21499224540076400339040371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14332816360050933559360247 21499224540076400339040371)
            ·
              refine ⟨32248836810114600508560557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21499224540076400339040371 32248836810114600508560557)
              ·
                refine ⟨12093313803792975190710209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32248836810114600508560557 12093313803792975190710209)
                ·
                  refine ⟨9069985352844731393032657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12093313803792975190710209 9069985352844731393032657)
                  ·
                    refine ⟨6802489014633548544774493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9069985352844731393032657 6802489014633548544774493)
                    ·
                      refine ⟨2550933380487580704290435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6802489014633548544774493 2550933380487580704290435)
                      ·
                        rfl

theorem cell23_4967925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 2, 2, 3].length) (baseStart_4967925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967925 prefixEnd_4967925 := by exact prefixLift 4967925
  have htrace : WordTrace (prefixWord ++ tailWord_4967925) baseStart_4967925 baseEnd_4967925 := by
    simpa [prefixWord, tailWord_4967925, baseEnd_4967925] using wordTrace_append hprefix tailTrace_4967925
  have hstable : (prefixWord ++ tailWord_4967925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967925).length < 2 ^ (prefixWord ++ tailWord_4967925).sum := by decide
  have hdescent : baseEnd_4967925 < baseStart_4967925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967978 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4]
def baseStart_4967978 : Nat := 118140960795 + 4967978 * 2 ^ 59
def prefixEnd_4967978 : Nat := 4983230072969 + 3 ^ 40 * 4967978 * 2
def baseEnd_4967978 : Nat := 2550960594962268996927691

theorem tailTrace_4967978 : CollatzResearch.WordTrace tailWord_4967978 prefixEnd_4967978 2550960594962268996927691 := by
  unfold tailWord_4967978
  simp only [CollatzResearch.WordTrace]
  refine ⟨45299260898967910984478147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120798029063914429291941725 45299260898967910984478147)
  ·
    refine ⟨67948891348451866476717221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45299260898967910984478147 67948891348451866476717221)
    ·
      refine ⟨12740417127834724964384479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67948891348451866476717221 12740417127834724964384479)
      ·
        refine ⟨19110625691752087446576719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12740417127834724964384479 19110625691752087446576719)
        ·
          refine ⟨28665938537628131169865079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19110625691752087446576719 28665938537628131169865079)
          ·
            refine ⟨42998907806442196754797619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28665938537628131169865079 42998907806442196754797619)
            ·
              refine ⟨64498361709663295132196429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42998907806442196754797619 64498361709663295132196429)
              ·
                refine ⟨24186885641123735674573661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64498361709663295132196429 24186885641123735674573661)
                ·
                  refine ⟨9070082115421400877965123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24186885641123735674573661 9070082115421400877965123)
                  ·
                    refine ⟨13605123173132101316947685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9070082115421400877965123 13605123173132101316947685)
                    ·
                      refine ⟨2550960594962268996927691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13605123173132101316947685 2550960594962268996927691)
                      ·
                        rfl

theorem cell23_4967978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_4967978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967978 prefixEnd_4967978 := by exact prefixLift 4967978
  have htrace : WordTrace (prefixWord ++ tailWord_4967978) baseStart_4967978 baseEnd_4967978 := by
    simpa [prefixWord, tailWord_4967978, baseEnd_4967978] using wordTrace_append hprefix tailTrace_4967978
  have hstable : (prefixWord ++ tailWord_4967978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967978).length < 2 ^ (prefixWord ++ tailWord_4967978).sum := by decide
  have hdescent : baseEnd_4967978 < baseStart_4967978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4967982 : List Nat := [4, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2]
def baseStart_4967982 : Nat := 118140960795 + 4967982 * 2 ^ 59
def prefixEnd_4967982 : Nat := 4983230072969 + 3 ^ 40 * 4967982 * 2
def baseEnd_4967982 : Nat := 2550962648884886981277673

theorem tailTrace_4967982 : CollatzResearch.WordTrace tailWord_4967982 prefixEnd_4967982 2550962648884886981277673 := by
  unfold tailWord_4967982
  simp only [CollatzResearch.WordTrace]
  refine ⟨22649648685982144077632275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120798126325238101747372133 22649648685982144077632275)
  ·
    refine ⟨33974473028973216116448413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22649648685982144077632275 33974473028973216116448413)
    ·
      refine ⟨12740427385864956043668155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33974473028973216116448413 12740427385864956043668155)
      ·
        refine ⟨19110641078797434065502233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12740427385864956043668155 19110641078797434065502233)
        ·
          refine ⟨14332980809098075549126675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19110641078797434065502233 14332980809098075549126675)
          ·
            refine ⟨21499471213647113323690013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14332980809098075549126675 21499471213647113323690013)
            ·
              refine ⟨8062301705117667496383755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21499471213647113323690013 8062301705117667496383755)
              ·
                refine ⟨12093452557676501244575633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062301705117667496383755 12093452557676501244575633)
                ·
                  refine ⟨9070089418257375933431725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12093452557676501244575633 9070089418257375933431725)
                  ·
                    refine ⟨3401283531846515975036897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9070089418257375933431725 3401283531846515975036897)
                    ·
                      refine ⟨2550962648884886981277673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401283531846515975036897 2550962648884886981277673)
                      ·
                        rfl

theorem cell23_4967982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_4967982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4967982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4967982 prefixEnd_4967982 := by exact prefixLift 4967982
  have htrace : WordTrace (prefixWord ++ tailWord_4967982) baseStart_4967982 baseEnd_4967982 := by
    simpa [prefixWord, tailWord_4967982, baseEnd_4967982] using wordTrace_append hprefix tailTrace_4967982
  have hstable : (prefixWord ++ tailWord_4967982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4967982).length < 2 ^ (prefixWord ++ tailWord_4967982).sum := by decide
  have hdescent : baseEnd_4967982 < baseStart_4967982 := by decide
  rcases family_descends (prefixWord ++ tailWord_4967982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968001 : List Nat := [1, 2, 5, 1, 1, 1, 12]
def baseStart_4968001 : Nat := 118140960795 + 4968001 * 2 ^ 59
def prefixEnd_4968001 : Nat := 4983230072969 + 3 ^ 40 * 4968001 * 2
def baseEnd_4968001 : Nat := 31493486481695338357285

theorem tailTrace_4968001 : CollatzResearch.WordTrace tailWord_4968001 prefixEnd_4968001 31493486481695338357285 := by
  unfold tailWord_4968001
  simp only [CollatzResearch.WordTrace]
  refine ⟨181197882474788318865999857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120798588316525545910666571 181197882474788318865999857)
  ·
    refine ⟨135898411856091239149499893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181197882474788318865999857 135898411856091239149499893)
    ·
      refine ⟨12740476111508553670265615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 135898411856091239149499893 12740476111508553670265615)
      ·
        refine ⟨19110714167262830505398423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12740476111508553670265615 19110714167262830505398423)
        ·
          refine ⟨28666071250894245758097635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19110714167262830505398423 28666071250894245758097635)
          ·
            refine ⟨42999106876341368637146453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28666071250894245758097635 42999106876341368637146453)
            ·
              refine ⟨31493486481695338357285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 42999106876341368637146453 31493486481695338357285)
              ·
                rfl

theorem cell23_4968001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 12].length) (baseStart_4968001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968001 prefixEnd_4968001 := by exact prefixLift 4968001
  have htrace : WordTrace (prefixWord ++ tailWord_4968001) baseStart_4968001 baseEnd_4968001 := by
    simpa [prefixWord, tailWord_4968001, baseEnd_4968001] using wordTrace_append hprefix tailTrace_4968001
  have hstable : (prefixWord ++ tailWord_4968001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968001).length < 2 ^ (prefixWord ++ tailWord_4968001).sum := by decide
  have hdescent : baseEnd_4968001 < baseStart_4968001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968012 : List Nat := [2, 2, 1, 3, 1, 4, 2, 1, 3, 2, 2]
def baseStart_4968012 : Nat := 118140960795 + 4968012 * 2 ^ 59
def prefixEnd_4968012 : Nat := 4983230072969 + 3 ^ 40 * 4968012 * 2
def baseEnd_4968012 : Nat := 2550978053304521863902535

theorem tailTrace_4968012 : CollatzResearch.WordTrace tailWord_4968012 prefixEnd_4968012 2550978053304521863902535 := by
  unfold tailWord_4968012
  simp only [CollatzResearch.WordTrace]
  refine ⟨90599141838874233872325145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120798855785165645163100193 90599141838874233872325145)
  ·
    refine ⟨67949356379155675404243859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90599141838874233872325145 67949356379155675404243859)
    ·
      refine ⟨101924034568733513106365789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67949356379155675404243859 101924034568733513106365789)
      ·
        refine ⟨38221512963275067414887171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101924034568733513106365789 38221512963275067414887171)
        ·
          refine ⟨57332269444912601122330757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38221512963275067414887171 57332269444912601122330757)
          ·
            refine ⟨10749800520921112710437017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57332269444912601122330757 10749800520921112710437017)
            ·
              refine ⟨8062350390690834532827763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10749800520921112710437017 8062350390690834532827763)
              ·
                refine ⟨12093525586036251799241645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062350390690834532827763 12093525586036251799241645)
                ·
                  refine ⟨4535072094763594424715617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12093525586036251799241645 4535072094763594424715617)
                  ·
                    refine ⟨3401304071072695818536713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535072094763594424715617 3401304071072695818536713)
                    ·
                      refine ⟨2550978053304521863902535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401304071072695818536713 2550978053304521863902535)
                      ·
                        rfl

theorem cell23_4968012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 1, 3, 2, 2].length) (baseStart_4968012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968012 prefixEnd_4968012 := by exact prefixLift 4968012
  have htrace : WordTrace (prefixWord ++ tailWord_4968012) baseStart_4968012 baseEnd_4968012 := by
    simpa [prefixWord, tailWord_4968012, baseEnd_4968012] using wordTrace_append hprefix tailTrace_4968012
  have hstable : (prefixWord ++ tailWord_4968012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968012).length < 2 ^ (prefixWord ++ tailWord_4968012).sum := by decide
  have hdescent : baseEnd_4968012 < baseStart_4968012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968029 : List Nat := [1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 4]
def baseStart_4968029 : Nat := 118140960795 + 4968029 * 2 ^ 59
def prefixEnd_4968029 : Nat := 4983230072969 + 3 ^ 40 * 4968029 * 2
def baseEnd_4968029 : Nat := 2550986782475648297389957

theorem tailTrace_4968029 : CollatzResearch.WordTrace tailWord_4968029 prefixEnd_4968029 2550986782475648297389957 := by
  unfold tailWord_4968029
  simp only [CollatzResearch.WordTrace]
  refine ⟨181198903718686879648019141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120799269145791253098679427 181198903718686879648019141)
  ·
    refine ⟨33974794447253789934003589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181198903718686879648019141 33974794447253789934003589)
    ·
      refine ⟨6370273958860085612625673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33974794447253789934003589 6370273958860085612625673)
      ·
        refine ⟨4777705469145064209469255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6370273958860085612625673 4777705469145064209469255)
        ·
          refine ⟨7166558203717596314203883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4777705469145064209469255 7166558203717596314203883)
          ·
            refine ⟨10749837305576394471305825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166558203717596314203883 10749837305576394471305825)
            ·
              refine ⟨8062377979182295853479369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10749837305576394471305825 8062377979182295853479369)
              ·
                refine ⟨6046783484386721890109527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8062377979182295853479369 6046783484386721890109527)
                ·
                  refine ⟨9070175226580082835164291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6046783484386721890109527 9070175226580082835164291)
                  ·
                    refine ⟨13605262839870124252746437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9070175226580082835164291 13605262839870124252746437)
                    ·
                      refine ⟨2550986782475648297389957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13605262839870124252746437 2550986782475648297389957)
                      ·
                        rfl

theorem cell23_4968029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_4968029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968029 prefixEnd_4968029 := by exact prefixLift 4968029
  have htrace : WordTrace (prefixWord ++ tailWord_4968029) baseStart_4968029 baseEnd_4968029 := by
    simpa [prefixWord, tailWord_4968029, baseEnd_4968029] using wordTrace_append hprefix tailTrace_4968029
  have hstable : (prefixWord ++ tailWord_4968029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968029).length < 2 ^ (prefixWord ++ tailWord_4968029).sum := by decide
  have hdescent : baseEnd_4968029 < baseStart_4968029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968041 : List Nat := [1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 5]
def baseStart_4968041 : Nat := 118140960795 + 4968041 * 2 ^ 59
def prefixEnd_4968041 : Nat := 4983230072969 + 3 ^ 40 * 4968041 * 2
def baseEnd_4968041 : Nat := 2550992944243502250439901

theorem tailTrace_4968041 : CollatzResearch.WordTrace tailWord_4968041 prefixEnd_4968041 2550992944243502250439901 := by
  unfold tailWord_4968041
  simp only [CollatzResearch.WordTrace]
  refine ⟨181199341394643405697455977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120799560929762270464970651 181199341394643405697455977)
  ·
    refine ⟨135899506045982554273091983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181199341394643405697455977 135899506045982554273091983)
    ·
      refine ⟨203849259068973831409637975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135899506045982554273091983 203849259068973831409637975)
      ·
        refine ⟨305773888603460747114456963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203849259068973831409637975 305773888603460747114456963)
        ·
          refine ⟨458660832905191120671685445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305773888603460747114456963 458660832905191120671685445)
          ·
            refine ⟨85998906169723335125941021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 458660832905191120671685445 85998906169723335125941021)
            ·
              refine ⟨32249589813646250672227883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 85998906169723335125941021 32249589813646250672227883)
              ·
                refine ⟨48374384720469376008341825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32249589813646250672227883 48374384720469376008341825)
                ·
                  refine ⟨36280788540352032006256369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48374384720469376008341825 36280788540352032006256369)
                  ·
                    refine ⟨27210591405264024004692277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36280788540352032006256369 27210591405264024004692277)
                    ·
                      refine ⟨2550992944243502250439901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27210591405264024004692277 2550992944243502250439901)
                      ·
                        rfl

theorem cell23_4968041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 2, 5].length) (baseStart_4968041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968041 prefixEnd_4968041 := by exact prefixLift 4968041
  have htrace : WordTrace (prefixWord ++ tailWord_4968041) baseStart_4968041 baseEnd_4968041 := by
    simpa [prefixWord, tailWord_4968041, baseEnd_4968041] using wordTrace_append hprefix tailTrace_4968041
  have hstable : (prefixWord ++ tailWord_4968041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968041).length < 2 ^ (prefixWord ++ tailWord_4968041).sum := by decide
  have hdescent : baseEnd_4968041 < baseStart_4968041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968088 : List Nat := [2, 1, 2, 4, 1, 2, 1, 2, 2, 1, 5]
def baseStart_4968088 : Nat := 118140960795 + 4968088 * 2 ^ 59
def prefixEnd_4968088 : Nat := 4983230072969 + 3 ^ 40 * 4968088 * 2
def baseEnd_4968088 : Nat := 2551017077834263566552185

theorem tailTrace_4968088 : CollatzResearch.WordTrace tailWord_4968088 prefixEnd_4968088 2551017077834263566552185 := by
  unfold tailWord_4968088
  simp only [CollatzResearch.WordTrace]
  refine ⟨90600527812736566362208459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120800703750315421816277945 90600527812736566362208459)
  ·
    refine ⟨135900791719104849543312689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90600527812736566362208459 135900791719104849543312689)
    ·
      refine ⟨101925593789328637157484517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135900791719104849543312689 101925593789328637157484517)
      ·
        refine ⟨19111048835499119467028347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101925593789328637157484517 19111048835499119467028347)
        ·
          refine ⟨28666573253248679200542521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19111048835499119467028347 28666573253248679200542521)
          ·
            refine ⟨21499929939936509400406891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28666573253248679200542521 21499929939936509400406891)
            ·
              refine ⟨32249894909904764100610337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21499929939936509400406891 32249894909904764100610337)
              ·
                refine ⟨24187421182428573075457753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32249894909904764100610337 24187421182428573075457753)
                ·
                  refine ⟨18140565886821429806593315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24187421182428573075457753 18140565886821429806593315)
                  ·
                    refine ⟨27210848830232144709889973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18140565886821429806593315 27210848830232144709889973)
                    ·
                      refine ⟨2551017077834263566552185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27210848830232144709889973 2551017077834263566552185)
                      ·
                        rfl

theorem cell23_4968088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_4968088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968088 prefixEnd_4968088 := by exact prefixLift 4968088
  have htrace : WordTrace (prefixWord ++ tailWord_4968088) baseStart_4968088 baseEnd_4968088 := by
    simpa [prefixWord, tailWord_4968088, baseEnd_4968088] using wordTrace_append hprefix tailTrace_4968088
  have hstable : (prefixWord ++ tailWord_4968088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968088).length < 2 ^ (prefixWord ++ tailWord_4968088).sum := by decide
  have hdescent : baseEnd_4968088 < baseStart_4968088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968119 : List Nat := [1, 1, 3, 1, 5, 2, 2, 2, 2, 2, 2]
def baseStart_4968119 : Nat := 118140960795 + 4968119 * 2 ^ 59
def prefixEnd_4968119 : Nat := 4983230072969 + 3 ^ 40 * 4968119 * 2
def baseEnd_4968119 : Nat := 2551032995734552945264543

theorem tailTrace_4968119 : CollatzResearch.WordTrace tailWord_4968119 prefixEnd_4968119 2551032995734552945264543 := by
  unfold tailWord_4968119
  simp only [CollatzResearch.WordTrace]
  refine ⟨181202186288360825018795411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120801457525573883345863607 181202186288360825018795411)
  ·
    refine ⟨271803279432541237528193117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181202186288360825018795411 271803279432541237528193117)
    ·
      refine ⟨101926229787202964073072419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271803279432541237528193117 101926229787202964073072419)
      ·
        refine ⟨152889344680804446109608629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101926229787202964073072419 152889344680804446109608629)
        ·
          refine ⟨14333376063825416822775809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152889344680804446109608629 14333376063825416822775809)
          ·
            refine ⟨10750032047869062617081857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14333376063825416822775809 10750032047869062617081857)
            ·
              refine ⟨8062524035901796962811393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10750032047869062617081857 8062524035901796962811393)
              ·
                refine ⟨6046893026926347722108545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8062524035901796962811393 6046893026926347722108545)
                ·
                  refine ⟨4535169770194760791581409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6046893026926347722108545 4535169770194760791581409)
                  ·
                    refine ⟨3401377327646070593686057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535169770194760791581409 3401377327646070593686057)
                    ·
                      refine ⟨2551032995734552945264543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401377327646070593686057 2551032995734552945264543)
                      ·
                        rfl

theorem cell23_4968119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 2, 2, 2, 2].length) (baseStart_4968119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968119 prefixEnd_4968119 := by exact prefixLift 4968119
  have htrace : WordTrace (prefixWord ++ tailWord_4968119) baseStart_4968119 baseEnd_4968119 := by
    simpa [prefixWord, tailWord_4968119, baseEnd_4968119] using wordTrace_append hprefix tailTrace_4968119
  have hstable : (prefixWord ++ tailWord_4968119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968119).length < 2 ^ (prefixWord ++ tailWord_4968119).sum := by decide
  have hdescent : baseEnd_4968119 < baseStart_4968119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968125 : List Nat := [1, 4, 1, 2, 1, 2, 3, 4, 5]
def baseStart_4968125 : Nat := 118140960795 + 4968125 * 2 ^ 59
def prefixEnd_4968125 : Nat := 4983230072969 + 3 ^ 40 * 4968125 * 2
def baseEnd_4968125 : Nat := 283448452957608880198835

theorem tailTrace_4968125 : CollatzResearch.WordTrace tailWord_4968125 prefixEnd_4968125 283448452957608880198835 := by
  unfold tailWord_4968125
  simp only [CollatzResearch.WordTrace]
  refine ⟨181202405126339088043513829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120801603417559392029009219 181202405126339088043513829)
  ·
    refine ⟨33975450961188579008158843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181202405126339088043513829 33975450961188579008158843)
    ·
      refine ⟨50963176441782868512238265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33975450961188579008158843 50963176441782868512238265)
      ·
        refine ⟨38222382331337151384178699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50963176441782868512238265 38222382331337151384178699)
        ·
          refine ⟨57333573497005727076268049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38222382331337151384178699 57333573497005727076268049)
          ·
            refine ⟨43000180122754295307201037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57333573497005727076268049 43000180122754295307201037)
            ·
              refine ⟨16125067546032860740200389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43000180122754295307201037 16125067546032860740200389)
              ·
                refine ⟨3023450164881161388787573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16125067546032860740200389 3023450164881161388787573)
                ·
                  refine ⟨283448452957608880198835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3023450164881161388787573 283448452957608880198835)
                  ·
                    rfl

theorem cell23_4968125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 4, 5].length) (baseStart_4968125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968125 prefixEnd_4968125 := by exact prefixLift 4968125
  have htrace : WordTrace (prefixWord ++ tailWord_4968125) baseStart_4968125 baseEnd_4968125 := by
    simpa [prefixWord, tailWord_4968125, baseEnd_4968125] using wordTrace_append hprefix tailTrace_4968125
  have hstable : (prefixWord ++ tailWord_4968125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968125).length < 2 ^ (prefixWord ++ tailWord_4968125).sum := by decide
  have hdescent : baseEnd_4968125 < baseStart_4968125 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968175 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 4, 4, 2]
def baseStart_4968175 : Nat := 118140960795 + 4968175 * 2 ^ 59
def prefixEnd_4968175 : Nat := 4983230072969 + 3 ^ 40 * 4968175 * 2
def baseEnd_4968175 : Nat := 2551061750651204726164285

theorem tailTrace_4968175 : CollatzResearch.WordTrace tailWord_4968175 prefixEnd_4968175 2551061750651204726164285 := by
  unfold tailWord_4968175
  simp only [CollatzResearch.WordTrace]
  refine ⟨181204228776157946582833979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120802819184105297721889319 181204228776157946582833979)
  ·
    refine ⟨271806343164236919874250969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181204228776157946582833979 271806343164236919874250969)
    ·
      refine ⟨203854757373177689905688227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271806343164236919874250969 203854757373177689905688227)
      ·
        refine ⟨305782136059766534858532341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203854757373177689905688227 305782136059766534858532341)
        ·
          refine ⟨28667075255603112642987407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 305782136059766534858532341 28667075255603112642987407)
          ·
            refine ⟨43000612883404668964481111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28667075255603112642987407 43000612883404668964481111)
            ·
              refine ⟨64500919325107003446721667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43000612883404668964481111 64500919325107003446721667)
              ·
                refine ⟨96751378987660505170082501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64500919325107003446721667 96751378987660505170082501)
                ·
                  refine ⟨18140883560186344719390469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96751378987660505170082501 18140883560186344719390469)
                  ·
                    refine ⟨3401415667534939634885713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18140883560186344719390469 3401415667534939634885713)
                    ·
                      refine ⟨2551061750651204726164285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401415667534939634885713 2551061750651204726164285)
                      ·
                        rfl

theorem cell23_4968175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 4, 4, 2].length) (baseStart_4968175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968175 prefixEnd_4968175 := by exact prefixLift 4968175
  have htrace : WordTrace (prefixWord ++ tailWord_4968175) baseStart_4968175 baseEnd_4968175 := by
    simpa [prefixWord, tailWord_4968175, baseEnd_4968175] using wordTrace_append hprefix tailTrace_4968175
  have hstable : (prefixWord ++ tailWord_4968175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968175).length < 2 ^ (prefixWord ++ tailWord_4968175).sum := by decide
  have hdescent : baseEnd_4968175 < baseStart_4968175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968188 : List Nat := [2, 2, 2, 1, 3, 1, 1, 2, 2, 1, 6]
def baseStart_4968188 : Nat := 118140960795 + 4968188 * 2 ^ 59
def prefixEnd_4968188 : Nat := 4983230072969 + 3 ^ 40 * 4968188 * 2
def baseEnd_4968188 : Nat := 2551068425899713175301725

theorem tailTrace_4968188 : CollatzResearch.WordTrace tailWord_4968188 prefixEnd_4968188 2551068425899713175301725 := by
  unfold tailWord_4968188
  simp only [CollatzResearch.WordTrace]
  refine ⟨90602351462555424901528609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120803135283407233202038145 90602351462555424901528609)
  ·
    refine ⟨67951763596916568676146457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90602351462555424901528609 67951763596916568676146457)
    ·
      refine ⟨50963822697687426507109843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67951763596916568676146457 50963822697687426507109843)
      ·
        refine ⟨76445734046531139760664765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50963822697687426507109843 76445734046531139760664765)
        ·
          refine ⟨28667150267449177410249287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76445734046531139760664765 28667150267449177410249287)
          ·
            refine ⟨43000725401173766115373931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28667150267449177410249287 43000725401173766115373931)
            ·
              refine ⟨64501088101760649173060897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43000725401173766115373931 64501088101760649173060897)
              ·
                refine ⟨48375816076320486879795673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64501088101760649173060897 48375816076320486879795673)
                ·
                  refine ⟨36281862057240365159846755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48375816076320486879795673 36281862057240365159846755)
                  ·
                    refine ⟨54422793085860547739770133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36281862057240365159846755 54422793085860547739770133)
                    ·
                      refine ⟨2551068425899713175301725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54422793085860547739770133 2551068425899713175301725)
                      ·
                        rfl

theorem cell23_4968188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 2, 2, 1, 6].length) (baseStart_4968188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968188 prefixEnd_4968188 := by exact prefixLift 4968188
  have htrace : WordTrace (prefixWord ++ tailWord_4968188) baseStart_4968188 baseEnd_4968188 := by
    simpa [prefixWord, tailWord_4968188, baseEnd_4968188] using wordTrace_append hprefix tailTrace_4968188
  have hstable : (prefixWord ++ tailWord_4968188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968188).length < 2 ^ (prefixWord ++ tailWord_4968188).sum := by decide
  have hdescent : baseEnd_4968188 < baseStart_4968188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968265 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 4]
def baseStart_4968265 : Nat := 118140960795 + 4968265 * 2 ^ 59
def prefixEnd_4968265 : Nat := 4983230072969 + 3 ^ 40 * 4968265 * 2
def baseEnd_4968265 : Nat := 2551107963910109374038871

theorem tailTrace_4968265 : CollatzResearch.WordTrace tailWord_4968265 prefixEnd_4968265 2551107963910109374038871 := by
  unfold tailWord_4968265
  simp only [CollatzResearch.WordTrace]
  refine ⟨181207511345831891953610249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120805007563887927969073499 181207511345831891953610249)
  ·
    refine ⟨135905633509373918965207687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181207511345831891953610249 135905633509373918965207687)
    ·
      refine ⟨203858450264060878447811531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135905633509373918965207687 203858450264060878447811531)
      ·
        refine ⟨305787675396091317671717297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203858450264060878447811531 305787675396091317671717297)
        ·
          refine ⟨229340756547068488253787973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305787675396091317671717297 229340756547068488253787973)
          ·
            refine ⟨43001391852575341547585245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 229340756547068488253787973 43001391852575341547585245)
            ·
              refine ⟨16125521944715753080344467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43001391852575341547585245 16125521944715753080344467)
              ·
                refine ⟨24188282917073629620516701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16125521944715753080344467 24188282917073629620516701)
                ·
                  refine ⟨9070606093902611107693763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24188282917073629620516701 9070606093902611107693763)
                  ·
                    refine ⟨13605909140853916661540645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9070606093902611107693763 13605909140853916661540645)
                    ·
                      refine ⟨2551107963910109374038871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13605909140853916661540645 2551107963910109374038871)
                      ·
                        rfl

theorem cell23_4968265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 3, 1, 4].length) (baseStart_4968265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968265 prefixEnd_4968265 := by exact prefixLift 4968265
  have htrace : WordTrace (prefixWord ++ tailWord_4968265) baseStart_4968265 baseEnd_4968265 := by
    simpa [prefixWord, tailWord_4968265, baseEnd_4968265] using wordTrace_append hprefix tailTrace_4968265
  have hstable : (prefixWord ++ tailWord_4968265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968265).length < 2 ^ (prefixWord ++ tailWord_4968265).sum := by decide
  have hdescent : baseEnd_4968265 < baseStart_4968265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968279 : List Nat := [1, 1, 3, 2, 5, 1, 3, 1, 1, 5]
def baseStart_4968279 : Nat := 118140960795 + 4968279 * 2 ^ 59
def prefixEnd_4968279 : Nat := 4983230072969 + 3 ^ 40 * 4968279 * 2
def baseEnd_4968279 : Nat := 850371717546424106421269

theorem tailTrace_4968279 : CollatzResearch.WordTrace tailWord_4968279 prefixEnd_4968279 850371717546424106421269 := by
  unfold tailWord_4968279
  simp only [CollatzResearch.WordTrace]
  refine ⟨181208021967781172344619891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120805347978520781563079927 181208021967781172344619891)
  ·
    refine ⟨271812032951671758516929837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181208021967781172344619891 271812032951671758516929837)
    ·
      refine ⟨101929512356876909443848689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271812032951671758516929837 101929512356876909443848689)
      ·
        refine ⟨76447134267657682082886517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101929512356876909443848689 76447134267657682082886517)
        ·
          refine ⟨7166918837592907695270611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76447134267657682082886517 7166918837592907695270611)
          ·
            refine ⟨10750378256389361542905917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7166918837592907695270611 10750378256389361542905917)
            ·
              refine ⟨4031391846146010578589719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10750378256389361542905917 4031391846146010578589719)
              ·
                refine ⟨6047087769219015867884579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031391846146010578589719 6047087769219015867884579)
                ·
                  refine ⟨9070631653828523801826869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6047087769219015867884579 9070631653828523801826869)
                  ·
                    refine ⟨850371717546424106421269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9070631653828523801826869 850371717546424106421269)
                    ·
                      rfl

theorem cell23_4968279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 1, 3, 1, 1, 5].length) (baseStart_4968279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968279 prefixEnd_4968279 := by exact prefixLift 4968279
  have htrace : WordTrace (prefixWord ++ tailWord_4968279) baseStart_4968279 baseEnd_4968279 := by
    simpa [prefixWord, tailWord_4968279, baseEnd_4968279] using wordTrace_append hprefix tailTrace_4968279
  have hstable : (prefixWord ++ tailWord_4968279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968279).length < 2 ^ (prefixWord ++ tailWord_4968279).sum := by decide
  have hdescent : baseEnd_4968279 < baseStart_4968279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968288 : List Nat := [2, 1, 1, 3, 3, 13]
def baseStart_4968288 : Nat := 118140960795 + 4968288 * 2 ^ 59
def prefixEnd_4968288 : Nat := 4983230072969 + 3 ^ 40 * 4968288 * 2
def baseEnd_4968288 : Nat := 10498435283807254255355

theorem tailTrace_4968288 : CollatzResearch.WordTrace tailWord_4968288 prefixEnd_4968288 10498435283807254255355 := by
  unfold tailWord_4968288
  simp only [CollatzResearch.WordTrace]
  refine ⟨90604175112374283440848759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120805566816499044587798345 90604175112374283440848759)
  ·
    refine ⟨135906262668561425161273139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90604175112374283440848759 135906262668561425161273139)
    ·
      refine ⟨203859394002842137741909709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135906262668561425161273139 203859394002842137741909709)
      ·
        refine ⟨76447272751065801653216141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203859394002842137741909709 76447272751065801653216141)
        ·
          refine ⟨28667727281649675619956053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76447272751065801653216141 28667727281649675619956053)
          ·
            refine ⟨10498435283807254255355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 28667727281649675619956053 10498435283807254255355)
            ·
              rfl

theorem cell23_4968288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 13].length) (baseStart_4968288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968288 prefixEnd_4968288 := by exact prefixLift 4968288
  have htrace : WordTrace (prefixWord ++ tailWord_4968288) baseStart_4968288 baseEnd_4968288 := by
    simpa [prefixWord, tailWord_4968288, baseEnd_4968288] using wordTrace_append hprefix tailTrace_4968288
  have hstable : (prefixWord ++ tailWord_4968288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968288).length < 2 ^ (prefixWord ++ tailWord_4968288).sum := by decide
  have hdescent : baseEnd_4968288 < baseStart_4968288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968295 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 4]
def baseStart_4968295 : Nat := 118140960795 + 4968295 * 2 ^ 59
def prefixEnd_4968295 : Nat := 4983230072969 + 3 ^ 40 * 4968295 * 2
def baseEnd_4968295 : Nat := 2551123368329744256663733

theorem tailTrace_4968295 : CollatzResearch.WordTrace tailWord_4968295 prefixEnd_4968295 2551123368329744256663733 := by
  unfold tailWord_4968295
  simp only [CollatzResearch.WordTrace]
  refine ⟨181208605535723207077202339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120805737023815471384801559 181208605535723207077202339)
  ·
    refine ⟨271812908303584810615803509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181208605535723207077202339 271812908303584810615803509)
    ·
      refine ⟨25482460153461075995231579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271812908303584810615803509 25482460153461075995231579)
      ·
        refine ⟨38223690230191613992847369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25482460153461075995231579 38223690230191613992847369)
        ·
          refine ⟨28667767672643710494635527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38223690230191613992847369 28667767672643710494635527)
          ·
            refine ⟨43001651508965565741953291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28667767672643710494635527 43001651508965565741953291)
            ·
              refine ⟨64502477263448348612929937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43001651508965565741953291 64502477263448348612929937)
              ·
                refine ⟨48376857947586261459697453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64502477263448348612929937 48376857947586261459697453)
                ·
                  refine ⟨18141321730344848047386545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48376857947586261459697453 18141321730344848047386545)
                  ·
                    refine ⟨13605991297758636035539909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18141321730344848047386545 13605991297758636035539909)
                    ·
                      refine ⟨2551123368329744256663733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13605991297758636035539909 2551123368329744256663733)
                      ·
                        rfl

theorem cell23_4968295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_4968295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968295 prefixEnd_4968295 := by exact prefixLift 4968295
  have htrace : WordTrace (prefixWord ++ tailWord_4968295) baseStart_4968295 baseEnd_4968295 := by
    simpa [prefixWord, tailWord_4968295, baseEnd_4968295] using wordTrace_append hprefix tailTrace_4968295
  have hstable : (prefixWord ++ tailWord_4968295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968295).length < 2 ^ (prefixWord ++ tailWord_4968295).sum := by decide
  have hdescent : baseEnd_4968295 < baseStart_4968295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968332 : List Nat := [2, 2, 1, 2, 1, 2, 1, 4, 4, 1, 3]
def baseStart_4968332 : Nat := 118140960795 + 4968332 * 2 ^ 59
def prefixEnd_4968332 : Nat := 4983230072969 + 3 ^ 40 * 4968332 * 2
def baseEnd_4968332 : Nat := 2551142367113960611901063

theorem tailTrace_4968332 : CollatzResearch.WordTrace tailWord_4968332 prefixEnd_4968332 2551142367113960611901063 := by
  unfold tailWord_4968332
  simp only [CollatzResearch.WordTrace]
  refine ⟨90604977518294581198149625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120806636691059441597532833 90604977518294581198149625)
  ·
    refine ⟨67953733138720935898612219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90604977518294581198149625 67953733138720935898612219)
    ·
      refine ⟨101930599708081403847918329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67953733138720935898612219 101930599708081403847918329)
      ·
        refine ⟨76447949781061052885938747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101930599708081403847918329 76447949781061052885938747)
        ·
          refine ⟨114671924671591579328908121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76447949781061052885938747 114671924671591579328908121)
          ·
            refine ⟨86003943503693684496681091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114671924671591579328908121 86003943503693684496681091)
            ·
              refine ⟨129005915255540526745021637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86003943503693684496681091 129005915255540526745021637)
              ·
                refine ⟨24188609110413848764691557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129005915255540526745021637 24188609110413848764691557)
                ·
                  refine ⟨4535364208202596643379667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24188609110413848764691557 4535364208202596643379667)
                  ·
                    refine ⟨6803046312303894965069501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4535364208202596643379667 6803046312303894965069501)
                    ·
                      refine ⟨2551142367113960611901063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6803046312303894965069501 2551142367113960611901063)
                      ·
                        rfl

theorem cell23_4968332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 4, 4, 1, 3].length) (baseStart_4968332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968332 prefixEnd_4968332 := by exact prefixLift 4968332
  have htrace : WordTrace (prefixWord ++ tailWord_4968332) baseStart_4968332 baseEnd_4968332 := by
    simpa [prefixWord, tailWord_4968332, baseEnd_4968332] using wordTrace_append hprefix tailTrace_4968332
  have hstable : (prefixWord ++ tailWord_4968332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968332).length < 2 ^ (prefixWord ++ tailWord_4968332).sum := by decide
  have hdescent : baseEnd_4968332 < baseStart_4968332 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968349 : List Nat := [1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 3]
def baseStart_4968349 : Nat := 118140960795 + 4968349 * 2 ^ 59
def prefixEnd_4968349 : Nat := 4983230072969 + 3 ^ 40 * 4968349 * 2
def baseEnd_4968349 : Nat := 2551151096285087045388485

theorem tailTrace_4968349 : CollatzResearch.WordTrace tailWord_4968349 prefixEnd_4968349 2551151096285087045388485 := by
  unfold tailWord_4968349
  simp only [CollatzResearch.WordTrace]
  refine ⟨181210575077527574299668101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120807050051685049533112067 181210575077527574299668101)
  ·
    refine ⟨33976982827036420181187769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181210575077527574299668101 33976982827036420181187769)
    ·
      refine ⟨25482737120277315135890827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33976982827036420181187769 25482737120277315135890827)
      ·
        refine ⟨38224105680415972703836241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25482737120277315135890827 38224105680415972703836241)
        ·
          refine ⟨28668079260311979527877181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38224105680415972703836241 28668079260311979527877181)
          ·
            refine ⟨10750529722616992322953943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28668079260311979527877181 10750529722616992322953943)
            ·
              refine ⟨16125794583925488484430915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10750529722616992322953943 16125794583925488484430915)
              ·
                refine ⟨24188691875888232726646373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16125794583925488484430915 24188691875888232726646373)
                ·
                  refine ⟨4535379726729043636246195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24188691875888232726646373 4535379726729043636246195)
                  ·
                    refine ⟨6803069590093565454369293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4535379726729043636246195 6803069590093565454369293)
                    ·
                      refine ⟨2551151096285087045388485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6803069590093565454369293 2551151096285087045388485)
                      ·
                        rfl

theorem cell23_4968349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_4968349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968349 prefixEnd_4968349 := by exact prefixLift 4968349
  have htrace : WordTrace (prefixWord ++ tailWord_4968349) baseStart_4968349 baseEnd_4968349 := by
    simpa [prefixWord, tailWord_4968349, baseEnd_4968349] using wordTrace_append hprefix tailTrace_4968349
  have hstable : (prefixWord ++ tailWord_4968349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968349).length < 2 ^ (prefixWord ++ tailWord_4968349).sum := by decide
  have hdescent : baseEnd_4968349 < baseStart_4968349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968350 : List Nat := [4, 3, 1, 3, 1, 1, 2, 1, 3, 2, 2]
def baseStart_4968350 : Nat := 118140960795 + 4968350 * 2 ^ 59
def prefixEnd_4968350 : Nat := 4983230072969 + 3 ^ 40 * 4968350 * 2
def baseEnd_4968350 : Nat := 2551151609765741541475981

theorem tailTrace_4968350 : CollatzResearch.WordTrace tailWord_4968350 prefixEnd_4968350 2551151609765741541475981 := by
  unfold tailWord_4968350
  simp only [CollatzResearch.WordTrace]
  refine ⟨22651326443815493933806813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120807074367015967646969669 22651326443815493933806813)
  ·
    refine ⟨8494247416430810225177555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22651326443815493933806813 8494247416430810225177555)
    ·
      refine ⟨12741371124646215337766333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8494247416430810225177555 12741371124646215337766333)
      ·
        refine ⟨4778014171742330751662375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12741371124646215337766333 4778014171742330751662375)
        ·
          refine ⟨7167021257613496127493563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778014171742330751662375 7167021257613496127493563)
          ·
            refine ⟨10750531886420244191240345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7167021257613496127493563 10750531886420244191240345)
            ·
              refine ⟨8062898914815183143430259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10750531886420244191240345 8062898914815183143430259)
              ·
                refine ⟨12094348372222774715145389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8062898914815183143430259 12094348372222774715145389)
                ·
                  refine ⟨4535380639583540518179521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12094348372222774715145389 4535380639583540518179521)
                  ·
                    refine ⟨3401535479687655388634641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535380639583540518179521 3401535479687655388634641)
                    ·
                      refine ⟨2551151609765741541475981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401535479687655388634641 2551151609765741541475981)
                      ·
                        rfl

theorem cell23_4968350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 1, 3, 2, 2].length) (baseStart_4968350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968350 prefixEnd_4968350 := by exact prefixLift 4968350
  have htrace : WordTrace (prefixWord ++ tailWord_4968350) baseStart_4968350 baseEnd_4968350 := by
    simpa [prefixWord, tailWord_4968350, baseEnd_4968350] using wordTrace_append hprefix tailTrace_4968350
  have hstable : (prefixWord ++ tailWord_4968350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968350).length < 2 ^ (prefixWord ++ tailWord_4968350).sum := by decide
  have hdescent : baseEnd_4968350 < baseStart_4968350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968375 : List Nat := [1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 5]
def baseStart_4968375 : Nat := 118140960795 + 4968375 * 2 ^ 59
def prefixEnd_4968375 : Nat := 4983230072969 + 3 ^ 40 * 4968375 * 2
def baseEnd_4968375 : Nat := 2551164446782103943663365

theorem tailTrace_4968375 : CollatzResearch.WordTrace tailWord_4968375 prefixEnd_4968375 2551164446782103943663365 := by
  unfold tailWord_4968375
  simp only [CollatzResearch.WordTrace]
  refine ⟨181211523375433380740114579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120807682250288920493409719 181211523375433380740114579)
  ·
    refine ⟨271817285063150071110171869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181211523375433380740114579 271817285063150071110171869)
    ·
      refine ⟨101931481898681276666314451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271817285063150071110171869 101931481898681276666314451)
      ·
        refine ⟨152897222848021914999471677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101931481898681276666314451 152897222848021914999471677)
        ·
          refine ⟨57336458568008218124801879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152897222848021914999471677 57336458568008218124801879)
          ·
            refine ⟨86004687852012327187202819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57336458568008218124801879 86004687852012327187202819)
            ·
              refine ⟨129007031778018490780804229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86004687852012327187202819 129007031778018490780804229)
              ·
                refine ⟨24188818458378467021400793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 129007031778018490780804229 24188818458378467021400793)
                ·
                  refine ⟨18141613843783850266050595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24188818458378467021400793 18141613843783850266050595)
                  ·
                    refine ⟨27212420765675775399075893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18141613843783850266050595 27212420765675775399075893)
                    ·
                      refine ⟨2551164446782103943663365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27212420765675775399075893 2551164446782103943663365)
                      ·
                        rfl

theorem cell23_4968375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_4968375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968375 prefixEnd_4968375 := by exact prefixLift 4968375
  have htrace : WordTrace (prefixWord ++ tailWord_4968375) baseStart_4968375 baseEnd_4968375 := by
    simpa [prefixWord, tailWord_4968375, baseEnd_4968375] using wordTrace_append hprefix tailTrace_4968375
  have hstable : (prefixWord ++ tailWord_4968375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968375).length < 2 ^ (prefixWord ++ tailWord_4968375).sum := by decide
  have hdescent : baseEnd_4968375 < baseStart_4968375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968392 : List Nat := [2, 1, 3, 1, 4, 2, 1, 1, 2, 1, 5]
def baseStart_4968392 : Nat := 118140960795 + 4968392 * 2 ^ 59
def prefixEnd_4968392 : Nat := 4983230072969 + 3 ^ 40 * 4968392 * 2
def baseEnd_4968392 : Nat := 2551173175953230377150787

theorem tailTrace_4968392 : CollatzResearch.WordTrace tailWord_4968392 prefixEnd_4968392 2551173175953230377150787 := by
  unfold tailWord_4968392
  simp only [CollatzResearch.WordTrace]
  refine ⟨90606071708185896321741715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120808095610914528428988953 90606071708185896321741715)
  ·
    refine ⟨135909107562278844482612573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90606071708185896321741715 135909107562278844482612573)
    ·
      refine ⟨50965915335854566680979715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135909107562278844482612573 50965915335854566680979715)
      ·
        refine ⟨76448873003781850021469573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50965915335854566680979715 76448873003781850021469573)
        ·
          refine ⟨14334163688209096879025545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76448873003781850021469573 14334163688209096879025545)
          ·
            refine ⟨10750622766156822659269159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14334163688209096879025545 10750622766156822659269159)
            ·
              refine ⟨16125934149235233988903739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10750622766156822659269159 16125934149235233988903739)
              ·
                refine ⟨24188901223852850983355609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16125934149235233988903739 24188901223852850983355609)
                ·
                  refine ⟨18141675917889638237516707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24188901223852850983355609 18141675917889638237516707)
                  ·
                    refine ⟨27212513876834457356275061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18141675917889638237516707 27212513876834457356275061)
                    ·
                      refine ⟨2551173175953230377150787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27212513876834457356275061 2551173175953230377150787)
                      ·
                        rfl

theorem cell23_4968392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 1, 1, 2, 1, 5].length) (baseStart_4968392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968392 prefixEnd_4968392 := by exact prefixLift 4968392
  have htrace : WordTrace (prefixWord ++ tailWord_4968392) baseStart_4968392 baseEnd_4968392 := by
    simpa [prefixWord, tailWord_4968392, baseEnd_4968392] using wordTrace_append hprefix tailTrace_4968392
  have hstable : (prefixWord ++ tailWord_4968392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968392).length < 2 ^ (prefixWord ++ tailWord_4968392).sum := by decide
  have hdescent : baseEnd_4968392 < baseStart_4968392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968423 : List Nat := [1, 1, 5, 2, 3, 1, 1, 3, 2, 2, 2]
def baseStart_4968423 : Nat := 118140960795 + 4968423 * 2 ^ 59
def prefixEnd_4968423 : Nat := 4983230072969 + 3 ^ 40 * 4968423 * 2
def baseEnd_4968423 : Nat := 2551189093853519755863145

theorem tailTrace_4968423 : CollatzResearch.WordTrace tailWord_4968423 prefixEnd_4968423 2551189093853519755863145 := by
  unfold tailWord_4968423
  simp only [CollatzResearch.WordTrace]
  refine ⟨181213274079259484937861923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120808849386172989958574615 181213274079259484937861923)
  ·
    refine ⟨271819911118889227406792885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181213274079259484937861923 271819911118889227406792885)
    ·
      refine ⟨25483116667395865069386833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271819911118889227406792885 25483116667395865069386833)
      ·
        refine ⟨19112337500546898802040125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25483116667395865069386833 19112337500546898802040125)
        ·
          refine ⟨7167126562705087050765047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19112337500546898802040125 7167126562705087050765047)
          ·
            refine ⟨10750689844057630576147571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7167126562705087050765047 10750689844057630576147571)
            ·
              refine ⟨16126034766086445864221357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10750689844057630576147571 16126034766086445864221357)
              ·
                refine ⟨6047263037282417199083009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16126034766086445864221357 6047263037282417199083009)
                ·
                  refine ⟨4535447277961812899312257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047263037282417199083009 4535447277961812899312257)
                  ·
                    refine ⟨3401585458471359674484193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535447277961812899312257 3401585458471359674484193)
                    ·
                      refine ⟨2551189093853519755863145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401585458471359674484193 2551189093853519755863145)
                      ·
                        rfl

theorem cell23_4968423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_4968423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968423 prefixEnd_4968423 := by exact prefixLift 4968423
  have htrace : WordTrace (prefixWord ++ tailWord_4968423) baseStart_4968423 baseEnd_4968423 := by
    simpa [prefixWord, tailWord_4968423, baseEnd_4968423] using wordTrace_append hprefix tailTrace_4968423
  have hstable : (prefixWord ++ tailWord_4968423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968423).length < 2 ^ (prefixWord ++ tailWord_4968423).sum := by decide
  have hdescent : baseEnd_4968423 < baseStart_4968423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968475 : List Nat := [1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6]
def baseStart_4968475 : Nat := 118140960795 + 4968475 * 2 ^ 59
def prefixEnd_4968475 : Nat := 4983230072969 + 3 ^ 40 * 4968475 * 2
def baseEnd_4968475 : Nat := 2551215794847553552412905

theorem tailTrace_4968475 : CollatzResearch.WordTrace tailWord_4968475 prefixEnd_4968475 2551215794847553552412905 := by
  unfold tailWord_4968475
  simp only [CollatzResearch.WordTrace]
  refine ⟨181215170675071097818754879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120810113783380731879169919 181215170675071097818754879)
  ·
    refine ⟨271822756012606646728132319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181215170675071097818754879 271822756012606646728132319)
    ·
      refine ⟨407734134018909970092198479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271822756012606646728132319 407734134018909970092198479)
      ·
        refine ⟨611601201028364955138297719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407734134018909970092198479 611601201028364955138297719)
        ·
          refine ⟨917401801542547432707446579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611601201028364955138297719 917401801542547432707446579)
          ·
            refine ⟨1376102702313821149061169869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 917401801542547432707446579 1376102702313821149061169869)
            ·
              refine ⟨516038513367682930897938701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1376102702313821149061169869 516038513367682930897938701)
              ·
                refine ⟨193514442512881099086727013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 516038513367682930897938701 193514442512881099086727013)
                ·
                  refine ⟨36283957971165206078761315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 193514442512881099086727013 36283957971165206078761315)
                  ·
                    refine ⟨54425936956747809118141973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36283957971165206078761315 54425936956747809118141973)
                    ·
                      refine ⟨2551215794847553552412905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54425936956747809118141973 2551215794847553552412905)
                      ·
                        rfl

theorem cell23_4968475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 1, 6].length) (baseStart_4968475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968475 prefixEnd_4968475 := by exact prefixLift 4968475
  have htrace : WordTrace (prefixWord ++ tailWord_4968475) baseStart_4968475 baseEnd_4968475 := by
    simpa [prefixWord, tailWord_4968475, baseEnd_4968475] using wordTrace_append hprefix tailTrace_4968475
  have hstable : (prefixWord ++ tailWord_4968475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968475).length < 2 ^ (prefixWord ++ tailWord_4968475).sum := by decide
  have hdescent : baseEnd_4968475 < baseStart_4968475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968479 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 2, 4, 2]
def baseStart_4968479 : Nat := 118140960795 + 4968479 * 2 ^ 59
def prefixEnd_4968479 : Nat := 4983230072969 + 3 ^ 40 * 4968479 * 2
def baseEnd_4968479 : Nat := 2551217848770171536762887

theorem tailTrace_4968479 : CollatzResearch.WordTrace tailWord_4968479 prefixEnd_4968479 2551217848770171536762887 := by
  unfold tailWord_4968479
  simp only [CollatzResearch.WordTrace]
  refine ⟨181215316567056606501900491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120810211044704404334600327 181215316567056606501900491)
  ·
    refine ⟨271822974850584909752850737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181215316567056606501900491 271822974850584909752850737)
    ·
      refine ⟨203867231137938682314638053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271822974850584909752850737 203867231137938682314638053)
      ·
        refine ⟨38225105838363502933994635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 203867231137938682314638053 38225105838363502933994635)
        ·
          refine ⟨57337658757545254400991953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38225105838363502933994635 57337658757545254400991953)
          ·
            refine ⟨43003244068158940800743965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57337658757545254400991953 43003244068158940800743965)
            ·
              refine ⟨16126216525559602800278987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43003244068158940800743965 16126216525559602800278987)
              ·
                refine ⟨24189324788339404200418481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16126216525559602800278987 24189324788339404200418481)
                ·
                  refine ⟨18141993591254553150313861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24189324788339404200418481 18141993591254553150313861)
                  ·
                    refine ⟨3401623798360228715683849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18141993591254553150313861 3401623798360228715683849)
                    ·
                      refine ⟨2551217848770171536762887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401623798360228715683849 2551217848770171536762887)
                      ·
                        rfl

theorem cell23_4968479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_4968479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968479 prefixEnd_4968479 := by exact prefixLift 4968479
  have htrace : WordTrace (prefixWord ++ tailWord_4968479) baseStart_4968479 baseEnd_4968479 := by
    simpa [prefixWord, tailWord_4968479, baseEnd_4968479] using wordTrace_append hprefix tailTrace_4968479
  have hstable : (prefixWord ++ tailWord_4968479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968479).length < 2 ^ (prefixWord ++ tailWord_4968479).sum := by decide
  have hdescent : baseEnd_4968479 < baseStart_4968479 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968499 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 3]
def baseStart_4968499 : Nat := 118140960795 + 4968499 * 2 ^ 59
def prefixEnd_4968499 : Nat := 4983230072969 + 3 ^ 40 * 4968499 * 2
def baseEnd_4968499 : Nat := 2551228118383261458512795

theorem tailTrace_4968499 : CollatzResearch.WordTrace tailWord_4968499 prefixEnd_4968499 2551228118383261458512795 := by
  unfold tailWord_4968499
  simp only [CollatzResearch.WordTrace]
  refine ⟨181216046026984149917628551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120810697351322766611752367 181216046026984149917628551)
  ·
    refine ⟨271824069040476224876442827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181216046026984149917628551 271824069040476224876442827)
    ·
      refine ⟨407736103560714337314664241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271824069040476224876442827 407736103560714337314664241)
      ·
        refine ⟨305802077670535752985998181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407736103560714337314664241 305802077670535752985998181)
        ·
          refine ⟨57337889563225453684874659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305802077670535752985998181 57337889563225453684874659)
          ·
            refine ⟨86006834344838180527311989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57337889563225453684874659 86006834344838180527311989)
            ·
              refine ⟨8063140719828579424435499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86006834344838180527311989 8063140719828579424435499)
              ·
                refine ⟨12094711079742869136653249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8063140719828579424435499 12094711079742869136653249)
                ·
                  refine ⟨9071033309807151852489937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12094711079742869136653249 9071033309807151852489937)
                  ·
                    refine ⟨6803274982355363889367453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9071033309807151852489937 6803274982355363889367453)
                    ·
                      refine ⟨2551228118383261458512795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6803274982355363889367453 2551228118383261458512795)
                      ·
                        rfl

theorem cell23_4968499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 2, 2, 3].length) (baseStart_4968499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968499 prefixEnd_4968499 := by exact prefixLift 4968499
  have htrace : WordTrace (prefixWord ++ tailWord_4968499) baseStart_4968499 baseEnd_4968499 := by
    simpa [prefixWord, tailWord_4968499, baseEnd_4968499] using wordTrace_append hprefix tailTrace_4968499
  have hstable : (prefixWord ++ tailWord_4968499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968499).length < 2 ^ (prefixWord ++ tailWord_4968499).sum := by decide
  have hdescent : baseEnd_4968499 < baseStart_4968499 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968549 : List Nat := [1, 3, 1, 3, 2, 2, 1, 4, 1, 5]
def baseStart_4968549 : Nat := 118140960795 + 4968549 * 2 ^ 59
def prefixEnd_4968549 : Nat := 4983230072969 + 3 ^ 40 * 4968549 * 2
def baseEnd_4968549 : Nat := 850417930805328754295855

theorem tailTrace_4968549 : CollatzResearch.WordTrace tailWord_4968549 prefixEnd_4968549 850417930805328754295855 := by
  unfold tailWord_4968549
  simp only [CollatzResearch.WordTrace]
  refine ⟨181217869676803008456948701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120811913117868672304632467 181217869676803008456948701)
  ·
    refine ⟨67956701128801128171355763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181217869676803008456948701 67956701128801128171355763)
    ·
      refine ⟨101935051693201692257033645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67956701128801128171355763 101935051693201692257033645)
      ·
        refine ⟨38225644384950634596387617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101935051693201692257033645 38225644384950634596387617)
        ·
          refine ⟨28669233288712975947290713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38225644384950634596387617 28669233288712975947290713)
          ·
            refine ⟨21501924966534731960468035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28669233288712975947290713 21501924966534731960468035)
            ·
              refine ⟨32252887449802097940702053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21501924966534731960468035 32252887449802097940702053)
              ·
                refine ⟨6047416396837893363881635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32252887449802097940702053 6047416396837893363881635)
                ·
                  refine ⟨9071124595256840045822453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6047416396837893363881635 9071124595256840045822453)
                  ·
                    refine ⟨850417930805328754295855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9071124595256840045822453 850417930805328754295855)
                    ·
                      rfl

theorem cell23_4968549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 1, 4, 1, 5].length) (baseStart_4968549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968549 prefixEnd_4968549 := by exact prefixLift 4968549
  have htrace : WordTrace (prefixWord ++ tailWord_4968549) baseStart_4968549 baseEnd_4968549 := by
    simpa [prefixWord, tailWord_4968549, baseEnd_4968549] using wordTrace_append hprefix tailTrace_4968549
  have hstable : (prefixWord ++ tailWord_4968549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968549).length < 2 ^ (prefixWord ++ tailWord_4968549).sum := by decide
  have hdescent : baseEnd_4968549 < baseStart_4968549 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968566 : List Nat := [5, 1, 1, 2, 1, 2, 2, 3, 1, 5]
def baseStart_4968566 : Nat := 118140960795 + 4968566 * 2 ^ 59
def prefixEnd_4968566 : Nat := 4983230072969 + 3 ^ 40 * 4968566 * 2
def baseEnd_4968566 : Nat := 850420840529037565458329

theorem tailTrace_4968566 : CollatzResearch.WordTrace tailWord_4968566 prefixEnd_4968566 850420840529037565458329 := by
  unfold tailWord_4968566
  simp only [CollatzResearch.WordTrace]
  refine ⟨11326155607358838772519847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120812326478494280240211701 11326155607358838772519847)
  ·
    refine ⟨16989233411038258158779771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11326155607358838772519847 16989233411038258158779771)
    ·
      refine ⟨25483850116557387238169657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16989233411038258158779771 25483850116557387238169657)
      ·
        refine ⟨19112887587418040428627243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25483850116557387238169657 19112887587418040428627243)
        ·
          refine ⟨28669331381127060642940865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19112887587418040428627243 28669331381127060642940865)
          ·
            refine ⟨21501998535845295482205649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28669331381127060642940865 21501998535845295482205649)
            ·
              refine ⟨16126498901883971611654237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21501998535845295482205649 16126498901883971611654237)
              ·
                refine ⟨6047437088206489354370339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16126498901883971611654237 6047437088206489354370339)
                ·
                  refine ⟨9071155632309734031555509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6047437088206489354370339 9071155632309734031555509)
                  ·
                    refine ⟨850420840529037565458329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9071155632309734031555509 850420840529037565458329)
                    ·
                      rfl

theorem cell23_4968566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_4968566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968566 prefixEnd_4968566 := by exact prefixLift 4968566
  have htrace : WordTrace (prefixWord ++ tailWord_4968566) baseStart_4968566 baseEnd_4968566 := by
    simpa [prefixWord, tailWord_4968566, baseEnd_4968566] using wordTrace_append hprefix tailTrace_4968566
  have hstable : (prefixWord ++ tailWord_4968566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968566).length < 2 ^ (prefixWord ++ tailWord_4968566).sum := by decide
  have hdescent : baseEnd_4968566 < baseStart_4968566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968579 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 4, 4]
def baseStart_4968579 : Nat := 118140960795 + 4968579 * 2 ^ 59
def prefixEnd_4968579 : Nat := 4983230072969 + 3 ^ 40 * 4968579 * 2
def baseEnd_4968579 : Nat := 850423065611873715170809

theorem tailTrace_4968579 : CollatzResearch.WordTrace tailWord_4968579 prefixEnd_4968579 850423065611873715170809 := by
  unfold tailWord_4968579
  simp only [CollatzResearch.WordTrace]
  refine ⟨181218963866694323580540791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120812642577796215720360527 181218963866694323580540791)
  ·
    refine ⟨271828445800041485370811187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181218963866694323580540791 271828445800041485370811187)
    ·
      refine ⟨407742668700062228056216781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271828445800041485370811187 407742668700062228056216781)
      ·
        refine ⟨152903500762523335521081293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407742668700062228056216781 152903500762523335521081293)
        ·
          refine ⟨57338812785946250820405485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152903500762523335521081293 57338812785946250820405485)
          ·
            refine ⟨21502054794729844057652057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57338812785946250820405485 21502054794729844057652057)
            ·
              refine ⟨16126541096047383043239043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21502054794729844057652057 16126541096047383043239043)
              ·
                refine ⟨24189811644071074564858565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16126541096047383043239043 24189811644071074564858565)
                ·
                  refine ⟨4535589683263326480910981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24189811644071074564858565 4535589683263326480910981)
                  ·
                    refine ⟨850423065611873715170809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4535589683263326480910981 850423065611873715170809)
                    ·
                      rfl

theorem cell23_4968579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 4, 4].length) (baseStart_4968579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968579 prefixEnd_4968579 := by exact prefixLift 4968579
  have htrace : WordTrace (prefixWord ++ tailWord_4968579) baseStart_4968579 baseEnd_4968579 := by
    simpa [prefixWord, tailWord_4968579, baseEnd_4968579] using wordTrace_append hprefix tailTrace_4968579
  have hstable : (prefixWord ++ tailWord_4968579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968579).length < 2 ^ (prefixWord ++ tailWord_4968579).sum := by decide
  have hdescent : baseEnd_4968579 < baseStart_4968579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968580 : List Nat := [2, 3, 2, 1, 2, 1, 5, 2, 1, 1, 3]
def baseStart_4968580 : Nat := 118140960795 + 4968580 * 2 ^ 59
def prefixEnd_4968580 : Nat := 4983230072969 + 3 ^ 40 * 4968580 * 2
def baseEnd_4968580 : Nat := 2551269710316275641599923

theorem tailTrace_4968580 : CollatzResearch.WordTrace tailWord_4968580 prefixEnd_4968580 2551269710316275641599923 := by
  unfold tailWord_4968580
  simp only [CollatzResearch.WordTrace]
  refine ⟨90609500169845350375663597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120812666893127133834218129 90609500169845350375663597)
  ·
    refine ⟨33978562563692006390873849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90609500169845350375663597 33978562563692006390873849)
    ·
      refine ⟨25483921922769004793155387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33978562563692006390873849 25483921922769004793155387)
      ·
        refine ⟨38225882884153507189733081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25483921922769004793155387 38225882884153507189733081)
        ·
          refine ⟨28669412163115130392299811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38225882884153507189733081 28669412163115130392299811)
          ·
            refine ⟨43004118244672695588449717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28669412163115130392299811 43004118244672695588449717)
            ·
              refine ⟨4031636085438065211417161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43004118244672695588449717 4031636085438065211417161)
              ·
                refine ⟨3023727064078548908562871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4031636085438065211417161 3023727064078548908562871)
                ·
                  refine ⟨4535590596117823362844307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023727064078548908562871 4535590596117823362844307)
                  ·
                    refine ⟨6803385894176735044266461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4535590596117823362844307 6803385894176735044266461)
                    ·
                      refine ⟨2551269710316275641599923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6803385894176735044266461 2551269710316275641599923)
                      ·
                        rfl

theorem cell23_4968580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_4968580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968580 prefixEnd_4968580 := by exact prefixLift 4968580
  have htrace : WordTrace (prefixWord ++ tailWord_4968580) baseStart_4968580 baseEnd_4968580 := by
    simpa [prefixWord, tailWord_4968580, baseEnd_4968580] using wordTrace_append hprefix tailTrace_4968580
  have hstable : (prefixWord ++ tailWord_4968580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968580).length < 2 ^ (prefixWord ++ tailWord_4968580).sum := by decide
  have hdescent : baseEnd_4968580 < baseStart_4968580 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968592 : List Nat := [2, 1, 1, 1, 1, 1, 8, 8]
def baseStart_4968592 : Nat := 118140960795 + 4968592 * 2 ^ 59
def prefixEnd_4968592 : Nat := 4983230072969 + 3 ^ 40 * 4968592 * 2
def baseEnd_4968592 : Nat := 94491698966078873875921

theorem tailTrace_4968592 : CollatzResearch.WordTrace tailWord_4968592 prefixEnd_4968592 94491698966078873875921 := by
  unfold tailWord_4968592
  simp only [CollatzResearch.WordTrace]
  refine ⟨90609719007823613400382015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120812958677098151200509353 90609719007823613400382015)
  ·
    refine ⟨135914578511735420100573023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90609719007823613400382015 135914578511735420100573023)
    ·
      refine ⟨203871867767603130150859535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135914578511735420100573023 203871867767603130150859535)
      ·
        refine ⟨305807801651404695226289303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203871867767603130150859535 305807801651404695226289303)
        ·
          refine ⟨458711702477107042839433955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305807801651404695226289303 458711702477107042839433955)
          ·
            refine ⟨688067553715660564259150933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458711702477107042839433955 688067553715660564259150933)
            ·
              refine ⟨8063291645105397237411925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 688067553715660564259150933 8063291645105397237411925)
              ·
                refine ⟨94491698966078873875921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8063291645105397237411925 94491698966078873875921)
                ·
                  rfl

theorem cell23_4968592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 8, 8].length) (baseStart_4968592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968592 prefixEnd_4968592 := by exact prefixLift 4968592
  have htrace : WordTrace (prefixWord ++ tailWord_4968592) baseStart_4968592 baseEnd_4968592 := by
    simpa [prefixWord, tailWord_4968592, baseEnd_4968592] using wordTrace_append hprefix tailTrace_4968592
  have hstable : (prefixWord ++ tailWord_4968592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968592).length < 2 ^ (prefixWord ++ tailWord_4968592).sum := by decide
  have hdescent : baseEnd_4968592 < baseStart_4968592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968680 : List Nat := [2, 1, 4, 1, 2, 2, 4, 1, 1, 3, 2]
def baseStart_4968680 : Nat := 118140960795 + 4968680 * 2 ^ 59
def prefixEnd_4968680 : Nat := 4983230072969 + 3 ^ 40 * 4968680 * 2
def baseEnd_4968680 : Nat := 2551321058381725250349463

theorem tailTrace_4968680 : CollatzResearch.WordTrace tailWord_4968680 prefixEnd_4968680 2551321058381725250349463 := by
  unfold tailWord_4968680
  simp only [CollatzResearch.WordTrace]
  refine ⟨90611323819664208914983747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120815098426218945219978329 90611323819664208914983747)
  ·
    refine ⟨135916985729496313372475621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90611323819664208914983747 135916985729496313372475621)
    ·
      refine ⟨25484434824280558757339179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135916985729496313372475621 25484434824280558757339179)
      ·
        refine ⟨38226652236420838136008769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25484434824280558757339179 38226652236420838136008769)
        ·
          refine ⟨28669989177315628602006577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38226652236420838136008769 28669989177315628602006577)
          ·
            refine ⟨21502491882986721451504933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28669989177315628602006577 21502491882986721451504933)
            ·
              refine ⟨4031717228060010272157175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21502491882986721451504933 4031717228060010272157175)
              ·
                refine ⟨6047575842090015408235763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031717228060010272157175 6047575842090015408235763)
                ·
                  refine ⟨9071363763135023112353645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6047575842090015408235763 9071363763135023112353645)
                  ·
                    refine ⟨3401761411175633667132617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9071363763135023112353645 3401761411175633667132617)
                    ·
                      refine ⟨2551321058381725250349463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401761411175633667132617 2551321058381725250349463)
                      ·
                        rfl

theorem cell23_4968680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_4968680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968680 prefixEnd_4968680 := by exact prefixLift 4968680
  have htrace : WordTrace (prefixWord ++ tailWord_4968680) baseStart_4968680 baseEnd_4968680 := by
    simpa [prefixWord, tailWord_4968680, baseEnd_4968680] using wordTrace_append hprefix tailTrace_4968680
  have hstable : (prefixWord ++ tailWord_4968680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968680).length < 2 ^ (prefixWord ++ tailWord_4968680).sum := by decide
  have hdescent : baseEnd_4968680 < baseStart_4968680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968689 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 4]
def baseStart_4968689 : Nat := 118140960795 + 4968689 * 2 ^ 59
def prefixEnd_4968689 : Nat := 4983230072969 + 3 ^ 40 * 4968689 * 2
def baseEnd_4968689 : Nat := 2551325679707615715136921

theorem tailTrace_4968689 : CollatzResearch.WordTrace tailWord_4968689 prefixEnd_4968689 2551325679707615715136921 := by
  unfold tailWord_4968689
  simp only [CollatzResearch.WordTrace]
  refine ⟨181222975896295812367045121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120815317264197208244696747 181222975896295812367045121)
  ·
    refine ⟨135917231922221859275283841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181222975896295812367045121 135917231922221859275283841)
    ·
      refine ⟨101937923941666394456462881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135917231922221859275283841 101937923941666394456462881)
      ·
        refine ⟨76453442956249795842347161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101937923941666394456462881 76453442956249795842347161)
        ·
          refine ⟨57340082217187346881760371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76453442956249795842347161 57340082217187346881760371)
          ·
            refine ⟨86010123325781020322640557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57340082217187346881760371 86010123325781020322640557)
            ·
              refine ⟨32253796247167882620990209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86010123325781020322640557 32253796247167882620990209)
              ·
                refine ⟨24190347185375911965742657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32253796247167882620990209 24190347185375911965742657)
                ·
                  refine ⟨18142760389031933974306993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24190347185375911965742657 18142760389031933974306993)
                  ·
                    refine ⟨13607070291773950480730245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18142760389031933974306993 13607070291773950480730245)
                    ·
                      refine ⟨2551325679707615715136921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13607070291773950480730245 2551325679707615715136921)
                      ·
                        rfl

theorem cell23_4968689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_4968689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968689 prefixEnd_4968689 := by exact prefixLift 4968689
  have htrace : WordTrace (prefixWord ++ tailWord_4968689) baseStart_4968689 baseEnd_4968689 := by
    simpa [prefixWord, tailWord_4968689, baseEnd_4968689] using wordTrace_append hprefix tailTrace_4968689
  have hstable : (prefixWord ++ tailWord_4968689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968689).length < 2 ^ (prefixWord ++ tailWord_4968689).sum := by decide
  have hdescent : baseEnd_4968689 < baseStart_4968689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968709 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 3]
def baseStart_4968709 : Nat := 118140960795 + 4968709 * 2 ^ 59
def prefixEnd_4968709 : Nat := 4983230072969 + 3 ^ 40 * 4968709 * 2
def baseEnd_4968709 : Nat := 2551335949320705636886829

theorem tailTrace_4968709 : CollatzResearch.WordTrace tailWord_4968709 prefixEnd_4968709 2551335949320705636886829 := by
  unfold tailWord_4968709
  simp only [CollatzResearch.WordTrace]
  refine ⟨181223705356223355782773181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120815803570815570521848787 181223705356223355782773181)
  ·
    refine ⟨67958889508583758418539943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181223705356223355782773181 67958889508583758418539943)
    ·
      refine ⟨101938334262875637627809915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67958889508583758418539943 101938334262875637627809915)
      ·
        refine ⟨152907501394313456441714873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101938334262875637627809915 152907501394313456441714873)
        ·
          refine ⟨114680626045735092331286155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152907501394313456441714873 114680626045735092331286155)
          ·
            refine ⟨172020939068602638496929233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114680626045735092331286155 172020939068602638496929233)
            ·
              refine ⟨129015704301451978872696925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172020939068602638496929233 129015704301451978872696925)
              ·
                refine ⟨48380889113044492077261347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129015704301451978872696925 48380889113044492077261347)
                ·
                  refine ⟨72571333669566738115892021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48380889113044492077261347 72571333669566738115892021)
                  ·
                    refine ⟨6803562531521881698364877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72571333669566738115892021 6803562531521881698364877)
                    ·
                      refine ⟨2551335949320705636886829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6803562531521881698364877 2551335949320705636886829)
                      ·
                        rfl

theorem cell23_4968709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 5, 3].length) (baseStart_4968709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968709 prefixEnd_4968709 := by exact prefixLift 4968709
  have htrace : WordTrace (prefixWord ++ tailWord_4968709) baseStart_4968709 baseEnd_4968709 := by
    simpa [prefixWord, tailWord_4968709, baseEnd_4968709] using wordTrace_append hprefix tailTrace_4968709
  have hstable : (prefixWord ++ tailWord_4968709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968709).length < 2 ^ (prefixWord ++ tailWord_4968709).sum := by decide
  have hdescent : baseEnd_4968709 < baseStart_4968709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968739 : List Nat := [1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5]
def baseStart_4968739 : Nat := 118140960795 + 4968739 * 2 ^ 59
def prefixEnd_4968739 : Nat := 4983230072969 + 3 ^ 40 * 4968739 * 2
def baseEnd_4968739 : Nat := 2551351353740340519511691

theorem tailTrace_4968739 : CollatzResearch.WordTrace tailWord_4968739 prefixEnd_4968739 2551351353740340519511691 := by
  unfold tailWord_4968739
  simp only [CollatzResearch.WordTrace]
  refine ⟨181224799546114670906365271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120816533030743113937576847 181224799546114670906365271)
  ·
    refine ⟨271837199319172006359547907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181224799546114670906365271 271837199319172006359547907)
    ·
      refine ⟨407755798978758009539321861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271837199319172006359547907 407755798978758009539321861)
      ·
        refine ⟨76454212308517126788622849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407755798978758009539321861 76454212308517126788622849)
        ·
          refine ⟨57340659231387845091467137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76454212308517126788622849 57340659231387845091467137)
          ·
            refine ⟨43005494423540883818600353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57340659231387845091467137 43005494423540883818600353)
            ·
              refine ⟨32254120817655662863950265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43005494423540883818600353 32254120817655662863950265)
              ·
                refine ⟨24190590613241747147962699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32254120817655662863950265 24190590613241747147962699)
                ·
                  refine ⟨36285885919862620721944049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24190590613241747147962699 36285885919862620721944049)
                  ·
                    refine ⟨27214414439896965541458037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36285885919862620721944049 27214414439896965541458037)
                    ·
                      refine ⟨2551351353740340519511691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27214414439896965541458037 2551351353740340519511691)
                      ·
                        rfl

theorem cell23_4968739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_4968739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968739 prefixEnd_4968739 := by exact prefixLift 4968739
  have htrace : WordTrace (prefixWord ++ tailWord_4968739) baseStart_4968739 baseEnd_4968739 := by
    simpa [prefixWord, tailWord_4968739, baseEnd_4968739] using wordTrace_append hprefix tailTrace_4968739
  have hstable : (prefixWord ++ tailWord_4968739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968739).length < 2 ^ (prefixWord ++ tailWord_4968739).sum := by decide
  have hdescent : baseEnd_4968739 < baseStart_4968739 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968750 : List Nat := [4, 1, 3, 3, 1, 2, 1, 1, 7]
def baseStart_4968750 : Nat := 118140960795 + 4968750 * 2 ^ 59
def prefixEnd_4968750 : Nat := 4983230072969 + 3 ^ 40 * 4968750 * 2
def baseEnd_4968750 : Nat := 283484111336393330719349

theorem tailTrace_4968750 : CollatzResearch.WordTrace tailWord_4968750 prefixEnd_4968750 283484111336393330719349 := by
  unfold tailWord_4968750
  simp only [CollatzResearch.WordTrace]
  refine ⟨22653150093634352473126963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120816800499383213190010469 22653150093634352473126963)
  ·
    refine ⟨33979725140451528709690445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22653150093634352473126963 33979725140451528709690445)
    ·
      refine ⟨12742396927669323266133917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33979725140451528709690445 12742396927669323266133917)
      ·
        refine ⟨4778398847875996224800219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12742396927669323266133917 4778398847875996224800219)
        ·
          refine ⟨7167598271813994337200329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778398847875996224800219 7167598271813994337200329)
          ·
            refine ⟨5375698703860495752900247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7167598271813994337200329 5375698703860495752900247)
            ·
              refine ⟨8063548055790743629350371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375698703860495752900247 8063548055790743629350371)
              ·
                refine ⟨12095322083686115444025557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8063548055790743629350371 12095322083686115444025557)
                ·
                  refine ⟨283484111336393330719349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12095322083686115444025557 283484111336393330719349)
                  ·
                    rfl

theorem cell23_4968750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 2, 1, 1, 7].length) (baseStart_4968750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968750 prefixEnd_4968750 := by exact prefixLift 4968750
  have htrace : WordTrace (prefixWord ++ tailWord_4968750) baseStart_4968750 baseEnd_4968750 := by
    simpa [prefixWord, tailWord_4968750, baseEnd_4968750] using wordTrace_append hprefix tailTrace_4968750
  have hstable : (prefixWord ++ tailWord_4968750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968750).length < 2 ^ (prefixWord ++ tailWord_4968750).sum := by decide
  have hdescent : baseEnd_4968750 < baseStart_4968750 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968756 : List Nat := [2, 5, 1, 1, 1, 2, 1, 1, 1, 1, 7]
def baseStart_4968756 : Nat := 118140960795 + 4968756 * 2 ^ 59
def prefixEnd_4968756 : Nat := 4983230072969 + 3 ^ 40 * 4968756 * 2
def baseEnd_4968756 : Nat := 2551360082911466952999113

theorem tailTrace_4968756 : CollatzResearch.WordTrace tailWord_4968756 prefixEnd_4968756 2551360082911466952999113 := by
  unfold tailWord_4968756
  simp only [CollatzResearch.WordTrace]
  refine ⟨90612709793526541404867061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120816946391368721873156081 90612709793526541404867061)
  ·
    refine ⟨8494941543143113256706287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90612709793526541404867061 8494941543143113256706287)
    ·
      refine ⟨12742412314714669885059431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8494941543143113256706287 12742412314714669885059431)
      ·
        refine ⟨19113618472072004827589147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12742412314714669885059431 19113618472072004827589147)
        ·
          refine ⟨28670427708108007241383721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19113618472072004827589147 28670427708108007241383721)
          ·
            refine ⟨21502820781081005431037791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28670427708108007241383721 21502820781081005431037791)
            ·
              refine ⟨32254231171621508146556687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21502820781081005431037791 32254231171621508146556687)
              ·
                refine ⟨48381346757432262219835031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32254231171621508146556687 48381346757432262219835031)
                ·
                  refine ⟨72572020136148393329752547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48381346757432262219835031 72572020136148393329752547)
                  ·
                    refine ⟨108858030204222589994628821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72572020136148393329752547 108858030204222589994628821)
                    ·
                      refine ⟨2551360082911466952999113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108858030204222589994628821 2551360082911466952999113)
                      ·
                        rfl

theorem cell23_4968756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 1, 1, 1, 7].length) (baseStart_4968756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968756 prefixEnd_4968756 := by exact prefixLift 4968756
  have htrace : WordTrace (prefixWord ++ tailWord_4968756) baseStart_4968756 baseEnd_4968756 := by
    simpa [prefixWord, tailWord_4968756, baseEnd_4968756] using wordTrace_append hprefix tailTrace_4968756
  have hstable : (prefixWord ++ tailWord_4968756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968756).length < 2 ^ (prefixWord ++ tailWord_4968756).sum := by decide
  have hdescent : baseEnd_4968756 < baseStart_4968756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968776 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 3, 4]
def baseStart_4968776 : Nat := 118140960795 + 4968776 * 2 ^ 59
def prefixEnd_4968776 : Nat := 4983230072969 + 3 ^ 40 * 4968776 * 2
def baseEnd_4968776 : Nat := 850456784174852291583007

theorem tailTrace_4968776 : CollatzResearch.WordTrace tailWord_4968776 prefixEnd_4968776 850456784174852291583007 := by
  unfold tailWord_4968776
  simp only [CollatzResearch.WordTrace]
  refine ⟨90613074523490313112731091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120817432697987084150308121 90613074523490313112731091)
  ·
    refine ⟨135919611785235469669096637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90613074523490313112731091 135919611785235469669096637)
    ·
      refine ⟨50969854419463301125911239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135919611785235469669096637 50969854419463301125911239)
      ·
        refine ⟨76454781629194951688866859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50969854419463301125911239 76454781629194951688866859)
        ·
          refine ⟨114682172443792427533300289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76454781629194951688866859 114682172443792427533300289)
          ·
            refine ⟨86011629332844320649975217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114682172443792427533300289 86011629332844320649975217)
            ·
              refine ⟨64508721999633240487481413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86011629332844320649975217 64508721999633240487481413)
              ·
                refine ⟨12095385374931232591402765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64508721999633240487481413 12095385374931232591402765)
                ·
                  refine ⟨4535769515599212221776037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12095385374931232591402765 4535769515599212221776037)
                  ·
                    refine ⟨850456784174852291583007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4535769515599212221776037 850456784174852291583007)
                    ·
                      rfl

theorem cell23_4968776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_4968776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968776 prefixEnd_4968776 := by exact prefixLift 4968776
  have htrace : WordTrace (prefixWord ++ tailWord_4968776) baseStart_4968776 baseEnd_4968776 := by
    simpa [prefixWord, tailWord_4968776, baseEnd_4968776] using wordTrace_append hprefix tailTrace_4968776
  have hstable : (prefixWord ++ tailWord_4968776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968776).length < 2 ^ (prefixWord ++ tailWord_4968776).sum := by decide
  have hdescent : baseEnd_4968776 < baseStart_4968776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968786 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3]
def baseStart_4968786 : Nat := 118140960795 + 4968786 * 2 ^ 59
def prefixEnd_4968786 : Nat := 4983230072969 + 3 ^ 40 * 4968786 * 2
def baseEnd_4968786 : Nat := 2551375487331101835623975

theorem tailTrace_4968786 : CollatzResearch.WordTrace tailWord_4968786 prefixEnd_4968786 2551375487331101835623975 := by
  unfold tailWord_4968786
  simp only [CollatzResearch.WordTrace]
  refine ⟨45306628444236099483331553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120817675851296265288884141 45306628444236099483331553)
  ·
    refine ⟨33979971333177074612498665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45306628444236099483331553 33979971333177074612498665)
    ·
      refine ⟨25484978499882805959373999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33979971333177074612498665 25484978499882805959373999)
      ·
        refine ⟨38227467749824208939060999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25484978499882805959373999 38227467749824208939060999)
        ·
          refine ⟨57341201624736313408591499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38227467749824208939060999 57341201624736313408591499)
          ·
            refine ⟨86011802437104470112887249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57341201624736313408591499 86011802437104470112887249)
            ·
              refine ⟨64508851827828352584665437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86011802437104470112887249 64508851827828352584665437)
              ·
                refine ⟨24190819435435632219249539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64508851827828352584665437 24190819435435632219249539)
                ·
                  refine ⟨36286229153153448328874309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24190819435435632219249539 36286229153153448328874309)
                  ·
                    refine ⟨6803667966216271561663933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36286229153153448328874309 6803667966216271561663933)
                    ·
                      refine ⟨2551375487331101835623975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6803667966216271561663933 2551375487331101835623975)
                      ·
                        rfl

theorem cell23_4968786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_4968786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968786 prefixEnd_4968786 := by exact prefixLift 4968786
  have htrace : WordTrace (prefixWord ++ tailWord_4968786) baseStart_4968786 baseEnd_4968786 := by
    simpa [prefixWord, tailWord_4968786, baseEnd_4968786] using wordTrace_append hprefix tailTrace_4968786
  have hstable : (prefixWord ++ tailWord_4968786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968786).length < 2 ^ (prefixWord ++ tailWord_4968786).sum := by decide
  have hdescent : baseEnd_4968786 < baseStart_4968786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968793 : List Nat := [1, 2, 1, 2, 2, 2, 1, 7, 1, 4]
def baseStart_4968793 : Nat := 118140960795 + 4968793 * 2 ^ 59
def prefixEnd_4968793 : Nat := 4983230072969 + 3 ^ 40 * 4968793 * 2
def baseEnd_4968793 : Nat := 850459693898561102745481

theorem tailTrace_4968793 : CollatzResearch.WordTrace tailWord_4968793 prefixEnd_4968793 850459693898561102745481 := by
  unfold tailWord_4968793
  simp only [CollatzResearch.WordTrace]
  refine ⟨181226769087919038128831033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120817846058612692085887355 181226769087919038128831033)
  ·
    refine ⟨135920076815939278596623275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181226769087919038128831033 135920076815939278596623275)
    ·
      refine ⟨203880115223908917894934913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135920076815939278596623275 203880115223908917894934913)
      ·
        refine ⟨152910086417931688421201185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203880115223908917894934913 152910086417931688421201185)
        ·
          refine ⟨114682564813448766315900889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152910086417931688421201185 114682564813448766315900889)
          ·
            refine ⟨86011923610086574736925667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114682564813448766315900889 86011923610086574736925667)
            ·
              refine ⟨129017885415129862105388501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86011923610086574736925667 129017885415129862105388501)
              ·
                refine ⟨3023856689417106143095043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 129017885415129862105388501 3023856689417106143095043)
                ·
                  refine ⟨4535785034125659214642565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3023856689417106143095043 4535785034125659214642565)
                  ·
                    refine ⟨850459693898561102745481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4535785034125659214642565 850459693898561102745481)
                    ·
                      rfl

theorem cell23_4968793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 7, 1, 4].length) (baseStart_4968793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968793 prefixEnd_4968793 := by exact prefixLift 4968793
  have htrace : WordTrace (prefixWord ++ tailWord_4968793) baseStart_4968793 baseEnd_4968793 := by
    simpa [prefixWord, tailWord_4968793, baseEnd_4968793] using wordTrace_append hprefix tailTrace_4968793
  have hstable : (prefixWord ++ tailWord_4968793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968793).length < 2 ^ (prefixWord ++ tailWord_4968793).sum := by decide
  have hdescent : baseEnd_4968793 < baseStart_4968793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968809 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 6]
def baseStart_4968809 : Nat := 118140960795 + 4968809 * 2 ^ 59
def prefixEnd_4968809 : Nat := 4983230072969 + 3 ^ 40 * 4968809 * 2
def baseEnd_4968809 : Nat := 2551387297386155245636369

theorem tailTrace_4968809 : CollatzResearch.WordTrace tailWord_4968809 prefixEnd_4968809 2551387297386155245636369 := by
  unfold tailWord_4968809
  simp only [CollatzResearch.WordTrace]
  refine ⟨181227352655861072861413481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120818235103907381907608987 181227352655861072861413481)
  ·
    refine ⟨135920514491895804646060111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181227352655861072861413481 135920514491895804646060111)
    ·
      refine ⟨203880771737843706969090167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135920514491895804646060111 203880771737843706969090167)
      ·
        refine ⟨305821157606765560453635251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203880771737843706969090167 305821157606765560453635251)
        ·
          refine ⟨458731736410148340680452877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305821157606765560453635251 458731736410148340680452877)
          ·
            refine ⟨172024401153805627755169829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 458731736410148340680452877 172024401153805627755169829)
            ·
              refine ⟨32254575216338555204094343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 172024401153805627755169829 32254575216338555204094343)
              ·
                refine ⟨48381862824507832806141515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32254575216338555204094343 48381862824507832806141515)
                ·
                  refine ⟨72572794236761749209212273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48381862824507832806141515 72572794236761749209212273)
                  ·
                    refine ⟨54429595677571311906909205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72572794236761749209212273 54429595677571311906909205)
                    ·
                      refine ⟨2551387297386155245636369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54429595677571311906909205 2551387297386155245636369)
                      ·
                        rfl

theorem cell23_4968809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 2, 6].length) (baseStart_4968809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968809 prefixEnd_4968809 := by exact prefixLift 4968809
  have htrace : WordTrace (prefixWord ++ tailWord_4968809) baseStart_4968809 baseEnd_4968809 := by
    simpa [prefixWord, tailWord_4968809, baseEnd_4968809] using wordTrace_append hprefix tailTrace_4968809
  have hstable : (prefixWord ++ tailWord_4968809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968809).length < 2 ^ (prefixWord ++ tailWord_4968809).sum := by decide
  have hdescent : baseEnd_4968809 < baseStart_4968809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968834 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 2, 1, 4]
def baseStart_4968834 : Nat := 118140960795 + 4968834 * 2 ^ 59
def prefixEnd_4968834 : Nat := 4983230072969 + 3 ^ 40 * 4968834 * 2
def baseEnd_4968834 : Nat := 2551400134402517647823755

theorem tailTrace_4968834 : CollatzResearch.WordTrace tailWord_4968834 prefixEnd_4968834 2551400134402517647823755 := by
  unfold tailWord_4968834
  simp only [CollatzResearch.WordTrace]
  refine ⟨45307066120192625532768389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120818842987180334754049037 45307066120192625532768389)
  ·
    refine ⟨8495074897536117287394073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45307066120192625532768389 8495074897536117287394073)
    ·
      refine ⟨6371306173152087965545555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8495074897536117287394073 6371306173152087965545555)
      ·
        refine ⟨9556959259728131948318333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6371306173152087965545555 9556959259728131948318333)
        ·
          refine ⟨3583859722398049480619375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9556959259728131948318333 3583859722398049480619375)
          ·
            refine ⟨5375789583597074220929063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3583859722398049480619375 5375789583597074220929063)
            ·
              refine ⟨8063684375395611331393595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5375789583597074220929063 8063684375395611331393595)
              ·
                refine ⟨12095526563093416997090393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8063684375395611331393595 12095526563093416997090393)
                ·
                  refine ⟨9071644922320062747817795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12095526563093416997090393 9071644922320062747817795)
                  ·
                    refine ⟨13607467383480094121726693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9071644922320062747817795 13607467383480094121726693)
                    ·
                      refine ⟨2551400134402517647823755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13607467383480094121726693 2551400134402517647823755)
                      ·
                        rfl

theorem cell23_4968834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_4968834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968834 prefixEnd_4968834 := by exact prefixLift 4968834
  have htrace : WordTrace (prefixWord ++ tailWord_4968834) baseStart_4968834 baseEnd_4968834 := by
    simpa [prefixWord, tailWord_4968834, baseEnd_4968834] using wordTrace_append hprefix tailTrace_4968834
  have hstable : (prefixWord ++ tailWord_4968834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968834).length < 2 ^ (prefixWord ++ tailWord_4968834).sum := by decide
  have hdescent : baseEnd_4968834 < baseStart_4968834 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968836 : List Nat := [2, 3, 2, 1, 1, 2, 1, 3, 3, 5]
def baseStart_4968836 : Nat := 118140960795 + 4968836 * 2 ^ 59
def prefixEnd_4968836 : Nat := 4983230072969 + 3 ^ 40 * 4968836 * 2
def baseEnd_4968836 : Nat := 850467053787942213332915

theorem tailTrace_4968836 : CollatzResearch.WordTrace tailWord_4968836 prefixEnd_4968836 850467053787942213332915 := by
  unfold tailWord_4968836
  simp only [CollatzResearch.WordTrace]
  refine ⟨90614168713381628236323181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120818891617842170981764241 90614168713381628236323181)
  ·
    refine ⟨33980313267518110588621193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90614168713381628236323181 33980313267518110588621193)
    ·
      refine ⟨25485234950638582941465895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33980313267518110588621193 25485234950638582941465895)
      ·
        refine ⟨38227852425957874412198843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25485234950638582941465895 38227852425957874412198843)
        ·
          refine ⟨57341778638936811618298265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38227852425957874412198843 57341778638936811618298265)
          ·
            refine ⟨43006333979202608713723699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57341778638936811618298265 43006333979202608713723699)
            ·
              refine ⟨64509500968803913070585549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43006333979202608713723699 64509500968803913070585549)
              ·
                refine ⟨24191062863301467401469581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64509500968803913070585549 24191062863301467401469581)
                ·
                  refine ⟨9071648573738050275551093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24191062863301467401469581 9071648573738050275551093)
                  ·
                    refine ⟨850467053787942213332915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9071648573738050275551093 850467053787942213332915)
                    ·
                      rfl

theorem cell23_4968836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 1, 3, 3, 5].length) (baseStart_4968836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968836 prefixEnd_4968836 := by exact prefixLift 4968836
  have htrace : WordTrace (prefixWord ++ tailWord_4968836) baseStart_4968836 baseEnd_4968836 := by
    simpa [prefixWord, tailWord_4968836, baseEnd_4968836] using wordTrace_append hprefix tailTrace_4968836
  have hstable : (prefixWord ++ tailWord_4968836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968836).length < 2 ^ (prefixWord ++ tailWord_4968836).sum := by decide
  have hdescent : baseEnd_4968836 < baseStart_4968836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968843 : List Nat := [1, 1, 1, 1, 4, 5, 1, 1, 1, 5, 2]
def baseStart_4968843 : Nat := 118140960795 + 4968843 * 2 ^ 59
def prefixEnd_4968843 : Nat := 4983230072969 + 3 ^ 40 * 4968843 * 2
def baseEnd_4968843 : Nat := 2551404755728408112611213

theorem tailTrace_4968843 : CollatzResearch.WordTrace tailWord_4968843 prefixEnd_4968843 2551404755728408112611213 := by
  unfold tailWord_4968843
  simp only [CollatzResearch.WordTrace]
  refine ⟨181228592737737896668151183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120819061825158597778767455 181228592737737896668151183)
  ·
    refine ⟨271842889106606845002226775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181228592737737896668151183 271842889106606845002226775)
    ·
      refine ⟨407764333659910267503340163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271842889106606845002226775 407764333659910267503340163)
      ·
        refine ⟨611646500489865401255010245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407764333659910267503340163 611646500489865401255010245)
        ·
          refine ⟨114683718841849762735314421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 611646500489865401255010245 114683718841849762735314421)
          ·
            refine ⟨10751598641423415256435727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 114683718841849762735314421 10751598641423415256435727)
            ·
              refine ⟨16127397962135122884653591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10751598641423415256435727 16127397962135122884653591)
              ·
                refine ⟨24191096943202684326980387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16127397962135122884653591 24191096943202684326980387)
                ·
                  refine ⟨36286645414804026490470581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24191096943202684326980387 36286645414804026490470581)
                  ·
                    refine ⟨3401873007637877483481617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36286645414804026490470581 3401873007637877483481617)
                    ·
                      refine ⟨2551404755728408112611213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401873007637877483481617 2551404755728408112611213)
                      ·
                        rfl

theorem cell23_4968843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 1, 1, 5, 2].length) (baseStart_4968843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968843 prefixEnd_4968843 := by exact prefixLift 4968843
  have htrace : WordTrace (prefixWord ++ tailWord_4968843) baseStart_4968843 baseEnd_4968843 := by
    simpa [prefixWord, tailWord_4968843, baseEnd_4968843] using wordTrace_append hprefix tailTrace_4968843
  have hstable : (prefixWord ++ tailWord_4968843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968843).length < 2 ^ (prefixWord ++ tailWord_4968843).sum := by decide
  have hdescent : baseEnd_4968843 < baseStart_4968843 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968874 : List Nat := [3, 1, 6, 1, 1, 1, 3, 1, 6]
def baseStart_4968874 : Nat := 118140960795 + 4968874 * 2 ^ 59
def prefixEnd_4968874 : Nat := 4983230072969 + 3 ^ 40 * 4968874 * 2
def baseEnd_4968874 : Nat := 283491185958744165702619

theorem tailTrace_4968874 : CollatzResearch.WordTrace tailWord_4968874 prefixEnd_4968874 283491185958744165702619 := by
  unfold tailWord_4968874
  simp only [CollatzResearch.WordTrace]
  refine ⟨45307430850156397240632419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120819815600417059308353117 45307430850156397240632419)
  ·
    refine ⟨67961146275234595860948629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45307430850156397240632419 67961146275234595860948629)
    ·
      refine ⟨3185678731651621680981967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 67961146275234595860948629 3185678731651621680981967)
      ·
        refine ⟨4778518097477432521472951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3185678731651621680981967 4778518097477432521472951)
        ·
          refine ⟨7167777146216148782209427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4778518097477432521472951 7167777146216148782209427)
          ·
            refine ⟨10751665719324223173314141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7167777146216148782209427 10751665719324223173314141)
            ·
              refine ⟨4031874644746583689992803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10751665719324223173314141 4031874644746583689992803)
              ·
                refine ⟨6047811967119875534989205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4031874644746583689992803 6047811967119875534989205)
                ·
                  refine ⟨283491185958744165702619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6047811967119875534989205 283491185958744165702619)
                  ·
                    rfl

theorem cell23_4968874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_4968874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968874 prefixEnd_4968874 := by exact prefixLift 4968874
  have htrace : WordTrace (prefixWord ++ tailWord_4968874) baseStart_4968874 baseEnd_4968874 := by
    simpa [prefixWord, tailWord_4968874, baseEnd_4968874] using wordTrace_append hprefix tailTrace_4968874
  have hstable : (prefixWord ++ tailWord_4968874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968874).length < 2 ^ (prefixWord ++ tailWord_4968874).sum := by decide
  have hdescent : baseEnd_4968874 < baseStart_4968874 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968940 : List Nat := [2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 3]
def baseStart_4968940 : Nat := 118140960795 + 4968940 * 2 ^ 59
def prefixEnd_4968940 : Nat := 4983230072969 + 3 ^ 40 * 4968940 * 2
def baseEnd_4968940 : Nat := 2551454563351894233098267

theorem tailTrace_4968940 : CollatzResearch.WordTrace tailWord_4968940 prefixEnd_4968940 2551454563351894233098267 := by
  unfold tailWord_4968940
  simp only [CollatzResearch.WordTrace]
  refine ⟨90616065309193241117216137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120821420412257654822954849 90616065309193241117216137)
  ·
    refine ⟨67962048981894930837912103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90616065309193241117216137 67962048981894930837912103)
    ·
      refine ⟨101943073472842396256868155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67962048981894930837912103 101943073472842396256868155)
      ·
        refine ⟨152914610209263594385302233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101943073472842396256868155 152914610209263594385302233)
        ·
          refine ⟨114685957656947695788976675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152914610209263594385302233 114685957656947695788976675)
          ·
            refine ⟨172028936485421543683465013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114685957656947695788976675 172028936485421543683465013)
            ·
              refine ⟨16127712795508269720324845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172028936485421543683465013 16127712795508269720324845)
              ·
                refine ⟨6047892298315601145121817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16127712795508269720324845 6047892298315601145121817)
                ·
                  refine ⟨4535919223736700858841363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047892298315601145121817 4535919223736700858841363)
                  ·
                    refine ⟨6803878835605051288262045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4535919223736700858841363 6803878835605051288262045)
                    ·
                      refine ⟨2551454563351894233098267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6803878835605051288262045 2551454563351894233098267)
                      ·
                        rfl

theorem cell23_4968940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 3].length) (baseStart_4968940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968940 prefixEnd_4968940 := by exact prefixLift 4968940
  have htrace : WordTrace (prefixWord ++ tailWord_4968940) baseStart_4968940 baseEnd_4968940 := by
    simpa [prefixWord, tailWord_4968940, baseEnd_4968940] using wordTrace_append hprefix tailTrace_4968940
  have hstable : (prefixWord ++ tailWord_4968940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968940).length < 2 ^ (prefixWord ++ tailWord_4968940).sum := by decide
  have hdescent : baseEnd_4968940 < baseStart_4968940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968956 : List Nat := [2, 2, 2, 1, 2, 1, 1, 2, 4, 6]
def baseStart_4968956 : Nat := 118140960795 + 4968956 * 2 ^ 59
def prefixEnd_4968956 : Nat := 4983230072969 + 3 ^ 40 * 4968956 * 2
def baseEnd_4968956 : Nat := 850487593014122056832731

theorem tailTrace_4968956 : CollatzResearch.WordTrace tailWord_4968956 prefixEnd_4968956 850487593014122056832731 := by
  unfold tailWord_4968956
  simp only [CollatzResearch.WordTrace]
  refine ⟨90616357093164258483507361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120821809457552344644676481 90616357093164258483507361)
  ·
    refine ⟨67962267819873193862630521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90616357093164258483507361 67962267819873193862630521)
    ·
      refine ⟨50971700864904895396972891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67962267819873193862630521 50971700864904895396972891)
      ·
        refine ⟨76457551297357343095459337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50971700864904895396972891 76457551297357343095459337)
        ·
          refine ⟨57343163473018007321594503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76457551297357343095459337 57343163473018007321594503)
          ·
            refine ⟨86014745209527010982391755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57343163473018007321594503 86014745209527010982391755)
            ·
              refine ⟨129022117814290516473587633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86014745209527010982391755 129022117814290516473587633)
              ·
                refine ⟨96766588360717887355190725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129022117814290516473587633 96766588360717887355190725)
                ·
                  refine ⟨18143735317634603879098261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96766588360717887355190725 18143735317634603879098261)
                  ·
                    refine ⟨850487593014122056832731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18143735317634603879098261 850487593014122056832731)
                    ·
                      rfl

theorem cell23_4968956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 4, 6].length) (baseStart_4968956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968956 prefixEnd_4968956 := by exact prefixLift 4968956
  have htrace : WordTrace (prefixWord ++ tailWord_4968956) baseStart_4968956 baseEnd_4968956 := by
    simpa [prefixWord, tailWord_4968956, baseEnd_4968956] using wordTrace_append hprefix tailTrace_4968956
  have hstable : (prefixWord ++ tailWord_4968956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968956).length < 2 ^ (prefixWord ++ tailWord_4968956).sum := by decide
  have hdescent : baseEnd_4968956 < baseStart_4968956 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968980 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 2, 3, 4]
def baseStart_4968980 : Nat := 118140960795 + 4968980 * 2 ^ 59
def prefixEnd_4968980 : Nat := 4983230072969 + 3 ^ 40 * 4968980 * 2
def baseEnd_4968980 : Nat := 2551475102578074076598083

theorem tailTrace_4968980 : CollatzResearch.WordTrace tailWord_4968980 prefixEnd_4968980 2551475102578074076598083 := by
  unfold tailWord_4968980
  simp only [CollatzResearch.WordTrace]
  refine ⟨90616794769120784532944197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120822393025494379377258929 90616794769120784532944197)
  ·
    refine ⟨16990649019210147099927037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90616794769120784532944197 16990649019210147099927037)
    ·
      refine ⟨6371493382203805162472639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16990649019210147099927037 6371493382203805162472639)
      ·
        refine ⟨9557240073305707743708959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6371493382203805162472639 9557240073305707743708959)
        ·
          refine ⟨14335860109958561615563439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9557240073305707743708959 14335860109958561615563439)
          ·
            refine ⟨21503790164937842423345159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14335860109958561615563439 21503790164937842423345159)
            ·
              refine ⟨32255685247406763635017739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21503790164937842423345159 32255685247406763635017739)
              ·
                refine ⟨48383527871110145452526609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32255685247406763635017739 48383527871110145452526609)
                ·
                  refine ⟨36287645903332609089394957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48383527871110145452526609 36287645903332609089394957)
                  ·
                    refine ⟨13607867213749728408523109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36287645903332609089394957 13607867213749728408523109)
                    ·
                      refine ⟨2551475102578074076598083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13607867213749728408523109 2551475102578074076598083)
                      ·
                        rfl

theorem cell23_4968980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_4968980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968980 prefixEnd_4968980 := by exact prefixLift 4968980
  have htrace : WordTrace (prefixWord ++ tailWord_4968980) baseStart_4968980 baseEnd_4968980 := by
    simpa [prefixWord, tailWord_4968980, baseEnd_4968980] using wordTrace_append hprefix tailTrace_4968980
  have hstable : (prefixWord ++ tailWord_4968980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968980).length < 2 ^ (prefixWord ++ tailWord_4968980).sum := by decide
  have hdescent : baseEnd_4968980 < baseStart_4968980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968993 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 4]
def baseStart_4968993 : Nat := 118140960795 + 4968993 * 2 ^ 59
def prefixEnd_4968993 : Nat := 4983230072969 + 3 ^ 40 * 4968993 * 2
def baseEnd_4968993 : Nat := 2551481777826582525735523

theorem tailTrace_4968993 : CollatzResearch.WordTrace tailWord_4968993 prefixEnd_4968993 2551481777826582525735523 := by
  unfold tailWord_4968993
  simp only [CollatzResearch.WordTrace]
  refine ⟨181234063687194472286111633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120822709124796314857407755 181234063687194472286111633)
  ·
    refine ⟨135925547765395854214583725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181234063687194472286111633 135925547765395854214583725)
    ·
      refine ⟨50972080412023445330468897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135925547765395854214583725 50972080412023445330468897)
      ·
        refine ⟨38229060309017583997851673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50972080412023445330468897 38229060309017583997851673)
        ·
          refine ⟨28671795231763187998388755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38229060309017583997851673 28671795231763187998388755)
          ·
            refine ⟨43007692847644781997583133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28671795231763187998388755 43007692847644781997583133)
            ·
              refine ⟨16127884817866793249093675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43007692847644781997583133 16127884817866793249093675)
              ·
                refine ⟨24191827226800189873640513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16127884817866793249093675 24191827226800189873640513)
                ·
                  refine ⟨18143870420100142405230385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24191827226800189873640513 18143870420100142405230385)
                  ·
                    refine ⟨13607902815075106803922789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18143870420100142405230385 13607902815075106803922789)
                    ·
                      refine ⟨2551481777826582525735523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13607902815075106803922789 2551481777826582525735523)
                      ·
                        rfl

theorem cell23_4968993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_4968993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968993 prefixEnd_4968993 := by exact prefixLift 4968993
  have htrace : WordTrace (prefixWord ++ tailWord_4968993) baseStart_4968993 baseEnd_4968993 := by
    simpa [prefixWord, tailWord_4968993, baseEnd_4968993] using wordTrace_append hprefix tailTrace_4968993
  have hstable : (prefixWord ++ tailWord_4968993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968993).length < 2 ^ (prefixWord ++ tailWord_4968993).sum := by decide
  have hdescent : baseEnd_4968993 < baseStart_4968993 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4968997 : List Nat := [1, 3, 1, 2, 2, 1, 4, 3, 2, 2, 2]
def baseStart_4968997 : Nat := 118140960795 + 4968997 * 2 ^ 59
def prefixEnd_4968997 : Nat := 4983230072969 + 3 ^ 40 * 4968997 * 2
def baseEnd_4968997 : Nat := 2551483831749200510085505

theorem tailTrace_4968997 : CollatzResearch.WordTrace tailWord_4968997 prefixEnd_4968997 2551483831749200510085505 := by
  unfold tailWord_4968997
  simp only [CollatzResearch.WordTrace]
  refine ⟨181234209579179980969257245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120822806386119987312838163 181234209579179980969257245)
  ·
    refine ⟨67962828592192492863471467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181234209579179980969257245 67962828592192492863471467)
    ·
      refine ⟨101944242888288739295207201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67962828592192492863471467 101944242888288739295207201)
      ·
        refine ⟨76458182166216554471405401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101944242888288739295207201 76458182166216554471405401)
        ·
          refine ⟨57343636624662415853554051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76458182166216554471405401 57343636624662415853554051)
          ·
            refine ⟨86015454936993623780331077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57343636624662415853554051 86015454936993623780331077)
            ·
              refine ⟨16127897800686304458812077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86015454936993623780331077 16127897800686304458812077)
              ·
                refine ⟨6047961675257364172054529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16127897800686304458812077 6047961675257364172054529)
                ·
                  refine ⟨4535971256443023129040897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6047961675257364172054529 4535971256443023129040897)
                  ·
                    refine ⟨3401978442332267346780673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4535971256443023129040897 3401978442332267346780673)
                    ·
                      refine ⟨2551483831749200510085505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3401978442332267346780673 2551483831749200510085505)
                      ·
                        rfl

theorem cell23_4968997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2, 2, 2].length) (baseStart_4968997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4968997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4968997 prefixEnd_4968997 := by exact prefixLift 4968997
  have htrace : WordTrace (prefixWord ++ tailWord_4968997) baseStart_4968997 baseEnd_4968997 := by
    simpa [prefixWord, tailWord_4968997, baseEnd_4968997] using wordTrace_append hprefix tailTrace_4968997
  have hstable : (prefixWord ++ tailWord_4968997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4968997).length < 2 ^ (prefixWord ++ tailWord_4968997).sum := by decide
  have hdescent : baseEnd_4968997 < baseStart_4968997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4968997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969013 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 3]
def baseStart_4969013 : Nat := 118140960795 + 4969013 * 2 ^ 59
def prefixEnd_4969013 : Nat := 4983230072969 + 3 ^ 40 * 4969013 * 2
def baseEnd_4969013 : Nat := 2551492047439672447485431

theorem tailTrace_4969013 : CollatzResearch.WordTrace tailWord_4969013 prefixEnd_4969013 2551492047439672447485431 := by
  unfold tailWord_4969013
  simp only [CollatzResearch.WordTrace]
  refine ⟨181234793147122015701839693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120823195431414677134559795 181234793147122015701839693)
  ·
    refine ⟨67963047430170755888189885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181234793147122015701839693 67963047430170755888189885)
    ·
      refine ⟨25486142786314033458071207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67963047430170755888189885 25486142786314033458071207)
      ·
        refine ⟨38229214179471050187106811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25486142786314033458071207 38229214179471050187106811)
        ·
          refine ⟨57343821269206575280660217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38229214179471050187106811 57343821269206575280660217)
          ·
            refine ⟨43007865951904931460495163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57343821269206575280660217 43007865951904931460495163)
            ·
              refine ⟨64511798927857397190742745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43007865951904931460495163 64511798927857397190742745)
              ·
                refine ⟨48383849195893047893057059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64511798927857397190742745 48383849195893047893057059)
                ·
                  refine ⟨72575773793839571839585589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48383849195893047893057059 72575773793839571839585589)
                  ·
                    refine ⟨6803978793172459859961149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72575773793839571839585589 6803978793172459859961149)
                    ·
                      refine ⟨2551492047439672447485431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6803978793172459859961149 2551492047439672447485431)
                      ·
                        rfl

theorem cell23_4969013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_4969013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969013 prefixEnd_4969013 := by exact prefixLift 4969013
  have htrace : WordTrace (prefixWord ++ tailWord_4969013) baseStart_4969013 baseEnd_4969013 := by
    simpa [prefixWord, tailWord_4969013, baseEnd_4969013] using wordTrace_append hprefix tailTrace_4969013
  have hstable : (prefixWord ++ tailWord_4969013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969013).length < 2 ^ (prefixWord ++ tailWord_4969013).sum := by decide
  have hdescent : baseEnd_4969013 < baseStart_4969013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969020 : List Nat := [2, 2, 2, 2, 3, 1, 1, 5, 5]
def baseStart_4969020 : Nat := 118140960795 + 4969020 * 2 ^ 59
def prefixEnd_4969020 : Nat := 4983230072969 + 3 ^ 40 * 4969020 * 2
def baseEnd_4969020 : Nat := 283499515756028213344211

theorem tailTrace_4969020 : CollatzResearch.WordTrace tailWord_4969020 prefixEnd_4969020 283499515756028213344211 := by
  unfold tailWord_4969020
  simp only [CollatzResearch.WordTrace]
  refine ⟨90617524229048327948672257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120823365638731103931563009 90617524229048327948672257)
  ·
    refine ⟨67963143171786245961504193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90617524229048327948672257 67963143171786245961504193)
    ·
      refine ⟨50972357378839684471128145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67963143171786245961504193 50972357378839684471128145)
      ·
        refine ⟨38229268034129763353346109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50972357378839684471128145 38229268034129763353346109)
        ·
          refine ⟨14335975512798661257504791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38229268034129763353346109 14335975512798661257504791)
          ·
            refine ⟨21503963269197991886257187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14335975512798661257504791 21503963269197991886257187)
            ·
              refine ⟨32255944903796987829385781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21503963269197991886257187 32255944903796987829385781)
              ·
                refine ⟨3023994834730967609004917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32255944903796987829385781 3023994834730967609004917)
                ·
                  refine ⟨283499515756028213344211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3023994834730967609004917 283499515756028213344211)
                  ·
                    rfl

theorem cell23_4969020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 5, 5].length) (baseStart_4969020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969020 prefixEnd_4969020 := by exact prefixLift 4969020
  have htrace : WordTrace (prefixWord ++ tailWord_4969020) baseStart_4969020 baseEnd_4969020 := by
    simpa [prefixWord, tailWord_4969020, baseEnd_4969020] using wordTrace_append hprefix tailTrace_4969020
  have hstable : (prefixWord ++ tailWord_4969020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969020).length < 2 ^ (prefixWord ++ tailWord_4969020).sum := by decide
  have hdescent : baseEnd_4969020 < baseStart_4969020 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969037 : List Nat := [1, 6, 1, 1, 2, 1, 2, 4, 5]
def baseStart_4969037 : Nat := 118140960795 + 4969037 * 2 ^ 59
def prefixEnd_4969037 : Nat := 4983230072969 + 3 ^ 40 * 4969037 * 2
def baseEnd_4969037 : Nat := 283500485663931150398369

theorem tailTrace_4969037 : CollatzResearch.WordTrace tailWord_4969037 prefixEnd_4969037 283500485663931150398369 := by
  unfold tailWord_4969037
  simp only [CollatzResearch.WordTrace]
  refine ⟨181235668499035067800713365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120823778999356711867142243 181235668499035067800713365)
  ·
    refine ⟨8495421960892268803158439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181235668499035067800713365 8495421960892268803158439)
    ·
      refine ⟨12743132941338403204737659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8495421960892268803158439 12743132941338403204737659)
      ·
        refine ⟨19114699412007604807106489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12743132941338403204737659 19114699412007604807106489)
        ·
          refine ⟨14336024559005703605329867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19114699412007604807106489 14336024559005703605329867)
          ·
            refine ⟨21504036838508555407994801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14336024559005703605329867 21504036838508555407994801)
            ·
              refine ⟨16128027628881416555996101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21504036838508555407994801 16128027628881416555996101)
              ·
                refine ⟨3024005180415265604249269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16128027628881416555996101 3024005180415265604249269)
                ·
                  refine ⟨283500485663931150398369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3024005180415265604249269 283500485663931150398369)
                  ·
                    rfl

theorem cell23_4969037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_4969037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969037 prefixEnd_4969037 := by exact prefixLift 4969037
  have htrace : WordTrace (prefixWord ++ tailWord_4969037) baseStart_4969037 baseEnd_4969037 := by
    simpa [prefixWord, tailWord_4969037, baseEnd_4969037] using wordTrace_append hprefix tailTrace_4969037
  have hstable : (prefixWord ++ tailWord_4969037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969037).length < 2 ^ (prefixWord ++ tailWord_4969037).sum := by decide
  have hdescent : baseEnd_4969037 < baseStart_4969037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969070 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4]
def baseStart_4969070 : Nat := 118140960795 + 4969070 * 2 ^ 59
def prefixEnd_4969070 : Nat := 4983230072969 + 3 ^ 40 * 4969070 * 2
def baseEnd_4969070 : Nat := 2551521315836978724472669

theorem tailTrace_4969070 : CollatzResearch.WordTrace tailWord_4969070 prefixEnd_4969070 2551521315836978724472669 := by
  unfold tailWord_4969070
  simp only [CollatzResearch.WordTrace]
  refine ⟨22654609013489439304583083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120824581405277009624443109 22654609013489439304583083)
  ·
    refine ⟨33981913520234158956874625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22654609013489439304583083 33981913520234158956874625)
    ·
      refine ⟨25486435140175619217655969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33981913520234158956874625 25486435140175619217655969)
      ·
        refine ⟨19114826355131714413241977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25486435140175619217655969 19114826355131714413241977)
        ·
          refine ⟨14336119766348785809931483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19114826355131714413241977 14336119766348785809931483)
          ·
            refine ⟨21504179649523178714897225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14336119766348785809931483 21504179649523178714897225)
            ·
              refine ⟨16128134737142384036172919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21504179649523178714897225 16128134737142384036172919)
              ·
                refine ⟨24192202105713576054259379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16128134737142384036172919 24192202105713576054259379)
                ·
                  refine ⟨36288303158570364081389069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24192202105713576054259379 36288303158570364081389069)
                  ·
                    refine ⟨13608113684463886530520901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36288303158570364081389069 13608113684463886530520901)
                    ·
                      refine ⟨2551521315836978724472669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13608113684463886530520901 2551521315836978724472669)
                      ·
                        rfl

theorem cell23_4969070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_4969070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969070 prefixEnd_4969070 := by exact prefixLift 4969070
  have htrace : WordTrace (prefixWord ++ tailWord_4969070) baseStart_4969070 baseEnd_4969070 := by
    simpa [prefixWord, tailWord_4969070, baseEnd_4969070] using wordTrace_append hprefix tailTrace_4969070
  have hstable : (prefixWord ++ tailWord_4969070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969070).length < 2 ^ (prefixWord ++ tailWord_4969070).sum := by decide
  have hdescent : baseEnd_4969070 < baseStart_4969070 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969093 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 8]
def baseStart_4969093 : Nat := 118140960795 + 4969093 * 2 ^ 59
def prefixEnd_4969093 : Nat := 4983230072969 + 3 ^ 40 * 4969093 * 2
def baseEnd_4969093 : Nat := 283503680654670237165007

theorem tailTrace_4969093 : CollatzResearch.WordTrace tailWord_4969093 prefixEnd_4969093 283503680654670237165007 := by
  unfold tailWord_4969093
  simp only [CollatzResearch.WordTrace]
  refine ⟨181237710986832189364751933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120825140657888126243167955 181237710986832189364751933)
  ·
    refine ⟨67964141620062071011781975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181237710986832189364751933 67964141620062071011781975)
    ·
      refine ⟨101946212430093106517672963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67964141620062071011781975 101946212430093106517672963)
      ·
        refine ⟨152919318645139659776509445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101946212430093106517672963 152919318645139659776509445)
        ·
          refine ⟨28672372245963686208095521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152919318645139659776509445 28672372245963686208095521)
          ·
            refine ⟨21504279184472764656071641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28672372245963686208095521 21504279184472764656071641)
            ·
              refine ⟨16128209388354573492053731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21504279184472764656071641 16128209388354573492053731)
              ·
                refine ⟨24192314082531860238080597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16128209388354573492053731 24192314082531860238080597)
                ·
                  refine ⟨283503680654670237165007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24192314082531860238080597 283503680654670237165007)
                  ·
                    rfl

theorem cell23_4969093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 8].length) (baseStart_4969093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969093 prefixEnd_4969093 := by exact prefixLift 4969093
  have htrace : WordTrace (prefixWord ++ tailWord_4969093) baseStart_4969093 baseEnd_4969093 := by
    simpa [prefixWord, tailWord_4969093, baseEnd_4969093] using wordTrace_append hprefix tailTrace_4969093
  have hstable : (prefixWord ++ tailWord_4969093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969093).length < 2 ^ (prefixWord ++ tailWord_4969093).sum := by decide
  have hdescent : baseEnd_4969093 < baseStart_4969093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969160 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 4]
def baseStart_4969160 : Nat := 118140960795 + 4969160 * 2 ^ 59
def prefixEnd_4969160 : Nat := 4983230072969 + 3 ^ 40 * 4969160 * 2
def baseEnd_4969160 : Nat := 2551567529095883372347255

theorem tailTrace_4969160 : CollatzResearch.WordTrace tailWord_4969160 prefixEnd_4969160 2551567529095883372347255 := by
  unfold tailWord_4969160
  simp only [CollatzResearch.WordTrace]
  refine ⟨90620077338794729903720467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120826769785059639871627289 90620077338794729903720467)
  ·
    refine ⟨135930116008192094855580701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90620077338794729903720467 135930116008192094855580701)
    ·
      refine ⟨50973793503072035570842763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135930116008192094855580701 50973793503072035570842763)
      ·
        refine ⟨76460690254608053356264145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50973793503072035570842763 76460690254608053356264145)
        ·
          refine ⟨57345517690956040017198109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76460690254608053356264145 57345517690956040017198109)
          ·
            refine ⟨21504569134108515006449291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57345517690956040017198109 21504569134108515006449291)
            ·
              refine ⟨32256853701162772509673937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21504569134108515006449291 32256853701162772509673937)
              ·
                refine ⟨24192640275872079382255453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32256853701162772509673937 24192640275872079382255453)
                ·
                  refine ⟨9072240103452029768345795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24192640275872079382255453 9072240103452029768345795)
                  ·
                    refine ⟨13608360155178044652518693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9072240103452029768345795 13608360155178044652518693)
                    ·
                      refine ⟨2551567529095883372347255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13608360155178044652518693 2551567529095883372347255)
                      ·
                        rfl

theorem cell23_4969160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 3, 1, 4].length) (baseStart_4969160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969160 prefixEnd_4969160 := by exact prefixLift 4969160
  have htrace : WordTrace (prefixWord ++ tailWord_4969160) baseStart_4969160 baseEnd_4969160 := by
    simpa [prefixWord, tailWord_4969160, baseEnd_4969160] using wordTrace_append hprefix tailTrace_4969160
  have hstable : (prefixWord ++ tailWord_4969160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969160).length < 2 ^ (prefixWord ++ tailWord_4969160).sum := by decide
  have hdescent : baseEnd_4969160 < baseStart_4969160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969203 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6]
def baseStart_4969203 : Nat := 118140960795 + 4969203 * 2 ^ 59
def prefixEnd_4969203 : Nat := 4983230072969 + 3 ^ 40 * 4969203 * 2
def baseEnd_4969203 : Nat := 2551589608764026704109557

theorem tailTrace_4969203 : CollatzResearch.WordTrace tailWord_4969203 prefixEnd_4969203 2551589608764026704109557 := by
  unfold tailWord_4969203
  simp only [CollatzResearch.WordTrace]
  refine ⟨181241723016433678151256263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120827815344289118767504175 181241723016433678151256263)
  ·
    refine ⟨271862584524650517226884395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181241723016433678151256263 271862584524650517226884395)
    ·
      refine ⟨407793876786975775840326593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271862584524650517226884395 407793876786975775840326593)
      ·
        refine ⟨305845407590231831880244945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407793876786975775840326593 305845407590231831880244945)
        ·
          refine ⟨229384055692673873910183709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305845407590231831880244945 229384055692673873910183709)
          ·
            refine ⟨86019020884752702716318891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229384055692673873910183709 86019020884752702716318891)
            ·
              refine ⟨129028531327129054074478337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86019020884752702716318891 129028531327129054074478337)
              ·
                refine ⟨96771398495346790555858753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129028531327129054074478337 96771398495346790555858753)
                ·
                  refine ⟨72578548871510092916894065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96771398495346790555858753 72578548871510092916894065)
                  ·
                    refine ⟨54433911653632569687670549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72578548871510092916894065 54433911653632569687670549)
                    ·
                      refine ⟨2551589608764026704109557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54433911653632569687670549 2551589608764026704109557)
                      ·
                        rfl

theorem cell23_4969203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 6].length) (baseStart_4969203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969203 prefixEnd_4969203 := by exact prefixLift 4969203
  have htrace : WordTrace (prefixWord ++ tailWord_4969203) baseStart_4969203 baseEnd_4969203 := by
    simpa [prefixWord, tailWord_4969203, baseEnd_4969203] using wordTrace_append hprefix tailTrace_4969203
  have hstable : (prefixWord ++ tailWord_4969203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969203).length < 2 ^ (prefixWord ++ tailWord_4969203).sum := by decide
  have hdescent : baseEnd_4969203 < baseStart_4969203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969210 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3]
def baseStart_4969210 : Nat := 118140960795 + 4969210 * 2 ^ 59
def prefixEnd_4969210 : Nat := 4983230072969 + 3 ^ 40 * 4969210 * 2
def baseEnd_4969210 : Nat := 2551593203128608176722025

theorem tailTrace_4969210 : CollatzResearch.WordTrace tailWord_4969210 prefixEnd_4969210 2551593203128608176722025 := by
  unfold tailWord_4969210
  simp only [CollatzResearch.WordTrace]
  refine ⟨45310494581852079586690271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120827985551605545564507389 45310494581852079586690271)
  ·
    refine ⟨67965741872778119380035407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45310494581852079586690271 67965741872778119380035407)
    ·
      refine ⟨101948612809167179070053111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67965741872778119380035407 101948612809167179070053111)
      ·
        refine ⟨152922919213750768605079667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101948612809167179070053111 152922919213750768605079667)
        ·
          refine ⟨229384378820626152907619501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152922919213750768605079667 229384378820626152907619501)
          ·
            refine ⟨86019142057734807340357313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229384378820626152907619501 86019142057734807340357313)
            ·
              refine ⟨64514356543301105505267985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86019142057734807340357313 64514356543301105505267985)
              ·
                refine ⟨48385767407475829128950989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64514356543301105505267985 48385767407475829128950989)
                ·
                  refine ⟨18144662777803435923356621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48385767407475829128950989 18144662777803435923356621)
                  ·
                    refine ⟨6804248541676288471258733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18144662777803435923356621 6804248541676288471258733)
                    ·
                      refine ⟨2551593203128608176722025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6804248541676288471258733 2551593203128608176722025)
                      ·
                        rfl

theorem cell23_4969210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 3, 3, 3].length) (baseStart_4969210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969210 prefixEnd_4969210 := by exact prefixLift 4969210
  have htrace : WordTrace (prefixWord ++ tailWord_4969210) baseStart_4969210 baseEnd_4969210 := by
    simpa [prefixWord, tailWord_4969210, baseEnd_4969210] using wordTrace_append hprefix tailTrace_4969210
  have hstable : (prefixWord ++ tailWord_4969210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969210).length < 2 ^ (prefixWord ++ tailWord_4969210).sum := by decide
  have hdescent : baseEnd_4969210 < baseStart_4969210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969280 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4]
def baseStart_4969280 : Nat := 118140960795 + 4969280 * 2 ^ 59
def prefixEnd_4969280 : Nat := 4983230072969 + 3 ^ 40 * 4969280 * 2
def baseEnd_4969280 : Nat := 2551629146774422902846703

theorem tailTrace_4969280 : CollatzResearch.WordTrace tailWord_4969280 prefixEnd_4969280 2551629146774422902846703 := by
  unfold tailWord_4969280
  simp only [CollatzResearch.WordTrace]
  refine ⟨90622265718577360150904647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120829687624769813534539529 90622265718577360150904647)
  ·
    refine ⟨135933398577866040226356971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90622265718577360150904647 135933398577866040226356971)
    ·
      refine ⟨203900097866799060339535457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135933398577866040226356971 203900097866799060339535457)
      ·
        refine ⟨152925073400099295254651593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203900097866799060339535457 152925073400099295254651593)
        ·
          refine ⟨114693805050074471440988695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152925073400099295254651593 114693805050074471440988695)
          ·
            refine ⟨172040707575111707161483043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114693805050074471440988695 172040707575111707161483043)
            ·
              refine ⟨258061061362667560742224565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172040707575111707161483043 258061061362667560742224565)
              ·
                refine ⟨24193224502750083819583553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 258061061362667560742224565 24193224502750083819583553)
                ·
                  refine ⟨18144918377062562864687665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24193224502750083819583553 18144918377062562864687665)
                  ·
                    refine ⟨13608688782796922148515749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18144918377062562864687665 13608688782796922148515749)
                    ·
                      refine ⟨2551629146774422902846703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13608688782796922148515749 2551629146774422902846703)
                      ·
                        rfl

theorem cell23_4969280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 2, 2, 4].length) (baseStart_4969280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969280 prefixEnd_4969280 := by exact prefixLift 4969280
  have htrace : WordTrace (prefixWord ++ tailWord_4969280) baseStart_4969280 baseEnd_4969280 := by
    simpa [prefixWord, tailWord_4969280, baseEnd_4969280] using wordTrace_append hprefix tailTrace_4969280
  have hstable : (prefixWord ++ tailWord_4969280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969280).length < 2 ^ (prefixWord ++ tailWord_4969280).sum := by decide
  have hdescent : baseEnd_4969280 < baseStart_4969280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969334 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_4969334 : Nat := 118140960795 + 4969334 * 2 ^ 59
def prefixEnd_4969334 : Nat := 4983230072969 + 3 ^ 40 * 4969334 * 2
def baseEnd_4969334 : Nat := 2551656874729765691571455

theorem tailTrace_4969334 : CollatzResearch.WordTrace tailWord_4969334 prefixEnd_4969334 2551656874729765691571455 := by
  unfold tailWord_4969334
  simp only [CollatzResearch.WordTrace]
  refine ⟨11327906311184942970267191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120831000652639391682850037 11327906311184942970267191)
  ·
    refine ⟨16991859466777414455400787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11327906311184942970267191 16991859466777414455400787)
    ·
      refine ⟨25487789200166121683101181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16991859466777414455400787 25487789200166121683101181)
      ·
        refine ⟨9557920950062295631162943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25487789200166121683101181 9557920950062295631162943)
        ·
          refine ⟨14336881425093443446744415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9557920950062295631162943 14336881425093443446744415)
          ·
            refine ⟨21505322137640165170116623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14336881425093443446744415 21505322137640165170116623)
            ·
              refine ⟨32257983206460247755174935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21505322137640165170116623 32257983206460247755174935)
              ·
                refine ⟨48386974809690371632762403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32257983206460247755174935 48386974809690371632762403)
                ·
                  refine ⟨72580462214535557449143605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48386974809690371632762403 72580462214535557449143605)
                  ·
                    refine ⟨6804418332612708510857213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72580462214535557449143605 6804418332612708510857213)
                    ·
                      refine ⟨2551656874729765691571455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6804418332612708510857213 2551656874729765691571455)
                      ·
                        rfl

theorem cell23_4969334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_4969334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969334 prefixEnd_4969334 := by exact prefixLift 4969334
  have htrace : WordTrace (prefixWord ++ tailWord_4969334) baseStart_4969334 baseEnd_4969334 := by
    simpa [prefixWord, tailWord_4969334, baseEnd_4969334] using wordTrace_append hprefix tailTrace_4969334
  have hstable : (prefixWord ++ tailWord_4969334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969334).length < 2 ^ (prefixWord ++ tailWord_4969334).sum := by decide
  have hdescent : baseEnd_4969334 < baseStart_4969334 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969354 : List Nat := [3, 1, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_4969354 : Nat := 118140960795 + 4969354 * 2 ^ 59
def prefixEnd_4969354 : Nat := 4983230072969 + 3 ^ 40 * 4969354 * 2
def baseEnd_4969354 : Nat := 850555714780951871107121

theorem tailTrace_4969354 : CollatzResearch.WordTrace tailWord_4969354 prefixEnd_4969354 850555714780951871107121 := by
  unfold tailWord_4969354
  simp only [CollatzResearch.WordTrace]
  refine ⟨45311807609721657735000779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120831486959257753960002077 45311807609721657735000779)
  ·
    refine ⟨67967711414582486602501169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45311807609721657735000779 67967711414582486602501169)
    ·
      refine ⟨50975783560936864951875877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67967711414582486602501169 50975783560936864951875877)
      ·
        refine ⟨9557959417675662178476727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50975783560936864951875877 9557959417675662178476727)
        ·
          refine ⟨14336939126513493267715091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9557959417675662178476727 14336939126513493267715091)
          ·
            refine ⟨21505408689770239901572637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14336939126513493267715091 21505408689770239901572637)
            ·
              refine ⟨8064528258663839963089739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21505408689770239901572637 8064528258663839963089739)
              ·
                refine ⟨12096792387995759944634609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8064528258663839963089739 12096792387995759944634609)
                ·
                  refine ⟨9072594290996819958475957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12096792387995759944634609 9072594290996819958475957)
                  ·
                    refine ⟨850555714780951871107121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9072594290996819958475957 850555714780951871107121)
                    ·
                      rfl

theorem cell23_4969354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_4969354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969354 prefixEnd_4969354 := by exact prefixLift 4969354
  have htrace : WordTrace (prefixWord ++ tailWord_4969354) baseStart_4969354 baseEnd_4969354 := by
    simpa [prefixWord, tailWord_4969354, baseEnd_4969354] using wordTrace_append hprefix tailTrace_4969354
  have hstable : (prefixWord ++ tailWord_4969354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969354).length < 2 ^ (prefixWord ++ tailWord_4969354).sum := by decide
  have hdescent : baseEnd_4969354 < baseStart_4969354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969367 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 5, 4]
def baseStart_4969367 : Nat := 118140960795 + 4969367 * 2 ^ 59
def prefixEnd_4969367 : Nat := 4983230072969 + 3 ^ 40 * 4969367 * 2
def baseEnd_4969367 : Nat := 850557939863788020819601

theorem tailTrace_4969367 : CollatzResearch.WordTrace tailWord_4969367 prefixEnd_4969367 850557939863788020819601 := by
  unfold tailWord_4969367
  simp only [CollatzResearch.WordTrace]
  refine ⟨181247704587839534160226355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120831803058559689440150903 181247704587839534160226355)
  ·
    refine ⟨271871556881759301240339533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181247704587839534160226355 271871556881759301240339533)
    ·
      refine ⟨101951833830659737965127325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271871556881759301240339533 101951833830659737965127325)
      ·
        refine ⟨38231937686497401736922747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101951833830659737965127325 38231937686497401736922747)
        ·
          refine ⟨57347906529746102605384121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38231937686497401736922747 57347906529746102605384121)
          ·
            refine ⟨43010929897309576954038091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57347906529746102605384121 43010929897309576954038091)
            ·
              refine ⟨64516394845964365431057137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43010929897309576954038091 64516394845964365431057137)
              ·
                refine ⟨48387296134473274073292853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64516394845964365431057137 48387296134473274073292853)
                ·
                  refine ⟨4536309012606869444371205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48387296134473274073292853 4536309012606869444371205)
                  ·
                    refine ⟨850557939863788020819601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4536309012606869444371205 850557939863788020819601)
                    ·
                      rfl

theorem cell23_4969367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_4969367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969367 prefixEnd_4969367 := by exact prefixLift 4969367
  have htrace : WordTrace (prefixWord ++ tailWord_4969367) baseStart_4969367 baseEnd_4969367 := by
    simpa [prefixWord, tailWord_4969367, baseEnd_4969367] using wordTrace_append hprefix tailTrace_4969367
  have hstable : (prefixWord ++ tailWord_4969367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969367).length < 2 ^ (prefixWord ++ tailWord_4969367).sum := by decide
  have hdescent : baseEnd_4969367 < baseStart_4969367 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969484 : List Nat := [2, 2, 1, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_4969484 : Nat := 118140960795 + 4969484 * 2 ^ 59
def prefixEnd_4969484 : Nat := 4983230072969 + 3 ^ 40 * 4969484 * 2
def baseEnd_4969484 : Nat := 2551733896827940104695765

theorem tailTrace_4969484 : CollatzResearch.WordTrace tailWord_4969484 prefixEnd_4969484 2551733896827940104695765 := by
  unfold tailWord_4969484
  simp only [CollatzResearch.WordTrace]
  refine ⟨90625985964207831571117753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120834647952277108761490337 90625985964207831571117753)
  ·
    refine ⟨67969489473155873678338315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90625985964207831571117753 67969489473155873678338315)
    ·
      refine ⟨101954234209733810517507473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67969489473155873678338315 101954234209733810517507473)
      ·
        refine ⟨76465675657300357888130605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101954234209733810517507473 76465675657300357888130605)
        ·
          refine ⟨28674628371487634208048977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76465675657300357888130605 28674628371487634208048977)
          ·
            refine ⟨21505971278615725656036733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28674628371487634208048977 21505971278615725656036733)
            ·
              refine ⟨8064739229480897121013775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21505971278615725656036733 8064739229480897121013775)
              ·
                refine ⟨12097108844221345681520663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8064739229480897121013775 12097108844221345681520663)
                ·
                  refine ⟨18145663266332018522280995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12097108844221345681520663 18145663266332018522280995)
                  ·
                    refine ⟨27218494899498027783421493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18145663266332018522280995 27218494899498027783421493)
                    ·
                      refine ⟨2551733896827940104695765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27218494899498027783421493 2551733896827940104695765)
                      ·
                        rfl

theorem cell23_4969484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_4969484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969484 prefixEnd_4969484 := by exact prefixLift 4969484
  have htrace : WordTrace (prefixWord ++ tailWord_4969484) baseStart_4969484 baseEnd_4969484 := by
    simpa [prefixWord, tailWord_4969484, baseEnd_4969484] using wordTrace_append hprefix tailTrace_4969484
  have hstable : (prefixWord ++ tailWord_4969484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969484).length < 2 ^ (prefixWord ++ tailWord_4969484).sum := by decide
  have hdescent : baseEnd_4969484 < baseStart_4969484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969511 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4969511 : Nat := 118140960795 + 4969511 * 2 ^ 59
def prefixEnd_4969511 : Nat := 4983230072969 + 3 ^ 40 * 4969511 * 2
def baseEnd_4969511 : Nat := 2551747760805611499058141

theorem tailTrace_4969511 : CollatzResearch.WordTrace tailWord_4969511 prefixEnd_4969511 2551747760805611499058141 := by
  unfold tailWord_4969511
  simp only [CollatzResearch.WordTrace]
  refine ⟨181252956699317846753468387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120835304466211897835645591 181252956699317846753468387)
  ·
    refine ⟨271879435048976770130202581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181252956699317846753468387 271879435048976770130202581)
    ·
      refine ⟨6372174258960393049926623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 271879435048976770130202581 6372174258960393049926623)
      ·
        refine ⟨9558261388440589574889935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6372174258960393049926623 9558261388440589574889935)
        ·
          refine ⟨14337392082660884362334903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9558261388440589574889935 14337392082660884362334903)
          ·
            refine ⟨21506088123991326543502355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14337392082660884362334903 21506088123991326543502355)
            ·
              refine ⟨32259132185986989815253533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21506088123991326543502355 32259132185986989815253533)
              ·
                refine ⟨12097174569745121180720075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32259132185986989815253533 12097174569745121180720075)
                ·
                  refine ⟨18145761854617681771080113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12097174569745121180720075 18145761854617681771080113)
                  ·
                    refine ⟨13609321390963261328310085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18145761854617681771080113 13609321390963261328310085)
                    ·
                      refine ⟨2551747760805611499058141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13609321390963261328310085 2551747760805611499058141)
                      ·
                        rfl

theorem cell23_4969511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4969511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969511 prefixEnd_4969511 := by exact prefixLift 4969511
  have htrace : WordTrace (prefixWord ++ tailWord_4969511) baseStart_4969511 baseEnd_4969511 := by
    simpa [prefixWord, tailWord_4969511, baseEnd_4969511] using wordTrace_append hprefix tailTrace_4969511
  have hstable : (prefixWord ++ tailWord_4969511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969511).length < 2 ^ (prefixWord ++ tailWord_4969511).sum := by decide
  have hdescent : baseEnd_4969511 < baseStart_4969511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969527 : List Nat := [1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_4969527 : Nat := 118140960795 + 4969527 * 2 ^ 59
def prefixEnd_4969527 : Nat := 4983230072969 + 3 ^ 40 * 4969527 * 2
def baseEnd_4969527 : Nat := 2551755976496083436458067

theorem tailTrace_4969527 : CollatzResearch.WordTrace tailWord_4969527 prefixEnd_4969527 2551755976496083436458067 := by
  unfold tailWord_4969527
  simp only [CollatzResearch.WordTrace]
  refine ⟨181253540267259881486050835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120835693511506587657367223 181253540267259881486050835)
  ·
    refine ⟨271880310400889822229076253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181253540267259881486050835 271880310400889822229076253)
    ·
      refine ⟨101955116400333683335903595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271880310400889822229076253 101955116400333683335903595)
      ·
        refine ⟨152932674600500525003855393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101955116400333683335903595 152932674600500525003855393)
        ·
          refine ⟨114699505950375393752891545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152932674600500525003855393 114699505950375393752891545)
          ·
            refine ⟨86024629462781545314668659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114699505950375393752891545 86024629462781545314668659)
            ·
              refine ⟨129036944194172317972002989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86024629462781545314668659 129036944194172317972002989)
              ·
                refine ⟨48388854072814619239501121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129036944194172317972002989 48388854072814619239501121)
                ·
                  refine ⟨36291640554610964429625841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48388854072814619239501121 36291640554610964429625841)
                  ·
                    refine ⟨27218730415958223322219381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36291640554610964429625841 27218730415958223322219381)
                    ·
                      refine ⟨2551755976496083436458067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27218730415958223322219381 2551755976496083436458067)
                      ·
                        rfl

theorem cell23_4969527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_4969527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969527 prefixEnd_4969527 := by exact prefixLift 4969527
  have htrace : WordTrace (prefixWord ++ tailWord_4969527) baseStart_4969527 baseEnd_4969527 := by
    simpa [prefixWord, tailWord_4969527, baseEnd_4969527] using wordTrace_append hprefix tailTrace_4969527
  have hstable : (prefixWord ++ tailWord_4969527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969527).length < 2 ^ (prefixWord ++ tailWord_4969527).sum := by decide
  have hdescent : baseEnd_4969527 < baseStart_4969527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969564 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4969564 : Nat := 118140960795 + 4969564 * 2 ^ 59
def prefixEnd_4969564 : Nat := 4983230072969 + 3 ^ 40 * 4969564 * 2
def baseEnd_4969564 : Nat := 850591658426766597231799

theorem tailTrace_4969564 : CollatzResearch.WordTrace tailWord_4969564 prefixEnd_4969564 850591658426766597231799 := by
  unfold tailWord_4969564
  simp only [CollatzResearch.WordTrace]
  refine ⟨90627444884062918402573873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120836593178750557870098497 90627444884062918402573873)
  ·
    refine ⟨67970583663047188801930405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90627444884062918402573873 67970583663047188801930405)
    ·
      refine ⟨12744484436821347900361951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 67970583663047188801930405 12744484436821347900361951)
      ·
        refine ⟨19116726655232021850542927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12744484436821347900361951 19116726655232021850542927)
        ·
          refine ⟨28675089982848032775814391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19116726655232021850542927 28675089982848032775814391)
          ·
            refine ⟨43012634974272049163721587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28675089982848032775814391 43012634974272049163721587)
            ·
              refine ⟨64518952461408073745582381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43012634974272049163721587 64518952461408073745582381)
              ·
                refine ⟨24194607173028027654593393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64518952461408073745582381 24194607173028027654593393)
                ·
                  refine ⟨18145955379771020740945045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24194607173028027654593393 18145955379771020740945045)
                  ·
                    refine ⟨850591658426766597231799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18145955379771020740945045 850591658426766597231799)
                    ·
                      rfl

theorem cell23_4969564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4969564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969564 prefixEnd_4969564 := by exact prefixLift 4969564
  have htrace : WordTrace (prefixWord ++ tailWord_4969564) baseStart_4969564 baseEnd_4969564 := by
    simpa [prefixWord, tailWord_4969564, baseEnd_4969564] using wordTrace_append hprefix tailTrace_4969564
  have hstable : (prefixWord ++ tailWord_4969564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969564).length < 2 ^ (prefixWord ++ tailWord_4969564).sum := by decide
  have hdescent : baseEnd_4969564 < baseStart_4969564 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969565 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 3]
def baseStart_4969565 : Nat := 118140960795 + 4969565 * 2 ^ 59
def prefixEnd_4969565 : Nat := 4983230072969 + 3 ^ 40 * 4969565 * 2
def baseEnd_4969565 : Nat := 2551775488760954287782893

theorem tailTrace_4969565 : CollatzResearch.WordTrace tailWord_4969565 prefixEnd_4969565 2551775488760954287782893 := by
  unfold tailWord_4969565
  simp only [CollatzResearch.WordTrace]
  refine ⟨181254926241122213975934149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120836617494081475983956099 181254926241122213975934149)
  ·
    refine ⟨33985298670210415120487653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181254926241122213975934149 33985298670210415120487653)
    ·
      refine ⟨6372243500664452835091435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33985298670210415120487653 6372243500664452835091435)
      ·
        refine ⟨9558365250996679252637153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6372243500664452835091435 9558365250996679252637153)
        ·
          refine ⟨7168773938247509439477865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9558365250996679252637153 7168773938247509439477865)
          ·
            refine ⟨5376580453685632079608399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7168773938247509439477865 5376580453685632079608399)
            ·
              refine ⟨8064870680528448119412599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376580453685632079608399 8064870680528448119412599)
              ·
                refine ⟨12097306020792672179118899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8064870680528448119412599 12097306020792672179118899)
                ·
                  refine ⟨18145959031189008268678349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12097306020792672179118899 18145959031189008268678349)
                  ·
                    refine ⟨6804734636695878100754381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18145959031189008268678349 6804734636695878100754381)
                    ·
                      refine ⟨2551775488760954287782893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6804734636695878100754381 2551775488760954287782893)
                      ·
                        rfl

theorem cell23_4969565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_4969565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969565 prefixEnd_4969565 := by exact prefixLift 4969565
  have htrace : WordTrace (prefixWord ++ tailWord_4969565) baseStart_4969565 baseEnd_4969565 := by
    simpa [prefixWord, tailWord_4969565, baseEnd_4969565] using wordTrace_append hprefix tailTrace_4969565
  have hstable : (prefixWord ++ tailWord_4969565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969565).length < 2 ^ (prefixWord ++ tailWord_4969565).sum := by decide
  have hdescent : baseEnd_4969565 < baseStart_4969565 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969661 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 4]
def baseStart_4969661 : Nat := 118140960795 + 4969661 * 2 ^ 59
def prefixEnd_4969661 : Nat := 4983230072969 + 3 ^ 40 * 4969661 * 2
def baseEnd_4969661 : Nat := 2551824782903785912182451

theorem tailTrace_4969661 : CollatzResearch.WordTrace tailWord_4969661 prefixEnd_4969661 2551824782903785912182451 := by
  unfold tailWord_4969661
  simp only [CollatzResearch.WordTrace]
  refine ⟨181258427648774422371428837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120838951765849614914285891 181258427648774422371428837)
  ·
    refine ⟨33985955184145204194642907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 181258427648774422371428837 33985955184145204194642907)
    ·
      refine ⟨50978932776217806291964361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33985955184145204194642907 50978932776217806291964361)
      ·
        refine ⟨38234199582163354718973271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50978932776217806291964361 38234199582163354718973271)
        ·
          refine ⟨57351299373245032078459907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38234199582163354718973271 57351299373245032078459907)
          ·
            refine ⟨86026949059867548117689861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57351299373245032078459907 86026949059867548117689861)
            ·
              refine ⟨16130052948725165272066849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86026949059867548117689861 16130052948725165272066849)
              ·
                refine ⟨12097539711543873954050137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16130052948725165272066849 12097539711543873954050137)
                ·
                  refine ⟨9073154783657905465537603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12097539711543873954050137 9073154783657905465537603)
                  ·
                    refine ⟨13609732175486858198306405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9073154783657905465537603 13609732175486858198306405)
                    ·
                      refine ⟨2551824782903785912182451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13609732175486858198306405 2551824782903785912182451)
                      ·
                        rfl

theorem cell23_4969661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 2, 1, 4].length) (baseStart_4969661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969661 prefixEnd_4969661 := by exact prefixLift 4969661
  have htrace : WordTrace (prefixWord ++ tailWord_4969661) baseStart_4969661 baseEnd_4969661 := by
    simpa [prefixWord, tailWord_4969661, baseEnd_4969661] using wordTrace_append hprefix tailTrace_4969661
  have hstable : (prefixWord ++ tailWord_4969661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969661).length < 2 ^ (prefixWord ++ tailWord_4969661).sum := by decide
  have hdescent : baseEnd_4969661 < baseStart_4969661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969688 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 3, 4]
def baseStart_4969688 : Nat := 118140960795 + 4969688 * 2 ^ 59
def prefixEnd_4969688 : Nat := 4983230072969 + 3 ^ 40 * 4969688 * 2
def baseEnd_4969688 : Nat := 850612882293819102181609

theorem tailTrace_4969688 : CollatzResearch.WordTrace tailWord_4969688 prefixEnd_4969688 850612882293819102181609 := by
  unfold tailWord_4969688
  simp only [CollatzResearch.WordTrace]
  refine ⟨90629706209838302991330859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120839608279784403988441145 90629706209838302991330859)
  ·
    refine ⟨135944559314757454486996289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90629706209838302991330859 135944559314757454486996289)
    ·
      refine ⟨101958419486068090865247217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135944559314757454486996289 101958419486068090865247217)
      ·
        refine ⟨76468814614551068148935413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101958419486068090865247217 76468814614551068148935413)
        ·
          refine ⟨7168951370114162638962695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 76468814614551068148935413 7168951370114162638962695)
          ·
            refine ⟨10753427055171243958444043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7168951370114162638962695 10753427055171243958444043)
            ·
              refine ⟨16130140582756865937666065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10753427055171243958444043 16130140582756865937666065)
              ·
                refine ⟨12097605437067649453249549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16130140582756865937666065 12097605437067649453249549)
                ·
                  refine ⟨4536602038900368544968581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12097605437067649453249549 4536602038900368544968581)
                  ·
                    refine ⟨850612882293819102181609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4536602038900368544968581 850612882293819102181609)
                    ·
                      rfl

theorem cell23_4969688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 3, 4].length) (baseStart_4969688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969688 prefixEnd_4969688 := by exact prefixLift 4969688
  have htrace : WordTrace (prefixWord ++ tailWord_4969688) baseStart_4969688 baseEnd_4969688 := by
    simpa [prefixWord, tailWord_4969688, baseEnd_4969688] using wordTrace_append hprefix tailTrace_4969688
  have hstable : (prefixWord ++ tailWord_4969688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969688).length < 2 ^ (prefixWord ++ tailWord_4969688).sum := by decide
  have hdescent : baseEnd_4969688 < baseStart_4969688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969778 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_4969778 : Nat := 118140960795 + 4969778 * 2 ^ 59
def prefixEnd_4969778 : Nat := 4983230072969 + 3 ^ 40 * 4969778 * 2
def baseEnd_4969778 : Nat := 850628286713453984806471

theorem tailTrace_4969778 : CollatzResearch.WordTrace tailWord_4969778 prefixEnd_4969778 850628286713453984806471 := by
  unfold tailWord_4969778
  simp only [CollatzResearch.WordTrace]
  refine ⟨45315673747337637838359497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120841796659567034235625325 45315673747337637838359497)
  ·
    refine ⟨33986755310503228378769623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45315673747337637838359497 33986755310503228378769623)
    ·
      refine ⟨50980132965754842568154435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33986755310503228378769623 50980132965754842568154435)
      ·
        refine ⟨76470199448632263852231653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50980132965754842568154435 76470199448632263852231653)
        ·
          refine ⟨14338162396618549472293435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 76470199448632263852231653 14338162396618549472293435)
          ·
            refine ⟨21507243594927824208440153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14338162396618549472293435 21507243594927824208440153)
            ·
              refine ⟨16130432696195868156330115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21507243594927824208440153 16130432696195868156330115)
              ·
                refine ⟨24195649044293802234495173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16130432696195868156330115 24195649044293802234495173)
                ·
                  refine ⟨4536684195805087918967845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24195649044293802234495173 4536684195805087918967845)
                  ·
                    refine ⟨850628286713453984806471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4536684195805087918967845 850628286713453984806471)
                    ·
                      rfl

theorem cell23_4969778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_4969778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969778 prefixEnd_4969778 := by exact prefixLift 4969778
  have htrace : WordTrace (prefixWord ++ tailWord_4969778) baseStart_4969778 baseEnd_4969778 := by
    simpa [prefixWord, tailWord_4969778, baseEnd_4969778] using wordTrace_append hprefix tailTrace_4969778
  have hstable : (prefixWord ++ tailWord_4969778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969778).length < 2 ^ (prefixWord ++ tailWord_4969778).sum := by decide
  have hdescent : baseEnd_4969778 < baseStart_4969778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969781 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 6]
def baseStart_4969781 : Nat := 118140960795 + 4969781 * 2 ^ 59
def prefixEnd_4969781 : Nat := 4983230072969 + 3 ^ 40 * 4969781 * 2
def baseEnd_4969781 : Nat := 2551886400582325442681899

theorem tailTrace_4969781 : CollatzResearch.WordTrace tailWord_4969781 prefixEnd_4969781 2551886400582325442681899 := by
  unfold tailWord_4969781
  simp only [CollatzResearch.WordTrace]
  refine ⟨181262804408339682865797197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120841869605559788577198131 181262804408339682865797197)
  ·
    refine ⟨67973551653127381074673949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181262804408339682865797197 67973551653127381074673949)
    ·
      refine ⟨25490081869922767903002731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67973551653127381074673949 25490081869922767903002731)
      ·
        refine ⟨38235122804884151854504097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25490081869922767903002731 38235122804884151854504097)
        ·
          refine ⟨28676342103663113890878073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38235122804884151854504097 28676342103663113890878073)
          ·
            refine ⟨21507256577747335418158555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28676342103663113890878073 21507256577747335418158555)
            ·
              refine ⟨32260884866621003127237833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21507256577747335418158555 32260884866621003127237833)
              ·
                refine ⟨24195663649965752345428375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32260884866621003127237833 24195663649965752345428375)
                ·
                  refine ⟨36293495474948628518142563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24195663649965752345428375 36293495474948628518142563)
                  ·
                    refine ⟨54440243212422942777213845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36293495474948628518142563 54440243212422942777213845)
                    ·
                      refine ⟨2551886400582325442681899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54440243212422942777213845 2551886400582325442681899)
                      ·
                        rfl

theorem cell23_4969781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_4969781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969781 prefixEnd_4969781 := by exact prefixLift 4969781
  have htrace : WordTrace (prefixWord ++ tailWord_4969781) baseStart_4969781 baseEnd_4969781 := by
    simpa [prefixWord, tailWord_4969781, baseEnd_4969781] using wordTrace_append hprefix tailTrace_4969781
  have hstable : (prefixWord ++ tailWord_4969781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969781).length < 2 ^ (prefixWord ++ tailWord_4969781).sum := by decide
  have hdescent : baseEnd_4969781 < baseStart_4969781 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969791 : List Nat := [1, 1, 2, 2, 4, 3, 2, 8]
def baseStart_4969791 : Nat := 118140960795 + 4969791 * 2 ^ 59
def prefixEnd_4969791 : Nat := 4983230072969 + 3 ^ 40 * 4969791 * 2
def baseEnd_4969791 : Nat := 94514501310698903835439

theorem tailTrace_4969791 : CollatzResearch.WordTrace tailWord_4969791 prefixEnd_4969791 94514501310698903835439 := by
  unfold tailWord_4969791
  simp only [CollatzResearch.WordTrace]
  refine ⟨181263169138303454573661227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120842112758868969715774151 181263169138303454573661227)
  ·
    refine ⟨271894753707455181860491841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181263169138303454573661227 271894753707455181860491841)
    ·
      refine ⟨203921065280591386395368881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271894753707455181860491841 203921065280591386395368881)
      ·
        refine ⟨152940798960443539796526661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203921065280591386395368881 152940798960443539796526661)
        ·
          refine ⟨28676399805083163711848749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 152940798960443539796526661 28676399805083163711848749)
          ·
            refine ⟨10753649926906186391943281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28676399805083163711848749 10753649926906186391943281)
            ·
              refine ⟨8065237445179639793957461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10753649926906186391943281 8065237445179639793957461)
              ·
                refine ⟨94514501310698903835439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8065237445179639793957461 94514501310698903835439)
                ·
                  rfl

theorem cell23_4969791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 2, 8].length) (baseStart_4969791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969791 prefixEnd_4969791 := by exact prefixLift 4969791
  have htrace : WordTrace (prefixWord ++ tailWord_4969791) baseStart_4969791 baseEnd_4969791 := by
    simpa [prefixWord, tailWord_4969791, baseEnd_4969791] using wordTrace_append hprefix tailTrace_4969791
  have hstable : (prefixWord ++ tailWord_4969791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969791).length < 2 ^ (prefixWord ++ tailWord_4969791).sum := by decide
  have hdescent : baseEnd_4969791 < baseStart_4969791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969818 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3]
def baseStart_4969818 : Nat := 118140960795 + 4969818 * 2 ^ 59
def prefixEnd_4969818 : Nat := 4983230072969 + 3 ^ 40 * 4969818 * 2
def baseEnd_4969818 : Nat := 2551905399366541797919229

theorem tailTrace_4969818 : CollatzResearch.WordTrace tailWord_4969818 prefixEnd_4969818 2551905399366541797919229 := by
  unfold tailWord_4969818
  simp only [CollatzResearch.WordTrace]
  refine ⟨45316038477301409546223527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120842769272803758789929405 45316038477301409546223527)
  ·
    refine ⟨67974057715952114319335291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45316038477301409546223527 67974057715952114319335291)
    ·
      refine ⟨101961086573928171479002937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67974057715952114319335291 101961086573928171479002937)
      ·
        refine ⟨76470814930446128609252203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101961086573928171479002937 76470814930446128609252203)
        ·
          refine ⟨114706222395669192913878305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76470814930446128609252203 114706222395669192913878305)
          ·
            refine ⟨86029666796751894685408729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114706222395669192913878305 86029666796751894685408729)
            ·
              refine ⟨64522250097563921014056547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86029666796751894685408729 64522250097563921014056547)
              ·
                refine ⟨96783375146345881521084821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64522250097563921014056547 96783375146345881521084821)
                ·
                  refine ⟨4536720709984963196300851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 96783375146345881521084821 4536720709984963196300851)
                  ·
                    refine ⟨6805081064977444794451277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4536720709984963196300851 6805081064977444794451277)
                    ·
                      refine ⟨2551905399366541797919229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6805081064977444794451277 2551905399366541797919229)
                      ·
                        rfl

theorem cell23_4969818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 1, 3].length) (baseStart_4969818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969818 prefixEnd_4969818 := by exact prefixLift 4969818
  have htrace : WordTrace (prefixWord ++ tailWord_4969818) baseStart_4969818 baseEnd_4969818 := by
    simpa [prefixWord, tailWord_4969818, baseEnd_4969818] using wordTrace_append hprefix tailTrace_4969818
  have hstable : (prefixWord ++ tailWord_4969818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969818).length < 2 ^ (prefixWord ++ tailWord_4969818).sum := by decide
  have hdescent : baseEnd_4969818 < baseStart_4969818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969836 : List Nat := [2, 2, 1, 1, 5, 3, 2, 2, 1, 2, 2]
def baseStart_4969836 : Nat := 118140960795 + 4969836 * 2 ^ 59
def prefixEnd_4969836 : Nat := 4983230072969 + 3 ^ 40 * 4969836 * 2
def baseEnd_4969836 : Nat := 2551914642018322727494147

theorem tailTrace_4969836 : CollatzResearch.WordTrace tailWord_4969836 prefixEnd_4969836 2551914642018322727494147 := by
  unfold tailWord_4969836
  simp only [CollatzResearch.WordTrace]
  refine ⟨90632405211570213629524681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120843206948760284839366241 90632405211570213629524681)
  ·
    refine ⟨67974303908677660222143511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90632405211570213629524681 67974303908677660222143511)
    ·
      refine ⟨101961455863016490333215267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67974303908677660222143511 101961455863016490333215267)
      ·
        refine ⟨152942183794524735499822901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101961455863016490333215267 152942183794524735499822901)
        ·
          refine ⟨14338329730736693953108397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 152942183794524735499822901 14338329730736693953108397)
          ·
            refine ⟨5376873649026260232415649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14338329730736693953108397 5376873649026260232415649)
            ·
              refine ⟨4032655236769695174311737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5376873649026260232415649 4032655236769695174311737)
              ·
                refine ⟨3024491427577271380733803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4032655236769695174311737 3024491427577271380733803)
                ·
                  refine ⟨4536737141365907071100705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3024491427577271380733803 4536737141365907071100705)
                  ·
                    refine ⟨3402552856024430303325529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4536737141365907071100705 3402552856024430303325529)
                    ·
                      refine ⟨2551914642018322727494147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3402552856024430303325529 2551914642018322727494147)
                      ·
                        rfl

theorem cell23_4969836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_4969836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969836 prefixEnd_4969836 := by exact prefixLift 4969836
  have htrace : WordTrace (prefixWord ++ tailWord_4969836) baseStart_4969836 baseEnd_4969836 := by
    simpa [prefixWord, tailWord_4969836, baseEnd_4969836] using wordTrace_append hprefix tailTrace_4969836
  have hstable : (prefixWord ++ tailWord_4969836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969836).length < 2 ^ (prefixWord ++ tailWord_4969836).sum := by decide
  have hdescent : baseEnd_4969836 < baseStart_4969836 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969841 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 4]
def baseStart_4969841 : Nat := 118140960795 + 4969841 * 2 ^ 59
def prefixEnd_4969841 : Nat := 4983230072969 + 3 ^ 40 * 4969841 * 2
def baseEnd_4969841 : Nat := 2551917209421595207931623

theorem tailTrace_4969841 : CollatzResearch.WordTrace tailWord_4969841 prefixEnd_4969841 2551917209421595207931623 := by
  unfold tailWord_4969841
  simp only [CollatzResearch.WordTrace]
  refine ⟨181264992788122313112981377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120843328525414875408654251 181264992788122313112981377)
  ·
    refine ⟨135948744591091734834736033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181264992788122313112981377 135948744591091734834736033)
    ·
      refine ⟨101961558443318801126052025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135948744591091734834736033 101961558443318801126052025)
      ·
        refine ⟨76471168832489100844539019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101961558443318801126052025 76471168832489100844539019)
        ·
          refine ⟨114706753248733651266808529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76471168832489100844539019 114706753248733651266808529)
          ·
            refine ⟨86030064936550238450106397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114706753248733651266808529 86030064936550238450106397)
            ·
              refine ⟨32261274351206339418789899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86030064936550238450106397 32261274351206339418789899)
              ·
                refine ⟨48391911526809509128184849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32261274351206339418789899 48391911526809509128184849)
                ·
                  refine ⟨36293933645107131846138637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48391911526809509128184849 36293933645107131846138637)
                  ·
                    refine ⟨13610225116915174442301989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36293933645107131846138637 13610225116915174442301989)
                    ·
                      refine ⟨2551917209421595207931623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13610225116915174442301989 2551917209421595207931623)
                      ·
                        rfl

theorem cell23_4969841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 2, 3, 4].length) (baseStart_4969841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969841 prefixEnd_4969841 := by exact prefixLift 4969841
  have htrace : WordTrace (prefixWord ++ tailWord_4969841) baseStart_4969841 baseEnd_4969841 := by
    simpa [prefixWord, tailWord_4969841, baseEnd_4969841] using wordTrace_append hprefix tailTrace_4969841
  have hstable : (prefixWord ++ tailWord_4969841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969841).length < 2 ^ (prefixWord ++ tailWord_4969841).sum := by decide
  have hdescent : baseEnd_4969841 < baseStart_4969841 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969851 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 2, 6]
def baseStart_4969851 : Nat := 118140960795 + 4969851 * 2 ^ 59
def prefixEnd_4969851 : Nat := 4983230072969 + 3 ^ 40 * 4969851 * 2
def baseEnd_4969851 : Nat := 850640781409380056268859

theorem tailTrace_4969851 : CollatzResearch.WordTrace tailWord_4969851 prefixEnd_4969851 850640781409380056268859 := by
  unfold tailWord_4969851
  simp only [CollatzResearch.WordTrace]
  refine ⟨181265357518086084820845407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120843571678724056547230271 181265357518086084820845407)
  ·
    refine ⟨271898036277129127231268111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181265357518086084820845407 271898036277129127231268111)
    ·
      refine ⟨407847054415693690846902167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271898036277129127231268111 407847054415693690846902167)
      ·
        refine ⟨611770581623540536270353251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407847054415693690846902167 611770581623540536270353251)
        ·
          refine ⟨917655872435310804405529877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611770581623540536270353251 917655872435310804405529877)
          ·
            refine ⟨43015119020405193956509213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 917655872435310804405529877 43015119020405193956509213)
            ·
              refine ⟨16130669632651947733690955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43015119020405193956509213 16130669632651947733690955)
              ·
                refine ⟨24196004448977921600536433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16130669632651947733690955 24196004448977921600536433)
                ·
                  refine ⟨18147003336733441200402325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24196004448977921600536433 18147003336733441200402325)
                  ·
                    refine ⟨850640781409380056268859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18147003336733441200402325 850640781409380056268859)
                    ·
                      rfl

theorem cell23_4969851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 2, 6].length) (baseStart_4969851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969851 prefixEnd_4969851 := by exact prefixLift 4969851
  have htrace : WordTrace (prefixWord ++ tailWord_4969851) baseStart_4969851 baseEnd_4969851 := by
    simpa [prefixWord, tailWord_4969851, baseEnd_4969851] using wordTrace_append hprefix tailTrace_4969851
  have hstable : (prefixWord ++ tailWord_4969851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969851).length < 2 ^ (prefixWord ++ tailWord_4969851).sum := by decide
  have hdescent : baseEnd_4969851 < baseStart_4969851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969861 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 5]
def baseStart_4969861 : Nat := 118140960795 + 4969861 * 2 ^ 59
def prefixEnd_4969861 : Nat := 4983230072969 + 3 ^ 40 * 4969861 * 2
def baseEnd_4969861 : Nat := 2551927479034685129681531

theorem tailTrace_4969861 : CollatzResearch.WordTrace tailWord_4969861 prefixEnd_4969861 2551927479034685129681531 := by
  unfold tailWord_4969861
  simp only [CollatzResearch.WordTrace]
  refine ⟨181265722248049856528709437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120843814832033237685806291 181265722248049856528709437)
  ·
    refine ⟨67974645843018696198266039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181265722248049856528709437 67974645843018696198266039)
    ·
      refine ⟨101961968764528044297399059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67974645843018696198266039 101961968764528044297399059)
      ·
        refine ⟨152942953146792066446098589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101961968764528044297399059 152942953146792066446098589)
        ·
          refine ⟨57353607430047024917286971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152942953146792066446098589 57353607430047024917286971)
          ·
            refine ⟨86030411145070537375930457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57353607430047024917286971 86030411145070537375930457)
            ·
              refine ⟨64522808358802903031947843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86030411145070537375930457 64522808358802903031947843)
              ·
                refine ⟨96784212538204354547921765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64522808358802903031947843 96784212538204354547921765)
                ·
                  refine ⟨18147039850913316477735331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96784212538204354547921765 18147039850913316477735331)
                  ·
                    refine ⟨27220559776369974716602997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18147039850913316477735331 27220559776369974716602997)
                    ·
                      refine ⟨2551927479034685129681531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27220559776369974716602997 2551927479034685129681531)
                      ·
                        rfl

theorem cell23_4969861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 4, 1, 5].length) (baseStart_4969861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969861 prefixEnd_4969861 := by exact prefixLift 4969861
  have htrace : WordTrace (prefixWord ++ tailWord_4969861) baseStart_4969861 baseEnd_4969861 := by
    simpa [prefixWord, tailWord_4969861, baseEnd_4969861] using wordTrace_append hprefix tailTrace_4969861
  have hstable : (prefixWord ++ tailWord_4969861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969861).length < 2 ^ (prefixWord ++ tailWord_4969861).sum := by decide
  have hdescent : baseEnd_4969861 < baseStart_4969861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969886 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_4969886 : Nat := 118140960795 + 4969886 * 2 ^ 59
def prefixEnd_4969886 : Nat := 4983230072969 + 3 ^ 40 * 4969886 * 2
def baseEnd_4969886 : Nat := 2551940316051047531868917

theorem tailTrace_4969886 : CollatzResearch.WordTrace tailWord_4969886 prefixEnd_4969886 2551940316051047531868917 := by
  unfold tailWord_4969886
  simp only [CollatzResearch.WordTrace]
  refine ⟨22658329259119910724796189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120844422715306190532246341 22658329259119910724796189)
  ·
    refine ⟨8496873472169966521798571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22658329259119910724796189 8496873472169966521798571)
    ·
      refine ⟨12745310208254949782697857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8496873472169966521798571 12745310208254949782697857)
      ·
        refine ⟨9558982656191212337023393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12745310208254949782697857 9558982656191212337023393)
        ·
          refine ⟨7169236992143409252767545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9558982656191212337023393 7169236992143409252767545)
          ·
            refine ⟨5376927744107556939575659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7169236992143409252767545 5376927744107556939575659)
            ·
              refine ⟨8065391616161335409363489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376927744107556939575659 8065391616161335409363489)
              ·
                refine ⟨6049043712121001557022617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8065391616161335409363489 6049043712121001557022617)
                ·
                  refine ⟨4536782784090751167766963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6049043712121001557022617 4536782784090751167766963)
                  ·
                    refine ⟨6805174176136126751650445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4536782784090751167766963 6805174176136126751650445)
                    ·
                      refine ⟨2551940316051047531868917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6805174176136126751650445 2551940316051047531868917)
                      ·
                        rfl

theorem cell23_4969886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_4969886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969886 prefixEnd_4969886 := by exact prefixLift 4969886
  have htrace : WordTrace (prefixWord ++ tailWord_4969886) baseStart_4969886 baseEnd_4969886 := by
    simpa [prefixWord, tailWord_4969886, baseEnd_4969886] using wordTrace_append hprefix tailTrace_4969886
  have hstable : (prefixWord ++ tailWord_4969886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969886).length < 2 ^ (prefixWord ++ tailWord_4969886).sum := by decide
  have hdescent : baseEnd_4969886 < baseStart_4969886 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969911 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 3, 7]
def baseStart_4969911 : Nat := 118140960795 + 4969911 * 2 ^ 59
def prefixEnd_4969911 : Nat := 4983230072969 + 3 ^ 40 * 4969911 * 2
def baseEnd_4969911 : Nat := 850651051022469978018767

theorem tailTrace_4969911 : CollatzResearch.WordTrace tailWord_4969911 prefixEnd_4969911 850651051022469978018767 := by
  unfold tailWord_4969911
  simp only [CollatzResearch.WordTrace]
  refine ⟨181267545897868715068029587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120845030598579143378686391 181267545897868715068029587)
  ·
    refine ⟨271901318846803072602044381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181267545897868715068029587 271901318846803072602044381)
    ·
      refine ⟨101962994567551152225766643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271901318846803072602044381 101962994567551152225766643)
      ·
        refine ⟨152944491851326728338649965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101962994567551152225766643 152944491851326728338649965)
        ·
          refine ⟨57354184444247523126993737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152944491851326728338649965 57354184444247523126993737)
          ·
            refine ⟨43015638333185642345245303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57354184444247523126993737 43015638333185642345245303)
            ·
              refine ⟨64523457499778463517867955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43015638333185642345245303 64523457499778463517867955)
              ·
                refine ⟨96785186249667695276801933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64523457499778463517867955 96785186249667695276801933)
                ·
                  refine ⟨36294444843625385728800725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96785186249667695276801933 36294444843625385728800725)
                  ·
                    refine ⟨850651051022469978018767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36294444843625385728800725 850651051022469978018767)
                    ·
                      rfl

theorem cell23_4969911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_4969911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969911 prefixEnd_4969911 := by exact prefixLift 4969911
  have htrace : WordTrace (prefixWord ++ tailWord_4969911) baseStart_4969911 baseEnd_4969911 := by
    simpa [prefixWord, tailWord_4969911, baseEnd_4969911] using wordTrace_append hprefix tailTrace_4969911
  have hstable : (prefixWord ++ tailWord_4969911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969911).length < 2 ^ (prefixWord ++ tailWord_4969911).sum := by decide
  have hdescent : baseEnd_4969911 < baseStart_4969911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969928 : List Nat := [2, 1, 3, 1, 3, 1, 2, 3, 2, 5]
def baseStart_4969928 : Nat := 118140960795 + 4969928 * 2 ^ 59
def prefixEnd_4969928 : Nat := 4983230072969 + 3 ^ 40 * 4969928 * 2
def baseEnd_4969928 : Nat := 850653960746178789181241

theorem tailTrace_4969928 : CollatzResearch.WordTrace tailWord_4969928 prefixEnd_4969928 850653960746178789181241 := by
  unfold tailWord_4969928
  simp only [CollatzResearch.WordTrace]
  refine ⟨90634082969403563485699219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120845443959204751314265625 90634082969403563485699219)
  ·
    refine ⟨135951124454105345228548829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90634082969403563485699219 135951124454105345228548829)
    ·
      refine ⟨50981671670289504460705811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135951124454105345228548829 50981671670289504460705811)
      ·
        refine ⟨76472507505434256691058717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50981671670289504460705811 76472507505434256691058717)
        ·
          refine ⟨28677190314537846259147019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76472507505434256691058717 28677190314537846259147019)
          ·
            refine ⟨43015785471806769388720529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28677190314537846259147019 43015785471806769388720529)
            ·
              refine ⟨32261839103855077041540397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43015785471806769388720529 32261839103855077041540397)
              ·
                refine ⟨12098189663945653890577649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32261839103855077041540397 12098189663945653890577649)
                ·
                  refine ⟨9073642247959240417933237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12098189663945653890577649 9073642247959240417933237)
                  ·
                    refine ⟨850653960746178789181241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9073642247959240417933237 850653960746178789181241)
                    ·
                      rfl

theorem cell23_4969928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_4969928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969928 prefixEnd_4969928 := by exact prefixLift 4969928
  have htrace : WordTrace (prefixWord ++ tailWord_4969928) baseStart_4969928 baseEnd_4969928 := by
    simpa [prefixWord, tailWord_4969928, baseEnd_4969928] using wordTrace_append hprefix tailTrace_4969928
  have hstable : (prefixWord ++ tailWord_4969928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969928).length < 2 ^ (prefixWord ++ tailWord_4969928).sum := by decide
  have hdescent : baseEnd_4969928 < baseStart_4969928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969932 : List Nat := [2, 2, 1, 4, 2, 3, 1, 3, 5]
def baseStart_4969932 : Nat := 118140960795 + 4969932 * 2 ^ 59
def prefixEnd_4969932 : Nat := 4983230072969 + 3 ^ 40 * 4969932 * 2
def baseEnd_4969932 : Nat := 283551548462350483543745

theorem tailTrace_4969932 : CollatzResearch.WordTrace tailWord_4969932 prefixEnd_4969932 283551548462350483543745 := by
  unfold tailWord_4969932
  simp only [CollatzResearch.WordTrace]
  refine ⟨90634155915396317827272025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120845541220528423769696033 90634155915396317827272025)
  ·
    refine ⟨67975616936547238370454019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90634155915396317827272025 67975616936547238370454019)
    ·
      refine ⟨101963425404820857555681029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67975616936547238370454019 101963425404820857555681029)
      ·
        refine ⟨19118142263403910791690193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 101963425404820857555681029 19118142263403910791690193)
        ·
          refine ⟨14338606697552933093767645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19118142263403910791690193 14338606697552933093767645)
          ·
            refine ⟨5376977511582349910162867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14338606697552933093767645 5376977511582349910162867)
            ·
              refine ⟨8065466267373524865244301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5376977511582349910162867 8065466267373524865244301)
              ·
                refine ⟨3024549850265071824466613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8065466267373524865244301 3024549850265071824466613)
                ·
                  refine ⟨283551548462350483543745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3024549850265071824466613 283551548462350483543745)
                  ·
                    rfl

theorem cell23_4969932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_4969932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969932 prefixEnd_4969932 := by exact prefixLift 4969932
  have htrace : WordTrace (prefixWord ++ tailWord_4969932) baseStart_4969932 baseEnd_4969932 := by
    simpa [prefixWord, tailWord_4969932, baseEnd_4969932] using wordTrace_append hprefix tailTrace_4969932
  have hstable : (prefixWord ++ tailWord_4969932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969932).length < 2 ^ (prefixWord ++ tailWord_4969932).sum := by decide
  have hdescent : baseEnd_4969932 < baseStart_4969932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969961 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 6]
def baseStart_4969961 : Nat := 118140960795 + 4969961 * 2 ^ 59
def prefixEnd_4969961 : Nat := 4983230072969 + 3 ^ 40 * 4969961 * 2
def baseEnd_4969961 : Nat := 2551978827100134738431071

theorem tailTrace_4969961 : CollatzResearch.WordTrace tailWord_4969961 prefixEnd_4969961 2551978827100134738431071 := by
  unfold tailWord_4969961
  simp only [CollatzResearch.WordTrace]
  refine ⟨181269369547687573607349737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120846246365125049071566491 181269369547687573607349737)
  ·
    refine ⟨135952027160765680205512303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181269369547687573607349737 135952027160765680205512303)
    ·
      refine ⟨203928040741148520308268455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135952027160765680205512303 203928040741148520308268455)
      ·
        refine ⟨305892061111722780462402683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203928040741148520308268455 305892061111722780462402683)
        ·
          refine ⟨458838091667584170693604025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305892061111722780462402683 458838091667584170693604025)
          ·
            refine ⟨344128568750688128020203019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 458838091667584170693604025 344128568750688128020203019)
            ·
              refine ⟨516192853126032192030304529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344128568750688128020203019 516192853126032192030304529)
              ·
                refine ⟨387144639844524144022728397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 516192853126032192030304529 387144639844524144022728397)
                ·
                  refine ⟨145179239941696554008523149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 387144639844524144022728397 145179239941696554008523149)
                  ·
                    refine ⟨54442214978136207753196181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 145179239941696554008523149 54442214978136207753196181)
                    ·
                      refine ⟨2551978827100134738431071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54442214978136207753196181 2551978827100134738431071)
                      ·
                        rfl

theorem cell23_4969961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 3, 6].length) (baseStart_4969961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969961 prefixEnd_4969961 := by exact prefixLift 4969961
  have htrace : WordTrace (prefixWord ++ tailWord_4969961) baseStart_4969961 baseEnd_4969961 := by
    simpa [prefixWord, tailWord_4969961, baseEnd_4969961] using wordTrace_append hprefix tailTrace_4969961
  have hstable : (prefixWord ++ tailWord_4969961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969961).length < 2 ^ (prefixWord ++ tailWord_4969961).sum := by decide
  have hdescent : baseEnd_4969961 < baseStart_4969961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4969971 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 10]
def baseStart_4969971 : Nat := 118140960795 + 4969971 * 2 ^ 59
def prefixEnd_4969971 : Nat := 4983230072969 + 3 ^ 40 * 4969971 * 2
def baseEnd_4969971 : Nat := 283553773545186633256225

theorem tailTrace_4969971 : CollatzResearch.WordTrace tailWord_4969971 prefixEnd_4969971 283553773545186633256225 := by
  unfold tailWord_4969971
  simp only [CollatzResearch.WordTrace]
  refine ⟨181269734277651345315213767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120846489518434230210142511 181269734277651345315213767)
  ·
    refine ⟨271904601416477017972820651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181269734277651345315213767 271904601416477017972820651)
    ·
      refine ⟨407856902124715526959230977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271904601416477017972820651 407856902124715526959230977)
      ·
        refine ⟨305892676593536645219423233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 407856902124715526959230977 305892676593536645219423233)
        ·
          refine ⟨229419507445152483914567425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305892676593536645219423233 229419507445152483914567425)
          ·
            refine ⟨172064630583864362935925569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229419507445152483914567425 172064630583864362935925569)
            ·
              refine ⟨129048472937898272201944177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172064630583864362935925569 129048472937898272201944177)
              ·
                refine ⟨96786354703423704151458133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129048472937898272201944177 96786354703423704151458133)
                ·
                  refine ⟨283553773545186633256225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 96786354703423704151458133 283553773545186633256225)
                  ·
                    rfl

theorem cell23_4969971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 10].length) (baseStart_4969971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4969971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4969971 prefixEnd_4969971 := by exact prefixLift 4969971
  have htrace : WordTrace (prefixWord ++ tailWord_4969971) baseStart_4969971 baseEnd_4969971 := by
    simpa [prefixWord, tailWord_4969971, baseEnd_4969971] using wordTrace_append hprefix tailTrace_4969971
  have hstable : (prefixWord ++ tailWord_4969971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4969971).length < 2 ^ (prefixWord ++ tailWord_4969971).sum := by decide
  have hdescent : baseEnd_4969971 < baseStart_4969971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4969971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970005 : List Nat := [1, 3, 2, 1, 3, 3, 2, 2, 6]
def baseStart_4970005 : Nat := 118140960795 + 4970005 * 2 ^ 59
def prefixEnd_4970005 : Nat := 4983230072969 + 3 ^ 40 * 4970005 * 2
def baseEnd_4970005 : Nat := 283555713360992507364541

theorem tailTrace_4970005 : CollatzResearch.WordTrace tailWord_4970005 prefixEnd_4970005 283555713360992507364541 := by
  unfold tailWord_4970005
  simp only [CollatzResearch.WordTrace]
  refine ⟨181270974359528169121951469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120847316239685446081300979 181270974359528169121951469)
  ·
    refine ⟨67976615384823063420731801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181270974359528169121951469 67976615384823063420731801)
    ·
      refine ⟨50982461538617297565548851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67976615384823063420731801 50982461538617297565548851)
      ·
        refine ⟨76473692307925946348323277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50982461538617297565548851 76473692307925946348323277)
        ·
          refine ⟨28677634615472229880621229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76473692307925946348323277 28677634615472229880621229)
          ·
            refine ⟨10754112980802086205232961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28677634615472229880621229 10754112980802086205232961)
            ·
              refine ⟨8065584735601564653924721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10754112980802086205232961 8065584735601564653924721)
              ·
                refine ⟨6049188551701173490443541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8065584735601564653924721 6049188551701173490443541)
                ·
                  refine ⟨283555713360992507364541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6049188551701173490443541 283555713360992507364541)
                  ·
                    rfl

theorem cell23_4970005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 2, 6].length) (baseStart_4970005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970005 prefixEnd_4970005 := by exact prefixLift 4970005
  have htrace : WordTrace (prefixWord ++ tailWord_4970005) baseStart_4970005 baseEnd_4970005 := by
    simpa [prefixWord, tailWord_4970005, baseEnd_4970005] using wordTrace_append hprefix tailTrace_4970005
  have hstable : (prefixWord ++ tailWord_4970005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970005).length < 2 ^ (prefixWord ++ tailWord_4970005).sum := by decide
  have hdescent : baseEnd_4970005 < baseStart_4970005 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970065 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 4, 4]
def baseStart_4970065 : Nat := 118140960795 + 4970065 * 2 ^ 59
def prefixEnd_4970065 : Nat := 4983230072969 + 3 ^ 40 * 4970065 * 2
def baseEnd_4970065 : Nat := 850677409696067443843531

theorem tailTrace_4970065 : CollatzResearch.WordTrace tailWord_4970065 prefixEnd_4970065 850677409696067443843531 := by
  unfold tailWord_4970065
  simp only [CollatzResearch.WordTrace]
  refine ⟨181273162739310799369135649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120848775159540532912757099 181273162739310799369135649)
  ·
    refine ⟨135954872054483099526851737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181273162739310799369135649 135954872054483099526851737)
    ·
      refine ⟨101966154040862324645138803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135954872054483099526851737 101966154040862324645138803)
      ·
        refine ⟨152949231061293486967708205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101966154040862324645138803 152949231061293486967708205)
        ·
          refine ⟨57355961647985057612890577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152949231061293486967708205 57355961647985057612890577)
          ·
            refine ⟨43016971235988793209667933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57355961647985057612890577 43016971235988793209667933)
            ·
              refine ⟨16131364213495797453625475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43016971235988793209667933 16131364213495797453625475)
              ·
                refine ⟨24197046320243696180438213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16131364213495797453625475 24197046320243696180438213)
                ·
                  refine ⟨4536946185045693033832165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24197046320243696180438213 4536946185045693033832165)
                  ·
                    refine ⟨850677409696067443843531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4536946185045693033832165 850677409696067443843531)
                    ·
                      rfl

theorem cell23_4970065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 4, 4].length) (baseStart_4970065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970065 prefixEnd_4970065 := by exact prefixLift 4970065
  have htrace : WordTrace (prefixWord ++ tailWord_4970065) baseStart_4970065 baseEnd_4970065 := by
    simpa [prefixWord, tailWord_4970065, baseEnd_4970065] using wordTrace_append hprefix tailTrace_4970065
  have hstable : (prefixWord ++ tailWord_4970065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970065).length < 2 ^ (prefixWord ++ tailWord_4970065).sum := by decide
  have hdescent : baseEnd_4970065 < baseStart_4970065 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970085 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 6]
def baseStart_4970085 : Nat := 118140960795 + 4970085 * 2 ^ 59
def prefixEnd_4970085 : Nat := 4983230072969 + 3 ^ 40 * 4970085 * 2
def baseEnd_4970085 : Nat := 2552042498701292253280501

theorem tailTrace_4970085 : CollatzResearch.WordTrace tailWord_4970085 prefixEnd_4970085 2552042498701292253280501 := by
  unfold tailWord_4970085
  simp only [CollatzResearch.WordTrace]
  refine ⟨181273892199238342784863709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120849261466158895189909139 181273892199238342784863709)
  ·
    refine ⟨67977709574714378544323891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181273892199238342784863709 67977709574714378544323891)
    ·
      refine ⟨101966564362071567816485837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67977709574714378544323891 101966564362071567816485837)
      ·
        refine ⟨38237461635776837931182189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101966564362071567816485837 38237461635776837931182189)
        ·
          refine ⟨14339048113416314224193321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38237461635776837931182189 14339048113416314224193321)
          ·
            refine ⟨10754286085062235668144991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14339048113416314224193321 10754286085062235668144991)
            ·
              refine ⟨16131429127593353502217487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754286085062235668144991 16131429127593353502217487)
              ·
                refine ⟨24197143691390030253326231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16131429127593353502217487 24197143691390030253326231)
                ·
                  refine ⟨36295715537085045379989347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24197143691390030253326231 36295715537085045379989347)
                  ·
                    refine ⟨54443573305627568069984021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36295715537085045379989347 54443573305627568069984021)
                    ·
                      refine ⟨2552042498701292253280501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54443573305627568069984021 2552042498701292253280501)
                      ·
                        rfl

theorem cell23_4970085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 1, 6].length) (baseStart_4970085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970085 prefixEnd_4970085 := by exact prefixLift 4970085
  have htrace : WordTrace (prefixWord ++ tailWord_4970085) baseStart_4970085 baseEnd_4970085 := by
    simpa [prefixWord, tailWord_4970085, baseEnd_4970085] using wordTrace_append hprefix tailTrace_4970085
  have hstable : (prefixWord ++ tailWord_4970085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970085).length < 2 ^ (prefixWord ++ tailWord_4970085).sum := by decide
  have hdescent : baseEnd_4970085 < baseStart_4970085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970105 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 3]
def baseStart_4970105 : Nat := 118140960795 + 4970105 * 2 ^ 59
def prefixEnd_4970105 : Nat := 4983230072969 + 3 ^ 40 * 4970105 * 2
def baseEnd_4970105 : Nat := 2552052768314382175030409

theorem tailTrace_4970105 : CollatzResearch.WordTrace tailWord_4970105 prefixEnd_4970105 2552052768314382175030409 := by
  unfold tailWord_4970105
  simp only [CollatzResearch.WordTrace]
  refine ⟨181274621659165886200591769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120849747772777257467061179 181274621659165886200591769)
  ·
    refine ⟨135955966244374414650443827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181274621659165886200591769 135955966244374414650443827)
    ·
      refine ⟨203933949366561621975665741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135955966244374414650443827 203933949366561621975665741)
      ·
        refine ⟨76475231012460608240874653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 203933949366561621975665741 76475231012460608240874653)
        ·
          refine ⟨28678211629672728090327995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76475231012460608240874653 28678211629672728090327995)
          ·
            refine ⟨43017317444509092135491993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28678211629672728090327995 43017317444509092135491993)
            ·
              refine ⟨32262988083381819101618995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43017317444509092135491993 32262988083381819101618995)
              ·
                refine ⟨48394482125072728652428493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32262988083381819101618995 48394482125072728652428493)
                ·
                  refine ⟨18147930796902273244660685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48394482125072728652428493 18147930796902273244660685)
                  ·
                    refine ⟨6805474048838352466747757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18147930796902273244660685 6805474048838352466747757)
                    ·
                      refine ⟨2552052768314382175030409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6805474048838352466747757 2552052768314382175030409)
                      ·
                        rfl

theorem cell23_4970105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_4970105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970105 prefixEnd_4970105 := by exact prefixLift 4970105
  have htrace : WordTrace (prefixWord ++ tailWord_4970105) baseStart_4970105 baseEnd_4970105 := by
    simpa [prefixWord, tailWord_4970105, baseEnd_4970105] using wordTrace_append hprefix tailTrace_4970105
  have hstable : (prefixWord ++ tailWord_4970105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970105).length < 2 ^ (prefixWord ++ tailWord_4970105).sum := by decide
  have hdescent : baseEnd_4970105 < baseStart_4970105 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970108 : List Nat := [2, 2, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_4970108 : Nat := 118140960795 + 4970108 * 2 ^ 59
def prefixEnd_4970108 : Nat := 4983230072969 + 3 ^ 40 * 4970108 * 2
def baseEnd_4970108 : Nat := 850684769585448554430965

theorem tailTrace_4970108 : CollatzResearch.WordTrace tailWord_4970108 prefixEnd_4970108 850684769585448554430965 := by
  unfold tailWord_4970108
  simp only [CollatzResearch.WordTrace]
  refine ⟨90637365539077508856475489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120849820718770011808633985 90637365539077508856475489)
  ·
    refine ⟨67978024154308131642356617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90637365539077508856475489 67978024154308131642356617)
    ·
      refine ⟨50983518115731098731767463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67978024154308131642356617 50983518115731098731767463)
      ·
        refine ⟨76475277173596648097651195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50983518115731098731767463 76475277173596648097651195)
        ·
          refine ⟨114712915760394972146476793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76475277173596648097651195 114712915760394972146476793)
          ·
            refine ⟨86034686820296229109857595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114712915760394972146476793 86034686820296229109857595)
            ·
              refine ⟨129052030230444343664786393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86034686820296229109857595 129052030230444343664786393)
              ·
                refine ⟨96789022672833257748589795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129052030230444343664786393 96789022672833257748589795)
                ·
                  refine ⟨145183534009249886622884693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96789022672833257748589795 145183534009249886622884693)
                  ·
                    refine ⟨850684769585448554430965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 145183534009249886622884693 850684769585448554430965)
                    ·
                      rfl

theorem cell23_4970108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_4970108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970108 prefixEnd_4970108 := by exact prefixLift 4970108
  have htrace : WordTrace (prefixWord ++ tailWord_4970108) baseStart_4970108 baseEnd_4970108 := by
    simpa [prefixWord, tailWord_4970108, baseEnd_4970108] using wordTrace_append hprefix tailTrace_4970108
  have hstable : (prefixWord ++ tailWord_4970108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970108).length < 2 ^ (prefixWord ++ tailWord_4970108).sum := by decide
  have hdescent : baseEnd_4970108 < baseStart_4970108 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970143 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 1, 2, 3]
def baseStart_4970143 : Nat := 118140960795 + 4970143 * 2 ^ 59
def prefixEnd_4970143 : Nat := 4983230072969 + 3 ^ 40 * 4970143 * 2
def baseEnd_4970143 : Nat := 2552072280579253026355235

theorem tailTrace_4970143 : CollatzResearch.WordTrace tailWord_4970143 prefixEnd_4970143 2552072280579253026355235 := by
  unfold tailWord_4970143
  simp only [CollatzResearch.WordTrace]
  refine ⟨181276007633028218690475083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120850671755352145793650055 181276007633028218690475083)
  ·
    refine ⟨271914011449542328035712625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181276007633028218690475083 271914011449542328035712625)
    ·
      refine ⟨203935508587156746026784469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271914011449542328035712625 203935508587156746026784469)
      ·
        refine ⟨4779738482511486235002761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 203935508587156746026784469 4779738482511486235002761)
        ·
          refine ⟨3584803861883614676252071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4779738482511486235002761 3584803861883614676252071)
          ·
            refine ⟨5377205792825422014378107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3584803861883614676252071 5377205792825422014378107)
            ·
              refine ⟨8065808689238133021567161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377205792825422014378107 8065808689238133021567161)
              ·
                refine ⟨6049356516928599766175371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8065808689238133021567161 6049356516928599766175371)
                ·
                  refine ⟨9074034775392899649263057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6049356516928599766175371 9074034775392899649263057)
                  ·
                    refine ⟨6805526081544674736947293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9074034775392899649263057 6805526081544674736947293)
                    ·
                      refine ⟨2552072280579253026355235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6805526081544674736947293 2552072280579253026355235)
                      ·
                        rfl

theorem cell23_4970143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_4970143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970143 prefixEnd_4970143 := by exact prefixLift 4970143
  have htrace : WordTrace (prefixWord ++ tailWord_4970143) baseStart_4970143 baseEnd_4970143 := by
    simpa [prefixWord, tailWord_4970143, baseEnd_4970143] using wordTrace_append hprefix tailTrace_4970143
  have hstable : (prefixWord ++ tailWord_4970143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970143).length < 2 ^ (prefixWord ++ tailWord_4970143).sum := by decide
  have hdescent : baseEnd_4970143 < baseStart_4970143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970149 : List Nat := [1, 3, 1, 2, 1, 2, 5, 2, 1, 3, 2]
def baseStart_4970149 : Nat := 118140960795 + 4970149 * 2 ^ 59
def prefixEnd_4970149 : Nat := 4983230072969 + 3 ^ 40 * 4970149 * 2
def baseEnd_4970149 : Nat := 2552075361463180002880207

theorem tailTrace_4970149 : CollatzResearch.WordTrace tailWord_4970149 prefixEnd_4970149 2552075361463180002880207 := by
  unfold tailWord_4970149
  simp only [CollatzResearch.WordTrace]
  refine ⟨181276226471006481715193501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120850817647337654476795667 181276226471006481715193501)
  ·
    refine ⟨67978584926627430643197563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181276226471006481715193501 67978584926627430643197563)
    ·
      refine ⟨101967877389941145964796345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67978584926627430643197563 101967877389941145964796345)
      ·
        refine ⟨76475908042455859473597259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101967877389941145964796345 76475908042455859473597259)
        ·
          refine ⟨114713862063683789210395889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76475908042455859473597259 114713862063683789210395889)
          ·
            refine ⟨86035396547762841907796917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114713862063683789210395889 86035396547762841907796917)
            ·
              refine ⟨8065818426352766428855961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86035396547762841907796917 8065818426352766428855961)
              ·
                refine ⟨6049363819764574821641971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8065818426352766428855961 6049363819764574821641971)
                ·
                  refine ⟨9074045729646862232462957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6049363819764574821641971 9074045729646862232462957)
                  ·
                    refine ⟨3402767148617573337173609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9074045729646862232462957 3402767148617573337173609)
                    ·
                      refine ⟨2552075361463180002880207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3402767148617573337173609 2552075361463180002880207)
                      ·
                        rfl

theorem cell23_4970149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 1, 3, 2].length) (baseStart_4970149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970149 prefixEnd_4970149 := by exact prefixLift 4970149
  have htrace : WordTrace (prefixWord ++ tailWord_4970149) baseStart_4970149 baseEnd_4970149 := by
    simpa [prefixWord, tailWord_4970149, baseEnd_4970149] using wordTrace_append hprefix tailTrace_4970149
  have hstable : (prefixWord ++ tailWord_4970149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970149).length < 2 ^ (prefixWord ++ tailWord_4970149).sum := by decide
  have hdescent : baseEnd_4970149 < baseStart_4970149 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970162 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2]
def baseStart_4970162 : Nat := 118140960795 + 4970162 * 2 ^ 59
def prefixEnd_4970162 : Nat := 4983230072969 + 3 ^ 40 * 4970162 * 2
def baseEnd_4970162 : Nat := 2552082036711688452017647

theorem tailTrace_4970162 : CollatzResearch.WordTrace tailWord_4970162 prefixEnd_4970162 2552082036711688452017647 := by
  unfold tailWord_4970162
  simp only [CollatzResearch.WordTrace]
  refine ⟨45319175154989846233854185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120851133746639589956944493 45319175154989846233854185)
  ·
    refine ⟨33989381366242384675390639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45319175154989846233854185 33989381366242384675390639)
    ·
      refine ⟨50984072049363577013085959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33989381366242384675390639 50984072049363577013085959)
      ·
        refine ⟨76476108074045365519628939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50984072049363577013085959 76476108074045365519628939)
        ·
          refine ⟨114714162111068048279443409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76476108074045365519628939 114714162111068048279443409)
          ·
            refine ⟨86035621583301036209582557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114714162111068048279443409 86035621583301036209582557)
            ·
              refine ⟨32263358093737888578593459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86035621583301036209582557 32263358093737888578593459)
              ·
                refine ⟨48395037140606832867890189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32263358093737888578593459 48395037140606832867890189)
                ·
                  refine ⟨18148138927727562325458821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48395037140606832867890189 18148138927727562325458821)
                  ·
                    refine ⟨3402776048948917936023529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18148138927727562325458821 3402776048948917936023529)
                    ·
                      refine ⟨2552082036711688452017647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3402776048948917936023529 2552082036711688452017647)
                      ·
                        rfl

theorem cell23_4970162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 3, 4, 2].length) (baseStart_4970162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970162 prefixEnd_4970162 := by exact prefixLift 4970162
  have htrace : WordTrace (prefixWord ++ tailWord_4970162) baseStart_4970162 baseEnd_4970162 := by
    simpa [prefixWord, tailWord_4970162, baseEnd_4970162] using wordTrace_append hprefix tailTrace_4970162
  have hstable : (prefixWord ++ tailWord_4970162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970162).length < 2 ^ (prefixWord ++ tailWord_4970162).sum := by decide
  have hdescent : baseEnd_4970162 < baseStart_4970162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970175 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 4]
def baseStart_4970175 : Nat := 118140960795 + 4970175 * 2 ^ 59
def prefixEnd_4970175 : Nat := 4983230072969 + 3 ^ 40 * 4970175 * 2
def baseEnd_4970175 : Nat := 2552088711960196901155087

theorem tailTrace_4970175 : CollatzResearch.WordTrace tailWord_4970175 prefixEnd_4970175 2552088711960196901155087 := by
  unfold tailWord_4970175
  simp only [CollatzResearch.WordTrace]
  refine ⟨181277174768912288155639979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120851449845941525437093319 181277174768912288155639979)
  ·
    refine ⟨271915762153368432233459969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181277174768912288155639979 271915762153368432233459969)
    ·
      refine ⟨203936821615026324175094977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271915762153368432233459969 203936821615026324175094977)
      ·
        refine ⟨152952616211269743131321233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203936821615026324175094977 152952616211269743131321233)
        ·
          refine ⟨114714462158452307348490925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152952616211269743131321233 114714462158452307348490925)
          ·
            refine ⟨43017923309419615255684097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 114714462158452307348490925 43017923309419615255684097)
            ·
              refine ⟨32263442482064711441763073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43017923309419615255684097 32263442482064711441763073)
              ·
                refine ⟨24197581861548533581322305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32263442482064711441763073 24197581861548533581322305)
                ·
                  refine ⟨18148186396161400185991729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24197581861548533581322305 18148186396161400185991729)
                  ·
                    refine ⟨13611139797121050139493797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18148186396161400185991729 13611139797121050139493797)
                    ·
                      refine ⟨2552088711960196901155087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13611139797121050139493797 2552088711960196901155087)
                      ·
                        rfl

theorem cell23_4970175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 4].length) (baseStart_4970175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970175 prefixEnd_4970175 := by exact prefixLift 4970175
  have htrace : WordTrace (prefixWord ++ tailWord_4970175) baseStart_4970175 baseEnd_4970175 := by
    simpa [prefixWord, tailWord_4970175, baseEnd_4970175] using wordTrace_append hprefix tailTrace_4970175
  have hstable : (prefixWord ++ tailWord_4970175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970175).length < 2 ^ (prefixWord ++ tailWord_4970175).sum := by decide
  have hdescent : baseEnd_4970175 < baseStart_4970175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970189 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 2, 6]
def baseStart_4970189 : Nat := 118140960795 + 4970189 * 2 ^ 59
def prefixEnd_4970189 : Nat := 4983230072969 + 3 ^ 40 * 4970189 * 2
def baseEnd_4970189 : Nat := 850698633563119948793341

theorem tailTrace_4970189 : CollatzResearch.WordTrace tailWord_4970189 prefixEnd_4970189 850698633563119948793341 := by
  unfold tailWord_4970189
  simp only [CollatzResearch.WordTrace]
  refine ⟨181277685390861568546649621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120851790260574379031099747 181277685390861568546649621)
  ·
    refine ⟨8497391502696636025624201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181277685390861568546649621 8497391502696636025624201)
    ·
      refine ⟨6373043627022477019218151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8497391502696636025624201 6373043627022477019218151)
      ·
        refine ⟨9559565440533715528827227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373043627022477019218151 9559565440533715528827227)
        ·
          refine ⟨14339348160800573293240841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9559565440533715528827227 14339348160800573293240841)
          ·
            refine ⟨10754511120600429969930631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14339348160800573293240841 10754511120600429969930631)
            ·
              refine ⟨16131766680900644954895947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754511120600429969930631 16131766680900644954895947)
              ·
                refine ⟨24197650021350967432343921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16131766680900644954895947 24197650021350967432343921)
                ·
                  refine ⟨18148237516013225574257941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24197650021350967432343921 18148237516013225574257941)
                  ·
                    refine ⟨850698633563119948793341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18148237516013225574257941 850698633563119948793341)
                    ·
                      rfl

theorem cell23_4970189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 2, 6].length) (baseStart_4970189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970189 prefixEnd_4970189 := by exact prefixLift 4970189
  have htrace : WordTrace (prefixWord ++ tailWord_4970189) baseStart_4970189 baseEnd_4970189 := by
    simpa [prefixWord, tailWord_4970189, baseEnd_4970189] using wordTrace_append hprefix tailTrace_4970189
  have hstable : (prefixWord ++ tailWord_4970189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970189).length < 2 ^ (prefixWord ++ tailWord_4970189).sum := by decide
  have hdescent : baseEnd_4970189 < baseStart_4970189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970196 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_4970196 : Nat := 118140960795 + 4970196 * 2 ^ 59
def prefixEnd_4970196 : Nat := 4983230072969 + 3 ^ 40 * 4970196 * 2
def baseEnd_4970196 : Nat := 2552099495053941318992491

theorem tailTrace_4970196 : CollatzResearch.WordTrace tailWord_4970196 prefixEnd_4970196 2552099495053941318992491 := by
  unfold tailWord_4970196
  simp only [CollatzResearch.WordTrace]
  refine ⟨90638970350918104371077221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120851960467890805828102961 90638970350918104371077221)
  ·
    refine ⟨16994806940797144569576979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 90638970350918104371077221 16994806940797144569576979)
    ·
      refine ⟨25492210411195716854365469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16994806940797144569576979 25492210411195716854365469)
      ·
        refine ⟨9559578904198393820387051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25492210411195716854365469 9559578904198393820387051)
        ·
          refine ⟨14339368356297590730580577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9559578904198393820387051 14339368356297590730580577)
          ·
            refine ⟨10754526267223193047935433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14339368356297590730580577 10754526267223193047935433)
            ·
              refine ⟨8065894700417394785951575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10754526267223193047935433 8065894700417394785951575)
              ·
                refine ⟨12098842050626092178927363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8065894700417394785951575 12098842050626092178927363)
                ·
                  refine ⟨18148263075939138268391045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12098842050626092178927363 18148263075939138268391045)
                  ·
                    refine ⟨3402799326738588425323321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18148263075939138268391045 3402799326738588425323321)
                    ·
                      refine ⟨2552099495053941318992491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3402799326738588425323321 2552099495053941318992491)
                      ·
                        rfl

theorem cell23_4970196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_4970196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970196 prefixEnd_4970196 := by exact prefixLift 4970196
  have htrace : WordTrace (prefixWord ++ tailWord_4970196) baseStart_4970196 baseEnd_4970196 := by
    simpa [prefixWord, tailWord_4970196, baseEnd_4970196] using wordTrace_append hprefix tailTrace_4970196
  have hstable : (prefixWord ++ tailWord_4970196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970196).length < 2 ^ (prefixWord ++ tailWord_4970196).sum := by decide
  have hdescent : baseEnd_4970196 < baseStart_4970196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970242 : List Nat := [3, 4, 1, 1, 1, 1, 2, 1, 1, 1, 7]
def baseStart_4970242 : Nat := 118140960795 + 4970242 * 2 ^ 59
def prefixEnd_4970242 : Nat := 4983230072969 + 3 ^ 40 * 4970242 * 2
def baseEnd_4970242 : Nat := 2552123115164048139017279

theorem tailTrace_4970242 : CollatzResearch.WordTrace tailWord_4970242 prefixEnd_4970242 2552123115164048139017279 := by
  unfold tailWord_4970242
  simp only [CollatzResearch.WordTrace]
  refine ⟨45319904614917389649582245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120853078973113039065552653 45319904614917389649582245)
  ·
    refine ⟨8497482115297010559296671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45319904614917389649582245 8497482115297010559296671)
    ·
      refine ⟨12746223172945515838945007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8497482115297010559296671 12746223172945515838945007)
      ·
        refine ⟨19119334759418273758417511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12746223172945515838945007 19119334759418273758417511)
        ·
          refine ⟨28679002139127410637626267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19119334759418273758417511 28679002139127410637626267)
          ·
            refine ⟨43018503208691115956439401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28679002139127410637626267 43018503208691115956439401)
            ·
              refine ⟨32263877406518336967329551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43018503208691115956439401 32263877406518336967329551)
              ·
                refine ⟨48395816109777505450994327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32263877406518336967329551 48395816109777505450994327)
                ·
                  refine ⟨72593724164666258176491491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48395816109777505450994327 72593724164666258176491491)
                  ·
                    refine ⟨108890586246999387264737237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72593724164666258176491491 108890586246999387264737237)
                    ·
                      refine ⟨2552123115164048139017279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108890586246999387264737237 2552123115164048139017279)
                      ·
                        rfl

theorem cell23_4970242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 1, 1, 7].length) (baseStart_4970242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970242 prefixEnd_4970242 := by exact prefixLift 4970242
  have htrace : WordTrace (prefixWord ++ tailWord_4970242) baseStart_4970242 baseEnd_4970242 := by
    simpa [prefixWord, tailWord_4970242, baseEnd_4970242] using wordTrace_append hprefix tailTrace_4970242
  have hstable : (prefixWord ++ tailWord_4970242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970242).length < 2 ^ (prefixWord ++ tailWord_4970242).sum := by decide
  have hdescent : baseEnd_4970242 < baseStart_4970242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970270 : List Nat := [4, 3, 2, 2, 1, 2, 1, 3, 5]
def baseStart_4970270 : Nat := 118140960795 + 4970270 * 2 ^ 59
def prefixEnd_4970270 : Nat := 4983230072969 + 3 ^ 40 * 4970270 * 2
def baseEnd_4970270 : Nat := 283570832513597114385239

theorem tailTrace_4970270 : CollatzResearch.WordTrace tailWord_4970270 prefixEnd_4970270 283570832513597114385239 := by
  unfold tailWord_4970270
  simp only [CollatzResearch.WordTrace]
  refine ⟨22660079962946014922543533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120853759802378746253565509 22660079962946014922543533)
  ·
    refine ⟨8497529986104755595953825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22660079962946014922543533 8497529986104755595953825)
    ·
      refine ⟨6373147489578566696965369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8497529986104755595953825 6373147489578566696965369)
      ·
        refine ⟨4779860617183925022724027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6373147489578566696965369 4779860617183925022724027)
        ·
          refine ⟨7169790925775887534086041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4779860617183925022724027 7169790925775887534086041)
          ·
            refine ⟨5377343194331915650564531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7169790925775887534086041 5377343194331915650564531)
            ·
              refine ⟨8066014791497873475846797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377343194331915650564531 8066014791497873475846797)
              ·
                refine ⟨3024755546811702553442549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8066014791497873475846797 3024755546811702553442549)
                ·
                  refine ⟨283570832513597114385239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3024755546811702553442549 283570832513597114385239)
                  ·
                    rfl

theorem cell23_4970270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_4970270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970270 prefixEnd_4970270 := by exact prefixLift 4970270
  have htrace : WordTrace (prefixWord ++ tailWord_4970270) baseStart_4970270 baseEnd_4970270 := by
    simpa [prefixWord, tailWord_4970270, baseEnd_4970270] using wordTrace_append hprefix tailTrace_4970270
  have hstable : (prefixWord ++ tailWord_4970270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970270).length < 2 ^ (prefixWord ++ tailWord_4970270).sum := by decide
  have hdescent : baseEnd_4970270 < baseStart_4970270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970272 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3]
def baseStart_4970272 : Nat := 118140960795 + 4970272 * 2 ^ 59
def prefixEnd_4970272 : Nat := 4983230072969 + 3 ^ 40 * 4970272 * 2
def baseEnd_4970272 : Nat := 2552138519583683021642141

theorem tailTrace_4970272 : CollatzResearch.WordTrace tailWord_4970272 prefixEnd_4970272 2552138519583683021642141 := by
  unfold tailWord_4970272
  simp only [CollatzResearch.WordTrace]
  refine ⟨90640356324780436860960535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120853808433040582481280713 90640356324780436860960535)
  ·
    refine ⟨135960534487170655291440803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90640356324780436860960535 135960534487170655291440803)
    ·
      refine ⟨203940801730755982937161205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135960534487170655291440803 203940801730755982937161205)
      ·
        refine ⟨19119450162258373400358863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203940801730755982937161205 19119450162258373400358863)
        ·
          refine ⟨28679175243387560100538295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19119450162258373400358863 28679175243387560100538295)
          ·
            refine ⟨43018762865081340150807443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28679175243387560100538295 43018762865081340150807443)
            ·
              refine ⟨64528144297622010226211165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43018762865081340150807443 64528144297622010226211165)
              ·
                refine ⟨24198054111608253834829187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64528144297622010226211165 24198054111608253834829187)
                ·
                  refine ⟨36297081167412380752243781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24198054111608253834829187 36297081167412380752243781)
                  ·
                    refine ⟨6805702718889821391045709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36297081167412380752243781 6805702718889821391045709)
                    ·
                      refine ⟨2552138519583683021642141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6805702718889821391045709 2552138519583683021642141)
                      ·
                        rfl

theorem cell23_4970272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 4, 3].length) (baseStart_4970272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970272 prefixEnd_4970272 := by exact prefixLift 4970272
  have htrace : WordTrace (prefixWord ++ tailWord_4970272) baseStart_4970272 baseEnd_4970272 := by
    simpa [prefixWord, tailWord_4970272, baseEnd_4970272] using wordTrace_append hprefix tailTrace_4970272
  have hstable : (prefixWord ++ tailWord_4970272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970272).length < 2 ^ (prefixWord ++ tailWord_4970272).sum := by decide
  have hdescent : baseEnd_4970272 < baseStart_4970272 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970275 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 8]
def baseStart_4970275 : Nat := 118140960795 + 4970275 * 2 ^ 59
def prefixEnd_4970275 : Nat := 4983230072969 + 3 ^ 40 * 4970275 * 2
def baseEnd_4970275 : Nat := 283571117780627389989403

theorem tailTrace_4970275 : CollatzResearch.WordTrace tailWord_4970275 prefixEnd_4970275 283571117780627389989403 := by
  unfold tailWord_4970275
  simp only [CollatzResearch.WordTrace]
  refine ⟨181280822068550005234280279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120853881379033336822853519 181280822068550005234280279)
  ·
    refine ⟨271921233102825007851420419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181280822068550005234280279 271921233102825007851420419)
    ·
      refine ⟨407881849654237511777130629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271921233102825007851420419 407881849654237511777130629)
      ·
        refine ⟨76477846810169533458211993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407881849654237511777130629 76477846810169533458211993)
        ·
          refine ⟨57358385107627150093658995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76477846810169533458211993 57358385107627150093658995)
          ·
            refine ⟨86037577661440725140488493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57358385107627150093658995 86037577661440725140488493)
            ·
              refine ⟨32264091623040271927683185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86037577661440725140488493 32264091623040271927683185)
              ·
                refine ⟨24198068717280203945762389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32264091623040271927683185 24198068717280203945762389)
                ·
                  refine ⟨283571117780627389989403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24198068717280203945762389 283571117780627389989403)
                  ·
                    rfl

theorem cell23_4970275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 8].length) (baseStart_4970275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970275 prefixEnd_4970275 := by exact prefixLift 4970275
  have htrace : WordTrace (prefixWord ++ tailWord_4970275) baseStart_4970275 baseEnd_4970275 := by
    simpa [prefixWord, tailWord_4970275, baseEnd_4970275] using wordTrace_append hprefix tailTrace_4970275
  have hstable : (prefixWord ++ tailWord_4970275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970275).length < 2 ^ (prefixWord ++ tailWord_4970275).sum := by decide
  have hdescent : baseEnd_4970275 < baseStart_4970275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970286 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4]
def baseStart_4970286 : Nat := 118140960795 + 4970286 * 2 ^ 59
def prefixEnd_4970286 : Nat := 4983230072969 + 3 ^ 40 * 4970286 * 2
def baseEnd_4970286 : Nat := 2552145708312845966867077

theorem tailTrace_4970286 : CollatzResearch.WordTrace tailWord_4970286 prefixEnd_4970286 2552145708312845966867077 := by
  unfold tailWord_4970286
  simp only [CollatzResearch.WordTrace]
  refine ⟨22660152908938769264116339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120854148847673436075287141 22660152908938769264116339)
  ·
    refine ⟨33990229363408153896174509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22660152908938769264116339 33990229363408153896174509)
    ·
      refine ⟨12746336011278057711065441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33990229363408153896174509 12746336011278057711065441)
      ·
        refine ⟨9559752008458543283299081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12746336011278057711065441 9559752008458543283299081)
        ·
          refine ⟨7169814006343907462474311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9559752008458543283299081 7169814006343907462474311)
          ·
            refine ⟨10754721009515861193711467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7169814006343907462474311 10754721009515861193711467)
            ·
              refine ⟨16132081514273791790567201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754721009515861193711467 16132081514273791790567201)
              ·
                refine ⟨12099061135705343842925401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16132081514273791790567201 12099061135705343842925401)
                ·
                  refine ⟨9074295851779007882194051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12099061135705343842925401 9074295851779007882194051)
                  ·
                    refine ⟨13611443777668511823291077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9074295851779007882194051 13611443777668511823291077)
                    ·
                      refine ⟨2552145708312845966867077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13611443777668511823291077 2552145708312845966867077)
                      ·
                        rfl

theorem cell23_4970286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_4970286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970286 prefixEnd_4970286 := by exact prefixLift 4970286
  have htrace : WordTrace (prefixWord ++ tailWord_4970286) baseStart_4970286 baseEnd_4970286 := by
    simpa [prefixWord, tailWord_4970286, baseEnd_4970286] using wordTrace_append hprefix tailTrace_4970286
  have hstable : (prefixWord ++ tailWord_4970286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970286).length < 2 ^ (prefixWord ++ tailWord_4970286).sum := by decide
  have hdescent : baseEnd_4970286 < baseStart_4970286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970289 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 3]
def baseStart_4970289 : Nat := 118140960795 + 4970289 * 2 ^ 59
def prefixEnd_4970289 : Nat := 4983230072969 + 3 ^ 40 * 4970289 * 2
def baseEnd_4970289 : Nat := 2552147248754809455129563

theorem tailTrace_4970289 : CollatzResearch.WordTrace tailWord_4970289 prefixEnd_4970289 2552147248754809455129563 := by
  unfold tailWord_4970289
  simp only [CollatzResearch.WordTrace]
  refine ⟨181281332690499285625289921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120854221793666190416859947 181281332690499285625289921)
  ·
    refine ⟨135960999517874464218967441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181281332690499285625289921 135960999517874464218967441)
    ·
      refine ⟨101970749638405848164225581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135960999517874464218967441 101970749638405848164225581)
      ·
        refine ⟨38239031114402193061584593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101970749638405848164225581 38239031114402193061584593)
        ·
          refine ⟨28679273335801644796188445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38239031114402193061584593 28679273335801644796188445)
          ·
            refine ⟨10754727500925616798570667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28679273335801644796188445 10754727500925616798570667)
            ·
              refine ⟨16132091251388425197856001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754727500925616798570667 16132091251388425197856001)
              ·
                refine ⟨12099068438541318898392001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16132091251388425197856001 12099068438541318898392001)
                ·
                  refine ⟨9074301328905989173794001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12099068438541318898392001 9074301328905989173794001)
                  ·
                    refine ⟨6805725996679491880345501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9074301328905989173794001 6805725996679491880345501)
                    ·
                      refine ⟨2552147248754809455129563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6805725996679491880345501 2552147248754809455129563)
                      ·
                        rfl

theorem cell23_4970289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 2, 3].length) (baseStart_4970289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970289 prefixEnd_4970289 := by exact prefixLift 4970289
  have htrace : WordTrace (prefixWord ++ tailWord_4970289) baseStart_4970289 baseEnd_4970289 := by
    simpa [prefixWord, tailWord_4970289, baseEnd_4970289] using wordTrace_append hprefix tailTrace_4970289
  have hstable : (prefixWord ++ tailWord_4970289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970289).length < 2 ^ (prefixWord ++ tailWord_4970289).sum := by decide
  have hdescent : baseEnd_4970289 < baseStart_4970289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970295 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_4970295 : Nat := 118140960795 + 4970295 * 2 ^ 59
def prefixEnd_4970295 : Nat := 4983230072969 + 3 ^ 40 * 4970295 * 2
def baseEnd_4970295 : Nat := 2552150329638736431654535

theorem tailTrace_4970295 : CollatzResearch.WordTrace tailWord_4970295 prefixEnd_4970295 2552150329638736431654535 := by
  unfold tailWord_4970295
  simp only [CollatzResearch.WordTrace]
  refine ⟨181281551528477548650008339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120854367685651699100005559 181281551528477548650008339)
  ·
    refine ⟨271922327292716322975012509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181281551528477548650008339 271922327292716322975012509)
    ·
      refine ⟨101970872734768621115629691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271922327292716322975012509 101970872734768621115629691)
      ·
        refine ⟨152956309102152931673444537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101970872734768621115629691 152956309102152931673444537)
        ·
          refine ⟨114717231826614698755083403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152956309102152931673444537 114717231826614698755083403)
          ·
            refine ⟨172075847739922048132625105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114717231826614698755083403 172075847739922048132625105)
            ·
              refine ⟨129056885804941536099468829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172075847739922048132625105 129056885804941536099468829)
              ·
                refine ⟨48396332176853076037300811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129056885804941536099468829 48396332176853076037300811)
                ·
                  refine ⟨72594498265279614055951217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48396332176853076037300811 72594498265279614055951217)
                  ·
                    refine ⟨54445873698959710541963413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72594498265279614055951217 54445873698959710541963413)
                    ·
                      refine ⟨2552150329638736431654535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54445873698959710541963413 2552150329638736431654535)
                      ·
                        rfl

theorem cell23_4970295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_4970295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970295 prefixEnd_4970295 := by exact prefixLift 4970295
  have htrace : WordTrace (prefixWord ++ tailWord_4970295) baseStart_4970295 baseEnd_4970295 := by
    simpa [prefixWord, tailWord_4970295, baseEnd_4970295] using wordTrace_append hprefix tailTrace_4970295
  have hstable : (prefixWord ++ tailWord_4970295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970295).length < 2 ^ (prefixWord ++ tailWord_4970295).sum := by decide
  have hdescent : baseEnd_4970295 < baseStart_4970295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970362 : List Nat := [3, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5]
def baseStart_4970362 : Nat := 118140960795 + 4970362 * 2 ^ 59
def prefixEnd_4970362 : Nat := 4983230072969 + 3 ^ 40 * 4970362 * 2
def baseEnd_4970362 : Nat := 2552184732842587669516727

theorem tailTrace_4970362 : CollatzResearch.WordTrace tailWord_4970362 prefixEnd_4970362 2552184732842587669516727 := by
  unfold tailWord_4970362
  simp only [CollatzResearch.WordTrace]
  refine ⟨45320998804808704773174335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120855996812823212728464893 45320998804808704773174335)
  ·
    refine ⟨67981498207213057159761503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45320998804808704773174335 67981498207213057159761503)
    ·
      refine ⟨101972247310819585739642255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67981498207213057159761503 101972247310819585739642255)
      ·
        refine ⟨152958370966229378609463383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101972247310819585739642255 152958370966229378609463383)
        ·
          refine ⟨229437556449344067914195075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152958370966229378609463383 229437556449344067914195075)
          ·
            refine ⟨344156334674016101871292613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229437556449344067914195075 344156334674016101871292613)
            ·
              refine ⟨64529312751378019100867365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344156334674016101871292613 64529312751378019100867365)
              ·
                refine ⟨12099246140883378581412631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64529312751378019100867365 12099246140883378581412631)
                ·
                  refine ⟨18148869211325067872118947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12099246140883378581412631 18148869211325067872118947)
                  ·
                    refine ⟨27223303816987601808178421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18148869211325067872118947 27223303816987601808178421)
                    ·
                      refine ⟨2552184732842587669516727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27223303816987601808178421 2552184732842587669516727)
                      ·
                        rfl

theorem cell23_4970362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 4, 1, 1, 5].length) (baseStart_4970362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970362 prefixEnd_4970362 := by exact prefixLift 4970362
  have htrace : WordTrace (prefixWord ++ tailWord_4970362) baseStart_4970362 baseEnd_4970362 := by
    simpa [prefixWord, tailWord_4970362, baseEnd_4970362] using wordTrace_append hprefix tailTrace_4970362
  have hstable : (prefixWord ++ tailWord_4970362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970362).length < 2 ^ (prefixWord ++ tailWord_4970362).sum := by decide
  have hdescent : baseEnd_4970362 < baseStart_4970362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970372 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_4970372 : Nat := 118140960795 + 4970372 * 2 ^ 59
def prefixEnd_4970372 : Nat := 4983230072969 + 3 ^ 40 * 4970372 * 2
def baseEnd_4970372 : Nat := 2552189867649132630391681

theorem tailTrace_4970372 : CollatzResearch.WordTrace tailWord_4970372 prefixEnd_4970372 2552189867649132630391681 := by
  unfold tailWord_4970372
  simp only [CollatzResearch.WordTrace]
  refine ⟨90642179974599295400280685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120856239966132393867040913 90642179974599295400280685)
  ·
    refine ⟨33990817490474735775105257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90642179974599295400280685 33990817490474735775105257)
    ·
      refine ⟨25493113117856051831328943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33990817490474735775105257 25493113117856051831328943)
      ·
        refine ⟨38239669676784077746993415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25493113117856051831328943 38239669676784077746993415)
        ·
          refine ⟨57359504515176116620490123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38239669676784077746993415 57359504515176116620490123)
          ·
            refine ⟨86039256772764174930735185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57359504515176116620490123 86039256772764174930735185)
            ·
              refine ⟨64529442579573131198051389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86039256772764174930735185 64529442579573131198051389)
              ·
                refine ⟨24198540967339924199269271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 64529442579573131198051389 24198540967339924199269271)
                ·
                  refine ⟨36297811451009886298903907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24198540967339924199269271 36297811451009886298903907)
                  ·
                    refine ⟨54446717176514829448355861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36297811451009886298903907 54446717176514829448355861)
                    ·
                      refine ⟨2552189867649132630391681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54446717176514829448355861 2552189867649132630391681)
                      ·
                        rfl

theorem cell23_4970372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_4970372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970372 prefixEnd_4970372 := by exact prefixLift 4970372
  have htrace : WordTrace (prefixWord ++ tailWord_4970372) baseStart_4970372 baseEnd_4970372 := by
    simpa [prefixWord, tailWord_4970372, baseEnd_4970372] using wordTrace_append hprefix tailTrace_4970372
  have hstable : (prefixWord ++ tailWord_4970372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970372).length < 2 ^ (prefixWord ++ tailWord_4970372).sum := by decide
  have hdescent : baseEnd_4970372 < baseStart_4970372 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970379 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 3]
def baseStart_4970379 : Nat := 118140960795 + 4970379 * 2 ^ 59
def prefixEnd_4970379 : Nat := 4983230072969 + 3 ^ 40 * 4970379 * 2
def baseEnd_4970379 : Nat := 2552193462013714103004149

theorem tailTrace_4970379 : CollatzResearch.WordTrace tailWord_4970379 prefixEnd_4970379 2552193462013714103004149 := by
  unfold tailWord_4970379
  simp only [CollatzResearch.WordTrace]
  refine ⟨181284615260173230996066191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120856410173448820664044127 181284615260173230996066191)
  ·
    refine ⟨271926922890259846494099287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181284615260173230996066191 271926922890259846494099287)
    ·
      refine ⟨407890384335389769741148931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271926922890259846494099287 407890384335389769741148931)
      ·
        refine ⟨611835576503084654611723397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407890384335389769741148931 611835576503084654611723397)
        ·
          refine ⟨114719170594328372739698137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 611835576503084654611723397 114719170594328372739698137)
          ·
            refine ⟨86039377945746279554773603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114719170594328372739698137 86039377945746279554773603)
            ·
              refine ⟨129059066918619419332160405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86039377945746279554773603 129059066918619419332160405)
              ·
                refine ⟨6049643761810285281195019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129059066918619419332160405 6049643761810285281195019)
                ·
                  refine ⟨9074465642715427921792529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6049643761810285281195019 9074465642715427921792529)
                  ·
                    refine ⟨6805849232036570941344397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9074465642715427921792529 6805849232036570941344397)
                    ·
                      refine ⟨2552193462013714103004149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6805849232036570941344397 2552193462013714103004149)
                      ·
                        rfl

theorem cell23_4970379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 2, 3].length) (baseStart_4970379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970379 prefixEnd_4970379 := by exact prefixLift 4970379
  have htrace : WordTrace (prefixWord ++ tailWord_4970379) baseStart_4970379 baseEnd_4970379 := by
    simpa [prefixWord, tailWord_4970379, baseEnd_4970379] using wordTrace_append hprefix tailTrace_4970379
  have hstable : (prefixWord ++ tailWord_4970379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970379).length < 2 ^ (prefixWord ++ tailWord_4970379).sum := by decide
  have hdescent : baseEnd_4970379 < baseStart_4970379 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970390 : List Nat := [5, 3, 1, 1, 2, 1, 1, 3, 1, 5]
def baseStart_4970390 : Nat := 118140960795 + 4970390 * 2 ^ 59
def prefixEnd_4970390 : Nat := 4983230072969 + 3 ^ 40 * 4970390 * 2
def baseEnd_4970390 : Nat := 850733036766971186655533

theorem tailTrace_4970390 : CollatzResearch.WordTrace tailWord_4970390 prefixEnd_4970390 850733036766971186655533 := by
  unfold tailWord_4970390
  simp only [CollatzResearch.WordTrace]
  refine ⟨11330313528945836242169789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120856677642088919916477749 11330313528945836242169789)
  ·
    refine ⟨4248867573354688590813671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11330313528945836242169789 4248867573354688590813671)
    ·
      refine ⟨6373301360032032886220507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4248867573354688590813671 6373301360032032886220507)
      ·
        refine ⟨9559952040048049329330761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373301360032032886220507 9559952040048049329330761)
        ·
          refine ⟨7169964030036036996998071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9559952040048049329330761 7169964030036036996998071)
          ·
            refine ⟨10754946045054055495497107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7169964030036036996998071 10754946045054055495497107)
            ·
              refine ⟨16132419067581083243245661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10754946045054055495497107 16132419067581083243245661)
              ·
                refine ⟨6049657150342906216217123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16132419067581083243245661 6049657150342906216217123)
                ·
                  refine ⟨9074485725514359324325685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6049657150342906216217123 9074485725514359324325685)
                  ·
                    refine ⟨850733036766971186655533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9074485725514359324325685 850733036766971186655533)
                    ·
                      rfl

theorem cell23_4970390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_4970390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970390 prefixEnd_4970390 := by exact prefixLift 4970390
  have htrace : WordTrace (prefixWord ++ tailWord_4970390) baseStart_4970390 baseEnd_4970390 := by
    simpa [prefixWord, tailWord_4970390, baseEnd_4970390] using wordTrace_append hprefix tailTrace_4970390
  have hstable : (prefixWord ++ tailWord_4970390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970390).length < 2 ^ (prefixWord ++ tailWord_4970390).sum := by decide
  have hdescent : baseEnd_4970390 < baseStart_4970390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970393 : List Nat := [1, 2, 1, 2, 1, 3, 3, 5, 1, 2, 2]
def baseStart_4970393 : Nat := 118140960795 + 4970393 * 2 ^ 59
def prefixEnd_4970393 : Nat := 4983230072969 + 3 ^ 40 * 4970393 * 2
def baseEnd_4970393 : Nat := 2552200650742877048229085

theorem tailTrace_4970393 : CollatzResearch.WordTrace tailWord_4970393 prefixEnd_4970393 2552200650742877048229085 := by
  unfold tailWord_4970393
  simp only [CollatzResearch.WordTrace]
  refine ⟨181285125882122511387075833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120856750588081674258050555 181285125882122511387075833)
  ·
    refine ⟨135963844411591883540306875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181285125882122511387075833 135963844411591883540306875)
    ·
      refine ⟨203945766617387825310460313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135963844411591883540306875 203945766617387825310460313)
      ·
        refine ⟨152959324963040868982845235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203945766617387825310460313 152959324963040868982845235)
        ·
          refine ⟨229438987444561303474267853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152959324963040868982845235 229438987444561303474267853)
          ·
            refine ⟨86039620291710488802850445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 229438987444561303474267853 86039620291710488802850445)
            ·
              refine ⟨32264857609391433301068917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86039620291710488802850445 32264857609391433301068917)
              ·
                refine ⟨3024830400880446871975211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32264857609391433301068917 3024830400880446871975211)
                ·
                  refine ⟨4537245601320670307962817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3024830400880446871975211 4537245601320670307962817)
                  ·
                    refine ⟨3402934200990502730972113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4537245601320670307962817 3402934200990502730972113)
                    ·
                      refine ⟨2552200650742877048229085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3402934200990502730972113 2552200650742877048229085)
                      ·
                        rfl

theorem cell23_4970393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 5, 1, 2, 2].length) (baseStart_4970393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970393 prefixEnd_4970393 := by exact prefixLift 4970393
  have htrace : WordTrace (prefixWord ++ tailWord_4970393) baseStart_4970393 baseEnd_4970393 := by
    simpa [prefixWord, tailWord_4970393, baseEnd_4970393] using wordTrace_append hprefix tailTrace_4970393
  have hstable : (prefixWord ++ tailWord_4970393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970393).length < 2 ^ (prefixWord ++ tailWord_4970393).sum := by decide
  have hdescent : baseEnd_4970393 < baseStart_4970393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970420 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_4970420 : Nat := 118140960795 + 4970420 * 2 ^ 59
def prefixEnd_4970420 : Nat := 4983230072969 + 3 ^ 40 * 4970420 * 2
def baseEnd_4970420 : Nat := 850738171573516147530487

theorem tailTrace_4970420 : CollatzResearch.WordTrace tailWord_4970420 prefixEnd_4970420 850738171573516147530487 := by
  unfold tailWord_4970420
  simp only [CollatzResearch.WordTrace]
  refine ⟨90643055326512347499154357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120857407102016463332205809 90643055326512347499154357)
  ·
    refine ⟨8497786436860532578045721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 90643055326512347499154357 8497786436860532578045721)
    ·
      refine ⟨6373339827645399433534291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8497786436860532578045721 6373339827645399433534291)
      ·
        refine ⟨9560009741468099150301437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373339827645399433534291 9560009741468099150301437)
        ·
          refine ⟨3585003653050537181363039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9560009741468099150301437 3585003653050537181363039)
          ·
            refine ⟨5377505479575805772044559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3585003653050537181363039 5377505479575805772044559)
            ·
              refine ⟨8066258219363708658066839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377505479575805772044559 8066258219363708658066839)
              ·
                refine ⟨12099387329045562987100259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8066258219363708658066839 12099387329045562987100259)
                ·
                  refine ⟨18149080993568344480650389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12099387329045562987100259 18149080993568344480650389)
                  ·
                    refine ⟨850738171573516147530487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18149080993568344480650389 850738171573516147530487)
                    ·
                      rfl

theorem cell23_4970420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_4970420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970420 prefixEnd_4970420 := by exact prefixLift 4970420
  have htrace : WordTrace (prefixWord ++ tailWord_4970420) baseStart_4970420 baseEnd_4970420 := by
    simpa [prefixWord, tailWord_4970420, baseEnd_4970420] using wordTrace_append hprefix tailTrace_4970420
  have hstable : (prefixWord ++ tailWord_4970420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970420).length < 2 ^ (prefixWord ++ tailWord_4970420).sum := by decide
  have hdescent : baseEnd_4970420 < baseStart_4970420 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970442 : List Nat := [3, 1, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_4970442 : Nat := 118140960795 + 4970442 * 2 ^ 59
def prefixEnd_4970442 : Nat := 4983230072969 + 3 ^ 40 * 4970442 * 2
def baseEnd_4970442 : Nat := 850741937098315785505453

theorem tailTrace_4970442 : CollatzResearch.WordTrace tailWord_4970442 prefixEnd_4970442 850741937098315785505453 := by
  unfold tailWord_4970442
  simp only [CollatzResearch.WordTrace]
  refine ⟨45321728264736248188902395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120857942039296661837073053 45321728264736248188902395)
  ·
    refine ⟨67982592397104372283353593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45321728264736248188902395 67982592397104372283353593)
    ·
      refine ⟨50986944297828279212515195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67982592397104372283353593 50986944297828279212515195)
      ·
        refine ⟨76480416446742418818772793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50986944297828279212515195 76480416446742418818772793)
        ·
          refine ⟨57360312335056814114079595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76480416446742418818772793 57360312335056814114079595)
          ·
            refine ⟨86040468502585221171119393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57360312335056814114079595 86040468502585221171119393)
            ·
              refine ⟨64530351376938915878339545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86040468502585221171119393 64530351376938915878339545)
              ·
                refine ⟨48397763532704186908754659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64530351376938915878339545 48397763532704186908754659)
                ·
                  refine ⟨72596645299056280363131989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48397763532704186908754659 72596645299056280363131989)
                  ·
                    refine ⟨850741937098315785505453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72596645299056280363131989 850741937098315785505453)
                    ·
                      rfl

theorem cell23_4970442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_4970442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970442 prefixEnd_4970442 := by exact prefixLift 4970442
  have htrace : WordTrace (prefixWord ++ tailWord_4970442) baseStart_4970442 baseEnd_4970442 := by
    simpa [prefixWord, tailWord_4970442, baseEnd_4970442] using wordTrace_append hprefix tailTrace_4970442
  have hstable : (prefixWord ++ tailWord_4970442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970442).length < 2 ^ (prefixWord ++ tailWord_4970442).sum := by decide
  have hdescent : baseEnd_4970442 < baseStart_4970442 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970453 : List Nat := [1, 3, 2, 3, 2, 1, 2, 3, 1, 3, 2]
def baseStart_4970453 : Nat := 118140960795 + 4970453 * 2 ^ 59
def prefixEnd_4970453 : Nat := 4983230072969 + 3 ^ 40 * 4970453 * 2
def baseEnd_4970453 : Nat := 2552231459582146813478809

theorem tailTrace_4970453 : CollatzResearch.WordTrace tailWord_4970453 prefixEnd_4970453 2552231459582146813478809 := by
  unfold tailWord_4970453
  simp only [CollatzResearch.WordTrace]
  refine ⟨181287314261905141634260013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120858209507936761089506675 181287314261905141634260013)
  ·
    refine ⟨67982742848214428112847505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181287314261905141634260013 67982742848214428112847505)
    ·
      refine ⟨50987057136160821084635629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67982742848214428112847505 50987057136160821084635629)
      ·
        refine ⟨19120146426060307906738361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50987057136160821084635629 19120146426060307906738361)
        ·
          refine ⟨14340109819545230930053771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19120146426060307906738361 14340109819545230930053771)
          ·
            refine ⟨21510164729317846395080657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14340109819545230930053771 21510164729317846395080657)
            ·
              refine ⟨16132623546988384796310493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21510164729317846395080657 16132623546988384796310493)
              ·
                refine ⟨6049733830120644298616435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16132623546988384796310493 6049733830120644298616435)
                ·
                  refine ⟨9074600745180966447924653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6049733830120644298616435 9074600745180966447924653)
                  ·
                    refine ⟨3402975279442862417971745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9074600745180966447924653 3402975279442862417971745)
                    ·
                      refine ⟨2552231459582146813478809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3402975279442862417971745 2552231459582146813478809)
                      ·
                        rfl

theorem cell23_4970453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 3, 1, 3, 2].length) (baseStart_4970453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970453 prefixEnd_4970453 := by exact prefixLift 4970453
  have htrace : WordTrace (prefixWord ++ tailWord_4970453) baseStart_4970453 baseEnd_4970453 := by
    simpa [prefixWord, tailWord_4970453, baseEnd_4970453] using wordTrace_append hprefix tailTrace_4970453
  have hstable : (prefixWord ++ tailWord_4970453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970453).length < 2 ^ (prefixWord ++ tailWord_4970453).sum := by decide
  have hdescent : baseEnd_4970453 < baseStart_4970453 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970500 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_4970500 : Nat := 118140960795 + 4970500 * 2 ^ 59
def prefixEnd_4970500 : Nat := 4983230072969 + 3 ^ 40 * 4970500 * 2
def baseEnd_4970500 : Nat := 2552255593172908129591093

theorem tailTrace_4970500 : CollatzResearch.WordTrace tailWord_4970500 prefixEnd_4970500 2552255593172908129591093 := by
  unfold tailWord_4970500
  simp only [CollatzResearch.WordTrace]
  refine ⟨90644514246367434330610477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120859352328489912440813969 90644514246367434330610477)
  ·
    refine ⟨33991692842387787873978929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90644514246367434330610477 33991692842387787873978929)
    ·
      refine ⟨25493769631790840905484197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33991692842387787873978929 25493769631790840905484197)
      ·
        refine ⟨4780081805960782669778287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25493769631790840905484197 4780081805960782669778287)
        ·
          refine ⟨7170122708941174004667431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780081805960782669778287 7170122708941174004667431)
          ·
            refine ⟨10755184063411761007001147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170122708941174004667431 10755184063411761007001147)
            ·
              refine ⟨16132776095117641510501721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10755184063411761007001147 16132776095117641510501721)
              ·
                refine ⟨12099582071338231132876291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16132776095117641510501721 12099582071338231132876291)
                ·
                  refine ⟨18149373107007346699314437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12099582071338231132876291 18149373107007346699314437)
                  ·
                    refine ⟨3403007457563877506121457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18149373107007346699314437 3403007457563877506121457)
                    ·
                      refine ⟨2552255593172908129591093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403007457563877506121457 2552255593172908129591093)
                      ·
                        rfl

theorem cell23_4970500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_4970500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970500 prefixEnd_4970500 := by exact prefixLift 4970500
  have htrace : WordTrace (prefixWord ++ tailWord_4970500) baseStart_4970500 baseEnd_4970500 := by
    simpa [prefixWord, tailWord_4970500, baseEnd_4970500] using wordTrace_append hprefix tailTrace_4970500
  have hstable : (prefixWord ++ tailWord_4970500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970500).length < 2 ^ (prefixWord ++ tailWord_4970500).sum := by decide
  have hdescent : baseEnd_4970500 < baseStart_4970500 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970512 : List Nat := [2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7]
def baseStart_4970512 : Nat := 118140960795 + 4970512 * 2 ^ 59
def prefixEnd_4970512 : Nat := 4983230072969 + 3 ^ 40 * 4970512 * 2
def baseEnd_4970512 : Nat := 2552261754940762082641037

theorem tailTrace_4970512 : CollatzResearch.WordTrace tailWord_4970512 prefixEnd_4970512 2552261754940762082641037 := by
  unfold tailWord_4970512
  simp only [CollatzResearch.WordTrace]
  refine ⟨90644733084345697355328895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120859644112460929807105193 90644733084345697355328895)
  ·
    refine ⟨135967099626518546032993343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90644733084345697355328895 135967099626518546032993343)
    ·
      refine ⟨203950649439777819049490015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135967099626518546032993343 203950649439777819049490015)
      ·
        refine ⟨305925974159666728574235023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203950649439777819049490015 305925974159666728574235023)
        ·
          refine ⟨458888961239500092861352535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305925974159666728574235023 458888961239500092861352535)
          ·
            refine ⟨688333441859250139292028803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458888961239500092861352535 688333441859250139292028803)
            ·
              refine ⟨1032500162788875208938043205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 688333441859250139292028803 1032500162788875208938043205)
              ·
                refine ⟨193593780522914101675883101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1032500162788875208938043205 193593780522914101675883101)
                ·
                  refine ⟨72597667696092788128456163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 193593780522914101675883101 72597667696092788128456163)
                  ·
                    refine ⟨108896501544139182192684245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72597667696092788128456163 108896501544139182192684245)
                    ·
                      refine ⟨2552261754940762082641037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 108896501544139182192684245 2552261754940762082641037)
                      ·
                        rfl

theorem cell23_4970512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 7].length) (baseStart_4970512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970512 prefixEnd_4970512 := by exact prefixLift 4970512
  have htrace : WordTrace (prefixWord ++ tailWord_4970512) baseStart_4970512 baseEnd_4970512 := by
    simpa [prefixWord, tailWord_4970512, baseEnd_4970512] using wordTrace_append hprefix tailTrace_4970512
  have hstable : (prefixWord ++ tailWord_4970512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970512).length < 2 ^ (prefixWord ++ tailWord_4970512).sum := by decide
  have hdescent : baseEnd_4970512 < baseStart_4970512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970553 : List Nat := [1, 2, 1, 5, 3, 2, 1, 1, 2, 5]
def baseStart_4970553 : Nat := 118140960795 + 4970553 * 2 ^ 59
def prefixEnd_4970553 : Nat := 4983230072969 + 3 ^ 40 * 4970553 * 2
def baseEnd_4970553 : Nat := 850760935882532140742783

theorem tailTrace_4970553 : CollatzResearch.WordTrace tailWord_4970553 prefixEnd_4970553 850760935882532140742783 := by
  unfold tailWord_4970553
  simp only [CollatzResearch.WordTrace]
  refine ⟨181290961561542858712900313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120860641041028572475266875 181290961561542858712900313)
  ·
    refine ⟨135968221171157144034675235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181290961561542858712900313 135968221171157144034675235)
    ·
      refine ⟨203952331756735716052012853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135968221171157144034675235 203952331756735716052012853)
      ·
        refine ⟨19120531102193973379876205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 203952331756735716052012853 19120531102193973379876205)
        ·
          refine ⟨7170199163322740017453577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19120531102193973379876205 7170199163322740017453577)
          ·
            refine ⟨5377649372492055013090183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7170199163322740017453577 5377649372492055013090183)
            ·
              refine ⟨8066474058738082519635275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377649372492055013090183 8066474058738082519635275)
              ·
                refine ⟨12099711088107123779452913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8066474058738082519635275 12099711088107123779452913)
                ·
                  refine ⟨9074783316080342834589685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12099711088107123779452913 9074783316080342834589685)
                  ·
                    refine ⟨850760935882532140742783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9074783316080342834589685 850760935882532140742783)
                    ·
                      rfl

theorem cell23_4970553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 2, 1, 1, 2, 5].length) (baseStart_4970553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970553 prefixEnd_4970553 := by exact prefixLift 4970553
  have htrace : WordTrace (prefixWord ++ tailWord_4970553) baseStart_4970553 baseEnd_4970553 := by
    simpa [prefixWord, tailWord_4970553, baseEnd_4970553] using wordTrace_append hprefix tailTrace_4970553
  have hstable : (prefixWord ++ tailWord_4970553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970553).length < 2 ^ (prefixWord ++ tailWord_4970553).sum := by decide
  have hdescent : baseEnd_4970553 < baseStart_4970553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970556 : List Nat := [2, 2, 2, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_4970556 : Nat := 118140960795 + 4970556 * 2 ^ 59
def prefixEnd_4970556 : Nat := 4983230072969 + 3 ^ 40 * 4970556 * 2
def baseEnd_4970556 : Nat := 2552284348089559910490835

theorem tailTrace_4970556 : CollatzResearch.WordTrace tailWord_4970556 prefixEnd_4970556 2552284348089559910490835 := by
  unfold tailWord_4970556
  simp only [CollatzResearch.WordTrace]
  refine ⟨90645535490265995112629761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120860713987021326816839681 90645535490265995112629761)
  ·
    refine ⟨67984151617699496334472321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 90645535490265995112629761 67984151617699496334472321)
    ·
      refine ⟨50988113713274622250854241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67984151617699496334472321 50988113713274622250854241)
      ·
        refine ⟨38241085284955966688140681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50988113713274622250854241 38241085284955966688140681)
        ·
          refine ⟨28680813963716975016105511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38241085284955966688140681 28680813963716975016105511)
          ·
            refine ⟨43021220945575462524158267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28680813963716975016105511 43021220945575462524158267)
            ·
              refine ⟨64531831418363193786237401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43021220945575462524158267 64531831418363193786237401)
              ·
                refine ⟨48398873563772395339678051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64531831418363193786237401 48398873563772395339678051)
                ·
                  refine ⟨72598310345658593009517077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48398873563772395339678051 72598310345658593009517077)
                  ·
                    refine ⟨3403045797452746547321113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 72598310345658593009517077 3403045797452746547321113)
                    ·
                      refine ⟨2552284348089559910490835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403045797452746547321113 2552284348089559910490835)
                      ·
                        rfl

theorem cell23_4970556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_4970556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970556 prefixEnd_4970556 := by exact prefixLift 4970556
  have htrace : WordTrace (prefixWord ++ tailWord_4970556) baseStart_4970556 baseEnd_4970556 := by
    simpa [prefixWord, tailWord_4970556, baseEnd_4970556] using wordTrace_append hprefix tailTrace_4970556
  have hstable : (prefixWord ++ tailWord_4970556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970556).length < 2 ^ (prefixWord ++ tailWord_4970556).sum := by decide
  have hdescent : baseEnd_4970556 < baseStart_4970556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970573 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 4, 4, 2]
def baseStart_4970573 : Nat := 118140960795 + 4970573 * 2 ^ 59
def prefixEnd_4970573 : Nat := 4983230072969 + 3 ^ 40 * 4970573 * 2
def baseEnd_4970573 : Nat := 2552293077260686343978257

theorem tailTrace_4970573 : CollatzResearch.WordTrace tailWord_4970573 prefixEnd_4970573 2552293077260686343978257 := by
  unfold tailWord_4970573
  simp only [CollatzResearch.WordTrace]
  refine ⟨181291691021470402128628373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120861127347646934752418915 181291691021470402128628373)
  ·
    refine ⟨8498048016631425099779455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 181291691021470402128628373 8498048016631425099779455)
    ·
      refine ⟨12747072024947137649669183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8498048016631425099779455 12747072024947137649669183)
      ·
        refine ⟨19120608037420706474503775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12747072024947137649669183 19120608037420706474503775)
        ·
          refine ⟨28680912056131059711755663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19120608037420706474503775 28680912056131059711755663)
          ·
            refine ⟨43021368084196589567633495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28680912056131059711755663 43021368084196589567633495)
            ·
              refine ⟨64532052126294884351450243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43021368084196589567633495 64532052126294884351450243)
              ·
                refine ⟨96798078189442326527175365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64532052126294884351450243 96798078189442326527175365)
                ·
                  refine ⟨18149639660520436223845381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 96798078189442326527175365 18149639660520436223845381)
                  ·
                    refine ⟨3403057436347581791971009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18149639660520436223845381 3403057436347581791971009)
                    ·
                      refine ⟨2552293077260686343978257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403057436347581791971009 2552293077260686343978257)
                      ·
                        rfl

theorem cell23_4970573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 4, 4, 2].length) (baseStart_4970573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970573 prefixEnd_4970573 := by exact prefixLift 4970573
  have htrace : WordTrace (prefixWord ++ tailWord_4970573) baseStart_4970573 baseEnd_4970573 := by
    simpa [prefixWord, tailWord_4970573, baseEnd_4970573] using wordTrace_append hprefix tailTrace_4970573
  have hstable : (prefixWord ++ tailWord_4970573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970573).length < 2 ^ (prefixWord ++ tailWord_4970573).sum := by decide
  have hdescent : baseEnd_4970573 < baseStart_4970573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970583 : List Nat := [1, 1, 3, 2, 2, 1, 4, 4, 1, 4]
def baseStart_4970583 : Nat := 118140960795 + 4970583 * 2 ^ 59
def prefixEnd_4970583 : Nat := 4983230072969 + 3 ^ 40 * 4970583 * 2
def baseEnd_4970583 : Nat := 850766070689077101617737

theorem tailTrace_4970583 : CollatzResearch.WordTrace tailWord_4970583 prefixEnd_4970583 850766070689077101617737 := by
  unfold tailWord_4970583
  simp only [CollatzResearch.WordTrace]
  refine ⟨181292055751434173836492403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120861370500956115890994935 181292055751434173836492403)
  ·
    refine ⟨271938083627151260754738605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181292055751434173836492403 271938083627151260754738605)
    ·
      refine ⟨101976781360181722783026977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 271938083627151260754738605 101976781360181722783026977)
      ·
        refine ⟨76482586020136292087270233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101976781360181722783026977 76482586020136292087270233)
        ·
          refine ⟨57361939515102219065452675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76482586020136292087270233 57361939515102219065452675)
          ·
            refine ⟨86042909272653328598179013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57361939515102219065452675 86042909272653328598179013)
            ·
              refine ⟨16133045488622499112158565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86042909272653328598179013 16133045488622499112158565)
              ·
                refine ⟨3024946029116718583529731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16133045488622499112158565 3024946029116718583529731)
                ·
                  refine ⟨4537419043675077875294597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3024946029116718583529731 4537419043675077875294597)
                  ·
                    refine ⟨850766070689077101617737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4537419043675077875294597 850766070689077101617737)
                    ·
                      rfl

theorem cell23_4970583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_4970583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970583 prefixEnd_4970583 := by exact prefixLift 4970583
  have htrace : WordTrace (prefixWord ++ tailWord_4970583) baseStart_4970583 baseEnd_4970583 := by
    simpa [prefixWord, tailWord_4970583, baseEnd_4970583] using wordTrace_append hprefix tailTrace_4970583
  have hstable : (prefixWord ++ tailWord_4970583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970583).length < 2 ^ (prefixWord ++ tailWord_4970583).sum := by decide
  have hdescent : baseEnd_4970583 < baseStart_4970583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970599 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_4970599 : Nat := 118140960795 + 4970599 * 2 ^ 59
def prefixEnd_4970599 : Nat := 4983230072969 + 3 ^ 40 * 4970599 * 2
def baseEnd_4970599 : Nat := 2552306427757703242253137

theorem tailTrace_4970599 : CollatzResearch.WordTrace tailWord_4970599 prefixEnd_4970599 2552306427757703242253137 := by
  unfold tailWord_4970599
  simp only [CollatzResearch.WordTrace]
  refine ⟨181292639319376208569074851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120861759546250805712716567 181292639319376208569074851)
  ·
    refine ⟨271938958979064312853612277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181292639319376208569074851 271938958979064312853612277)
    ·
      refine ⟨25494277404287279330026151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 271938958979064312853612277 25494277404287279330026151)
      ·
        refine ⟨38241416106430918995039227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25494277404287279330026151 38241416106430918995039227)
        ·
          refine ⟨57362124159646378492558841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38241416106430918995039227 57362124159646378492558841)
          ·
            refine ⟨43021593119734783869419131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57362124159646378492558841 43021593119734783869419131)
            ·
              refine ⟨64532389679602175804128697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43021593119734783869419131 64532389679602175804128697)
              ·
                refine ⟨48399292259701631853096523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64532389679602175804128697 48399292259701631853096523)
                ·
                  refine ⟨72598938389552447779644785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48399292259701631853096523 72598938389552447779644785)
                  ·
                    refine ⟨54449203792164335834733589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72598938389552447779644785 54449203792164335834733589)
                    ·
                      refine ⟨2552306427757703242253137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54449203792164335834733589 2552306427757703242253137)
                      ·
                        rfl

theorem cell23_4970599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_4970599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970599 prefixEnd_4970599 := by exact prefixLift 4970599
  have htrace : WordTrace (prefixWord ++ tailWord_4970599) baseStart_4970599 baseEnd_4970599 := by
    simpa [prefixWord, tailWord_4970599, baseEnd_4970599] using wordTrace_append hprefix tailTrace_4970599
  have hstable : (prefixWord ++ tailWord_4970599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970599).length < 2 ^ (prefixWord ++ tailWord_4970599).sum := by decide
  have hdescent : baseEnd_4970599 < baseStart_4970599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970606 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3]
def baseStart_4970606 : Nat := 118140960795 + 4970606 * 2 ^ 59
def prefixEnd_4970606 : Nat := 4983230072969 + 3 ^ 40 * 4970606 * 2
def baseEnd_4970606 : Nat := 2552310022122284714865605

theorem tailTrace_4970606 : CollatzResearch.WordTrace tailWord_4970606 prefixEnd_4970606 2552310022122284714865605 := by
  unfold tailWord_4970606
  simp only [CollatzResearch.WordTrace]
  refine ⟨22661611828793856095572459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120861929753567232509719781 22661611828793856095572459)
  ·
    refine ⟨33992417743190784143358689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22661611828793856095572459 33992417743190784143358689)
    ·
      refine ⟨25494313307393088107519017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33992417743190784143358689 25494313307393088107519017)
      ·
        refine ⟨19120734980544816080639263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25494313307393088107519017 19120734980544816080639263)
        ·
          refine ⟨28681102470817224120958895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19120734980544816080639263 28681102470817224120958895)
          ·
            refine ⟨43021653706225836181438343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28681102470817224120958895 43021653706225836181438343)
            ·
              refine ⟨64532480559338754272157515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43021653706225836181438343 64532480559338754272157515)
              ·
                refine ⟨96798720839008131408236273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64532480559338754272157515 96798720839008131408236273)
                ·
                  refine ⟨72599040629256098556177205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 96798720839008131408236273 72599040629256098556177205)
                  ·
                    refine ⟨6806160058992759239641613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 72599040629256098556177205 6806160058992759239641613)
                    ·
                      refine ⟨2552310022122284714865605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6806160058992759239641613 2552310022122284714865605)
                      ·
                        rfl

theorem cell23_4970606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3].length) (baseStart_4970606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970606 prefixEnd_4970606 := by exact prefixLift 4970606
  have htrace : WordTrace (prefixWord ++ tailWord_4970606) baseStart_4970606 baseEnd_4970606 := by
    simpa [prefixWord, tailWord_4970606, baseEnd_4970606] using wordTrace_append hprefix tailTrace_4970606
  have hstable : (prefixWord ++ tailWord_4970606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970606).length < 2 ^ (prefixWord ++ tailWord_4970606).sum := by decide
  have hdescent : baseEnd_4970606 < baseStart_4970606 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970633 : List Nat := [1, 2, 1, 1, 4, 2, 3, 2, 2, 3, 2]
def baseStart_4970633 : Nat := 118140960795 + 4970633 * 2 ^ 59
def prefixEnd_4970633 : Nat := 4983230072969 + 3 ^ 40 * 4970633 * 2
def baseEnd_4970633 : Nat := 2552323886099956109227981

theorem tailTrace_4970633 : CollatzResearch.WordTrace tailWord_4970633 prefixEnd_4970633 2552323886099956109227981 := by
  unfold tailWord_4970633
  simp only [CollatzResearch.WordTrace]
  refine ⟨181293879401253032375812553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120862586267502021583875035 181293879401253032375812553)
  ·
    refine ⟨135970409550939774281859415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181293879401253032375812553 135970409550939774281859415)
    ·
      refine ⟨203955614326409661422789123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135970409550939774281859415 203955614326409661422789123)
      ·
        refine ⟨305933421489614492134183685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203955614326409661422789123 305933421489614492134183685)
        ·
          refine ⟨57362516529302717275159441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 305933421489614492134183685 57362516529302717275159441)
          ·
            refine ⟨43021887396977037956369581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57362516529302717275159441 43021887396977037956369581)
            ·
              refine ⟨16133207773866389233638593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43021887396977037956369581 16133207773866389233638593)
              ·
                refine ⟨12099905830399791925228945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16133207773866389233638593 12099905830399791925228945)
                ·
                  refine ⟨9074929372799843943921709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12099905830399791925228945 9074929372799843943921709)
                  ·
                    refine ⟨3403098514799941478970641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9074929372799843943921709 3403098514799941478970641)
                    ·
                      refine ⟨2552323886099956109227981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403098514799941478970641 2552323886099956109227981)
                      ·
                        rfl

theorem cell23_4970633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 2, 2, 3, 2].length) (baseStart_4970633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970633 prefixEnd_4970633 := by exact prefixLift 4970633
  have htrace : WordTrace (prefixWord ++ tailWord_4970633) baseStart_4970633 baseEnd_4970633 := by
    simpa [prefixWord, tailWord_4970633, baseEnd_4970633] using wordTrace_append hprefix tailTrace_4970633
  have hstable : (prefixWord ++ tailWord_4970633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970633).length < 2 ^ (prefixWord ++ tailWord_4970633).sum := by decide
  have hdescent : baseEnd_4970633 < baseStart_4970633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970660 : List Nat := [2, 3, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_4970660 : Nat := 118140960795 + 4970660 * 2 ^ 59
def prefixEnd_4970660 : Nat := 4983230072969 + 3 ^ 40 * 4970660 * 2
def baseEnd_4970660 : Nat := 850779250025875834530119

theorem tailTrace_4970660 : CollatzResearch.WordTrace tailWord_4970660 prefixEnd_4970660 850779250025875834530119 := by
  unfold tailWord_4970660
  simp only [CollatzResearch.WordTrace]
  refine ⟨90647432086077607993522717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120863242781436810658030289 90647432086077607993522717)
  ·
    refine ⟨33992787032279102997571019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 90647432086077607993522717 33992787032279102997571019)
    ·
      refine ⟨50989180548418654496356529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33992787032279102997571019 50989180548418654496356529)
      ·
        refine ⟨38241885411313990872267397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50989180548418654496356529 38241885411313990872267397)
        ·
          refine ⟨7170353514621373288550137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38241885411313990872267397 7170353514621373288550137)
          ·
            refine ⟨5377765135966029966412603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7170353514621373288550137 5377765135966029966412603)
            ·
              refine ⟨8066647703949044949618905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5377765135966029966412603 8066647703949044949618905)
              ·
                refine ⟨6049985777961783712214179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8066647703949044949618905 6049985777961783712214179)
                ·
                  refine ⟨9074978666942675568321269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6049985777961783712214179 9074978666942675568321269)
                  ·
                    refine ⟨850779250025875834530119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9074978666942675568321269 850779250025875834530119)
                    ·
                      rfl

theorem cell23_4970660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_4970660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970660 prefixEnd_4970660 := by exact prefixLift 4970660
  have htrace : WordTrace (prefixWord ++ tailWord_4970660) baseStart_4970660 baseEnd_4970660 := by
    simpa [prefixWord, tailWord_4970660, baseEnd_4970660] using wordTrace_append hprefix tailTrace_4970660
  have hstable : (prefixWord ++ tailWord_4970660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970660).length < 2 ^ (prefixWord ++ tailWord_4970660).sum := by decide
  have hdescent : baseEnd_4970660 < baseStart_4970660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970673 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 1, 6]
def baseStart_4970673 : Nat := 118140960795 + 4970673 * 2 ^ 59
def prefixEnd_4970673 : Nat := 4983230072969 + 3 ^ 40 * 4970673 * 2
def baseEnd_4970673 : Nat := 850781475108711984242599

theorem tailTrace_4970673 : CollatzResearch.WordTrace tailWord_4970673 prefixEnd_4970673 850781475108711984242599 := by
  unfold tailWord_4970673
  simp only [CollatzResearch.WordTrace]
  refine ⟨181295338321108119207268673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120863558880738746138179115 181295338321108119207268673)
  ·
    refine ⟨135971503740831089405451505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181295338321108119207268673 135971503740831089405451505)
    ·
      refine ⟨101978627805623317054088629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135971503740831089405451505 101978627805623317054088629)
      ·
        refine ⟨9560496356777185973820809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101978627805623317054088629 9560496356777185973820809)
        ·
          refine ⟨7170372267582889480365607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9560496356777185973820809 7170372267582889480365607)
          ·
            refine ⟨10755558401374334220548411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170372267582889480365607 10755558401374334220548411)
            ·
              refine ⟨16133337602061501330822617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10755558401374334220548411 16133337602061501330822617)
              ·
                refine ⟨12100003201546125998116963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16133337602061501330822617 12100003201546125998116963)
                ·
                  refine ⟨18150004802319188997175445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12100003201546125998116963 18150004802319188997175445)
                  ·
                    refine ⟨850781475108711984242599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18150004802319188997175445 850781475108711984242599)
                    ·
                      rfl

theorem cell23_4970673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 1, 6].length) (baseStart_4970673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970673 prefixEnd_4970673 := by exact prefixLift 4970673
  have htrace : WordTrace (prefixWord ++ tailWord_4970673) baseStart_4970673 baseEnd_4970673 := by
    simpa [prefixWord, tailWord_4970673, baseEnd_4970673] using wordTrace_append hprefix tailTrace_4970673
  have hstable : (prefixWord ++ tailWord_4970673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970673).length < 2 ^ (prefixWord ++ tailWord_4970673).sum := by decide
  have hdescent : baseEnd_4970673 < baseStart_4970673 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970677 : List Nat := [1, 3, 3, 4, 1, 1, 3, 1, 1, 5]
def baseStart_4970677 : Nat := 118140960795 + 4970677 * 2 ^ 59
def prefixEnd_4970677 : Nat := 4983230072969 + 3 ^ 40 * 4970677 * 2
def baseEnd_4970677 : Nat := 850782159749584645692593

theorem tailTrace_4970677 : CollatzResearch.WordTrace tailWord_4970677 prefixEnd_4970677 850782159749584645692593 := by
  unfold tailWord_4970677
  simp only [CollatzResearch.WordTrace]
  refine ⟨181295484213093627890414285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120863656142062418593609523 181295484213093627890414285)
  ·
    refine ⟨67985806579910110458905357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 181295484213093627890414285 67985806579910110458905357)
    ·
      refine ⟨25494677467466291422089509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67985806579910110458905357 25494677467466291422089509)
      ·
        refine ⟨4780252025149929641641783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25494677467466291422089509 4780252025149929641641783)
        ·
          refine ⟨7170378037724894462462675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780252025149929641641783 7170378037724894462462675)
          ·
            refine ⟨10755567056587341693694013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7170378037724894462462675 10755567056587341693694013)
            ·
              refine ⟨4033337646220253135135255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10755567056587341693694013 4033337646220253135135255)
              ·
                refine ⟨6050006469330379702702883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4033337646220253135135255 6050006469330379702702883)
                ·
                  refine ⟨9075009703995569554054325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6050006469330379702702883 9075009703995569554054325)
                  ·
                    refine ⟨850782159749584645692593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9075009703995569554054325 850782159749584645692593)
                    ·
                      rfl

theorem cell23_4970677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 1, 1, 5].length) (baseStart_4970677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970677 prefixEnd_4970677 := by exact prefixLift 4970677
  have htrace : WordTrace (prefixWord ++ tailWord_4970677) baseStart_4970677 baseEnd_4970677 := by
    simpa [prefixWord, tailWord_4970677, baseEnd_4970677] using wordTrace_append hprefix tailTrace_4970677
  have hstable : (prefixWord ++ tailWord_4970677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970677).length < 2 ^ (prefixWord ++ tailWord_4970677).sum := by decide
  have hdescent : baseEnd_4970677 < baseStart_4970677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970686 : List Nat := [4, 2, 1, 1, 4, 11]
def baseStart_4970686 : Nat := 118140960795 + 4970686 * 2 ^ 59
def prefixEnd_4970686 : Nat := 4983230072969 + 3 ^ 40 * 4970686 * 2
def baseEnd_4970686 : Nat := 10503502471500594246359

theorem tailTrace_4970686 : CollatzResearch.WordTrace tailWord_4970686 prefixEnd_4970686 10503502471500594246359 := by
  unfold tailWord_4970686
  simp only [CollatzResearch.WordTrace]
  refine ⟨22661976558757627803436489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120863874980040681618327941 22661976558757627803436489)
  ·
    refine ⟨16996482419068220852577367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22661976558757627803436489 16996482419068220852577367)
    ·
      refine ⟨25494723628602331278866051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16996482419068220852577367 25494723628602331278866051)
      ·
        refine ⟨38242085442903496918299077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25494723628602331278866051 38242085442903496918299077)
        ·
          refine ⟨7170391020544405672181077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38242085442903496918299077 7170391020544405672181077)
          ·
            refine ⟨10503502471500594246359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 7170391020544405672181077 10503502471500594246359)
            ·
              rfl

theorem cell23_4970686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 11].length) (baseStart_4970686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970686 prefixEnd_4970686 := by exact prefixLift 4970686
  have htrace : WordTrace (prefixWord ++ tailWord_4970686) baseStart_4970686 baseEnd_4970686 := by
    simpa [prefixWord, tailWord_4970686, baseEnd_4970686] using wordTrace_append hprefix tailTrace_4970686
  have hstable : (prefixWord ++ tailWord_4970686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970686).length < 2 ^ (prefixWord ++ tailWord_4970686).sum := by decide
  have hdescent : baseEnd_4970686 < baseStart_4970686 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970696 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 5, 3, 3]
def baseStart_4970696 : Nat := 118140960795 + 4970696 * 2 ^ 59
def prefixEnd_4970696 : Nat := 4983230072969 + 3 ^ 40 * 4970696 * 2
def baseEnd_4970696 : Nat := 2552356235381189362740191

theorem tailTrace_4970696 : CollatzResearch.WordTrace tailWord_4970696 prefixEnd_4970696 2552356235381189362740191 := by
  unfold tailWord_4970696
  simp only [CollatzResearch.WordTrace]
  refine ⟨90648088600012397067677971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120864118133349862756903961 90648088600012397067677971)
  ·
    refine ⟨135972132900018595601516957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90648088600012397067677971 135972132900018595601516957)
    ·
      refine ⟨50989549837506973350568859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135972132900018595601516957 50989549837506973350568859)
      ·
        refine ⟨76484324756260460025853289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50989549837506973350568859 76484324756260460025853289)
        ·
          refine ⟨57363243567195345019389967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76484324756260460025853289 57363243567195345019389967)
          ·
            refine ⟨86044865350793017529084951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57363243567195345019389967 86044865350793017529084951)
            ·
              refine ⟨129067298026189526293627427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86044865350793017529084951 129067298026189526293627427)
              ·
                refine ⟨193600947039284289440441141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 129067298026189526293627427 193600947039284289440441141)
                ·
                  refine ⟨18150088784932902135041357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 193600947039284289440441141 18150088784932902135041357)
                  ·
                    refine ⟨6806283294349838300640509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18150088784932902135041357 6806283294349838300640509)
                    ·
                      refine ⟨2552356235381189362740191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6806283294349838300640509 2552356235381189362740191)
                      ·
                        rfl

theorem cell23_4970696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 3, 3].length) (baseStart_4970696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970696 prefixEnd_4970696 := by exact prefixLift 4970696
  have htrace : WordTrace (prefixWord ++ tailWord_4970696) baseStart_4970696 baseEnd_4970696 := by
    simpa [prefixWord, tailWord_4970696, baseEnd_4970696] using wordTrace_append hprefix tailTrace_4970696
  have hstable : (prefixWord ++ tailWord_4970696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970696).length < 2 ^ (prefixWord ++ tailWord_4970696).sum := by decide
  have hdescent : baseEnd_4970696 < baseStart_4970696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970699 : List Nat := [1, 1, 1, 1, 3, 2, 3, 1, 1, 9]
def baseStart_4970699 : Nat := 118140960795 + 4970699 * 2 ^ 59
def prefixEnd_4970699 : Nat := 4983230072969 + 3 ^ 40 * 4970699 * 2
def baseEnd_4970699 : Nat := 850785925274384283667559

theorem tailTrace_4970699 : CollatzResearch.WordTrace tailWord_4970699 prefixEnd_4970699 850785925274384283667559 := by
  unfold tailWord_4970699
  simp only [CollatzResearch.WordTrace]
  refine ⟨181296286619013925647715151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120864191079342617098476767 181296286619013925647715151)
  ·
    refine ⟨271944429928520888471572727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181296286619013925647715151 271944429928520888471572727)
    ·
      refine ⟨407916644892781332707359091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271944429928520888471572727 407916644892781332707359091)
      ·
        refine ⟨611874967339171999061038637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 407916644892781332707359091 611874967339171999061038637)
        ·
          refine ⟨229453112752189499647889489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 611874967339171999061038637 229453112752189499647889489)
          ·
            refine ⟨172089834564142124735917117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 229453112752189499647889489 172089834564142124735917117)
            ·
              refine ⟨64533687961553296775968919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172089834564142124735917117 64533687961553296775968919)
              ·
                refine ⟨96800531942329945163953379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64533687961553296775968919 96800531942329945163953379)
                ·
                  refine ⟨145200797913494917745930069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 96800531942329945163953379 145200797913494917745930069)
                  ·
                    refine ⟨850785925274384283667559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 145200797913494917745930069 850785925274384283667559)
                    ·
                      rfl

theorem cell23_4970699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 9].length) (baseStart_4970699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970699 prefixEnd_4970699 := by exact prefixLift 4970699
  have htrace : WordTrace (prefixWord ++ tailWord_4970699) baseStart_4970699 baseEnd_4970699 := by
    simpa [prefixWord, tailWord_4970699, baseEnd_4970699] using wordTrace_append hprefix tailTrace_4970699
  have hstable : (prefixWord ++ tailWord_4970699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970699).length < 2 ^ (prefixWord ++ tailWord_4970699).sum := by decide
  have hdescent : baseEnd_4970699 < baseStart_4970699 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970710 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 1, 2, 4]
def baseStart_4970710 : Nat := 118140960795 + 4970710 * 2 ^ 59
def prefixEnd_4970710 : Nat := 4983230072969 + 3 ^ 40 * 4970710 * 2
def baseEnd_4970710 : Nat := 2552363424110352307965127

theorem tailTrace_4970710 : CollatzResearch.WordTrace tailWord_4970710 prefixEnd_4970710 2552363424110352307965127 := by
  unfold tailWord_4970710
  simp only [CollatzResearch.WordTrace]
  refine ⟨11331042988873379657897849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 120864458547982716350910389 11331042988873379657897849)
  ·
    refine ⟨8498282241655034743423387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11331042988873379657897849 8498282241655034743423387)
    ·
      refine ⟨12747423362482552115135081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8498282241655034743423387 12747423362482552115135081)
      ·
        refine ⟨9560567521861914086351311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12747423362482552115135081 9560567521861914086351311)
        ·
          refine ⟨14340851282792871129526967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9560567521861914086351311 14340851282792871129526967)
          ·
            refine ⟨21511276924189306694290451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14340851282792871129526967 21511276924189306694290451)
            ·
              refine ⟨32266915386283960041435677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21511276924189306694290451 32266915386283960041435677)
              ·
                refine ⟨12100093269856485015538379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32266915386283960041435677 12100093269856485015538379)
                ·
                  refine ⟨18150139904784727523307569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12100093269856485015538379 18150139904784727523307569)
                  ·
                    refine ⟨13612604928588545642480677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18150139904784727523307569 13612604928588545642480677)
                    ·
                      refine ⟨2552363424110352307965127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13612604928588545642480677 2552363424110352307965127)
                      ·
                        rfl

theorem cell23_4970710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_4970710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970710 prefixEnd_4970710 := by exact prefixLift 4970710
  have htrace : WordTrace (prefixWord ++ tailWord_4970710) baseStart_4970710 baseEnd_4970710 := by
    simpa [prefixWord, tailWord_4970710, baseEnd_4970710] using wordTrace_append hprefix tailTrace_4970710
  have hstable : (prefixWord ++ tailWord_4970710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970710).length < 2 ^ (prefixWord ++ tailWord_4970710).sum := by decide
  have hdescent : baseEnd_4970710 < baseStart_4970710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970746 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_4970746 : Nat := 118140960795 + 4970746 * 2 ^ 59
def prefixEnd_4970746 : Nat := 4983230072969 + 3 ^ 40 * 4970746 * 2
def baseEnd_4970746 : Nat := 850793969804638055704987

theorem tailTrace_4970746 : CollatzResearch.WordTrace tailWord_4970746 prefixEnd_4970746 850793969804638055704987 := by
  unfold tailWord_4970746
  simp only [CollatzResearch.WordTrace]
  refine ⟨45324500212460913168669023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120865333899895768449784061 45324500212460913168669023)
  ·
    refine ⟨67986750318691369753003535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45324500212460913168669023 67986750318691369753003535)
    ·
      refine ⟨101980125478037054629505303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67986750318691369753003535 101980125478037054629505303)
      ·
        refine ⟨152970188217055581944257955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101980125478037054629505303 152970188217055581944257955)
        ·
          refine ⟨229455282325583372916386933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152970188217055581944257955 229455282325583372916386933)
          ·
            refine ⟨21511432718023441210911275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 229455282325583372916386933 21511432718023441210911275)
            ·
              refine ⟨32267149077035161816366913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21511432718023441210911275 32267149077035161816366913)
              ·
                refine ⟨24200361807776371362275185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32267149077035161816366913 24200361807776371362275185)
                ·
                  refine ⟨18150271355832278521706389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24200361807776371362275185 18150271355832278521706389)
                  ·
                    refine ⟨850793969804638055704987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18150271355832278521706389 850793969804638055704987)
                    ·
                      rfl

theorem cell23_4970746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_4970746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970746 prefixEnd_4970746 := by exact prefixLift 4970746
  have htrace : WordTrace (prefixWord ++ tailWord_4970746) baseStart_4970746 baseEnd_4970746 := by
    simpa [prefixWord, tailWord_4970746, baseEnd_4970746] using wordTrace_append hprefix tailTrace_4970746
  have hstable : (prefixWord ++ tailWord_4970746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970746).length < 2 ^ (prefixWord ++ tailWord_4970746).sum := by decide
  have hdescent : baseEnd_4970746 < baseStart_4970746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970776 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 7]
def baseStart_4970776 : Nat := 118140960795 + 4970776 * 2 ^ 59
def prefixEnd_4970776 : Nat := 4983230072969 + 3 ^ 40 * 4970776 * 2
def baseEnd_4970776 : Nat := 283599701537061005526647

theorem tailTrace_4970776 : CollatzResearch.WordTrace tailWord_4970776 prefixEnd_4970776 283599701537061005526647 := by
  unfold tailWord_4970776
  simp only [CollatzResearch.WordTrace]
  refine ⟨90649547519867483899134091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120866063359823311865512121 90649547519867483899134091)
  ·
    refine ⟨135974321279801225848701137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90649547519867483899134091 135974321279801225848701137)
    ·
      refine ⟨101980740959850919386525853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135974321279801225848701137 101980740959850919386525853)
      ·
        refine ⟨38242777859944094769947195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 101980740959850919386525853 38242777859944094769947195)
        ·
          refine ⟨57364166789916142154920793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38242777859944094769947195 57364166789916142154920793)
          ·
            refine ⟨43023125092437106616190595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57364166789916142154920793 43023125092437106616190595)
            ·
              refine ⟨64534687638655659924285893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43023125092437106616190595 64534687638655659924285893)
              ·
                refine ⟨12100253932247936235803605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64534687638655659924285893 12100253932247936235803605)
                ·
                  refine ⟨283599701537061005526647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12100253932247936235803605 283599701537061005526647)
                  ·
                    rfl

theorem cell23_4970776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 7].length) (baseStart_4970776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970776 prefixEnd_4970776 := by exact prefixLift 4970776
  have htrace : WordTrace (prefixWord ++ tailWord_4970776) baseStart_4970776 baseEnd_4970776 := by
    simpa [prefixWord, tailWord_4970776, baseEnd_4970776] using wordTrace_append hprefix tailTrace_4970776
  have hstable : (prefixWord ++ tailWord_4970776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970776).length < 2 ^ (prefixWord ++ tailWord_4970776).sum := by decide
  have hdescent : baseEnd_4970776 < baseStart_4970776 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970863 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 3]
def baseStart_4970863 : Nat := 118140960795 + 4970863 * 2 ^ 59
def prefixEnd_4970863 : Nat := 4983230072969 + 3 ^ 40 * 4970863 * 2
def baseEnd_4970863 : Nat := 2552441986650490209351923

theorem tailTrace_4970863 : CollatzResearch.WordTrace tailWord_4970863 prefixEnd_4970863 2552441986650490209351923 := by
  unfold tailWord_4970863
  simp only [CollatzResearch.WordTrace]
  refine ⟨181302268190419781656685243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 120868178793613187771123495 181302268190419781656685243)
  ·
    refine ⟨271953402285629672485027865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 181302268190419781656685243 271953402285629672485027865)
    ·
      refine ⟨203965051714222254363770899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271953402285629672485027865 203965051714222254363770899)
      ·
        refine ⟨305947577571333381545656349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203965051714222254363770899 305947577571333381545656349)
        ·
          refine ⟨114730341589250018079621131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 305947577571333381545656349 114730341589250018079621131)
          ·
            refine ⟨172095512383875027119431697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114730341589250018079621131 172095512383875027119431697)
            ·
              refine ⟨129071634287906270339573773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172095512383875027119431697 129071634287906270339573773)
              ·
                refine ⟨48401862857964851377340165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129071634287906270339573773 48401862857964851377340165)
                ·
                  refine ⟨9075349285868409633251281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48401862857964851377340165 9075349285868409633251281)
                  ·
                    refine ⟨6806511964401307224938461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9075349285868409633251281 6806511964401307224938461)
                    ·
                      refine ⟨2552441986650490209351923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6806511964401307224938461 2552441986650490209351923)
                      ·
                        rfl

theorem cell23_4970863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 2, 3].length) (baseStart_4970863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970863 prefixEnd_4970863 := by exact prefixLift 4970863
  have htrace : WordTrace (prefixWord ++ tailWord_4970863) baseStart_4970863 baseEnd_4970863 := by
    simpa [prefixWord, tailWord_4970863, baseEnd_4970863] using wordTrace_append hprefix tailTrace_4970863
  have hstable : (prefixWord ++ tailWord_4970863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970863).length < 2 ^ (prefixWord ++ tailWord_4970863).sum := by decide
  have hdescent : baseEnd_4970863 < baseStart_4970863 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970896 : List Nat := [2, 1, 1, 1, 1, 1, 2, 1, 4, 9]
def baseStart_4970896 : Nat := 118140960795 + 4970896 * 2 ^ 59
def prefixEnd_4970896 : Nat := 4983230072969 + 3 ^ 40 * 4970896 * 2
def baseEnd_4970896 : Nat := 850819643837362860079757

theorem tailTrace_4970896 : CollatzResearch.WordTrace tailWord_4970896 prefixEnd_4970896 850819643837362860079757 := by
  unfold tailWord_4970896
  simp only [CollatzResearch.WordTrace]
  refine ⟨90651735899650114146318271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120868981199533485528424361 90651735899650114146318271)
  ·
    refine ⟨135977603849475171219477407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90651735899650114146318271 135977603849475171219477407)
    ·
      refine ⟨203966405774212756829216111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135977603849475171219477407 203966405774212756829216111)
      ·
        refine ⟨305949608661319135243824167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 203966405774212756829216111 305949608661319135243824167)
        ·
          refine ⟨458924412991978702865736251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 305949608661319135243824167 458924412991978702865736251)
          ·
            refine ⟨688386619487968054298604377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 458924412991978702865736251 688386619487968054298604377)
            ·
              refine ⟨516289964615976040723953283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 688386619487968054298604377 516289964615976040723953283)
              ·
                refine ⟨774434946923964061085929925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 516289964615976040723953283 774434946923964061085929925)
                ·
                  refine ⟨145206552548243261453611861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 774434946923964061085929925 145206552548243261453611861)
                  ·
                    refine ⟨850819643837362860079757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 145206552548243261453611861 850819643837362860079757)
                    ·
                      rfl

theorem cell23_4970896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 1, 4, 9].length) (baseStart_4970896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970896 prefixEnd_4970896 := by exact prefixLift 4970896
  have htrace : WordTrace (prefixWord ++ tailWord_4970896) baseStart_4970896 baseEnd_4970896 := by
    simpa [prefixWord, tailWord_4970896, baseEnd_4970896] using wordTrace_append hprefix tailTrace_4970896
  have hstable : (prefixWord ++ tailWord_4970896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970896).length < 2 ^ (prefixWord ++ tailWord_4970896).sum := by decide
  have hdescent : baseEnd_4970896 < baseStart_4970896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970904 : List Nat := [2, 1, 2, 5, 1, 2, 2, 3, 1, 4]
def baseStart_4970904 : Nat := 118140960795 + 4970904 * 2 ^ 59
def prefixEnd_4970904 : Nat := 4983230072969 + 3 ^ 40 * 4970904 * 2
def baseEnd_4970904 : Nat := 850821013119108182979745

theorem tailTrace_4970904 : CollatzResearch.WordTrace tailWord_4970904 prefixEnd_4970904 850821013119108182979745 := by
  unfold tailWord_4970904
  simp only [CollatzResearch.WordTrace]
  refine ⟨90651881791635622829463883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120869175722180830439285177 90651881791635622829463883)
  ·
    refine ⟨135977822687453434244195825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90651881791635622829463883 135977822687453434244195825)
    ·
      refine ⟨101983367015590075683146869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 135977822687453434244195825 101983367015590075683146869)
      ·
        refine ⟨9560940657711569595295019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 101983367015590075683146869 9560940657711569595295019)
        ·
          refine ⟨14341410986567354392942529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9560940657711569595295019 14341410986567354392942529)
          ·
            refine ⟨10756058239925515794706897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14341410986567354392942529 10756058239925515794706897)
            ·
              refine ⟨8067043679944136846030173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10756058239925515794706897 8067043679944136846030173)
              ·
                refine ⟨3025141379979051317261315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8067043679944136846030173 3025141379979051317261315)
                ·
                  refine ⟨4537712069968576975891973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3025141379979051317261315 4537712069968576975891973)
                  ·
                    refine ⟨850821013119108182979745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4537712069968576975891973 850821013119108182979745)
                    ·
                      rfl

theorem cell23_4970904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 3, 1, 4].length) (baseStart_4970904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970904 prefixEnd_4970904 := by exact prefixLift 4970904
  have htrace : WordTrace (prefixWord ++ tailWord_4970904) baseStart_4970904 baseEnd_4970904 := by
    simpa [prefixWord, tailWord_4970904, baseEnd_4970904] using wordTrace_append hprefix tailTrace_4970904
  have hstable : (prefixWord ++ tailWord_4970904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970904).length < 2 ^ (prefixWord ++ tailWord_4970904).sum := by decide
  have hdescent : baseEnd_4970904 < baseStart_4970904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970920 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 1, 2, 6]
def baseStart_4970920 : Nat := 118140960795 + 4970920 * 2 ^ 59
def prefixEnd_4970920 : Nat := 4983230072969 + 3 ^ 40 * 4970920 * 2
def baseEnd_4970920 : Nat := 2552471255047796486339161

theorem tailTrace_4970920 : CollatzResearch.WordTrace tailWord_4970920 prefixEnd_4970920 2552471255047796486339161 := by
  unfold tailWord_4970920
  simp only [CollatzResearch.WordTrace]
  refine ⟨90652173575606640195755107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120869564767475520261006809 90652173575606640195755107)
  ·
    refine ⟨135978260363409960293632661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90652173575606640195755107 135978260363409960293632661)
    ·
      refine ⟨6373980954534841888764031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 135978260363409960293632661 6373980954534841888764031)
      ·
        refine ⟨9560971431802262833146047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6373980954534841888764031 9560971431802262833146047)
        ·
          refine ⟨14341457147703394249719071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9560971431802262833146047 14341457147703394249719071)
          ·
            refine ⟨21512185721555091374578607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14341457147703394249719071 21512185721555091374578607)
            ·
              refine ⟨32268278582332637061867911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21512185721555091374578607 32268278582332637061867911)
              ·
                refine ⟨48402417873498955592801867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32268278582332637061867911 48402417873498955592801867)
                ·
                  refine ⟨72603626810248433389202801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48402417873498955592801867 72603626810248433389202801)
                  ·
                    refine ⟨54452720107686325041902101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 72603626810248433389202801 54452720107686325041902101)
                    ·
                      refine ⟨2552471255047796486339161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 54452720107686325041902101 2552471255047796486339161)
                      ·
                        rfl

theorem cell23_4970920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_4970920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970920 prefixEnd_4970920 := by exact prefixLift 4970920
  have htrace : WordTrace (prefixWord ++ tailWord_4970920) baseStart_4970920 baseEnd_4970920 := by
    simpa [prefixWord, tailWord_4970920, baseEnd_4970920] using wordTrace_append hprefix tailTrace_4970920
  have hstable : (prefixWord ++ tailWord_4970920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970920).length < 2 ^ (prefixWord ++ tailWord_4970920).sum := by decide
  have hdescent : baseEnd_4970920 < baseStart_4970920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970970 : List Nat := [3, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5]
def baseStart_4970970 : Nat := 118140960795 + 4970970 * 2 ^ 59
def prefixEnd_4970970 : Nat := 4983230072969 + 3 ^ 40 * 4970970 * 2
def baseEnd_4970970 : Nat := 2552496929080521290713931

theorem tailTrace_4970970 : CollatzResearch.WordTrace tailWord_4970970 prefixEnd_4970970 2552496929080521290713931 := by
  unfold tailWord_4970970
  simp only [CollatzResearch.WordTrace]
  refine ⟨45326542700258034732707591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120870780534021425953886909 45326542700258034732707591)
  ·
    refine ⟨67989814050387052099061387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45326542700258034732707591 67989814050387052099061387)
    ·
      refine ⟨101984721075580578148592081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67989814050387052099061387 101984721075580578148592081)
      ·
        refine ⟨76488540806685433611444061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 101984721075580578148592081 76488540806685433611444061)
        ·
          refine ⟨28683202802507037604291523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76488540806685433611444061 28683202802507037604291523)
          ·
            refine ⟨43024804203760556406437285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28683202802507037604291523 43024804203760556406437285)
            ·
              refine ⟨8067150788205104326206991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43024804203760556406437285 8067150788205104326206991)
              ·
                refine ⟨12100726182307656489310487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8067150788205104326206991 12100726182307656489310487)
                ·
                  refine ⟨18151089273461484733965731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12100726182307656489310487 18151089273461484733965731)
                  ·
                    refine ⟨27226633910192227100948597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18151089273461484733965731 27226633910192227100948597)
                    ·
                      refine ⟨2552496929080521290713931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27226633910192227100948597 2552496929080521290713931)
                      ·
                        rfl

theorem cell23_4970970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 1, 1, 1, 5].length) (baseStart_4970970 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970970 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970970 prefixEnd_4970970 := by exact prefixLift 4970970
  have htrace : WordTrace (prefixWord ++ tailWord_4970970) baseStart_4970970 baseEnd_4970970 := by
    simpa [prefixWord, tailWord_4970970, baseEnd_4970970] using wordTrace_append hprefix tailTrace_4970970
  have hstable : (prefixWord ++ tailWord_4970970).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970970).length < 2 ^ (prefixWord ++ tailWord_4970970).sum := by decide
  have hdescent : baseEnd_4970970 < baseStart_4970970 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970978 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 3, 1, 3]
def baseStart_4970978 : Nat := 118140960795 + 4970978 * 2 ^ 59
def prefixEnd_4970978 : Nat := 4983230072969 + 3 ^ 40 * 4970978 * 2
def baseEnd_4970978 : Nat := 2552501036925757259413895

theorem tailTrace_4970978 : CollatzResearch.WordTrace tailWord_4970978 prefixEnd_4970978 2552501036925757259413895 := by
  unfold tailWord_4970978
  simp only [CollatzResearch.WordTrace]
  refine ⟨45326615646250789074280397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 120870975056668770864747725 45326615646250789074280397)
  ·
    refine ⟨16997480867344045902855149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45326615646250789074280397 16997480867344045902855149)
    ·
      refine ⟨6374055325254017213570681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16997480867344045902855149 6374055325254017213570681)
      ·
        refine ⟨4780541493940512910178011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6374055325254017213570681 4780541493940512910178011)
        ·
          refine ⟨7170812240910769365267017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4780541493940512910178011 7170812240910769365267017)
          ·
            refine ⟨5378109180683077023950263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7170812240910769365267017 5378109180683077023950263)
            ·
              refine ⟨8067163771024615535925395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5378109180683077023950263 8067163771024615535925395)
              ·
                refine ⟨12100745656536923303888093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8067163771024615535925395 12100745656536923303888093)
                ·
                  refine ⟨4537779621201346238958035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12100745656536923303888093 4537779621201346238958035)
                  ·
                    refine ⟨6806669431802019358437053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4537779621201346238958035 6806669431802019358437053)
                    ·
                      refine ⟨2552501036925757259413895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6806669431802019358437053 2552501036925757259413895)
                      ·
                        rfl

theorem cell23_4970978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_4970978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970978 prefixEnd_4970978 := by exact prefixLift 4970978
  have htrace : WordTrace (prefixWord ++ tailWord_4970978) baseStart_4970978 baseEnd_4970978 := by
    simpa [prefixWord, tailWord_4970978, baseEnd_4970978] using wordTrace_append hprefix tailTrace_4970978
  have hstable : (prefixWord ++ tailWord_4970978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970978).length < 2 ^ (prefixWord ++ tailWord_4970978).sum := by decide
  have hdescent : baseEnd_4970978 < baseStart_4970978 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970984 : List Nat := [2, 1, 4, 1, 1, 3, 3, 1, 3, 2, 2]
def baseStart_4970984 : Nat := 118140960795 + 4970984 * 2 ^ 59
def prefixEnd_4970984 : Nat := 4983230072969 + 3 ^ 40 * 4970984 * 2
def baseEnd_4970984 : Nat := 2552504117809684235938867

theorem tailTrace_4970984 : CollatzResearch.WordTrace tailWord_4970984 prefixEnd_4970984 2552504117809684235938867 := by
  unfold tailWord_4970984
  simp only [CollatzResearch.WordTrace]
  refine ⟨90653340711490709660920003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 120871120948654279547893337 90653340711490709660920003)
  ·
    refine ⟨135980011067236064491380005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 90653340711490709660920003 135980011067236064491380005)
    ·
      refine ⟨25496252075106762092133751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 135980011067236064491380005 25496252075106762092133751)
      ·
        refine ⟨38244378112660143138200627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25496252075106762092133751 38244378112660143138200627)
        ·
          refine ⟨57366567168990214707300941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38244378112660143138200627 57366567168990214707300941)
          ·
            refine ⟨21512462688371330515237853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57366567168990214707300941 21512462688371330515237853)
            ·
              refine ⟨8067173508139248943214195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21512462688371330515237853 8067173508139248943214195)
              ·
                refine ⟨12100760262208873414821293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8067173508139248943214195 12100760262208873414821293)
                ·
                  refine ⟨4537785098328327530557985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12100760262208873414821293 4537785098328327530557985)
                  ·
                    refine ⟨3403338823746245647918489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4537785098328327530557985 3403338823746245647918489)
                    ·
                      refine ⟨2552504117809684235938867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3403338823746245647918489 2552504117809684235938867)
                      ·
                        rfl

theorem cell23_4970984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 1, 3, 2, 2].length) (baseStart_4970984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970984 prefixEnd_4970984 := by exact prefixLift 4970984
  have htrace : WordTrace (prefixWord ++ tailWord_4970984) baseStart_4970984 baseEnd_4970984 := by
    simpa [prefixWord, tailWord_4970984, baseEnd_4970984] using wordTrace_append hprefix tailTrace_4970984
  have hstable : (prefixWord ++ tailWord_4970984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970984).length < 2 ^ (prefixWord ++ tailWord_4970984).sum := by decide
  have hdescent : baseEnd_4970984 < baseStart_4970984 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4970990 : List Nat := [4, 1, 2, 1, 2, 3, 2, 8]
def baseStart_4970990 : Nat := 118140960795 + 4970990 * 2 ^ 59
def prefixEnd_4970990 : Nat := 4983230072969 + 3 ^ 40 * 4970990 * 2
def baseEnd_4970990 : Nat := 94537303655318933794957

theorem tailTrace_4970990 : CollatzResearch.WordTrace tailWord_4970990 prefixEnd_4970990 94537303655318933794957 := by
  unfold tailWord_4970990
  simp only [CollatzResearch.WordTrace]
  refine ⟨22663362532619960293319803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 120871266840639788231038949 22663362532619960293319803)
  ·
    refine ⟨33995043798929940439979705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22663362532619960293319803 33995043798929940439979705)
    ·
      refine ⟨25496282849197455329984779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33995043798929940439979705 25496282849197455329984779)
      ·
        refine ⟨38244424273796182994977169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25496282849197455329984779 38244424273796182994977169)
        ·
          refine ⟨28683318205347137246232877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38244424273796182994977169 28683318205347137246232877)
          ·
            refine ⟨10756244327005176467337329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28683318205347137246232877 10756244327005176467337329)
            ·
              refine ⟨8067183245253882350502997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10756244327005176467337329 8067183245253882350502997)
              ·
                refine ⟨94537303655318933794957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8067183245253882350502997 94537303655318933794957)
                ·
                  rfl

theorem cell23_4970990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 2, 8].length) (baseStart_4970990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4970990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4970990 prefixEnd_4970990 := by exact prefixLift 4970990
  have htrace : WordTrace (prefixWord ++ tailWord_4970990) baseStart_4970990 baseEnd_4970990 := by
    simpa [prefixWord, tailWord_4970990, baseEnd_4970990] using wordTrace_append hprefix tailTrace_4970990
  have hstable : (prefixWord ++ tailWord_4970990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4970990).length < 2 ^ (prefixWord ++ tailWord_4970990).sum := by decide
  have hdescent : baseEnd_4970990 < baseStart_4970990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4970990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
