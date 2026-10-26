import V185TrunkScan21Chunk136

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_1669406 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 5]
def baseStart_1669406 : Nat := 118140960795 + 1669406 * 2 ^ 59
def prefixEnd_1669406 : Nat := 4983230072969 + 3 ^ 40 * 1669406 * 2
def baseEnd_1669406 : Nat := 380981193555466966687799

theorem tailTrace_1669406 : CollatzResearch.WordTrace tailWord_1669406 prefixEnd_1669406 380981193555466966687799 := by
  unfold tailWord_1669406
  simp only [CollatzResearch.WordTrace]
  refine ⟨7611029873754331086374509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40592159326689765793997381 7611029873754331086374509)
  ·
    refine ⟨2854136202657874157390441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7611029873754331086374509 2854136202657874157390441)
    ·
      refine ⟨2140602151993405618042831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2854136202657874157390441 2140602151993405618042831)
      ·
        refine ⟨3210903227990108427064247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2140602151993405618042831 3210903227990108427064247)
        ·
          refine ⟨4816354841985162640596371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3210903227990108427064247 4816354841985162640596371)
          ·
            refine ⟨7224532262977743960894557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816354841985162640596371 7224532262977743960894557)
            ·
              refine ⟨2709199598616653985335459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7224532262977743960894557 2709199598616653985335459)
              ·
                refine ⟨4063799397924980978003189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709199598616653985335459 4063799397924980978003189)
                ·
                  refine ⟨380981193555466966687799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4063799397924980978003189 380981193555466966687799)
                  ·
                    rfl

theorem cell21_1669406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 5].length) (baseStart_1669406 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669406 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669406 prefixEnd_1669406 := by exact prefixLift 1669406
  have htrace : WordTrace (prefixWord ++ tailWord_1669406) baseStart_1669406 baseEnd_1669406 := by
    simpa [prefixWord, tailWord_1669406, baseEnd_1669406] using wordTrace_append hprefix tailTrace_1669406
  have hstable : (prefixWord ++ tailWord_1669406).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669406).length < 2 ^ (prefixWord ++ tailWord_1669406).sum := by decide
  have hdescent : baseEnd_1669406 < baseStart_1669406 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669431 : List Nat := [1, 1, 3, 1, 2, 1, 1, 6, 5]
def baseStart_1669431 : Nat := 118140960795 + 1669431 * 2 ^ 59
def prefixEnd_1669431 : Nat := 4983230072969 + 3 ^ 40 * 1669431 * 2
def baseEnd_1669431 : Nat := 380986898896072478771081

theorem tailTrace_1669431 : CollatzResearch.WordTrace tailWord_1669431 prefixEnd_1669431 380986898896072478771081 := by
  unfold tailWord_1669431
  simp only [CollatzResearch.WordTrace]
  refine ⟨60889150814944077960656147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40592767209962718640437431 60889150814944077960656147)
  ·
    refine ⟨91333726222416116940984221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60889150814944077960656147 91333726222416116940984221)
    ·
      refine ⟨34250147333406043852869083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91333726222416116940984221 34250147333406043852869083)
      ·
        refine ⟨51375221000109065779303625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34250147333406043852869083 51375221000109065779303625)
        ·
          refine ⟨38531415750081799334477719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51375221000109065779303625 38531415750081799334477719)
          ·
            refine ⟨57797123625122699001716579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38531415750081799334477719 57797123625122699001716579)
            ·
              refine ⟨86695685437684048502574869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57797123625122699001716579 86695685437684048502574869)
              ·
                refine ⟨4063860254891439773558197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 86695685437684048502574869 4063860254891439773558197)
                ·
                  refine ⟨380986898896072478771081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4063860254891439773558197 380986898896072478771081)
                  ·
                    rfl

theorem cell21_1669431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 6, 5].length) (baseStart_1669431 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669431 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669431 prefixEnd_1669431 := by exact prefixLift 1669431
  have htrace : WordTrace (prefixWord ++ tailWord_1669431) baseStart_1669431 baseEnd_1669431 := by
    simpa [prefixWord, tailWord_1669431, baseEnd_1669431] using wordTrace_append hprefix tailTrace_1669431
  have hstable : (prefixWord ++ tailWord_1669431).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669431).length < 2 ^ (prefixWord ++ tailWord_1669431).sum := by decide
  have hdescent : baseEnd_1669431 < baseStart_1669431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669468 : List Nat := [2, 2, 4, 3, 2, 1, 1, 6]
def baseStart_1669468 : Nat := 118140960795 + 1669468 * 2 ^ 59
def prefixEnd_1669468 : Nat := 4983230072969 + 3 ^ 40 * 1669468 * 2
def baseEnd_1669468 : Nat := 126998447600056212218113

theorem tailTrace_1669468 : CollatzResearch.WordTrace tailWord_1669468 prefixEnd_1669468 126998447600056212218113 := by
  unfold tailWord_1669468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30445250157905016639876529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40593666877206688853168705 30445250157905016639876529)
  ·
    refine ⟨22833937618428762479907397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30445250157905016639876529 22833937618428762479907397)
    ·
      refine ⟨4281363303455392964982637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22833937618428762479907397 4281363303455392964982637)
      ·
        refine ⟨1605511238795772361868489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4281363303455392964982637 1605511238795772361868489)
        ·
          refine ⟨1204133429096829271401367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605511238795772361868489 1204133429096829271401367)
          ·
            refine ⟨1806200143645243907102051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204133429096829271401367 1806200143645243907102051)
            ·
              refine ⟨2709300215467865860653077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806200143645243907102051 2709300215467865860653077)
              ·
                refine ⟨126998447600056212218113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2709300215467865860653077 126998447600056212218113)
                ·
                  rfl

theorem cell21_1669468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 1, 6].length) (baseStart_1669468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669468 prefixEnd_1669468 := by exact prefixLift 1669468
  have htrace : WordTrace (prefixWord ++ tailWord_1669468) baseStart_1669468 baseEnd_1669468 := by
    simpa [prefixWord, tailWord_1669468, baseEnd_1669468] using wordTrace_append hprefix tailTrace_1669468
  have hstable : (prefixWord ++ tailWord_1669468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669468).length < 2 ^ (prefixWord ++ tailWord_1669468).sum := by decide
  have hdescent : baseEnd_1669468 < baseStart_1669468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669479 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 4]
def baseStart_1669479 : Nat := 118140960795 + 1669479 * 2 ^ 59
def prefixEnd_1669479 : Nat := 4983230072969 + 3 ^ 40 * 1669479 * 2
def baseEnd_1669479 : Nat := 380997853150035061970983

theorem tailTrace_1669479 : CollatzResearch.WordTrace tailWord_1669479 prefixEnd_1669479 380997853150035061970983 := by
  unfold tailWord_1669479
  simp only [CollatzResearch.WordTrace]
  refine ⟨60890901518770182158403491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40593934345846788105602327 60890901518770182158403491)
  ·
    refine ⟨91336352278155273237605237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60890901518770182158403491 91336352278155273237605237)
    ·
      refine ⟨8562783026077056866025491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91336352278155273237605237 8562783026077056866025491)
      ·
        refine ⟨12844174539115585299038237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562783026077056866025491 12844174539115585299038237)
        ·
          refine ⟨4816565452168344487139339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12844174539115585299038237 4816565452168344487139339)
          ·
            refine ⟨7224848178252516730709009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4816565452168344487139339 7224848178252516730709009)
            ·
              refine ⟨5418636133689387548031757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7224848178252516730709009 5418636133689387548031757)
              ·
                refine ⟨2031988550133520330511909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5418636133689387548031757 2031988550133520330511909)
                ·
                  refine ⟨380997853150035061970983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2031988550133520330511909 380997853150035061970983)
                  ·
                    rfl

theorem cell21_1669479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 4].length) (baseStart_1669479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669479 prefixEnd_1669479 := by exact prefixLift 1669479
  have htrace : WordTrace (prefixWord ++ tailWord_1669479) baseStart_1669479 baseEnd_1669479 := by
    simpa [prefixWord, tailWord_1669479, baseEnd_1669479] using wordTrace_append hprefix tailTrace_1669479
  have hstable : (prefixWord ++ tailWord_1669479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669479).length < 2 ^ (prefixWord ++ tailWord_1669479).sum := by decide
  have hdescent : baseEnd_1669479 < baseStart_1669479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669690 : List Nat := [3, 1, 1, 1, 3, 4, 1, 1, 6]
def baseStart_1669690 : Nat := 118140960795 + 1669690 * 2 ^ 59
def prefixEnd_1669690 : Nat := 4983230072969 + 3 ^ 40 * 1669690 * 2
def baseEnd_1669690 : Nat := 381046006224745583953885

theorem tailTrace_1669690 : CollatzResearch.WordTrace tailWord_1669690 prefixEnd_1669690 381046006224745583953885 := by
  unfold tailWord_1669690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15224649330251441298583631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40599064880670510129556349 15224649330251441298583631)
  ·
    refine ⟨22836973995377161947875447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15224649330251441298583631 22836973995377161947875447)
    ·
      refine ⟨34255460993065742921813171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22836973995377161947875447 34255460993065742921813171)
      ·
        refine ⟨51383191489598614382719757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34255460993065742921813171 51383191489598614382719757)
        ·
          refine ⟨19268696808599480393519909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51383191489598614382719757 19268696808599480393519909)
          ·
            refine ⟨3612880651612402573784983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19268696808599480393519909 3612880651612402573784983)
            ·
              refine ⟨5419320977418603860677475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3612880651612402573784983 5419320977418603860677475)
              ·
                refine ⟨8128981466127905791016213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5419320977418603860677475 8128981466127905791016213)
                ·
                  refine ⟨381046006224745583953885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8128981466127905791016213 381046006224745583953885)
                  ·
                    rfl

theorem cell21_1669690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 1, 6].length) (baseStart_1669690 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669690 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669690 prefixEnd_1669690 := by exact prefixLift 1669690
  have htrace : WordTrace (prefixWord ++ tailWord_1669690) baseStart_1669690 baseEnd_1669690 := by
    simpa [prefixWord, tailWord_1669690, baseEnd_1669690] using wordTrace_append hprefix tailTrace_1669690
  have hstable : (prefixWord ++ tailWord_1669690).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669690).length < 2 ^ (prefixWord ++ tailWord_1669690).sum := by decide
  have hdescent : baseEnd_1669690 < baseStart_1669690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669693 : List Nat := [1, 4, 1, 3, 2, 1, 2, 4, 3]
def baseStart_1669693 : Nat := 118140960795 + 1669693 * 2 ^ 59
def prefixEnd_1669693 : Nat := 4983230072969 + 3 ^ 40 * 1669693 * 2
def baseEnd_1669693 : Nat := 381046690865618245403879

theorem tailTrace_1669693 : CollatzResearch.WordTrace tailWord_1669693 prefixEnd_1669693 381046690865618245403879 := by
  unfold tailWord_1669693
  simp only [CollatzResearch.WordTrace]
  refine ⟨60898706739994896706693733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40599137826663264471129155 60898706739994896706693733)
  ·
    refine ⟨11418507513749043132505075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60898706739994896706693733 11418507513749043132505075)
    ·
      refine ⟨17127761270623564698757613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11418507513749043132505075 17127761270623564698757613)
      ·
        refine ⟨6422910476483836762034105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17127761270623564698757613 6422910476483836762034105)
        ·
          refine ⟨4817182857362877571525579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6422910476483836762034105 4817182857362877571525579)
          ·
            refine ⟨7225774286044316357288369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817182857362877571525579 7225774286044316357288369)
            ·
              refine ⟨5419330714533237267966277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7225774286044316357288369 5419330714533237267966277)
              ·
                refine ⟨1016124508974981987743677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5419330714533237267966277 1016124508974981987743677)
                ·
                  refine ⟨381046690865618245403879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016124508974981987743677 381046690865618245403879)
                  ·
                    rfl

theorem cell21_1669693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 3].length) (baseStart_1669693 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669693 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669693 prefixEnd_1669693 := by exact prefixLift 1669693
  have htrace : WordTrace (prefixWord ++ tailWord_1669693) baseStart_1669693 baseEnd_1669693 := by
    simpa [prefixWord, tailWord_1669693, baseEnd_1669693] using wordTrace_append hprefix tailTrace_1669693
  have hstable : (prefixWord ++ tailWord_1669693).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669693).length < 2 ^ (prefixWord ++ tailWord_1669693).sum := by decide
  have hdescent : baseEnd_1669693 < baseStart_1669693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669828 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 5]
def baseStart_1669828 : Nat := 118140960795 + 1669828 * 2 ^ 59
def prefixEnd_1669828 : Nat := 4983230072969 + 3 ^ 40 * 1669828 * 2
def baseEnd_1669828 : Nat := 381077499704888010653603

theorem tailTrace_1669828 : CollatzResearch.WordTrace tailWord_1669828 prefixEnd_1669828 381077499704888010653603 := by
  unfold tailWord_1669828
  simp only [CollatzResearch.WordTrace]
  refine ⟨30451815297252907381429069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40602420396337209841905425 30451815297252907381429069)
  ·
    refine ⟨11419430736469840268035901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30451815297252907381429069 11419430736469840268035901)
    ·
      refine ⟨4282286526176190100513463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11419430736469840268035901 4282286526176190100513463)
      ·
        refine ⟨6423429789264285150770195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4282286526176190100513463 6423429789264285150770195)
        ·
          refine ⟨9635144683896427726155293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6423429789264285150770195 9635144683896427726155293)
          ·
            refine ⟨3613179256461160397308235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9635144683896427726155293 3613179256461160397308235)
            ·
              refine ⟨5419768884691740595962353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613179256461160397308235 5419768884691740595962353)
              ·
                refine ⟨4064826663518805446971765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5419768884691740595962353 4064826663518805446971765)
                ·
                  refine ⟨381077499704888010653603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4064826663518805446971765 381077499704888010653603)
                  ·
                    rfl

theorem cell21_1669828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 5].length) (baseStart_1669828 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669828 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669828 prefixEnd_1669828 := by exact prefixLift 1669828
  have htrace : WordTrace (prefixWord ++ tailWord_1669828) baseStart_1669828 baseEnd_1669828 := by
    simpa [prefixWord, tailWord_1669828, baseEnd_1669828] using wordTrace_append hprefix tailTrace_1669828
  have hstable : (prefixWord ++ tailWord_1669828).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669828).length < 2 ^ (prefixWord ++ tailWord_1669828).sum := by decide
  have hdescent : baseEnd_1669828 < baseStart_1669828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669859 : List Nat := [1, 1, 1, 7, 1, 1, 3, 2, 4]
def baseStart_1669859 : Nat := 118140960795 + 1669859 * 2 ^ 59
def prefixEnd_1669859 : Nat := 4983230072969 + 3 ^ 40 * 1669859 * 2
def baseEnd_1669859 : Nat := 381084574327238845636873

theorem tailTrace_1669859 : CollatzResearch.WordTrace tailWord_1669859 prefixEnd_1669859 381084574327238845636873 := by
  unfold tailWord_1669859
  simp only [CollatzResearch.WordTrace]
  refine ⟨60904761257393507057236631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40603174171595671371491087 60904761257393507057236631)
  ·
    refine ⟨91357141886090260585854947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60904761257393507057236631 91357141886090260585854947)
    ·
      refine ⟨137035712829135390878782421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91357141886090260585854947 137035712829135390878782421)
      ·
        refine ⟨3211774519432860723721463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 137035712829135390878782421 3211774519432860723721463)
        ·
          refine ⟨4817661779149291085582195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3211774519432860723721463 4817661779149291085582195)
          ·
            refine ⟨7226492668723936628373293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4817661779149291085582195 7226492668723936628373293)
            ·
              refine ⟨2709934750771476235639985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7226492668723936628373293 2709934750771476235639985)
              ·
                refine ⟨2032451063078607176729989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2709934750771476235639985 2032451063078607176729989)
                ·
                  refine ⟨381084574327238845636873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2032451063078607176729989 381084574327238845636873)
                  ·
                    rfl

theorem cell21_1669859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 2, 4].length) (baseStart_1669859 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669859 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669859 prefixEnd_1669859 := by exact prefixLift 1669859
  have htrace : WordTrace (prefixWord ++ tailWord_1669859) baseStart_1669859 baseEnd_1669859 := by
    simpa [prefixWord, tailWord_1669859, baseEnd_1669859] using wordTrace_append hprefix tailTrace_1669859
  have hstable : (prefixWord ++ tailWord_1669859).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669859).length < 2 ^ (prefixWord ++ tailWord_1669859).sum := by decide
  have hdescent : baseEnd_1669859 < baseStart_1669859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669890 : List Nat := [3, 4, 1, 1, 1, 2, 4, 5]
def baseStart_1669890 : Nat := 118140960795 + 1669890 * 2 ^ 59
def prefixEnd_1669890 : Nat := 4983230072969 + 3 ^ 40 * 1669890 * 2
def baseEnd_1669890 : Nat := 127030549649863226873381

theorem tailTrace_1669890 : CollatzResearch.WordTrace tailWord_1669890 prefixEnd_1669890 127030549649863226873381 := by
  unfold tailWord_1669890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226472980070299837903781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40603927946854132901076749 15226472980070299837903781)
  ·
    refine ⟨2854963683763181219606959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15226472980070299837903781 2854963683763181219606959)
    ·
      refine ⟨4282445525644771829410439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2854963683763181219606959 4282445525644771829410439)
      ·
        refine ⟨6423668288467157744115659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4282445525644771829410439 6423668288467157744115659)
        ·
          refine ⟨9635502432700736616173489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6423668288467157744115659 9635502432700736616173489)
          ·
            refine ⟨7226626824525552462130117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9635502432700736616173489 7226626824525552462130117)
            ·
              refine ⟨1354992529598541086649397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7226626824525552462130117 1354992529598541086649397)
              ·
                refine ⟨127030549649863226873381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1354992529598541086649397 127030549649863226873381)
                ·
                  rfl

theorem cell21_1669890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 4, 5].length) (baseStart_1669890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669890 prefixEnd_1669890 := by exact prefixLift 1669890
  have htrace : WordTrace (prefixWord ++ tailWord_1669890) baseStart_1669890 baseEnd_1669890 := by
    simpa [prefixWord, tailWord_1669890, baseEnd_1669890] using wordTrace_append hprefix tailTrace_1669890
  have hstable : (prefixWord ++ tailWord_1669890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669890).length < 2 ^ (prefixWord ++ tailWord_1669890).sum := by decide
  have hdescent : baseEnd_1669890 < baseStart_1669890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669921 : List Nat := [1, 2, 3, 2, 1, 2, 5, 2, 3]
def baseStart_1669921 : Nat := 118140960795 + 1669921 * 2 ^ 59
def prefixEnd_1669921 : Nat := 4983230072969 + 3 ^ 40 * 1669921 * 2
def baseEnd_1669921 : Nat := 381098723571940515603413

theorem tailTrace_1669921 : CollatzResearch.WordTrace tailWord_1669921 prefixEnd_1669921 381098723571940515603413 := by
  unfold tailWord_1669921
  simp only [CollatzResearch.WordTrace]
  refine ⟨60907022583168891645993617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40604681722112594430662411 60907022583168891645993617)
  ·
    refine ⟨45680266937376668734495213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60907022583168891645993617 45680266937376668734495213)
    ·
      refine ⟨17130100101516250775435705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45680266937376668734495213 17130100101516250775435705)
      ·
        refine ⟨12847575076137188081576779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17130100101516250775435705 12847575076137188081576779)
        ·
          refine ⟨19271362614205782122365169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12847575076137188081576779 19271362614205782122365169)
          ·
            refine ⟨14453521960654336591773877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19271362614205782122365169 14453521960654336591773877)
            ·
              refine ⟨1355017683811344055478801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14453521960654336591773877 1355017683811344055478801)
              ·
                refine ⟨1016263262858508041609101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355017683811344055478801 1016263262858508041609101)
                ·
                  refine ⟨381098723571940515603413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016263262858508041609101 381098723571940515603413)
                  ·
                    rfl

theorem cell21_1669921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 5, 2, 3].length) (baseStart_1669921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669921 prefixEnd_1669921 := by exact prefixLift 1669921
  have htrace : WordTrace (prefixWord ++ tailWord_1669921) baseStart_1669921 baseEnd_1669921 := by
    simpa [prefixWord, tailWord_1669921, baseEnd_1669921] using wordTrace_append hprefix tailTrace_1669921
  have hstable : (prefixWord ++ tailWord_1669921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669921).length < 2 ^ (prefixWord ++ tailWord_1669921).sum := by decide
  have hdescent : baseEnd_1669921 < baseStart_1669921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1669932 : List Nat := [2, 2, 1, 1, 1, 4, 4, 6]
def baseStart_1669932 : Nat := 118140960795 + 1669932 * 2 ^ 59
def prefixEnd_1669932 : Nat := 4983230072969 + 3 ^ 40 * 1669932 * 2
def baseEnd_1669932 : Nat := 127033744640602313640019

theorem tailTrace_1669932 : CollatzResearch.WordTrace tailWord_1669932 prefixEnd_1669932 127033744640602313640019 := by
  unfold tailWord_1669932
  simp only [CollatzResearch.WordTrace]
  refine ⟨30453711893064520262322025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40604949190752693683096033 30453711893064520262322025)
  ·
    refine ⟨22840283919798390196741519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30453711893064520262322025 22840283919798390196741519)
    ·
      refine ⟨34260425879697585295112279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22840283919798390196741519 34260425879697585295112279)
      ·
        refine ⟨51390638819546377942668419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34260425879697585295112279 51390638819546377942668419)
        ·
          refine ⟨77085958229319566914002629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51390638819546377942668419 77085958229319566914002629)
          ·
            refine ⟨14453617167997418796375493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77085958229319566914002629 14453617167997418796375493)
            ·
              refine ⟨2710053218999516024320405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14453617167997418796375493 2710053218999516024320405)
              ·
                refine ⟨127033744640602313640019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2710053218999516024320405 127033744640602313640019)
                ·
                  rfl

theorem cell21_1669932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 4, 6].length) (baseStart_1669932 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1669932 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1669932 prefixEnd_1669932 := by exact prefixLift 1669932
  have htrace : WordTrace (prefixWord ++ tailWord_1669932) baseStart_1669932 baseEnd_1669932 := by
    simpa [prefixWord, tailWord_1669932, baseEnd_1669932] using wordTrace_append hprefix tailTrace_1669932
  have hstable : (prefixWord ++ tailWord_1669932).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1669932).length < 2 ^ (prefixWord ++ tailWord_1669932).sum := by decide
  have hdescent : baseEnd_1669932 < baseStart_1669932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1669932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670039 : List Nat := [1, 1, 3, 3, 1, 2, 4, 1, 5]
def baseStart_1670039 : Nat := 118140960795 + 1670039 * 2 ^ 59
def prefixEnd_1670039 : Nat := 4983230072969 + 3 ^ 40 * 1670039 * 2
def baseEnd_1670039 : Nat := 381125652779598532636505

theorem tailTrace_1670039 : CollatzResearch.WordTrace tailWord_1670039 prefixEnd_1670039 381125652779598532636505 := by
  unfold tailWord_1670039
  simp only [CollatzResearch.WordTrace]
  refine ⟨60911326396741397798789171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40607550931160931865859447 60911326396741397798789171)
  ·
    refine ⟨91366989595112096698183757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60911326396741397798789171 91366989595112096698183757)
    ·
      refine ⟨34262621098167036261818909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91366989595112096698183757 34262621098167036261818909)
      ·
        refine ⟨12848482911812638598182091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34262621098167036261818909 12848482911812638598182091)
        ·
          refine ⟨19272724367718957897273137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12848482911812638598182091 19272724367718957897273137)
          ·
            refine ⟨14454543275789218422954853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19272724367718957897273137 14454543275789218422954853)
            ·
              refine ⟨2710226864210478454304035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14454543275789218422954853 2710226864210478454304035)
              ·
                refine ⟨4065340296315717681456053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2710226864210478454304035 4065340296315717681456053)
                ·
                  refine ⟨381125652779598532636505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4065340296315717681456053 381125652779598532636505)
                  ·
                    rfl

theorem cell21_1670039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 4, 1, 5].length) (baseStart_1670039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670039 prefixEnd_1670039 := by exact prefixLift 1670039
  have htrace : WordTrace (prefixWord ++ tailWord_1670039) baseStart_1670039 baseEnd_1670039 := by
    simpa [prefixWord, tailWord_1670039, baseEnd_1670039] using wordTrace_append hprefix tailTrace_1670039
  have hstable : (prefixWord ++ tailWord_1670039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670039).length < 2 ^ (prefixWord ++ tailWord_1670039).sum := by decide
  have hdescent : baseEnd_1670039 < baseStart_1670039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670073 : List Nat := [1, 2, 1, 4, 2, 4, 1, 3, 3]
def baseStart_1670073 : Nat := 118140960795 + 1670073 * 2 ^ 59
def prefixEnd_1670073 : Nat := 4983230072969 + 3 ^ 40 * 1670073 * 2
def baseEnd_1670073 : Nat := 381133412042822029069769

theorem tailTrace_1670073 : CollatzResearch.WordTrace tailWord_1670073 prefixEnd_1670073 381133412042822029069769 := by
  unfold tailWord_1670073
  simp only [CollatzResearch.WordTrace]
  refine ⟨60912566478618221605526873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40608377652412147737017915 60912566478618221605526873)
  ·
    refine ⟨45684424858963666204145155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60912566478618221605526873 45684424858963666204145155)
    ·
      refine ⟨68526637288445499306217733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45684424858963666204145155 68526637288445499306217733)
      ·
        refine ⟨12848744491583531119915825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68526637288445499306217733 12848744491583531119915825)
        ·
          refine ⟨9636558368687648339936869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12848744491583531119915825 9636558368687648339936869)
          ·
            refine ⟨1806854694128934063738163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9636558368687648339936869 1806854694128934063738163)
            ·
              refine ⟨2710282041193401095607245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806854694128934063738163 2710282041193401095607245)
              ·
                refine ⟨1016355765447525410852717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2710282041193401095607245 1016355765447525410852717)
                ·
                  refine ⟨381133412042822029069769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016355765447525410852717 381133412042822029069769)
                  ·
                    rfl

theorem cell21_1670073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 3, 3].length) (baseStart_1670073 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670073 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670073 prefixEnd_1670073 := by exact prefixLift 1670073
  have htrace : WordTrace (prefixWord ++ tailWord_1670073) baseStart_1670073 baseEnd_1670073 := by
    simpa [prefixWord, tailWord_1670073, baseEnd_1670073] using wordTrace_append hprefix tailTrace_1670073
  have hstable : (prefixWord ++ tailWord_1670073).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670073).length < 2 ^ (prefixWord ++ tailWord_1670073).sum := by decide
  have hdescent : baseEnd_1670073 < baseStart_1670073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670101 : List Nat := [1, 3, 2, 3, 3, 1, 2, 6]
def baseStart_1670101 : Nat := 118140960795 + 1670101 * 2 ^ 59
def prefixEnd_1670101 : Nat := 4983230072969 + 3 ^ 40 * 1670101 * 2
def baseEnd_1670101 : Nat := 127046600674766734201015

theorem tailTrace_1670101 : CollatzResearch.WordTrace tailWord_1670101 prefixEnd_1670101 127046600674766734201015 := by
  unfold tailWord_1670101
  simp only [CollatzResearch.WordTrace]
  refine ⟨60913587722516782387546157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40609058481677854925030771 60913587722516782387546157)
  ·
    refine ⟨22842595395943793395329809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60913587722516782387546157 22842595395943793395329809)
    ·
      refine ⟨17131946546957845046497357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22842595395943793395329809 17131946546957845046497357)
      ·
        refine ⟨6424479955109191892436509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17131946546957845046497357 6424479955109191892436509)
        ·
          refine ⟨2409179983165946959663691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6424479955109191892436509 2409179983165946959663691)
          ·
            refine ⟨3613769974748920439495537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409179983165946959663691 3613769974748920439495537)
            ·
              refine ⟨2710327481061690329621653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3613769974748920439495537 2710327481061690329621653)
              ·
                refine ⟨127046600674766734201015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2710327481061690329621653 127046600674766734201015)
                ·
                  rfl

theorem cell21_1670101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 2, 6].length) (baseStart_1670101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670101 prefixEnd_1670101 := by exact prefixLift 1670101
  have htrace : WordTrace (prefixWord ++ tailWord_1670101) baseStart_1670101 baseEnd_1670101 := by
    simpa [prefixWord, tailWord_1670101, baseEnd_1670101] using wordTrace_append hprefix tailTrace_1670101
  have hstable : (prefixWord ++ tailWord_1670101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670101).length < 2 ^ (prefixWord ++ tailWord_1670101).sum := by decide
  have hdescent : baseEnd_1670101 < baseStart_1670101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670177 : List Nat := [1, 2, 3, 2, 3, 2, 3, 5]
def baseStart_1670177 : Nat := 118140960795 + 1670177 * 2 ^ 59
def prefixEnd_1670177 : Nat := 4983230072969 + 3 ^ 40 * 1670177 * 2
def baseEnd_1670177 : Nat := 127052382086580319778741

theorem tailTrace_1670177 : CollatzResearch.WordTrace tailWord_1670177 prefixEnd_1670177 127052382086580319778741 := by
  unfold tailWord_1670177
  simp only [CollatzResearch.WordTrace]
  refine ⟨60916359670241447367312785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40610906446827631578208523 60916359670241447367312785)
  ·
    refine ⟨45687269752681085525484589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60916359670241447367312785 45687269752681085525484589)
    ·
      refine ⟨17132726157255407072056721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45687269752681085525484589 17132726157255407072056721)
      ·
        refine ⟨12849544617941555304042541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17132726157255407072056721 12849544617941555304042541)
        ·
          refine ⟨4818579231728083239015953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12849544617941555304042541 4818579231728083239015953)
          ·
            refine ⟨3613934423796062429261965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4818579231728083239015953 3613934423796062429261965)
            ·
              refine ⟨1355225408923523410973237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3613934423796062429261965 1355225408923523410973237)
              ·
                refine ⟨127052382086580319778741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1355225408923523410973237 127052382086580319778741)
                ·
                  rfl

theorem cell21_1670177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 3, 5].length) (baseStart_1670177 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670177 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670177 prefixEnd_1670177 := by exact prefixLift 1670177
  have htrace : WordTrace (prefixWord ++ tailWord_1670177) baseStart_1670177 baseEnd_1670177 := by
    simpa [prefixWord, tailWord_1670177, baseEnd_1670177] using wordTrace_append hprefix tailTrace_1670177
  have hstable : (prefixWord ++ tailWord_1670177).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670177).length < 2 ^ (prefixWord ++ tailWord_1670177).sum := by decide
  have hdescent : baseEnd_1670177 < baseStart_1670177 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670236 : List Nat := [2, 2, 4, 1, 1, 1, 3, 7]
def baseStart_1670236 : Nat := 118140960795 + 1670236 * 2 ^ 59
def prefixEnd_1670236 : Nat := 4983230072969 + 3 ^ 40 * 1670236 * 2
def baseEnd_1670236 : Nat := 127056870287856655950923

theorem tailTrace_1670236 : CollatzResearch.WordTrace tailWord_1670236 prefixEnd_1670236 127056870287856655950923 := by
  unfold tailWord_1670236
  simp only [CollatzResearch.WordTrace]
  refine ⟨30459255788513850221855281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40612341051351800295807041 30459255788513850221855281)
  ·
    refine ⟨22844441841385387666391461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30459255788513850221855281 22844441841385387666391461)
    ·
      refine ⟨4283332845259760187448399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22844441841385387666391461 4283332845259760187448399)
      ·
        refine ⟨6424999267889640281172599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283332845259760187448399 6424999267889640281172599)
        ·
          refine ⟨9637498901834460421758899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6424999267889640281172599 9637498901834460421758899)
          ·
            refine ⟨14456248352751690632638349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9637498901834460421758899 14456248352751690632638349)
            ·
              refine ⟨5421093132281883987239381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14456248352751690632638349 5421093132281883987239381)
              ·
                refine ⟨127056870287856655950923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5421093132281883987239381 127056870287856655950923)
                ·
                  rfl

theorem cell21_1670236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 7].length) (baseStart_1670236 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670236 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670236 prefixEnd_1670236 := by exact prefixLift 1670236
  have htrace : WordTrace (prefixWord ++ tailWord_1670236) baseStart_1670236 baseEnd_1670236 := by
    simpa [prefixWord, tailWord_1670236, baseEnd_1670236] using wordTrace_append hprefix tailTrace_1670236
  have hstable : (prefixWord ++ tailWord_1670236).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670236).length < 2 ^ (prefixWord ++ tailWord_1670236).sum := by decide
  have hdescent : baseEnd_1670236 < baseStart_1670236 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670242 : List Nat := [3, 3, 2, 2, 1, 3, 1, 3, 3]
def baseStart_1670242 : Nat := 118140960795 + 1670242 * 2 ^ 59
def prefixEnd_1670242 : Nat := 4983230072969 + 3 ^ 40 * 1670242 * 2
def baseEnd_1670242 : Nat := 381171980145315290752757

theorem tailTrace_1670242 : CollatzResearch.WordTrace tailWord_1670242 prefixEnd_1670242 381171980145315290752757 := by
  unfold tailWord_1670242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15229682603751490867107245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40612486943337308978952653 15229682603751490867107245)
  ·
    refine ⟨5711130976406809075165217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15229682603751490867107245 5711130976406809075165217)
    ·
      refine ⟨4283348232305106806373913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5711130976406809075165217 4283348232305106806373913)
      ·
        refine ⟨3212511174228830104780435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4283348232305106806373913 3212511174228830104780435)
        ·
          refine ⟨4818766761343245157170653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3212511174228830104780435 4818766761343245157170653)
          ·
            refine ⟨1807037535503716933938995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4818766761343245157170653 1807037535503716933938995)
            ·
              refine ⟨2710556303255575400908493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807037535503716933938995 2710556303255575400908493)
              ·
                refine ⟨1016458613720840775340685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2710556303255575400908493 1016458613720840775340685)
                ·
                  refine ⟨381171980145315290752757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016458613720840775340685 381171980145315290752757)
                  ·
                    rfl

theorem cell21_1670242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 3].length) (baseStart_1670242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670242 prefixEnd_1670242 := by exact prefixLift 1670242
  have htrace : WordTrace (prefixWord ++ tailWord_1670242) baseStart_1670242 baseEnd_1670242 := by
    simpa [prefixWord, tailWord_1670242, baseEnd_1670242] using wordTrace_append hprefix tailTrace_1670242
  have hstable : (prefixWord ++ tailWord_1670242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670242).length < 2 ^ (prefixWord ++ tailWord_1670242).sum := by decide
  have hdescent : baseEnd_1670242 < baseStart_1670242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670267 : List Nat := [1, 1, 1, 1, 1, 4, 1, 8, 3]
def baseStart_1670267 : Nat := 118140960795 + 1670267 * 2 ^ 59
def prefixEnd_1670267 : Nat := 4983230072969 + 3 ^ 40 * 1670267 * 2
def baseEnd_1670267 : Nat := 381177685485920802836039

theorem tailTrace_1670267 : CollatzResearch.WordTrace tailWord_1670267 prefixEnd_1670267 381177685485920802836039 := by
  unfold tailWord_1670267
  simp only [CollatzResearch.WordTrace]
  refine ⟨60919642239915392738089055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40613094826610261825392703 60919642239915392738089055)
  ·
    refine ⟨91379463359873089107133583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60919642239915392738089055 91379463359873089107133583)
    ·
      refine ⟨137069195039809633660700375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91379463359873089107133583 137069195039809633660700375)
      ·
        refine ⟨205603792559714450491050563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137069195039809633660700375 205603792559714450491050563)
        ·
          refine ⟨308405688839571675736575845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205603792559714450491050563 308405688839571675736575845)
          ·
            refine ⟨57826066657419689200607971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 308405688839571675736575845 57826066657419689200607971)
            ·
              refine ⟨86739099986129533800911957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57826066657419689200607971 86739099986129533800911957)
              ·
                refine ⟨1016473827962455474229437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 86739099986129533800911957 1016473827962455474229437)
                ·
                  refine ⟨381177685485920802836039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016473827962455474229437 381177685485920802836039)
                  ·
                    rfl

theorem cell21_1670267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 3].length) (baseStart_1670267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670267 prefixEnd_1670267 := by exact prefixLift 1670267
  have htrace : WordTrace (prefixWord ++ tailWord_1670267) baseStart_1670267 baseEnd_1670267 := by
    simpa [prefixWord, tailWord_1670267, baseEnd_1670267] using wordTrace_append hprefix tailTrace_1670267
  have hstable : (prefixWord ++ tailWord_1670267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670267).length < 2 ^ (prefixWord ++ tailWord_1670267).sum := by decide
  have hdescent : baseEnd_1670267 < baseStart_1670267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670433 : List Nat := [1, 2, 3, 2, 1, 1, 1, 6, 4]
def baseStart_1670433 : Nat := 118140960795 + 1670433 * 2 ^ 59
def prefixEnd_1670433 : Nat := 4983230072969 + 3 ^ 40 * 1670433 * 2
def baseEnd_1670433 : Nat := 381215568947541403069033

theorem tailTrace_1670433 : CollatzResearch.WordTrace tailWord_1670433 prefixEnd_1670433 381215568947541403069033 := by
  unfold tailWord_1670433
  simp only [CollatzResearch.WordTrace]
  refine ⟨60925696757314003088631953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40617131171542668725754635 60925696757314003088631953)
  ·
    refine ⟨45694272567985502316473965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60925696757314003088631953 45694272567985502316473965)
    ·
      refine ⟨17135352212994563368677737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45694272567985502316473965 17135352212994563368677737)
      ·
        refine ⟨12851514159745922526508303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17135352212994563368677737 12851514159745922526508303)
        ·
          refine ⟨19277271239618883789762455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12851514159745922526508303 19277271239618883789762455)
          ·
            refine ⟨28915906859428325684643683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19277271239618883789762455 28915906859428325684643683)
            ·
              refine ⟨43373860289142488526965525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28915906859428325684643683 43373860289142488526965525)
              ·
                refine ⟨2033149701053554149701509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43373860289142488526965525 2033149701053554149701509)
                ·
                  refine ⟨381215568947541403069033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033149701053554149701509 381215568947541403069033)
                  ·
                    rfl

theorem cell21_1670433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 6, 4].length) (baseStart_1670433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670433 prefixEnd_1670433 := by exact prefixLift 1670433
  have htrace : WordTrace (prefixWord ++ tailWord_1670433) baseStart_1670433 baseEnd_1670433 := by
    simpa [prefixWord, tailWord_1670433, baseEnd_1670433] using wordTrace_append hprefix tailTrace_1670433
  have hstable : (prefixWord ++ tailWord_1670433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670433).length < 2 ^ (prefixWord ++ tailWord_1670433).sum := by decide
  have hdescent : baseEnd_1670433 < baseStart_1670433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670450 : List Nat := [3, 2, 1, 1, 4, 2, 1, 3, 4]
def baseStart_1670450 : Nat := 118140960795 + 1670450 * 2 ^ 59
def prefixEnd_1670450 : Nat := 4983230072969 + 3 ^ 40 * 1670450 * 2
def baseEnd_1670450 : Nat := 381219448579153151285665

theorem tailTrace_1670450 : CollatzResearch.WordTrace tailWord_1670450 prefixEnd_1670450 381219448579153151285665 := by
  unfold tailWord_1670450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15231579199563103748000201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40617544532168276661333869 15231579199563103748000201)
  ·
    refine ⟨11423684399672327811000151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15231579199563103748000201 11423684399672327811000151)
    ·
      refine ⟨17135526599508491716500227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11423684399672327811000151 17135526599508491716500227)
      ·
        refine ⟨25703289899262737574750341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17135526599508491716500227 25703289899262737574750341)
        ·
          refine ⟨4819366856111763295265689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25703289899262737574750341 4819366856111763295265689)
          ·
            refine ⟨3614525142083822471449267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4819366856111763295265689 3614525142083822471449267)
            ·
              refine ⟨5421787713125733707173901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3614525142083822471449267 5421787713125733707173901)
              ·
                refine ⟨2033170392422150140190213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5421787713125733707173901 2033170392422150140190213)
                ·
                  refine ⟨381219448579153151285665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033170392422150140190213 381219448579153151285665)
                  ·
                    rfl

theorem cell21_1670450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 3, 4].length) (baseStart_1670450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670450 prefixEnd_1670450 := by exact prefixLift 1670450
  have htrace : WordTrace (prefixWord ++ tailWord_1670450) baseStart_1670450 baseEnd_1670450 := by
    simpa [prefixWord, tailWord_1670450, baseEnd_1670450] using wordTrace_append hprefix tailTrace_1670450
  have hstable : (prefixWord ++ tailWord_1670450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670450).length < 2 ^ (prefixWord ++ tailWord_1670450).sum := by decide
  have hdescent : baseEnd_1670450 < baseStart_1670450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670529 : List Nat := [1, 2, 4, 3, 2, 1, 2, 3, 3]
def baseStart_1670529 : Nat := 118140960795 + 1670529 * 2 ^ 59
def prefixEnd_1670529 : Nat := 4983230072969 + 3 ^ 40 * 1670529 * 2
def baseEnd_1670529 : Nat := 381237477455466569468837

theorem tailTrace_1670529 : CollatzResearch.WordTrace tailWord_1670529 prefixEnd_1670529 381237477455466569468837 := by
  unfold tailWord_1670529
  simp only [CollatzResearch.WordTrace]
  refine ⟨60929198164966211484126641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40619465443310807656084427 60929198164966211484126641)
  ·
    refine ⟨45696898623724658613094981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60929198164966211484126641 45696898623724658613094981)
    ·
      refine ⟨8568168491948373489955309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45696898623724658613094981 8568168491948373489955309)
      ·
        refine ⟨3213063184480640058733241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8568168491948373489955309 3213063184480640058733241)
        ·
          refine ⟨2409797388360480044049931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3213063184480640058733241 2409797388360480044049931)
          ·
            refine ⟨3614696082540720066074897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409797388360480044049931 3614696082540720066074897)
            ·
              refine ⟨2711022061905540049556173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3614696082540720066074897 2711022061905540049556173)
              ·
                refine ⟨1016633273214577518583565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2711022061905540049556173 1016633273214577518583565)
                ·
                  refine ⟨381237477455466569468837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016633273214577518583565 381237477455466569468837)
                  ·
                    rfl

theorem cell21_1670529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 2, 3, 3].length) (baseStart_1670529 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670529 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670529 prefixEnd_1670529 := by exact prefixLift 1670529
  have htrace : WordTrace (prefixWord ++ tailWord_1670529) baseStart_1670529 baseEnd_1670529 := by
    simpa [prefixWord, tailWord_1670529, baseEnd_1670529] using wordTrace_append hprefix tailTrace_1670529
  have hstable : (prefixWord ++ tailWord_1670529).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670529).length < 2 ^ (prefixWord ++ tailWord_1670529).sum := by decide
  have hdescent : baseEnd_1670529 < baseStart_1670529 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670664 : List Nat := [2, 1, 3, 2, 1, 1, 6, 2, 3]
def baseStart_1670664 : Nat := 118140960795 + 1670664 * 2 ^ 59
def prefixEnd_1670664 : Nat := 4983230072969 + 3 ^ 40 * 1670664 * 2
def baseEnd_1670664 : Nat := 381268286294736334718561

theorem tailTrace_1670664 : CollatzResearch.WordTrace tailWord_1670664 prefixEnd_1670664 381268286294736334718561 := by
  unfold tailWord_1670664
  simp only [CollatzResearch.WordTrace]
  refine ⟨30467061009738564770145523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40622748012984753026860697 30467061009738564770145523)
  ·
    refine ⟨45700591514607847155218285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30467061009738564770145523 45700591514607847155218285)
    ·
      refine ⟨17137721817977942683206857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45700591514607847155218285 17137721817977942683206857)
      ·
        refine ⟨12853291363483457012405143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17137721817977942683206857 12853291363483457012405143)
        ·
          refine ⟨19279937045225185518607715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12853291363483457012405143 19279937045225185518607715)
          ·
            refine ⟨28919905567837778277911573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19279937045225185518607715 28919905567837778277911573)
            ·
              refine ⟨1355620573492395856777105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28919905567837778277911573 1355620573492395856777105)
              ·
                refine ⟨1016715430119296892582829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1355620573492395856777105 1016715430119296892582829)
                ·
                  refine ⟨381268286294736334718561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1016715430119296892582829 381268286294736334718561)
                  ·
                    rfl

theorem cell21_1670664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 6, 2, 3].length) (baseStart_1670664 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670664 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670664 prefixEnd_1670664 := by exact prefixLift 1670664
  have htrace : WordTrace (prefixWord ++ tailWord_1670664) baseStart_1670664 baseEnd_1670664 := by
    simpa [prefixWord, tailWord_1670664, baseEnd_1670664] using wordTrace_append hprefix tailTrace_1670664
  have hstable : (prefixWord ++ tailWord_1670664).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670664).length < 2 ^ (prefixWord ++ tailWord_1670664).sum := by decide
  have hdescent : baseEnd_1670664 < baseStart_1670664 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670675 : List Nat := [1, 1, 1, 2, 1, 6, 3, 6]
def baseStart_1670675 : Nat := 118140960795 + 1670675 * 2 ^ 59
def prefixEnd_1670675 : Nat := 4983230072969 + 3 ^ 40 * 1670675 * 2
def baseEnd_1670675 : Nat := 127090265548200920011735

theorem tailTrace_1670675 : CollatzResearch.WordTrace tailWord_1670675 prefixEnd_1670675 127090265548200920011735 := by
  unfold tailWord_1670675
  simp only [CollatzResearch.WordTrace]
  refine ⟨60934523222437278418941479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40623015481624852279294319 60934523222437278418941479)
  ·
    refine ⟨91401784833655917628412219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60934523222437278418941479 91401784833655917628412219)
    ·
      refine ⟨137102677250483876442618329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91401784833655917628412219 137102677250483876442618329)
      ·
        refine ⟨102827007937862907331963747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137102677250483876442618329 102827007937862907331963747)
        ·
          refine ⟨154240511906794360997945621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102827007937862907331963747 154240511906794360997945621)
          ·
            refine ⟨7230023995630985671778701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154240511906794360997945621 7230023995630985671778701)
            ·
              refine ⟨2711258998361619626917013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7230023995630985671778701 2711258998361619626917013)
              ·
                refine ⟨127090265548200920011735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2711258998361619626917013 127090265548200920011735)
                ·
                  rfl

theorem cell21_1670675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 3, 6].length) (baseStart_1670675 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670675 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670675 prefixEnd_1670675 := by exact prefixLift 1670675
  have htrace : WordTrace (prefixWord ++ tailWord_1670675) baseStart_1670675 baseEnd_1670675 := by
    simpa [prefixWord, tailWord_1670675, baseEnd_1670675] using wordTrace_append hprefix tailTrace_1670675
  have hstable : (prefixWord ++ tailWord_1670675).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670675).length < 2 ^ (prefixWord ++ tailWord_1670675).sum := by decide
  have hdescent : baseEnd_1670675 < baseStart_1670675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670788 : List Nat := [2, 3, 2, 1, 5, 1, 2, 1, 4]
def baseStart_1670788 : Nat := 118140960795 + 1670788 * 2 ^ 59
def prefixEnd_1670788 : Nat := 4983230072969 + 3 ^ 40 * 1670788 * 2
def baseEnd_1670788 : Nat := 381296584784139674651641

theorem tailTrace_1670788 : CollatzResearch.WordTrace tailWord_1670788 prefixEnd_1670788 381296584784139674651641 := by
  unfold tailWord_1670788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30469322335513949358902509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40625763114018599145203345 30469322335513949358902509)
  ·
    refine ⟨11425995875817731009588441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30469322335513949358902509 11425995875817731009588441)
    ·
      refine ⟨8569496906863298257191331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11425995875817731009588441 8569496906863298257191331)
      ·
        refine ⟨12854245360294947385786997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8569496906863298257191331 12854245360294947385786997)
        ·
          refine ⟨1205085502527651317417531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12854245360294947385786997 1205085502527651317417531)
          ·
            refine ⟨1807628253791476976126297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1205085502527651317417531 1807628253791476976126297)
            ·
              refine ⟨1355721190343607732094723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1807628253791476976126297 1355721190343607732094723)
              ·
                refine ⟨2033581785515411598142085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355721190343607732094723 2033581785515411598142085)
                ·
                  refine ⟨381296584784139674651641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033581785515411598142085 381296584784139674651641)
                  ·
                    rfl

theorem cell21_1670788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 2, 1, 4].length) (baseStart_1670788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670788 prefixEnd_1670788 := by exact prefixLift 1670788
  have htrace : WordTrace (prefixWord ++ tailWord_1670788) baseStart_1670788 baseEnd_1670788 := by
    simpa [prefixWord, tailWord_1670788, baseEnd_1670788] using wordTrace_append hprefix tailTrace_1670788
  have hstable : (prefixWord ++ tailWord_1670788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670788).length < 2 ^ (prefixWord ++ tailWord_1670788).sum := by decide
  have hdescent : baseEnd_1670788 < baseStart_1670788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670844 : List Nat := [2, 2, 2, 3, 1, 4, 1, 6]
def baseStart_1670844 : Nat := 118140960795 + 1670844 * 2 ^ 59
def prefixEnd_1670844 : Nat := 4983230072969 + 3 ^ 40 * 1670844 * 2
def baseEnd_1670844 : Nat := 127103121582365340572731

theorem tailTrace_1670844 : CollatzResearch.WordTrace tailWord_1670844 prefixEnd_1670844 127103121582365340572731 := by
  unfold tailWord_1670844
  simp only [CollatzResearch.WordTrace]
  refine ⟨30470343579412510140921793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40627124772550013521229057 30470343579412510140921793)
  ·
    refine ⟨22852757684559382605691345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30470343579412510140921793 22852757684559382605691345)
    ·
      refine ⟨17139568263419536954268509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22852757684559382605691345 17139568263419536954268509)
      ·
        refine ⟨6427338098782326357850691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17139568263419536954268509 6427338098782326357850691)
        ·
          refine ⟨9641007148173489536776037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6427338098782326357850691 9641007148173489536776037)
          ·
            refine ⟨1807688840282529288145507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9641007148173489536776037 1807688840282529288145507)
            ·
              refine ⟨2711533260423793932218261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1807688840282529288145507 2711533260423793932218261)
              ·
                refine ⟨127103121582365340572731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2711533260423793932218261 127103121582365340572731)
                ·
                  rfl

theorem cell21_1670844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 1, 6].length) (baseStart_1670844 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670844 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670844 prefixEnd_1670844 := by exact prefixLift 1670844
  have htrace : WordTrace (prefixWord ++ tailWord_1670844) baseStart_1670844 baseEnd_1670844 := by
    simpa [prefixWord, tailWord_1670844, baseEnd_1670844] using wordTrace_append hprefix tailTrace_1670844
  have hstable : (prefixWord ++ tailWord_1670844).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670844).length < 2 ^ (prefixWord ++ tailWord_1670844).sum := by decide
  have hdescent : baseEnd_1670844 < baseStart_1670844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1670872 : List Nat := [2, 1, 2, 2, 3, 1, 2, 2, 6]
def baseStart_1670872 : Nat := 118140960795 + 1670872 * 2 ^ 59
def prefixEnd_1670872 : Nat := 4983230072969 + 3 ^ 40 * 1670872 * 2
def baseEnd_1670872 : Nat := 381315754728574195251469

theorem tailTrace_1670872 : CollatzResearch.WordTrace tailWord_1670872 prefixEnd_1670872 381315754728574195251469 := by
  unfold tailWord_1670872
  simp only [CollatzResearch.WordTrace]
  refine ⟨30470854201361790531931435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40627805601815720709241913 30470854201361790531931435)
  ·
    refine ⟨45706281302042685797897153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30470854201361790531931435 45706281302042685797897153)
    ·
      refine ⟨34279710976532014348422865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45706281302042685797897153 34279710976532014348422865)
      ·
        refine ⟨25709783232399010761317149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34279710976532014348422865 25709783232399010761317149)
        ·
          refine ⟨9641168712149629035493931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25709783232399010761317149 9641168712149629035493931)
          ·
            refine ⟨14461753068224443553240897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9641168712149629035493931 14461753068224443553240897)
            ·
              refine ⟨10846314801168332664930673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14461753068224443553240897 10846314801168332664930673)
              ·
                refine ⟨8134736100876249498698005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10846314801168332664930673 8134736100876249498698005)
                ·
                  refine ⟨381315754728574195251469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8134736100876249498698005 381315754728574195251469)
                  ·
                    rfl

theorem cell21_1670872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 6].length) (baseStart_1670872 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1670872 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1670872 prefixEnd_1670872 := by exact prefixLift 1670872
  have htrace : WordTrace (prefixWord ++ tailWord_1670872) baseStart_1670872 baseEnd_1670872 := by
    simpa [prefixWord, tailWord_1670872, baseEnd_1670872] using wordTrace_append hprefix tailTrace_1670872
  have hstable : (prefixWord ++ tailWord_1670872).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1670872).length < 2 ^ (prefixWord ++ tailWord_1670872).sum := by decide
  have hdescent : baseEnd_1670872 < baseStart_1670872 := by decide
  rcases family_descends (prefixWord ++ tailWord_1670872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671058 : List Nat := [3, 2, 3, 2, 1, 1, 3, 2, 4]
def baseStart_1671058 : Nat := 118140960795 + 1671058 * 2 ^ 59
def prefixEnd_1671058 : Nat := 4983230072969 + 3 ^ 40 * 1671058 * 2
def baseEnd_1671058 : Nat := 381358202462679205151089

theorem tailTrace_1671058 : CollatzResearch.WordTrace tailWord_1671058 prefixEnd_1671058 381358202462679205151089 := by
  unfold tailWord_1671058
  simp only [CollatzResearch.WordTrace]
  refine ⟨15237123095012433707533457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40632328253366489886755885 15237123095012433707533457)
  ·
    refine ⟨11427842321259325280650093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15237123095012433707533457 11427842321259325280650093)
    ·
      refine ⟨4285440870472246980243785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11427842321259325280650093 4285440870472246980243785)
      ·
        refine ⟨3214080652854185235182839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4285440870472246980243785 3214080652854185235182839)
        ·
          refine ⟨4821120979281277852774259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3214080652854185235182839 4821120979281277852774259)
          ·
            refine ⟨7231681468921916779161389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4821120979281277852774259 7231681468921916779161389)
            ·
              refine ⟨2711880550845718792185521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7231681468921916779161389 2711880550845718792185521)
              ·
                refine ⟨2033910413134289094139141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2711880550845718792185521 2033910413134289094139141)
                ·
                  refine ⟨381358202462679205151089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2033910413134289094139141 381358202462679205151089)
                  ·
                    rfl

theorem cell21_1671058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 2, 4].length) (baseStart_1671058 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671058 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671058 prefixEnd_1671058 := by exact prefixLift 1671058
  have htrace : WordTrace (prefixWord ++ tailWord_1671058) baseStart_1671058 baseEnd_1671058 := by
    simpa [prefixWord, tailWord_1671058, baseEnd_1671058] using wordTrace_append hprefix tailTrace_1671058
  have hstable : (prefixWord ++ tailWord_1671058).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671058).length < 2 ^ (prefixWord ++ tailWord_1671058).sum := by decide
  have hdescent : baseEnd_1671058 < baseStart_1671058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671083 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 10]
def baseStart_1671083 : Nat := 118140960795 + 1671083 * 2 ^ 59
def prefixEnd_1671083 : Nat := 4983230072969 + 3 ^ 40 * 1671083 * 2
def baseEnd_1671083 : Nat := 381363907803284717234371

theorem tailTrace_1671083 : CollatzResearch.WordTrace tailWord_1671083 prefixEnd_1671083 381363907803284717234371 := by
  unfold tailWord_1671083
  simp only [CollatzResearch.WordTrace]
  refine ⟨60949404204959164099793903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40632936136639442733195935 60949404204959164099793903)
  ·
    refine ⟨91424106307438746149690855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60949404204959164099793903 91424106307438746149690855)
    ·
      refine ⟨137136159461158119224536283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91424106307438746149690855 137136159461158119224536283)
      ·
        refine ⟨205704239191737178836804425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137136159461158119224536283 205704239191737178836804425)
        ·
          refine ⟨154278179393802884127603319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205704239191737178836804425 154278179393802884127603319)
          ·
            refine ⟨231417269090704326191404979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154278179393802884127603319 231417269090704326191404979)
            ·
              refine ⟨347125903636056489287107469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231417269090704326191404979 347125903636056489287107469)
              ·
                refine ⟨130172213863521183482665301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 347125903636056489287107469 130172213863521183482665301)
                ·
                  refine ⟨381363907803284717234371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 130172213863521183482665301 381363907803284717234371)
                  ·
                    rfl

theorem cell21_1671083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_1671083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671083 prefixEnd_1671083 := by exact prefixLift 1671083
  have htrace : WordTrace (prefixWord ++ tailWord_1671083) baseStart_1671083 baseEnd_1671083 := by
    simpa [prefixWord, tailWord_1671083, baseEnd_1671083] using wordTrace_append hprefix tailTrace_1671083
  have hstable : (prefixWord ++ tailWord_1671083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671083).length < 2 ^ (prefixWord ++ tailWord_1671083).sum := by decide
  have hdescent : baseEnd_1671083 < baseStart_1671083 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671114 : List Nat := [3, 1, 2, 1, 2, 1, 11]
def baseStart_1671114 : Nat := 118140960795 + 1671114 * 2 ^ 59
def prefixEnd_1671114 : Nat := 4983230072969 + 3 ^ 40 * 1671114 * 2
def baseEnd_1671114 : Nat := 42374553602848394690849

theorem tailTrace_1671114 : CollatzResearch.WordTrace tailWord_1671114 prefixEnd_1671114 42374553602848394690849 := by
  unfold tailWord_1671114
  simp only [CollatzResearch.WordTrace]
  refine ⟨15237633716961714098543099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40633689911897904262781597 15237633716961714098543099)
  ·
    refine ⟨22856450575442571147814649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15237633716961714098543099 22856450575442571147814649)
    ·
      refine ⟨17142337931581928360860987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22856450575442571147814649 17142337931581928360860987)
      ·
        refine ⟨25713506897372892541291481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17142337931581928360860987 25713506897372892541291481)
        ·
          refine ⟨19285130173029669405968611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25713506897372892541291481 19285130173029669405968611)
          ·
            refine ⟨28927695259544504108952917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19285130173029669405968611 28927695259544504108952917)
            ·
              refine ⟨42374553602848394690849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 28927695259544504108952917 42374553602848394690849)
              ·
                rfl

theorem cell21_1671114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 11].length) (baseStart_1671114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671114 prefixEnd_1671114 := by exact prefixLift 1671114
  have htrace : WordTrace (prefixWord ++ tailWord_1671114) baseStart_1671114 baseEnd_1671114 := by
    simpa [prefixWord, tailWord_1671114, baseEnd_1671114] using wordTrace_append hprefix tailTrace_1671114
  have hstable : (prefixWord ++ tailWord_1671114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671114).length < 2 ^ (prefixWord ++ tailWord_1671114).sum := by decide
  have hdescent : baseEnd_1671114 < baseStart_1671114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671601 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 5]
def baseStart_1671601 : Nat := 118140960795 + 1671601 * 2 ^ 59
def prefixEnd_1671601 : Nat := 4983230072969 + 3 ^ 40 * 1671601 * 2
def baseEnd_1671601 : Nat := 381482122460630927599979

theorem tailTrace_1671601 : CollatzResearch.WordTrace tailWord_1671601 prefixEnd_1671601 381482122460630927599979 := by
  unfold tailWord_1671601
  simp only [CollatzResearch.WordTrace]
  refine ⟨60968297217082538567150657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40645531478055025711433771 60968297217082538567150657)
  ·
    refine ⟨45726222912811903925362993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60968297217082538567150657 45726222912811903925362993)
    ·
      refine ⟨34294667184608927944022245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45726222912811903925362993 34294667184608927944022245)
      ·
        refine ⟨6430250097114173989504171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34294667184608927944022245 6430250097114173989504171)
        ·
          refine ⟨9645375145671260984256257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6430250097114173989504171 9645375145671260984256257)
          ·
            refine ⟨7234031359253445738192193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9645375145671260984256257 7234031359253445738192193)
            ·
              refine ⟨5425523519440084303644145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234031359253445738192193 5425523519440084303644145)
              ·
                refine ⟨4069142639580063227733109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5425523519440084303644145 4069142639580063227733109)
                ·
                  refine ⟨381482122460630927599979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4069142639580063227733109 381482122460630927599979)
                  ·
                    rfl

theorem cell21_1671601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_1671601 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671601 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671601 prefixEnd_1671601 := by exact prefixLift 1671601
  have htrace : WordTrace (prefixWord ++ tailWord_1671601) baseStart_1671601 baseEnd_1671601 := by
    simpa [prefixWord, tailWord_1671601, baseEnd_1671601] using wordTrace_append hprefix tailTrace_1671601
  have hstable : (prefixWord ++ tailWord_1671601).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671601).length < 2 ^ (prefixWord ++ tailWord_1671601).sum := by decide
  have hdescent : baseEnd_1671601 < baseStart_1671601 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671660 : List Nat := [2, 2, 1, 1, 2, 1, 4, 1, 7]
def baseStart_1671660 : Nat := 118140960795 + 1671660 * 2 ^ 59
def prefixEnd_1671660 : Nat := 4983230072969 + 3 ^ 40 * 1671660 * 2
def baseEnd_1671660 : Nat := 381495587064459936116525

theorem tailTrace_1671660 : CollatzResearch.WordTrace tailWord_1671660 prefixEnd_1671660 381495587064459936116525 := by
  unfold tailWord_1671660
  simp only [CollatzResearch.WordTrace]
  refine ⟨30485224561934395821774217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40646966082579194429032289 30485224561934395821774217)
  ·
    refine ⟨22863918421450796866330663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30485224561934395821774217 22863918421450796866330663)
    ·
      refine ⟨34295877632176195299495995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22863918421450796866330663 34295877632176195299495995)
      ·
        refine ⟨51443816448264292949243993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34295877632176195299495995 51443816448264292949243993)
        ·
          refine ⟨38582862336198219711932995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51443816448264292949243993 38582862336198219711932995)
          ·
            refine ⟨57874293504297329567899493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38582862336198219711932995 57874293504297329567899493)
            ·
              refine ⟨10851430032055749293981155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57874293504297329567899493 10851430032055749293981155)
              ·
                refine ⟨16277145048083623940971733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10851430032055749293981155 16277145048083623940971733)
                ·
                  refine ⟨381495587064459936116525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16277145048083623940971733 381495587064459936116525)
                  ·
                    rfl

theorem cell21_1671660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 7].length) (baseStart_1671660 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671660 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671660 prefixEnd_1671660 := by exact prefixLift 1671660
  have htrace : WordTrace (prefixWord ++ tailWord_1671660) baseStart_1671660 baseEnd_1671660 := by
    simpa [prefixWord, tailWord_1671660, baseEnd_1671660] using wordTrace_append hprefix tailTrace_1671660
  have hstable : (prefixWord ++ tailWord_1671660).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671660).length < 2 ^ (prefixWord ++ tailWord_1671660).sum := by decide
  have hdescent : baseEnd_1671660 < baseStart_1671660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671686 : List Nat := [6, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1671686 : Nat := 118140960795 + 1671686 * 2 ^ 59
def prefixEnd_1671686 : Nat := 4983230072969 + 3 ^ 40 * 1671686 * 2
def baseEnd_1671686 : Nat := 381501520618689668683139

theorem tailTrace_1671686 : CollatzResearch.WordTrace tailWord_1671686 prefixEnd_1671686 381501520618689668683139 := by
  unfold tailWord_1671686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1905356169430456190124841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40647598281183065389329941 1905356169430456190124841)
  ·
    refine ⟨1429017127072842142593631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1905356169430456190124841 1429017127072842142593631)
    ·
      refine ⟨2143525690609263213890447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1429017127072842142593631 2143525690609263213890447)
      ·
        refine ⟨3215288535913894820835671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2143525690609263213890447 3215288535913894820835671)
        ·
          refine ⟨4822932803870842231253507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3215288535913894820835671 4822932803870842231253507)
          ·
            refine ⟨7234399205806263346880261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822932803870842231253507 7234399205806263346880261)
            ·
              refine ⟨1356449851088674377540049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7234399205806263346880261 1356449851088674377540049)
              ·
                refine ⟨1017337388316505783155037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1356449851088674377540049 1017337388316505783155037)
                ·
                  refine ⟨381501520618689668683139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017337388316505783155037 381501520618689668683139)
                  ·
                    rfl

theorem cell21_1671686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1671686 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671686 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671686 prefixEnd_1671686 := by exact prefixLift 1671686
  have htrace : WordTrace (prefixWord ++ tailWord_1671686) baseStart_1671686 baseEnd_1671686 := by
    simpa [prefixWord, tailWord_1671686, baseEnd_1671686] using wordTrace_append hprefix tailTrace_1671686
  have hstable : (prefixWord ++ tailWord_1671686).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671686).length < 2 ^ (prefixWord ++ tailWord_1671686).sum := by decide
  have hdescent : baseEnd_1671686 < baseStart_1671686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671708 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1671708 : Nat := 118140960795 + 1671708 * 2 ^ 59
def prefixEnd_1671708 : Nat := 4983230072969 + 3 ^ 40 * 1671708 * 2
def baseEnd_1671708 : Nat := 381506541318422519316427

theorem tailTrace_1671708 : CollatzResearch.WordTrace tailWord_1671708 prefixEnd_1671708 381506541318422519316427 := by
  unfold tailWord_1671708
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486099913847447920647889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40648133218463263894197185 30486099913847447920647889)
  ·
    refine ⟨22864574935385585940485917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30486099913847447920647889 22864574935385585940485917)
    ·
      refine ⟨8574215600769594727682219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22864574935385585940485917 8574215600769594727682219)
      ·
        refine ⟨12861323401154392091523329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8574215600769594727682219 12861323401154392091523329)
        ·
          refine ⟨9645992550865794068642497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12861323401154392091523329 9645992550865794068642497)
          ·
            refine ⟨7234494413149345551481873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9645992550865794068642497 7234494413149345551481873)
            ·
              refine ⟨5425870809862009163611405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7234494413149345551481873 5425870809862009163611405)
              ·
                refine ⟨2034701553698253436354277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5425870809862009163611405 2034701553698253436354277)
                ·
                  refine ⟨381506541318422519316427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034701553698253436354277 381506541318422519316427)
                  ·
                    rfl

theorem cell21_1671708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1671708 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671708 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671708 prefixEnd_1671708 := by exact prefixLift 1671708
  have htrace : WordTrace (prefixWord ++ tailWord_1671708) baseStart_1671708 baseEnd_1671708 := by
    simpa [prefixWord, tailWord_1671708, baseEnd_1671708] using wordTrace_append hprefix tailTrace_1671708
  have hstable : (prefixWord ++ tailWord_1671708).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671708).length < 2 ^ (prefixWord ++ tailWord_1671708).sum := by decide
  have hdescent : baseEnd_1671708 < baseStart_1671708 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671736 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 7]
def baseStart_1671736 : Nat := 118140960795 + 1671736 * 2 ^ 59
def prefixEnd_1671736 : Nat := 4983230072969 + 3 ^ 40 * 1671736 * 2
def baseEnd_1671736 : Nat := 381512931299900692849703

theorem tailTrace_1671736 : CollatzResearch.WordTrace tailWord_1671736 prefixEnd_1671736 381512931299900692849703 := by
  unfold tailWord_1671736
  simp only [CollatzResearch.WordTrace]
  refine ⟨30486610535796728311657531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40648814047728971082210041 30486610535796728311657531)
  ·
    refine ⟨45729915803695092467486297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30486610535796728311657531 45729915803695092467486297)
    ·
      refine ⟨34297436852771319350614723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45729915803695092467486297 34297436852771319350614723)
      ·
        refine ⟨51446155279156979025922085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34297436852771319350614723 51446155279156979025922085)
        ·
          refine ⟨9646154114841933567360391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51446155279156979025922085 9646154114841933567360391)
          ·
            refine ⟨14469231172262900351040587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9646154114841933567360391 14469231172262900351040587)
            ·
              refine ⟨21703846758394350526560881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14469231172262900351040587 21703846758394350526560881)
              ·
                refine ⟨16277885068795762894920661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21703846758394350526560881 16277885068795762894920661)
                ·
                  refine ⟨381512931299900692849703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16277885068795762894920661 381512931299900692849703)
                  ·
                    rfl

theorem cell21_1671736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 7].length) (baseStart_1671736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671736 prefixEnd_1671736 := by exact prefixLift 1671736
  have htrace : WordTrace (prefixWord ++ tailWord_1671736) baseStart_1671736 baseEnd_1671736 := by
    simpa [prefixWord, tailWord_1671736, baseEnd_1671736] using wordTrace_append hprefix tailTrace_1671736
  have hstable : (prefixWord ++ tailWord_1671736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671736).length < 2 ^ (prefixWord ++ tailWord_1671736).sum := by decide
  have hdescent : baseEnd_1671736 < baseStart_1671736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671818 : List Nat := [3, 1, 2, 3, 3, 2, 2, 1, 4]
def baseStart_1671818 : Nat := 118140960795 + 1671818 * 2 ^ 59
def prefixEnd_1671818 : Nat := 4983230072969 + 3 ^ 40 * 1671818 * 2
def baseEnd_1671818 : Nat := 381531644817086772482869

theorem tailTrace_1671818 : CollatzResearch.WordTrace tailWord_1671818 prefixEnd_1671818 381531644817086772482869 := by
  unfold tailWord_1671818
  simp only [CollatzResearch.WordTrace]
  refine ⟨15244052964324096156950027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40650807904864256418533405 15244052964324096156950027)
  ·
    refine ⟨22866079446486144235425041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15244052964324096156950027 22866079446486144235425041)
    ·
      refine ⟨17149559584864608176568781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22866079446486144235425041 17149559584864608176568781)
      ·
        refine ⟨6431084844324228066213293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17149559584864608176568781 6431084844324228066213293)
        ·
          refine ⟨2411656816621585524829985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6431084844324228066213293 2411656816621585524829985)
          ·
            refine ⟨1808742612466189143622489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2411656816621585524829985 1808742612466189143622489)
            ·
              refine ⟨1356556959349641857716867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1808742612466189143622489 1356556959349641857716867)
              ·
                refine ⟨2034835439024462786575301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356556959349641857716867 2034835439024462786575301)
                ·
                  refine ⟨381531644817086772482869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034835439024462786575301 381531644817086772482869)
                  ·
                    rfl

theorem cell21_1671818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 2, 2, 1, 4].length) (baseStart_1671818 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671818 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671818 prefixEnd_1671818 := by exact prefixLift 1671818
  have htrace : WordTrace (prefixWord ++ tailWord_1671818) baseStart_1671818 baseEnd_1671818 := by
    simpa [prefixWord, tailWord_1671818, baseEnd_1671818] using wordTrace_append hprefix tailTrace_1671818
  have hstable : (prefixWord ++ tailWord_1671818).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671818).length < 2 ^ (prefixWord ++ tailWord_1671818).sum := by decide
  have hdescent : baseEnd_1671818 < baseStart_1671818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671919 : List Nat := [1, 1, 2, 1, 5, 3, 1, 1, 6]
def baseStart_1671919 : Nat := 118140960795 + 1671919 * 2 ^ 59
def prefixEnd_1671919 : Nat := 4983230072969 + 3 ^ 40 * 1671919 * 2
def baseEnd_1671919 : Nat := 381554694393133041299329

theorem tailTrace_1671919 : CollatzResearch.WordTrace tailWord_1671919 prefixEnd_1671919 381554694393133041299329 := by
  unfold tailWord_1671919
  simp only [CollatzResearch.WordTrace]
  refine ⟨60979895629930478877226811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40653263753286985918151207 60979895629930478877226811)
  ·
    refine ⟨91469843444895718315840217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60979895629930478877226811 91469843444895718315840217)
    ·
      refine ⟨68602382583671788736880163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91469843444895718315840217 68602382583671788736880163)
      ·
        refine ⟨102903573875507683105320245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68602382583671788736880163 102903573875507683105320245)
        ·
          refine ⟨9647210050828845291123773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 102903573875507683105320245 9647210050828845291123773)
          ·
            refine ⟨3617703769060816984171415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9647210050828845291123773 3617703769060816984171415)
            ·
              refine ⟨5426555653591225476257123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3617703769060816984171415 5426555653591225476257123)
              ·
                refine ⟨8139833480386838214385685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5426555653591225476257123 8139833480386838214385685)
                ·
                  refine ⟨381554694393133041299329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8139833480386838214385685 381554694393133041299329)
                  ·
                    rfl

theorem cell21_1671919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_1671919 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671919 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671919 prefixEnd_1671919 := by exact prefixLift 1671919
  have htrace : WordTrace (prefixWord ++ tailWord_1671919) baseStart_1671919 baseEnd_1671919 := by
    simpa [prefixWord, tailWord_1671919, baseEnd_1671919] using wordTrace_append hprefix tailTrace_1671919
  have hstable : (prefixWord ++ tailWord_1671919).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671919).length < 2 ^ (prefixWord ++ tailWord_1671919).sum := by decide
  have hdescent : baseEnd_1671919 < baseStart_1671919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671922 : List Nat := [3, 2, 1, 3, 1, 2, 2, 4, 3]
def baseStart_1671922 : Nat := 118140960795 + 1671922 * 2 ^ 59
def prefixEnd_1671922 : Nat := 4983230072969 + 3 ^ 40 * 1671922 * 2
def baseEnd_1671922 : Nat := 381555379034005702749323

theorem tailTrace_1671922 : CollatzResearch.WordTrace tailWord_1671922 prefixEnd_1671922 381555379034005702749323 := by
  unfold tailWord_1671922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15245001262229902597396505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40653336699279740259724013 15245001262229902597396505)
  ·
    refine ⟨11433750946672426948047379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15245001262229902597396505 11433750946672426948047379)
    ·
      refine ⟨17150626420008640422071069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11433750946672426948047379 17150626420008640422071069)
      ·
        refine ⟨6431484907503240158276651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17150626420008640422071069 6431484907503240158276651)
        ·
          refine ⟨9647227361254860237414977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6431484907503240158276651 9647227361254860237414977)
          ·
            refine ⟨7235420520941145178061233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9647227361254860237414977 7235420520941145178061233)
            ·
              refine ⟨5426565390705858883545925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235420520941145178061233 5426565390705858883545925)
              ·
                refine ⟨1017481010757348540664861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5426565390705858883545925 1017481010757348540664861)
                ·
                  refine ⟨381555379034005702749323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017481010757348540664861 381555379034005702749323)
                  ·
                    rfl

theorem cell21_1671922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 3].length) (baseStart_1671922 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671922 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671922 prefixEnd_1671922 := by exact prefixLift 1671922
  have htrace : WordTrace (prefixWord ++ tailWord_1671922) baseStart_1671922 baseEnd_1671922 := by
    simpa [prefixWord, tailWord_1671922, baseEnd_1671922] using wordTrace_append hprefix tailTrace_1671922
  have hstable : (prefixWord ++ tailWord_1671922).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671922).length < 2 ^ (prefixWord ++ tailWord_1671922).sum := by decide
  have hdescent : baseEnd_1671922 < baseStart_1671922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1671933 : List Nat := [1, 4, 1, 1, 1, 1, 4, 8]
def baseStart_1671933 : Nat := 118140960795 + 1671933 * 2 ^ 59
def prefixEnd_1671933 : Nat := 4983230072969 + 3 ^ 40 * 1671933 * 2
def baseEnd_1671933 : Nat := 127185963127957376021989

theorem tailTrace_1671933 : CollatzResearch.WordTrace tailWord_1671933 prefixEnd_1671933 127185963127957376021989 := by
  unfold tailWord_1671933
  simp only [CollatzResearch.WordTrace]
  refine ⟨60980406251879759268236453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40653604167919839512157635 60980406251879759268236453)
  ·
    refine ⟨11433826172227454862794335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 60980406251879759268236453 11433826172227454862794335)
    ·
      refine ⟨17150739258341182294191503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11433826172227454862794335 17150739258341182294191503)
      ·
        refine ⟨25726108887511773441287255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17150739258341182294191503 25726108887511773441287255)
        ·
          refine ⟨38589163331267660161930883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25726108887511773441287255 38589163331267660161930883)
          ·
            refine ⟨57883744996901490242896325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38589163331267660161930883 57883744996901490242896325)
            ·
              refine ⟨10853202186919029420543061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57883744996901490242896325 10853202186919029420543061)
              ·
                refine ⟨127185963127957376021989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10853202186919029420543061 127185963127957376021989)
                ·
                  rfl

theorem cell21_1671933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 8].length) (baseStart_1671933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1671933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1671933 prefixEnd_1671933 := by exact prefixLift 1671933
  have htrace : WordTrace (prefixWord ++ tailWord_1671933) baseStart_1671933 baseEnd_1671933 := by
    simpa [prefixWord, tailWord_1671933, baseEnd_1671933] using wordTrace_append hprefix tailTrace_1671933
  have hstable : (prefixWord ++ tailWord_1671933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1671933).length < 2 ^ (prefixWord ++ tailWord_1671933).sum := by decide
  have hdescent : baseEnd_1671933 < baseStart_1671933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1671933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672009 : List Nat := [1, 2, 1, 1, 2, 5, 2, 7]
def baseStart_1672009 : Nat := 118140960795 + 1672009 * 2 ^ 59
def prefixEnd_1672009 : Nat := 4983230072969 + 3 ^ 40 * 1672009 * 2
def baseEnd_1672009 : Nat := 127191744539770961599715

theorem tailTrace_1672009 : CollatzResearch.WordTrace tailWord_1672009 prefixEnd_1672009 127191744539770961599715 := by
  unfold tailWord_1672009
  simp only [CollatzResearch.WordTrace]
  refine ⟨60983178199604424248003081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40655452133069616165335387 60983178199604424248003081)
  ·
    refine ⟨45737383649703318186002311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60983178199604424248003081 45737383649703318186002311)
    ·
      refine ⟨68606075474554977279003467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45737383649703318186002311 68606075474554977279003467)
      ·
        refine ⟨102909113211832465918505201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68606075474554977279003467 102909113211832465918505201)
        ·
          refine ⟨77181834908874349438878901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102909113211832465918505201 77181834908874349438878901)
          ·
            refine ⟨7235797022706970259894897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77181834908874349438878901 7235797022706970259894897)
            ·
              refine ⟨5426847767030227694921173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7235797022706970259894897 5426847767030227694921173)
              ·
                refine ⟨127191744539770961599715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5426847767030227694921173 127191744539770961599715)
                ·
                  rfl

theorem cell21_1672009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 7].length) (baseStart_1672009 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672009 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672009 prefixEnd_1672009 := by exact prefixLift 1672009
  have htrace : WordTrace (prefixWord ++ tailWord_1672009) baseStart_1672009 baseEnd_1672009 := by
    simpa [prefixWord, tailWord_1672009, baseEnd_1672009] using wordTrace_append hprefix tailTrace_1672009
  have hstable : (prefixWord ++ tailWord_1672009).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672009).length < 2 ^ (prefixWord ++ tailWord_1672009).sum := by decide
  have hdescent : baseEnd_1672009 < baseStart_1672009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672074 : List Nat := [3, 1, 2, 4, 1, 1, 1, 5, 3]
def baseStart_1672074 : Nat := 118140960795 + 1672074 * 2 ^ 59
def prefixEnd_1672074 : Nat := 4983230072969 + 3 ^ 40 * 1672074 * 2
def baseEnd_1672074 : Nat := 381590067504887216215679

theorem tailTrace_1672074 : CollatzResearch.WordTrace tailWord_1672074 prefixEnd_1672074 381590067504887216215679 := by
  unfold tailWord_1672074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15246387236092235087279819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40657032629579293566079517 15246387236092235087279819)
  ·
    refine ⟨22869580854138352630919729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15246387236092235087279819 22869580854138352630919729)
    ·
      refine ⟨17152185640603764473189797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22869580854138352630919729 17152185640603764473189797)
      ·
        refine ⟨3216034807613205838723087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17152185640603764473189797 3216034807613205838723087)
        ·
          refine ⟨4824052211419808758084631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216034807613205838723087 4824052211419808758084631)
          ·
            refine ⟨7236078317129713137126947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824052211419808758084631 7236078317129713137126947)
            ·
              refine ⟨10854117475694569705690421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7236078317129713137126947 10854117475694569705690421)
              ·
                refine ⟨1017573513346365909908477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10854117475694569705690421 1017573513346365909908477)
                ·
                  refine ⟨381590067504887216215679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017573513346365909908477 381590067504887216215679)
                  ·
                    rfl

theorem cell21_1672074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 3].length) (baseStart_1672074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672074 prefixEnd_1672074 := by exact prefixLift 1672074
  have htrace : WordTrace (prefixWord ++ tailWord_1672074) baseStart_1672074 baseEnd_1672074 := by
    simpa [prefixWord, tailWord_1672074, baseEnd_1672074] using wordTrace_append hprefix tailTrace_1672074
  have hstable : (prefixWord ++ tailWord_1672074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672074).length < 2 ^ (prefixWord ++ tailWord_1672074).sum := by decide
  have hdescent : baseEnd_1672074 < baseStart_1672074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672085 : List Nat := [1, 3, 2, 1, 1, 5, 8]
def baseStart_1672085 : Nat := 118140960795 + 1672085 * 2 ^ 59
def prefixEnd_1672085 : Nat := 4983230072969 + 3 ^ 40 * 1672085 * 2
def baseEnd_1672085 : Nat := 42399175317194849059147

theorem tailTrace_1672085 : CollatzResearch.WordTrace tailWord_1672085 prefixEnd_1672085 42399175317194849059147 := by
  unfold tailWord_1672085
  simp only [CollatzResearch.WordTrace]
  refine ⟨60985950147329089227769709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40657300098219392818513139 60985950147329089227769709)
  ·
    refine ⟨22869731305248408460413641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 60985950147329089227769709 22869731305248408460413641)
    ·
      refine ⟨17152298478936306345310231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22869731305248408460413641 17152298478936306345310231)
      ·
        refine ⟨25728447718404459517965347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17152298478936306345310231 25728447718404459517965347)
        ·
          refine ⟨38592671577606689276948021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25728447718404459517965347 38592671577606689276948021)
          ·
            refine ⟨3618062960400627119713877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38592671577606689276948021 3618062960400627119713877)
            ·
              refine ⟨42399175317194849059147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3618062960400627119713877 42399175317194849059147)
              ·
                rfl

theorem cell21_1672085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 8].length) (baseStart_1672085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672085 prefixEnd_1672085 := by exact prefixLift 1672085
  have htrace : WordTrace (prefixWord ++ tailWord_1672085) baseStart_1672085 baseEnd_1672085 := by
    simpa [prefixWord, tailWord_1672085, baseEnd_1672085] using wordTrace_append hprefix tailTrace_1672085
  have hstable : (prefixWord ++ tailWord_1672085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672085).length < 2 ^ (prefixWord ++ tailWord_1672085).sum := by decide
  have hdescent : baseEnd_1672085 < baseStart_1672085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672150 : List Nat := [5, 2, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1672150 : Nat := 118140960795 + 1672150 * 2 ^ 59
def prefixEnd_1672150 : Nat := 4983230072969 + 3 ^ 40 * 1672150 * 2
def baseEnd_1672150 : Nat := 381607411740327972948857

theorem tailTrace_1672150 : CollatzResearch.WordTrace tailWord_1672150 prefixEnd_1672150 381607411740327972948857 := by
  unfold tailWord_1672150
  simp only [CollatzResearch.WordTrace]
  refine ⟨3811770055755850333055369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40658880594729070219257269 3811770055755850333055369)
  ·
    refine ⟨2858827541816887749791527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3811770055755850333055369 2858827541816887749791527)
    ·
      refine ⟨4288241312725331624687291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2858827541816887749791527 4288241312725331624687291)
      ·
        refine ⟨6432361969087997437030937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4288241312725331624687291 6432361969087997437030937)
        ·
          refine ⟨4824271476815998077773203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6432361969087997437030937 4824271476815998077773203)
          ·
            refine ⟨7236407215223997116659805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824271476815998077773203 7236407215223997116659805)
            ·
              refine ⟨2713652705708998918747427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7236407215223997116659805 2713652705708998918747427)
              ·
                refine ⟨4070479058563498378121141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2713652705708998918747427 4070479058563498378121141)
                ·
                  refine ⟨381607411740327972948857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4070479058563498378121141 381607411740327972948857)
                  ·
                    rfl

theorem cell21_1672150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1672150 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672150 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672150 prefixEnd_1672150 := by exact prefixLift 1672150
  have htrace : WordTrace (prefixWord ++ tailWord_1672150) baseStart_1672150 baseEnd_1672150 := by
    simpa [prefixWord, tailWord_1672150, baseEnd_1672150] using wordTrace_append hprefix tailTrace_1672150
  have hstable : (prefixWord ++ tailWord_1672150).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672150).length < 2 ^ (prefixWord ++ tailWord_1672150).sum := by decide
  have hdescent : baseEnd_1672150 < baseStart_1672150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672223 : List Nat := [1, 1, 2, 4, 1, 3, 2, 3, 4]
def baseStart_1672223 : Nat := 118140960795 + 1672223 * 2 ^ 59
def prefixEnd_1672223 : Nat := 4983230072969 + 3 ^ 40 * 1672223 * 2
def baseEnd_1672223 : Nat := 381624071334896068232041

theorem tailTrace_1672223 : CollatzResearch.WordTrace tailWord_1672223 prefixEnd_1672223 381624071334896068232041 := by
  unfold tailWord_1672223
  simp only [CollatzResearch.WordTrace]
  refine ⟨60990983420829138796293323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40660655613886092530862215 60990983420829138796293323)
  ·
    refine ⟨91486475131243708194439985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60990983420829138796293323 91486475131243708194439985)
    ·
      refine ⟨68614856348432781145829989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91486475131243708194439985 68614856348432781145829989)
      ·
        refine ⟨12865285565331146464843123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68614856348432781145829989 12865285565331146464843123)
        ·
          refine ⟨19297928347996719697264685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12865285565331146464843123 19297928347996719697264685)
          ·
            refine ⟨7236723130498769886474257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19297928347996719697264685 7236723130498769886474257)
            ·
              refine ⟨5427542347874077414855693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7236723130498769886474257 5427542347874077414855693)
              ·
                refine ⟨2035328380452779030570885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5427542347874077414855693 2035328380452779030570885)
                ·
                  refine ⟨381624071334896068232041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035328380452779030570885 381624071334896068232041)
                  ·
                    rfl

theorem cell21_1672223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 3, 4].length) (baseStart_1672223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672223 prefixEnd_1672223 := by exact prefixLift 1672223
  have htrace : WordTrace (prefixWord ++ tailWord_1672223) baseStart_1672223 baseEnd_1672223 := by
    simpa [prefixWord, tailWord_1672223, baseEnd_1672223] using wordTrace_append hprefix tailTrace_1672223
  have hstable : (prefixWord ++ tailWord_1672223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672223).length < 2 ^ (prefixWord ++ tailWord_1672223).sum := by decide
  have hdescent : baseEnd_1672223 < baseStart_1672223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672254 : List Nat := [4, 2, 1, 3, 1, 2, 8]
def baseStart_1672254 : Nat := 118140960795 + 1672254 * 2 ^ 59
def prefixEnd_1672254 : Nat := 4983230072969 + 3 ^ 40 * 1672254 * 2
def baseEnd_1672254 : Nat := 42403460661916322579479

theorem tailTrace_1672254 : CollatzResearch.WordTrace tailWord_1672254 prefixEnd_1672254 42403460661916322579479 := by
  unfold tailWord_1672254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7624014260464603886333977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40661409389144554060447877 7624014260464603886333977)
  ·
    refine ⟨5718010695348452914750483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7624014260464603886333977 5718010695348452914750483)
    ·
      refine ⟨8577016043022679372125725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5718010695348452914750483 8577016043022679372125725)
      ·
        refine ⟨3216381016133504764547147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8577016043022679372125725 3216381016133504764547147)
        ·
          refine ⟨4824571524200257146820721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216381016133504764547147 4824571524200257146820721)
          ·
            refine ⟨3618428643150192860115541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4824571524200257146820721 3618428643150192860115541)
            ·
              refine ⟨42403460661916322579479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3618428643150192860115541 42403460661916322579479)
              ·
                rfl

theorem cell21_1672254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 8].length) (baseStart_1672254 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672254 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672254 prefixEnd_1672254 := by exact prefixLift 1672254
  have htrace : WordTrace (prefixWord ++ tailWord_1672254) baseStart_1672254 baseEnd_1672254 := by
    simpa [prefixWord, tailWord_1672254, baseEnd_1672254] using wordTrace_append hprefix tailTrace_1672254
  have hstable : (prefixWord ++ tailWord_1672254).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672254).length < 2 ^ (prefixWord ++ tailWord_1672254).sum := by decide
  have hdescent : baseEnd_1672254 < baseStart_1672254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672257 : List Nat := [1, 2, 5, 1, 3, 2, 1, 2, 4]
def baseStart_1672257 : Nat := 118140960795 + 1672257 * 2 ^ 59
def prefixEnd_1672257 : Nat := 4983230072969 + 3 ^ 40 * 1672257 * 2
def baseEnd_1672257 : Nat := 381631830598119564665305

theorem tailTrace_1672257 : CollatzResearch.WordTrace tailWord_1672257 prefixEnd_1672257 381631830598119564665305 := by
  unfold tailWord_1672257
  simp only [CollatzResearch.WordTrace]
  refine ⟨60992223502705962603031025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40661482335137308402020683 60992223502705962603031025)
  ·
    refine ⟨45744167627029471952273269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 60992223502705962603031025 45744167627029471952273269)
    ·
      refine ⟨4288515715034012995525619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45744167627029471952273269 4288515715034012995525619)
      ·
        refine ⟨6432773572551019493288429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4288515715034012995525619 6432773572551019493288429)
        ·
          refine ⟨2412290089706632309983161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6432773572551019493288429 2412290089706632309983161)
          ·
            refine ⟨1809217567279974232487371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2412290089706632309983161 1809217567279974232487371)
            ·
              refine ⟨2713826350919961348731057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809217567279974232487371 2713826350919961348731057)
              ·
                refine ⟨2035369763189971011548293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2713826350919961348731057 2035369763189971011548293)
                ·
                  refine ⟨381631830598119564665305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035369763189971011548293 381631830598119564665305)
                  ·
                    rfl

theorem cell21_1672257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 2, 4].length) (baseStart_1672257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672257 prefixEnd_1672257 := by exact prefixLift 1672257
  have htrace : WordTrace (prefixWord ++ tailWord_1672257) baseStart_1672257 baseEnd_1672257 := by
    simpa [prefixWord, tailWord_1672257, baseEnd_1672257] using wordTrace_append hprefix tailTrace_1672257
  have hstable : (prefixWord ++ tailWord_1672257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672257).length < 2 ^ (prefixWord ++ tailWord_1672257).sum := by decide
  have hdescent : baseEnd_1672257 < baseStart_1672257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672302 : List Nat := [4, 1, 2, 2, 1, 2, 3, 3, 3]
def baseStart_1672302 : Nat := 118140960795 + 1672302 * 2 ^ 59
def prefixEnd_1672302 : Nat := 4983230072969 + 3 ^ 40 * 1672302 * 2
def baseEnd_1672302 : Nat := 381642100211209486415213

theorem tailTrace_1672302 : CollatzResearch.WordTrace tailWord_1672302 prefixEnd_1672302 381642100211209486415213 := by
  unfold tailWord_1672302
  simp only [CollatzResearch.WordTrace]
  refine ⟨7624233098442866911052395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40662576525028623525612773 7624233098442866911052395)
  ·
    refine ⟨11436349647664300366578593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7624233098442866911052395 11436349647664300366578593)
    ·
      refine ⟨8577262235748225274933945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11436349647664300366578593 8577262235748225274933945)
      ·
        refine ⟨6432946676811168956200459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8577262235748225274933945 6432946676811168956200459)
        ·
          refine ⟨9649420015216753434300689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6432946676811168956200459 9649420015216753434300689)
          ·
            refine ⟨7237065011412565075725517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9649420015216753434300689 7237065011412565075725517)
            ·
              refine ⟨2713899379279711903397069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7237065011412565075725517 2713899379279711903397069)
              ·
                refine ⟨1017712267229891963773901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2713899379279711903397069 1017712267229891963773901)
                ·
                  refine ⟨381642100211209486415213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1017712267229891963773901 381642100211209486415213)
                  ·
                    rfl

theorem cell21_1672302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 3, 3, 3].length) (baseStart_1672302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672302 prefixEnd_1672302 := by exact prefixLift 1672302
  have htrace : WordTrace (prefixWord ++ tailWord_1672302) baseStart_1672302 baseEnd_1672302 := by
    simpa [prefixWord, tailWord_1672302, baseEnd_1672302] using wordTrace_append hprefix tailTrace_1672302
  have hstable : (prefixWord ++ tailWord_1672302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672302).length < 2 ^ (prefixWord ++ tailWord_1672302).sum := by decide
  have hdescent : baseEnd_1672302 < baseStart_1672302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672375 : List Nat := [1, 1, 3, 1, 4, 1, 4, 2, 4]
def baseStart_1672375 : Nat := 118140960795 + 1672375 * 2 ^ 59
def prefixEnd_1672375 : Nat := 4983230072969 + 3 ^ 40 * 1672375 * 2
def baseEnd_1672375 : Nat := 381658759805777581698397

theorem tailTrace_1672375 : CollatzResearch.WordTrace tailWord_1672375 prefixEnd_1672375 381658759805777581698397 := by
  unfold tailWord_1672375
  simp only [CollatzResearch.WordTrace]
  refine ⟨60996527316278468755826579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40664351544185645837217719 60996527316278468755826579)
  ·
    refine ⟨91494790974417703133739869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60996527316278468755826579 91494790974417703133739869)
    ·
      refine ⟨34310546615406638675152451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91494790974417703133739869 34310546615406638675152451)
      ·
        refine ⟨51465819923109958012728677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34310546615406638675152451 51465819923109958012728677)
        ·
          refine ⟨9649841235583117127386627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51465819923109958012728677 9649841235583117127386627)
          ·
            refine ⟨14474761853374675691079941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9649841235583117127386627 14474761853374675691079941)
            ·
              refine ⟨2714017847507751692077489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14474761853374675691079941 2714017847507751692077489)
              ·
                refine ⟨2035513385630813769058117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2714017847507751692077489 2035513385630813769058117)
                ·
                  refine ⟨381658759805777581698397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035513385630813769058117 381658759805777581698397)
                  ·
                    rfl

theorem cell21_1672375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 4, 2, 4].length) (baseStart_1672375 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672375 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672375 prefixEnd_1672375 := by exact prefixLift 1672375
  have htrace : WordTrace (prefixWord ++ tailWord_1672375) baseStart_1672375 baseEnd_1672375 := by
    simpa [prefixWord, tailWord_1672375, baseEnd_1672375] using wordTrace_append hprefix tailTrace_1672375
  have hstable : (prefixWord ++ tailWord_1672375).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672375).length < 2 ^ (prefixWord ++ tailWord_1672375).sum := by decide
  have hdescent : baseEnd_1672375 < baseStart_1672375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672403 : List Nat := [1, 1, 1, 2, 1, 1, 1, 8, 5]
def baseStart_1672403 : Nat := 118140960795 + 1672403 * 2 ^ 59
def prefixEnd_1672403 : Nat := 4983230072969 + 3 ^ 40 * 1672403 * 2
def baseEnd_1672403 : Nat := 381665149787255755231673

theorem tailTrace_1672403 : CollatzResearch.WordTrace tailWord_1672403 prefixEnd_1672403 381665149787255755231673 := by
  unfold tailWord_1672403
  simp only [CollatzResearch.WordTrace]
  refine ⟨60997548560177029537845863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40665032373451353025230575 60997548560177029537845863)
  ·
    refine ⟨91496322840265544306768795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 60997548560177029537845863 91496322840265544306768795)
    ·
      refine ⟨137244484260398316460153193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91496322840265544306768795 137244484260398316460153193)
      ·
        refine ⟨102933363195298737345114895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137244484260398316460153193 102933363195298737345114895)
        ·
          refine ⟨154400044792948106017672343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102933363195298737345114895 154400044792948106017672343)
          ·
            refine ⟨231600067189422159026508515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154400044792948106017672343 231600067189422159026508515)
            ·
              refine ⟨347400100784133238539762773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231600067189422159026508515 347400100784133238539762773)
              ·
                refine ⟨4071094931064061389137845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 347400100784133238539762773 4071094931064061389137845)
                ·
                  refine ⟨381665149787255755231673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071094931064061389137845 381665149787255755231673)
                  ·
                    rfl

theorem cell21_1672403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_1672403 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672403 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672403 prefixEnd_1672403 := by exact prefixLift 1672403
  have htrace : WordTrace (prefixWord ++ tailWord_1672403) baseStart_1672403 baseEnd_1672403 := by
    simpa [prefixWord, tailWord_1672403, baseEnd_1672403] using wordTrace_append hprefix tailTrace_1672403
  have hstable : (prefixWord ++ tailWord_1672403).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672403).length < 2 ^ (prefixWord ++ tailWord_1672403).sum := by decide
  have hdescent : baseEnd_1672403 < baseStart_1672403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672448 : List Nat := [2, 1, 1, 2, 1, 1, 3, 10]
def baseStart_1672448 : Nat := 118140960795 + 1672448 * 2 ^ 59
def prefixEnd_1672448 : Nat := 4983230072969 + 3 ^ 40 * 1672448 * 2
def baseEnd_1672448 : Nat := 127225139800115225660527

theorem tailTrace_1672448 : CollatzResearch.WordTrace tailWord_1672448 prefixEnd_1672448 127225139800115225660527 := by
  unfold tailWord_1672448
  simp only [CollatzResearch.WordTrace]
  refine ⟨30499594922507001111616999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40666126563342668148822665 30499594922507001111616999)
  ·
    refine ⟨45749392383760501667425499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30499594922507001111616999 45749392383760501667425499)
    ·
      refine ⟨68624088575640752501138249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45749392383760501667425499 68624088575640752501138249)
      ·
        refine ⟨51468066431730564375853687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68624088575640752501138249 51468066431730564375853687)
        ·
          refine ⟨77202099647595846563780531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51468066431730564375853687 77202099647595846563780531)
          ·
            refine ⟨115803149471393769845670797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77202099647595846563780531 115803149471393769845670797)
            ·
              refine ⟨43426181051772663692126549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 115803149471393769845670797 43426181051772663692126549)
              ·
                refine ⟨127225139800115225660527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 43426181051772663692126549 127225139800115225660527)
                ·
                  rfl

theorem cell21_1672448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 10].length) (baseStart_1672448 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672448 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672448 prefixEnd_1672448 := by exact prefixLift 1672448
  have htrace : WordTrace (prefixWord ++ tailWord_1672448) baseStart_1672448 baseEnd_1672448 := by
    simpa [prefixWord, tailWord_1672448, baseEnd_1672448] using wordTrace_append hprefix tailTrace_1672448
  have hstable : (prefixWord ++ tailWord_1672448).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672448).length < 2 ^ (prefixWord ++ tailWord_1672448).sum := by decide
  have hdescent : baseEnd_1672448 < baseStart_1672448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672482 : List Nat := [3, 3, 1, 1, 4, 2, 7]
def baseStart_1672482 : Nat := 118140960795 + 1672482 * 2 ^ 59
def prefixEnd_1672482 : Nat := 4983230072969 + 3 ^ 40 * 1672482 * 2
def baseEnd_1672482 : Nat := 42409242073729908157205

theorem tailTrace_1672482 : CollatzResearch.WordTrace tailWord_1672482 prefixEnd_1672482 42409242073729908157205 := by
  unfold tailWord_1672482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15250107481722706507492925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40666953284593884019981133 15250107481722706507492925)
  ·
    refine ⟨5718790305646014940309847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15250107481722706507492925 5718790305646014940309847)
    ·
      refine ⟨8578185458469022410464771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5718790305646014940309847 8578185458469022410464771)
      ·
        refine ⟨12867278187703533615697157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8578185458469022410464771 12867278187703533615697157)
        ·
          refine ⟨2412614660194412552943217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12867278187703533615697157 2412614660194412552943217)
          ·
            refine ⟨1809460995145809414707413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2412614660194412552943217 1809460995145809414707413)
            ·
              refine ⟨42409242073729908157205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1809460995145809414707413 42409242073729908157205)
              ·
                rfl

theorem cell21_1672482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 7].length) (baseStart_1672482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672482 prefixEnd_1672482 := by exact prefixLift 1672482
  have htrace : WordTrace (prefixWord ++ tailWord_1672482) baseStart_1672482 baseEnd_1672482 := by
    simpa [prefixWord, tailWord_1672482, baseEnd_1672482] using wordTrace_append hprefix tailTrace_1672482
  have hstable : (prefixWord ++ tailWord_1672482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672482).length < 2 ^ (prefixWord ++ tailWord_1672482).sum := by decide
  have hdescent : baseEnd_1672482 < baseStart_1672482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672606 : List Nat := [4, 3, 1, 2, 2, 1, 2, 1, 5]
def baseStart_1672606 : Nat := 118140960795 + 1672606 * 2 ^ 59
def prefixEnd_1672606 : Nat := 4983230072969 + 3 ^ 40 * 1672606 * 2
def baseEnd_1672606 : Nat := 381711477152972513347925

theorem tailTrace_1672606 : CollatzResearch.WordTrace tailWord_1672606 prefixEnd_1672606 381711477152972513347925 := by
  unfold tailWord_1672606
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625619072305199400935709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40669968385627730138323781 7625619072305199400935709)
  ·
    refine ⟨2859607152114449775350891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7625619072305199400935709 2859607152114449775350891)
    ·
      refine ⟨4289410728171674663026337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2859607152114449775350891 4289410728171674663026337)
      ·
        refine ⟨3217058046128755997269753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4289410728171674663026337 3217058046128755997269753)
        ·
          refine ⟨2412793534596566997952315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3217058046128755997269753 2412793534596566997952315)
          ·
            refine ⟨3619190301894850496928473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2412793534596566997952315 3619190301894850496928473)
            ·
              refine ⟨2714392726421137872696355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3619190301894850496928473 2714392726421137872696355)
              ·
                refine ⟨4071589089631706809044533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2714392726421137872696355 4071589089631706809044533)
                ·
                  refine ⟨381711477152972513347925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071589089631706809044533 381711477152972513347925)
                  ·
                    rfl

theorem cell21_1672606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 2, 1, 5].length) (baseStart_1672606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672606 prefixEnd_1672606 := by exact prefixLift 1672606
  have htrace : WordTrace (prefixWord ++ tailWord_1672606) baseStart_1672606 baseEnd_1672606 := by
    simpa [prefixWord, tailWord_1672606, baseEnd_1672606] using wordTrace_append hprefix tailTrace_1672606
  have hstable : (prefixWord ++ tailWord_1672606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672606).length < 2 ^ (prefixWord ++ tailWord_1672606).sum := by decide
  have hdescent : baseEnd_1672606 < baseStart_1672606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672631 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 5]
def baseStart_1672631 : Nat := 118140960795 + 1672631 * 2 ^ 59
def prefixEnd_1672631 : Nat := 4983230072969 + 3 ^ 40 * 1672631 * 2
def baseEnd_1672631 : Nat := 381717182493578025431207

theorem tailTrace_1672631 : CollatzResearch.WordTrace tailWord_1672631 prefixEnd_1672631 381717182493578025431207 := by
  unfold tailWord_1672631
  simp only [CollatzResearch.WordTrace]
  refine ⟨61005864403351024477145747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40670576268900682984763831 61005864403351024477145747)
  ·
    refine ⟨91508796605026536715718621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61005864403351024477145747 91508796605026536715718621)
    ·
      refine ⟨34315798726884951268394483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91508796605026536715718621 34315798726884951268394483)
      ·
        refine ⟨51473698090327426902591725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34315798726884951268394483 51473698090327426902591725)
        ·
          refine ⟨19302636783872785088471897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51473698090327426902591725 19302636783872785088471897)
          ·
            refine ⟨14476977587904588816353923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19302636783872785088471897 14476977587904588816353923)
            ·
              refine ⟨21715466381856883224530885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14476977587904588816353923 21715466381856883224530885)
              ·
                refine ⟨4071649946598165604599541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21715466381856883224530885 4071649946598165604599541)
                ·
                  refine ⟨381717182493578025431207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4071649946598165604599541 381717182493578025431207)
                  ·
                    rfl

theorem cell21_1672631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_1672631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672631 prefixEnd_1672631 := by exact prefixLift 1672631
  have htrace : WordTrace (prefixWord ++ tailWord_1672631) baseStart_1672631 baseEnd_1672631 := by
    simpa [prefixWord, tailWord_1672631, baseEnd_1672631] using wordTrace_append hprefix tailTrace_1672631
  have hstable : (prefixWord ++ tailWord_1672631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672631).length < 2 ^ (prefixWord ++ tailWord_1672631).sum := by decide
  have hdescent : baseEnd_1672631 < baseStart_1672631 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672679 : List Nat := [1, 1, 5, 2, 1, 3, 1, 3, 4]
def baseStart_1672679 : Nat := 118140960795 + 1672679 * 2 ^ 59
def prefixEnd_1672679 : Nat := 4983230072969 + 3 ^ 40 * 1672679 * 2
def baseEnd_1672679 : Nat := 381728136747540608631109

theorem tailTrace_1672679 : CollatzResearch.WordTrace tailWord_1672679 prefixEnd_1672679 381728136747540608631109 := by
  unfold tailWord_1672679
  simp only [CollatzResearch.WordTrace]
  refine ⟨61007615107177128674893091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40671743404784752449928727 61007615107177128674893091)
  ·
    refine ⟨91511422660765693012339637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61007615107177128674893091 91511422660765693012339637)
    ·
      refine ⟨8579195874446783719906841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91511422660765693012339637 8579195874446783719906841)
      ·
        refine ⟨6434396905835087789930131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8579195874446783719906841 6434396905835087789930131)
        ·
          refine ⟨9651595358752631684895197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6434396905835087789930131 9651595358752631684895197)
          ·
            refine ⟨3619348259532236881835699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9651595358752631684895197 3619348259532236881835699)
            ·
              refine ⟨5429022389298355322753549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3619348259532236881835699 5429022389298355322753549)
              ·
                refine ⟨2035883395986883246032581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5429022389298355322753549 2035883395986883246032581)
                ·
                  refine ⟨381728136747540608631109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2035883395986883246032581 381728136747540608631109)
                  ·
                    rfl

theorem cell21_1672679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 3, 1, 3, 4].length) (baseStart_1672679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672679 prefixEnd_1672679 := by exact prefixLift 1672679
  have htrace : WordTrace (prefixWord ++ tailWord_1672679) baseStart_1672679 baseEnd_1672679 := by
    simpa [prefixWord, tailWord_1672679, baseEnd_1672679] using wordTrace_append hprefix tailTrace_1672679
  have hstable : (prefixWord ++ tailWord_1672679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672679).length < 2 ^ (prefixWord ++ tailWord_1672679).sum := by decide
  have hdescent : baseEnd_1672679 < baseStart_1672679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672890 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 4]
def baseStart_1672890 : Nat := 118140960795 + 1672890 * 2 ^ 59
def prefixEnd_1672890 : Nat := 4983230072969 + 3 ^ 40 * 1672890 * 2
def baseEnd_1672890 : Nat := 381776289822251130614011

theorem tailTrace_1672890 : CollatzResearch.WordTrace tailWord_1672890 prefixEnd_1672890 381776289822251130614011 := by
  unfold tailWord_1672890
  simp only [CollatzResearch.WordTrace]
  refine ⟨15253827727353177927706031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40676873939608474473882749 15253827727353177927706031)
  ·
    refine ⟨22880741591029766891559047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15253827727353177927706031 22880741591029766891559047)
    ·
      refine ⟨34321112386544650337338571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22880741591029766891559047 34321112386544650337338571)
      ·
        refine ⟨51481668579816975506007857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34321112386544650337338571 51481668579816975506007857)
        ·
          refine ⟨38611251434862731629505893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51481668579816975506007857 38611251434862731629505893)
          ·
            refine ⟨7239609644036762180532355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38611251434862731629505893 7239609644036762180532355)
            ·
              refine ⟨10859414466055143270798533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7239609644036762180532355 10859414466055143270798533)
              ·
                refine ⟨2036140212385339363274725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10859414466055143270798533 2036140212385339363274725)
                ·
                  refine ⟨381776289822251130614011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036140212385339363274725 381776289822251130614011)
                  ·
                    rfl

theorem cell21_1672890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 4].length) (baseStart_1672890 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672890 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672890 prefixEnd_1672890 := by exact prefixLift 1672890
  have htrace : WordTrace (prefixWord ++ tailWord_1672890) baseStart_1672890 baseEnd_1672890 := by
    simpa [prefixWord, tailWord_1672890, baseEnd_1672890] using wordTrace_append hprefix tailTrace_1672890
  have hstable : (prefixWord ++ tailWord_1672890).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672890).length < 2 ^ (prefixWord ++ tailWord_1672890).sum := by decide
  have hdescent : baseEnd_1672890 < baseStart_1672890 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1672921 : List Nat := [1, 2, 1, 2, 3, 4, 3, 5]
def baseStart_1672921 : Nat := 118140960795 + 1672921 * 2 ^ 59
def prefixEnd_1672921 : Nat := 4983230072969 + 3 ^ 40 * 1672921 * 2
def baseEnd_1672921 : Nat := 127261121481533988532427

theorem tailTrace_1672921 : CollatzResearch.WordTrace tailWord_1672921 prefixEnd_1672921 127261121481533988532427 := by
  unfold tailWord_1672921
  simp only [CollatzResearch.WordTrace]
  refine ⟨61016441572300404005202617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40677627714866936003468411 61016441572300404005202617)
  ·
    refine ⟨45762331179225303003901963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61016441572300404005202617 45762331179225303003901963)
    ·
      refine ⟨68643496768837954505852945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45762331179225303003901963 68643496768837954505852945)
      ·
        refine ⟨51482622576628465879389709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68643496768837954505852945 51482622576628465879389709)
        ·
          refine ⟨19305983466235674704771141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51482622576628465879389709 19305983466235674704771141)
          ·
            refine ⟨3619871899919189007144589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19305983466235674704771141 3619871899919189007144589)
            ·
              refine ⟨1357451962469695877679221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3619871899919189007144589 1357451962469695877679221)
              ·
                refine ⟨127261121481533988532427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1357451962469695877679221 127261121481533988532427)
                ·
                  rfl

theorem cell21_1672921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 3, 5].length) (baseStart_1672921 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1672921 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1672921 prefixEnd_1672921 := by exact prefixLift 1672921
  have htrace : WordTrace (prefixWord ++ tailWord_1672921) baseStart_1672921 baseEnd_1672921 := by
    simpa [prefixWord, tailWord_1672921, baseEnd_1672921] using wordTrace_append hprefix tailTrace_1672921
  have hstable : (prefixWord ++ tailWord_1672921).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1672921).length < 2 ^ (prefixWord ++ tailWord_1672921).sum := by decide
  have hdescent : baseEnd_1672921 < baseStart_1672921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1672921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673014 : List Nat := [5, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1673014 : Nat := 118140960795 + 1673014 * 2 ^ 59
def prefixEnd_1673014 : Nat := 4983230072969 + 3 ^ 40 * 1673014 * 2
def baseEnd_1673014 : Nat := 127268196103884823515697

theorem tailTrace_1673014 : CollatzResearch.WordTrace tailWord_1673014 prefixEnd_1673014 127268196103884823515697 := by
  unfold tailWord_1673014
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813739597560217555521131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40679889040642320592225397 3813739597560217555521131)
  ·
    refine ⟨5720609396340326333281697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3813739597560217555521131 5720609396340326333281697)
    ·
      refine ⟨4290457047255244749961273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5720609396340326333281697 4290457047255244749961273)
      ·
        refine ⟨3217842785441433562470955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4290457047255244749961273 3217842785441433562470955)
        ·
          refine ⟨4826764178162150343706433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3217842785441433562470955 4826764178162150343706433)
          ·
            refine ⟨3620073133621612757779825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4826764178162150343706433 3620073133621612757779825)
            ·
              refine ⟨2715054850216209568334869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3620073133621612757779825 2715054850216209568334869)
              ·
                refine ⟨127268196103884823515697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2715054850216209568334869 127268196103884823515697)
                ·
                  rfl

theorem cell21_1673014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1673014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673014 prefixEnd_1673014 := by exact prefixLift 1673014
  have htrace : WordTrace (prefixWord ++ tailWord_1673014) baseStart_1673014 baseEnd_1673014 := by
    simpa [prefixWord, tailWord_1673014, baseEnd_1673014] using wordTrace_append hprefix tailTrace_1673014
  have hstable : (prefixWord ++ tailWord_1673014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673014).length < 2 ^ (prefixWord ++ tailWord_1673014).sum := by decide
  have hdescent : baseEnd_1673014 < baseStart_1673014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673017 : List Nat := [1, 2, 1, 7, 1, 2, 2, 1, 4]
def baseStart_1673017 : Nat := 118140960795 + 1673017 * 2 ^ 59
def prefixEnd_1673017 : Nat := 4983230072969 + 3 ^ 40 * 1673017 * 2
def baseEnd_1673017 : Nat := 381805272952527131997085

theorem tailTrace_1673017 : CollatzResearch.WordTrace tailWord_1673017 prefixEnd_1673017 381805272952527131997085 := by
  unfold tailWord_1673017
  simp only [CollatzResearch.WordTrace]
  refine ⟨61019942979952612400697305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40679961986635074933798203 61019942979952612400697305)
  ·
    refine ⟨45764957234964459300522979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61019942979952612400697305 45764957234964459300522979)
    ·
      refine ⟨68647435852446688950784469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45764957234964459300522979 68647435852446688950784469)
      ·
        refine ⟨1608924277791719272284011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 68647435852446688950784469 1608924277791719272284011)
        ·
          refine ⟨2413386416687578908426017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1608924277791719272284011 2413386416687578908426017)
          ·
            refine ⟨1810039812515684181319513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413386416687578908426017 1810039812515684181319513)
            ·
              refine ⟨1357529859386763135989635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810039812515684181319513 1357529859386763135989635)
              ·
                refine ⟨2036294789080144703984453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357529859386763135989635 2036294789080144703984453)
                ·
                  refine ⟨381805272952527131997085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036294789080144703984453 381805272952527131997085)
                  ·
                    rfl

theorem cell21_1673017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_1673017 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673017 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673017 prefixEnd_1673017 := by exact prefixLift 1673017
  have htrace : WordTrace (prefixWord ++ tailWord_1673017) baseStart_1673017 baseEnd_1673017 := by
    simpa [prefixWord, tailWord_1673017, baseEnd_1673017] using wordTrace_append hprefix tailTrace_1673017
  have hstable : (prefixWord ++ tailWord_1673017).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673017).length < 2 ^ (prefixWord ++ tailWord_1673017).sum := by decide
  have hdescent : baseEnd_1673017 < baseStart_1673017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673059 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 4]
def baseStart_1673059 : Nat := 118140960795 + 1673059 * 2 ^ 59
def prefixEnd_1673059 : Nat := 4983230072969 + 3 ^ 40 * 1673059 * 2
def baseEnd_1673059 : Nat := 381814857924744392296999

theorem tailTrace_1673059 : CollatzResearch.WordTrace tailWord_1673059 prefixEnd_1673059 381814857924744392296999 := by
  unfold tailWord_1673059
  simp only [CollatzResearch.WordTrace]
  refine ⟨61021474845800453573726231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40680983230533635715817487 61021474845800453573726231)
  ·
    refine ⟨91532212268700680360589347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61021474845800453573726231 91532212268700680360589347)
    ·
      refine ⟨137298318403051020540884021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91532212268700680360589347 137298318403051020540884021)
      ·
        refine ⟨12871717350286033175707877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137298318403051020540884021 12871717350286033175707877)
        ·
          refine ⟨2413447003178631220445227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12871717350286033175707877 2413447003178631220445227)
          ·
            refine ⟨3620170504767946830667841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413447003178631220445227 3620170504767946830667841)
            ·
              refine ⟨2715127878575960123000881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3620170504767946830667841 2715127878575960123000881)
              ·
                refine ⟨2036345908931970092250661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715127878575960123000881 2036345908931970092250661)
                ·
                  refine ⟨381814857924744392296999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036345908931970092250661 381814857924744392296999)
                  ·
                    rfl

theorem cell21_1673059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 4].length) (baseStart_1673059 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673059 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673059 prefixEnd_1673059 := by exact prefixLift 1673059
  have htrace : WordTrace (prefixWord ++ tailWord_1673059) baseStart_1673059 baseEnd_1673059 := by
    simpa [prefixWord, tailWord_1673059, baseEnd_1673059] using wordTrace_append hprefix tailTrace_1673059
  have hstable : (prefixWord ++ tailWord_1673059).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673059).length < 2 ^ (prefixWord ++ tailWord_1673059).sum := by decide
  have hdescent : baseEnd_1673059 < baseStart_1673059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673110 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1673110 : Nat := 118140960795 + 1673110 * 2 ^ 59
def prefixEnd_1673110 : Nat := 4983230072969 + 3 ^ 40 * 1673110 * 2
def baseEnd_1673110 : Nat := 381826496819579636946895

theorem tailTrace_1673110 : CollatzResearch.WordTrace tailWord_1673110 prefixEnd_1673110 381826496819579636946895 := by
  unfold tailWord_1673110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3813958435538480580239549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40682223312410459522555189 3813958435538480580239549)
  ·
    refine ⟨1430234413326930217589831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3813958435538480580239549 1430234413326930217589831)
    ·
      refine ⟨2145351619990395326384747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1430234413326930217589831 2145351619990395326384747)
      ·
        refine ⟨3218027429985592989577121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145351619990395326384747 3218027429985592989577121)
        ·
          refine ⟨2413520572489194742182841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3218027429985592989577121 2413520572489194742182841)
          ·
            refine ⟨1810140429366896056637131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2413520572489194742182841 1810140429366896056637131)
            ·
              refine ⟨2715210644050344084955697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810140429366896056637131 2715210644050344084955697)
              ·
                refine ⟨2036407983037758063716773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715210644050344084955697 2036407983037758063716773)
                ·
                  refine ⟨381826496819579636946895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036407983037758063716773 381826496819579636946895)
                  ·
                    rfl

theorem cell21_1673110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1673110 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673110 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673110 prefixEnd_1673110 := by exact prefixLift 1673110
  have htrace : WordTrace (prefixWord ++ tailWord_1673110) baseStart_1673110 baseEnd_1673110 := by
    simpa [prefixWord, tailWord_1673110, baseEnd_1673110] using wordTrace_append hprefix tailTrace_1673110
  have hstable : (prefixWord ++ tailWord_1673110).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673110).length < 2 ^ (prefixWord ++ tailWord_1673110).sum := by decide
  have hdescent : baseEnd_1673110 < baseStart_1673110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673146 : List Nat := [3, 1, 1, 1, 2, 1, 2, 3, 7]
def baseStart_1673146 : Nat := 118140960795 + 1673146 * 2 ^ 59
def prefixEnd_1673146 : Nat := 4983230072969 + 3 ^ 40 * 1673146 * 2
def baseEnd_1673146 : Nat := 381834712510051574346821

theorem tailTrace_1673146 : CollatzResearch.WordTrace tailWord_1673146 prefixEnd_1673146 381834712510051574346821 := by
  unfold tailWord_1673146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15256161999121316858035823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40683098664323511621428861 15256161999121316858035823)
  ·
    refine ⟨22884242998681975287053735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15256161999121316858035823 22884242998681975287053735)
    ·
      refine ⟨34326364498022962930580603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22884242998681975287053735 34326364498022962930580603)
      ·
        refine ⟨51489546747034444395870905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34326364498022962930580603 51489546747034444395870905)
        ·
          refine ⟨38617160060275833296903179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51489546747034444395870905 38617160060275833296903179)
          ·
            refine ⟨57925740090413749945354769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38617160060275833296903179 57925740090413749945354769)
            ·
              refine ⟨43444305067810312459016077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57925740090413749945354769 43444305067810312459016077)
              ·
                refine ⟨16291614400428867172131029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43444305067810312459016077 16291614400428867172131029)
                ·
                  refine ⟨381834712510051574346821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16291614400428867172131029 381834712510051574346821)
                  ·
                    rfl

theorem cell21_1673146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 3, 7].length) (baseStart_1673146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673146 prefixEnd_1673146 := by exact prefixLift 1673146
  have htrace : WordTrace (prefixWord ++ tailWord_1673146) baseStart_1673146 baseEnd_1673146 := by
    simpa [prefixWord, tailWord_1673146, baseEnd_1673146] using wordTrace_append hprefix tailTrace_1673146
  have hstable : (prefixWord ++ tailWord_1673146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673146).length < 2 ^ (prefixWord ++ tailWord_1673146).sum := by decide
  have hdescent : baseEnd_1673146 < baseStart_1673146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673149 : List Nat := [1, 4, 1, 2, 3, 1, 4, 5]
def baseStart_1673149 : Nat := 118140960795 + 1673149 * 2 ^ 59
def prefixEnd_1673149 : Nat := 4983230072969 + 3 ^ 40 * 1673149 * 2
def baseEnd_1673149 : Nat := 127278465716974745265605

theorem tailTrace_1673149 : CollatzResearch.WordTrace tailWord_1673149 prefixEnd_1673149 127278465716974745265605 := by
  unfold tailWord_1673149
  simp only [CollatzResearch.WordTrace]
  refine ⟨61024757415474398944502501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40683171610316265963001667 61024757415474398944502501)
  ·
    refine ⟨11442142015401449802094219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61024757415474398944502501 11442142015401449802094219)
    ·
      refine ⟨17163213023102174703141329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11442142015401449802094219 17163213023102174703141329)
      ·
        refine ⟨12872409767326631027355997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17163213023102174703141329 12872409767326631027355997)
        ·
          refine ⟨4827153662747486635258499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12872409767326631027355997 4827153662747486635258499)
          ·
            refine ⟨7240730494121229952887749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827153662747486635258499 7240730494121229952887749)
            ·
              refine ⟨1357636967647730616166453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7240730494121229952887749 1357636967647730616166453)
              ·
                refine ⟨127278465716974745265605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1357636967647730616166453 127278465716974745265605)
                ·
                  rfl

theorem cell21_1673149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 4, 5].length) (baseStart_1673149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673149 prefixEnd_1673149 := by exact prefixLift 1673149
  have htrace : WordTrace (prefixWord ++ tailWord_1673149) baseStart_1673149 baseEnd_1673149 := by
    simpa [prefixWord, tailWord_1673149, baseEnd_1673149] using wordTrace_append hprefix tailTrace_1673149
  have hstable : (prefixWord ++ tailWord_1673149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673149).length < 2 ^ (prefixWord ++ tailWord_1673149).sum := by decide
  have hdescent : baseEnd_1673149 < baseStart_1673149 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673186 : List Nat := [3, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1673186 : Nat := 118140960795 + 1673186 * 2 ^ 59
def prefixEnd_1673186 : Nat := 4983230072969 + 3 ^ 40 * 1673186 * 2
def baseEnd_1673186 : Nat := 381843841055020393680073

theorem tailTrace_1673186 : CollatzResearch.WordTrace tailWord_1673186 prefixEnd_1673186 381843841055020393680073 := by
  unfold tailWord_1673186
  simp only [CollatzResearch.WordTrace]
  refine ⟨15256526729085088565899853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40684071277560236175732941 15256526729085088565899853)
  ·
    refine ⟨5721197523406908212212445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15256526729085088565899853 5721197523406908212212445)
    ·
      refine ⟨2145449071277590579579667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5721197523406908212212445 2145449071277590579579667)
      ·
        refine ⟨3218173606916385869369501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2145449071277590579579667 3218173606916385869369501)
        ·
          refine ⟨1206815102593644701013563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3218173606916385869369501 1206815102593644701013563)
          ·
            refine ⟨1810222653890467051520345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206815102593644701013563 1810222653890467051520345)
            ·
              refine ⟨1357666990417850288640259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1810222653890467051520345 1357666990417850288640259)
              ·
                refine ⟨2036500485626775432960389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1357666990417850288640259 2036500485626775432960389)
                ·
                  refine ⟨381843841055020393680073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036500485626775432960389 381843841055020393680073)
                  ·
                    rfl

theorem cell21_1673186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1673186 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673186 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673186 prefixEnd_1673186 := by exact prefixLift 1673186
  have htrace : WordTrace (prefixWord ++ tailWord_1673186) baseStart_1673186 baseEnd_1673186 := by
    simpa [prefixWord, tailWord_1673186, baseEnd_1673186] using wordTrace_append hprefix tailTrace_1673186
  have hstable : (prefixWord ++ tailWord_1673186).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673186).length < 2 ^ (prefixWord ++ tailWord_1673186).sum := by decide
  have hdescent : baseEnd_1673186 < baseStart_1673186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673194 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 4]
def baseStart_1673194 : Nat := 118140960795 + 1673194 * 2 ^ 59
def prefixEnd_1673194 : Nat := 4983230072969 + 3 ^ 40 * 1673194 * 2
def baseEnd_1673194 : Nat := 381845666764014157546723

theorem tailTrace_1673194 : CollatzResearch.WordTrace tailWord_1673194 prefixEnd_1673194 381845666764014157546723 := by
  unfold tailWord_1673194
  simp only [CollatzResearch.WordTrace]
  refine ⟨15256599675077842907472659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40684265800207581086593757 15256599675077842907472659)
  ·
    refine ⟨22884899512616764361208989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15256599675077842907472659 22884899512616764361208989)
    ·
      refine ⟨8581837317231286635453371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22884899512616764361208989 8581837317231286635453371)
      ·
        refine ⟨12872755975846929953180057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8581837317231286635453371 12872755975846929953180057)
        ·
          refine ⟨9654566981885197464885043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12872755975846929953180057 9654566981885197464885043)
          ·
            refine ⟨14481850472827796197327565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9654566981885197464885043 14481850472827796197327565)
            ·
              refine ⟨5430693927310423573997837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14481850472827796197327565 5430693927310423573997837)
              ·
                refine ⟨2036510222741408840249189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5430693927310423573997837 2036510222741408840249189)
                ·
                  refine ⟨381845666764014157546723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036510222741408840249189 381845666764014157546723)
                  ·
                    rfl

theorem cell21_1673194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 4].length) (baseStart_1673194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673194 prefixEnd_1673194 := by exact prefixLift 1673194
  have htrace : WordTrace (prefixWord ++ tailWord_1673194) baseStart_1673194 baseEnd_1673194 := by
    simpa [prefixWord, tailWord_1673194, baseEnd_1673194] using wordTrace_append hprefix tailTrace_1673194
  have hstable : (prefixWord ++ tailWord_1673194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673194).length < 2 ^ (prefixWord ++ tailWord_1673194).sum := by decide
  have hdescent : baseEnd_1673194 < baseStart_1673194 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673267 : List Nat := [1, 1, 1, 2, 4, 1, 2, 9]
def baseStart_1673267 : Nat := 118140960795 + 1673267 * 2 ^ 59
def prefixEnd_1673267 : Nat := 4983230072969 + 3 ^ 40 * 1673267 * 2
def baseEnd_1673267 : Nat := 127287442119527417609969

theorem tailTrace_1673267 : CollatzResearch.WordTrace tailWord_1673267 prefixEnd_1673267 127287442119527417609969 := by
  unfold tailWord_1673267
  simp only [CollatzResearch.WordTrace]
  refine ⟨61029061229046905097298055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40686040819364603398198703 61029061229046905097298055)
  ·
    refine ⟨91543591843570357645947083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61029061229046905097298055 91543591843570357645947083)
    ·
      refine ⟨137315387765355536468920625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91543591843570357645947083 137315387765355536468920625)
      ·
        refine ⟨102986540824016652351690469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137315387765355536468920625 102986540824016652351690469)
        ·
          refine ⟨19309976404503122315941963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 102986540824016652351690469 19309976404503122315941963)
          ·
            refine ⟨28964964606754683473912945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19309976404503122315941963 28964964606754683473912945)
            ·
              refine ⟨21723723455066012605434709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28964964606754683473912945 21723723455066012605434709)
              ·
                refine ⟨127287442119527417609969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21723723455066012605434709 127287442119527417609969)
                ·
                  rfl

theorem cell21_1673267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 9].length) (baseStart_1673267 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673267 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673267 prefixEnd_1673267 := by exact prefixLift 1673267
  have htrace : WordTrace (prefixWord ++ tailWord_1673267) baseStart_1673267 baseEnd_1673267 := by
    simpa [prefixWord, tailWord_1673267, baseEnd_1673267] using wordTrace_append hprefix tailTrace_1673267
  have hstable : (prefixWord ++ tailWord_1673267).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673267).length < 2 ^ (prefixWord ++ tailWord_1673267).sum := by decide
  have hdescent : baseEnd_1673267 < baseStart_1673267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673270 : List Nat := [5, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1673270 : Nat := 118140960795 + 1673270 * 2 ^ 59
def prefixEnd_1673270 : Nat := 4983230072969 + 3 ^ 40 * 1673270 * 2
def baseEnd_1673270 : Nat := 381863010999454914279901

theorem tailTrace_1673270 : CollatzResearch.WordTrace tailWord_1673270 prefixEnd_1673270 381863010999454914279901 := by
  unfold tailWord_1673270
  simp only [CollatzResearch.WordTrace]
  refine ⟨3814323165502252288103579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40686113765357357739771509 3814323165502252288103579)
  ·
    refine ⟨5721484748253378432155369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3814323165502252288103579 5721484748253378432155369)
    ·
      refine ⟨4291113561190033824116527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5721484748253378432155369 4291113561190033824116527)
      ·
        refine ⟨6436670341785050736174791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4291113561190033824116527 6436670341785050736174791)
        ·
          refine ⟨9655005512677576104262187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6436670341785050736174791 9655005512677576104262187)
          ·
            refine ⟨14482508269016364156393281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9655005512677576104262187 14482508269016364156393281)
            ·
              refine ⟨10861881201762273117294961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14482508269016364156393281 10861881201762273117294961)
              ·
                refine ⟨8146410901321704837971221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10861881201762273117294961 8146410901321704837971221)
                ·
                  refine ⟨381863010999454914279901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8146410901321704837971221 381863010999454914279901)
                  ·
                    rfl

theorem cell21_1673270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1673270 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673270 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673270 prefixEnd_1673270 := by exact prefixLift 1673270
  have htrace : WordTrace (prefixWord ++ tailWord_1673270) baseStart_1673270 baseEnd_1673270 := by
    simpa [prefixWord, tailWord_1673270, baseEnd_1673270] using wordTrace_append hprefix tailTrace_1673270
  have hstable : (prefixWord ++ tailWord_1673270).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673270).length < 2 ^ (prefixWord ++ tailWord_1673270).sum := by decide
  have hdescent : baseEnd_1673270 < baseStart_1673270 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673273 : List Nat := [1, 2, 1, 5, 3, 1, 2, 3, 3]
def baseStart_1673273 : Nat := 118140960795 + 1673273 * 2 ^ 59
def prefixEnd_1673273 : Nat := 4983230072969 + 3 ^ 40 * 1673273 * 2
def baseEnd_1673273 : Nat := 381863695640327575729895

theorem tailTrace_1673273 : CollatzResearch.WordTrace tailWord_1673273 prefixEnd_1673273 381863695640327575729895 := by
  unfold tailWord_1673273
  simp only [CollatzResearch.WordTrace]
  refine ⟨61029280067025168122016473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40686186711350112081344315 61029280067025168122016473)
  ·
    refine ⟨45771960050268876091512355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61029280067025168122016473 45771960050268876091512355)
    ·
      refine ⟨68657940075403314137268533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45771960050268876091512355 68657940075403314137268533)
      ·
        refine ⟨6436681882069060700368925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68657940075403314137268533 6436681882069060700368925)
        ·
          refine ⟨2413755705775897762638347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6436681882069060700368925 2413755705775897762638347)
          ·
            refine ⟨3620633558663846643957521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2413755705775897762638347 3620633558663846643957521)
            ·
              refine ⟨2715475168997884982968141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3620633558663846643957521 2715475168997884982968141)
              ·
                refine ⟨1018303188374206868613053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2715475168997884982968141 1018303188374206868613053)
                ·
                  refine ⟨381863695640327575729895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018303188374206868613053 381863695640327575729895)
                  ·
                    rfl

theorem cell21_1673273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_1673273 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673273 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673273 prefixEnd_1673273 := by exact prefixLift 1673273
  have htrace : WordTrace (prefixWord ++ tailWord_1673273) baseStart_1673273 baseEnd_1673273 := by
    simpa [prefixWord, tailWord_1673273, baseEnd_1673273] using wordTrace_append hprefix tailTrace_1673273
  have hstable : (prefixWord ++ tailWord_1673273).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673273).length < 2 ^ (prefixWord ++ tailWord_1673273).sum := by decide
  have hdescent : baseEnd_1673273 < baseStart_1673273 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673349 : List Nat := [1, 3, 1, 1, 5, 2, 3, 2, 3]
def baseStart_1673349 : Nat := 118140960795 + 1673349 * 2 ^ 59
def prefixEnd_1673349 : Nat := 4983230072969 + 3 ^ 40 * 1673349 * 2
def baseEnd_1673349 : Nat := 381881039875768332463073

theorem tailTrace_1673349 : CollatzResearch.WordTrace tailWord_1673349 prefixEnd_1673349 381881039875768332463073 := by
  unfold tailWord_1673349
  simp only [CollatzResearch.WordTrace]
  refine ⟨61032052014749833101783101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40688034676499888734522067 61032052014749833101783101)
  ·
    refine ⟨22887019505531187413168663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61032052014749833101783101 22887019505531187413168663)
    ·
      refine ⟨34330529258296781119752995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22887019505531187413168663 34330529258296781119752995)
      ·
        refine ⟨51495793887445171679629493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34330529258296781119752995 51495793887445171679629493)
        ·
          refine ⟨4827730676947984844965265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51495793887445171679629493 4827730676947984844965265)
          ·
            refine ⟨3620798007710988633723949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4827730676947984844965265 3620798007710988633723949)
            ·
              refine ⟨1357799252891620737646481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3620798007710988633723949 1357799252891620737646481)
              ·
                refine ⟨1018349439668715553234861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1357799252891620737646481 1018349439668715553234861)
                ·
                  refine ⟨381881039875768332463073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018349439668715553234861 381881039875768332463073)
                  ·
                    rfl

theorem cell21_1673349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_1673349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673349 prefixEnd_1673349 := by exact prefixLift 1673349
  have htrace : WordTrace (prefixWord ++ tailWord_1673349) baseStart_1673349 baseEnd_1673349 := by
    simpa [prefixWord, tailWord_1673349, baseEnd_1673349] using wordTrace_append hprefix tailTrace_1673349
  have hstable : (prefixWord ++ tailWord_1673349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673349).length < 2 ^ (prefixWord ++ tailWord_1673349).sum := by decide
  have hdescent : baseEnd_1673349 < baseStart_1673349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673391 : List Nat := [1, 1, 2, 1, 2, 3, 1, 7, 3]
def baseStart_1673391 : Nat := 118140960795 + 1673391 * 2 ^ 59
def prefixEnd_1673391 : Nat := 4983230072969 + 3 ^ 40 * 1673391 * 2
def baseEnd_1673391 : Nat := 381890624847985592762987

theorem tailTrace_1673391 : CollatzResearch.WordTrace tailWord_1673391 prefixEnd_1673391 381890624847985592762987 := by
  unfold tailWord_1673391
  simp only [CollatzResearch.WordTrace]
  refine ⟨61033583880597674274812027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40689055920398449516541351 61033583880597674274812027)
  ·
    refine ⟨91550375820896511412218041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61033583880597674274812027 91550375820896511412218041)
    ·
      refine ⟨68662781865672383559163531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91550375820896511412218041 68662781865672383559163531)
      ·
        refine ⟨102994172798508575338745297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68662781865672383559163531 102994172798508575338745297)
        ·
          refine ⟨77245629598881431504058973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102994172798508575338745297 77245629598881431504058973)
          ·
            refine ⟨28967111099580536814022115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77245629598881431504058973 28967111099580536814022115)
            ·
              refine ⟨43450666649370805221033173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28967111099580536814022115 43450666649370805221033173)
              ·
                refine ⟨1018374999594628247367965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43450666649370805221033173 1018374999594628247367965)
                ·
                  refine ⟨381890624847985592762987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018374999594628247367965 381890624847985592762987)
                  ·
                    rfl

theorem cell21_1673391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 3].length) (baseStart_1673391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673391 prefixEnd_1673391 := by exact prefixLift 1673391
  have htrace : WordTrace (prefixWord ++ tailWord_1673391) baseStart_1673391 baseEnd_1673391 := by
    simpa [prefixWord, tailWord_1673391, baseEnd_1673391] using wordTrace_append hprefix tailTrace_1673391
  have hstable : (prefixWord ++ tailWord_1673391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673391).length < 2 ^ (prefixWord ++ tailWord_1673391).sum := by decide
  have hdescent : baseEnd_1673391 < baseStart_1673391 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673408 : List Nat := [2, 1, 1, 2, 5, 2, 1, 4, 3]
def baseStart_1673408 : Nat := 118140960795 + 1673408 * 2 ^ 59
def prefixEnd_1673408 : Nat := 4983230072969 + 3 ^ 40 * 1673408 * 2
def baseEnd_1673408 : Nat := 381894504479597340979619

theorem tailTrace_1673408 : CollatzResearch.WordTrace tailWord_1673408 prefixEnd_1673408 381894504479597340979619 := by
  unfold tailWord_1673408
  simp only [CollatzResearch.WordTrace]
  refine ⟨30517101960768043089090439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40689469281024057452120585 30517101960768043089090439)
  ·
    refine ⟨45775652941152064633635659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30517101960768043089090439 45775652941152064633635659)
    ·
      refine ⟨68663479411728096950453489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45775652941152064633635659 68663479411728096950453489)
      ·
        refine ⟨51497609558796072712840117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68663479411728096950453489 51497609558796072712840117)
        ·
          refine ⟨4827900896137131816828761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51497609558796072712840117 4827900896137131816828761)
          ·
            refine ⟨3620925672102848862621571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4827900896137131816828761 3620925672102848862621571)
            ·
              refine ⟨5431388508154273293932357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620925672102848862621571 5431388508154273293932357)
              ·
                refine ⟨1018385345278926242612317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5431388508154273293932357 1018385345278926242612317)
                ·
                  refine ⟨381894504479597340979619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018385345278926242612317 381894504479597340979619)
                  ·
                    rfl

theorem cell21_1673408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 3].length) (baseStart_1673408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673408 prefixEnd_1673408 := by exact prefixLift 1673408
  have htrace : WordTrace (prefixWord ++ tailWord_1673408) baseStart_1673408 baseEnd_1673408 := by
    simpa [prefixWord, tailWord_1673408, baseEnd_1673408] using wordTrace_append hprefix tailTrace_1673408
  have hstable : (prefixWord ++ tailWord_1673408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673408).length < 2 ^ (prefixWord ++ tailWord_1673408).sum := by decide
  have hdescent : baseEnd_1673408 < baseStart_1673408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673422 : List Nat := [4, 1, 1, 1, 4, 1, 2, 3, 4]
def baseStart_1673422 : Nat := 118140960795 + 1673422 * 2 ^ 59
def prefixEnd_1673422 : Nat := 4983230072969 + 3 ^ 40 * 1673422 * 2
def baseEnd_1673422 : Nat := 381897699470336427746257

theorem tailTrace_1673422 : CollatzResearch.WordTrace tailWord_1673422 prefixEnd_1673422 381897699470336427746257 := by
  unfold tailWord_1673422
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629339317935670821148815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40689809695656911046127013 7629339317935670821148815)
  ·
    refine ⟨11444008976903506231723223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629339317935670821148815 11444008976903506231723223)
    ·
      refine ⟨17166013465355259347584835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11444008976903506231723223 17166013465355259347584835)
      ·
        refine ⟨25749020198032889021377253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17166013465355259347584835 25749020198032889021377253)
        ·
          refine ⟨4827941287131166691508235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25749020198032889021377253 4827941287131166691508235)
          ·
            refine ⟨7241911930696750037262353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827941287131166691508235 7241911930696750037262353)
            ·
              refine ⟨5431433948022562527946765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241911930696750037262353 5431433948022562527946765)
              ·
                refine ⟨2036787730508460947980037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5431433948022562527946765 2036787730508460947980037)
                ·
                  refine ⟨381897699470336427746257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036787730508460947980037 381897699470336427746257)
                  ·
                    rfl

theorem cell21_1673422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 3, 4].length) (baseStart_1673422 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673422 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673422 prefixEnd_1673422 := by exact prefixLift 1673422
  have htrace : WordTrace (prefixWord ++ tailWord_1673422) baseStart_1673422 baseEnd_1673422 := by
    simpa [prefixWord, tailWord_1673422, baseEnd_1673422] using wordTrace_append hprefix tailTrace_1673422
  have hstable : (prefixWord ++ tailWord_1673422).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673422).length < 2 ^ (prefixWord ++ tailWord_1673422).sum := by decide
  have hdescent : baseEnd_1673422 < baseStart_1673422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673450 : List Nat := [3, 1, 3, 1, 1, 2, 1, 2, 7]
def baseStart_1673450 : Nat := 118140960795 + 1673450 * 2 ^ 59
def prefixEnd_1673450 : Nat := 4983230072969 + 3 ^ 40 * 1673450 * 2
def baseEnd_1673450 : Nat := 381904089451814601279533

theorem tailTrace_1673450 : CollatzResearch.WordTrace tailWord_1673450 prefixEnd_1673450 381904089451814601279533 := by
  unfold tailWord_1673450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15258933946845981837802451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40690490524922618234139869 15258933946845981837802451)
  ·
    refine ⟨22888400920268972756703677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15258933946845981837802451 22888400920268972756703677)
    ·
      refine ⟨8583150345100864783763879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22888400920268972756703677 8583150345100864783763879)
      ·
        refine ⟨12874725517651297175645819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8583150345100864783763879 12874725517651297175645819)
        ·
          refine ⟨19312088276476945763468729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12874725517651297175645819 19312088276476945763468729)
          ·
            refine ⟨14484066207357709322601547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19312088276476945763468729 14484066207357709322601547)
            ·
              refine ⟨21726099311036563983902321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14484066207357709322601547 21726099311036563983902321)
              ·
                refine ⟨16294574483277422987926741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21726099311036563983902321 16294574483277422987926741)
                ·
                  refine ⟨381904089451814601279533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16294574483277422987926741 381904089451814601279533)
                  ·
                    rfl

theorem cell21_1673450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 2, 7].length) (baseStart_1673450 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673450 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673450 prefixEnd_1673450 := by exact prefixLift 1673450
  have htrace : WordTrace (prefixWord ++ tailWord_1673450) baseStart_1673450 baseEnd_1673450 := by
    simpa [prefixWord, tailWord_1673450, baseEnd_1673450] using wordTrace_append hprefix tailTrace_1673450
  have hstable : (prefixWord ++ tailWord_1673450).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673450).length < 2 ^ (prefixWord ++ tailWord_1673450).sum := by decide
  have hdescent : baseEnd_1673450 < baseStart_1673450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673518 : List Nat := [4, 1, 3, 3, 2, 1, 1, 1, 5]
def baseStart_1673518 : Nat := 118140960795 + 1673518 * 2 ^ 59
def prefixEnd_1673518 : Nat := 4983230072969 + 3 ^ 40 * 1673518 * 2
def baseEnd_1673518 : Nat := 381919607978261594146061

theorem tailTrace_1673518 : CollatzResearch.WordTrace tailWord_1673518 prefixEnd_1673518 381919607978261594146061 := by
  unfold tailWord_1673518
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629776993892196870585651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40692143967425049976456805 7629776993892196870585651)
  ·
    refine ⟨11444665490838295305878477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7629776993892196870585651 11444665490838295305878477)
    ·
      refine ⟨4291749559064360739704429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11444665490838295305878477 4291749559064360739704429)
      ·
        refine ⟨1609406084649135277389161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4291749559064360739704429 1609406084649135277389161)
        ·
          refine ⟨1207054563486851458041871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609406084649135277389161 1207054563486851458041871)
          ·
            refine ⟨1810581845230277187062807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207054563486851458041871 1810581845230277187062807)
            ·
              refine ⟨2715872767845415780594211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810581845230277187062807 2715872767845415780594211)
              ·
                refine ⟨4073809151768123670891317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715872767845415780594211 4073809151768123670891317)
                ·
                  refine ⟨381919607978261594146061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4073809151768123670891317 381919607978261594146061)
                  ·
                    rfl

theorem cell21_1673518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 1, 1, 5].length) (baseStart_1673518 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673518 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673518 prefixEnd_1673518 := by exact prefixLift 1673518
  have htrace : WordTrace (prefixWord ++ tailWord_1673518) baseStart_1673518 baseEnd_1673518 := by
    simpa [prefixWord, tailWord_1673518, baseEnd_1673518] using wordTrace_append hprefix tailTrace_1673518
  have hstable : (prefixWord ++ tailWord_1673518).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673518).length < 2 ^ (prefixWord ++ tailWord_1673518).sum := by decide
  have hdescent : baseEnd_1673518 < baseStart_1673518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673566 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 4]
def baseStart_1673566 : Nat := 118140960795 + 1673566 * 2 ^ 59
def prefixEnd_1673566 : Nat := 4983230072969 + 3 ^ 40 * 1673566 * 2
def baseEnd_1673566 : Nat := 381930562232224177345963

theorem tailTrace_1673566 : CollatzResearch.WordTrace tailWord_1673566 prefixEnd_1673566 381930562232224177345963 := by
  unfold tailWord_1673566
  simp only [CollatzResearch.WordTrace]
  refine ⟨7629995831870459895304069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40693311103309119441621701 7629995831870459895304069)
  ·
    refine ⟨1430624218475711230369513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7629995831870459895304069 1430624218475711230369513)
    ·
      refine ⟨1072968163856783422777135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430624218475711230369513 1072968163856783422777135)
      ·
        refine ⟨1609452245785175134165703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1072968163856783422777135 1609452245785175134165703)
        ·
          refine ⟨2414178368677762701248555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609452245785175134165703 2414178368677762701248555)
          ·
            refine ⟨3621267553016644051872833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414178368677762701248555 3621267553016644051872833)
            ·
              refine ⟨2715950664762483038904625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621267553016644051872833 2715950664762483038904625)
              ·
                refine ⟨2036962998571862279178469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2715950664762483038904625 2036962998571862279178469)
                ·
                  refine ⟨381930562232224177345963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2036962998571862279178469 381930562232224177345963)
                  ·
                    rfl

theorem cell21_1673566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 4].length) (baseStart_1673566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673566 prefixEnd_1673566 := by exact prefixLift 1673566
  have htrace : WordTrace (prefixWord ++ tailWord_1673566) baseStart_1673566 baseEnd_1673566 := by
    simpa [prefixWord, tailWord_1673566, baseEnd_1673566] using wordTrace_append hprefix tailTrace_1673566
  have hstable : (prefixWord ++ tailWord_1673566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673566).length < 2 ^ (prefixWord ++ tailWord_1673566).sum := by decide
  have hdescent : baseEnd_1673566 < baseStart_1673566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673650 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 4]
def baseStart_1673650 : Nat := 118140960795 + 1673650 * 2 ^ 59
def prefixEnd_1673650 : Nat := 4983230072969 + 3 ^ 40 * 1673650 * 2
def baseEnd_1673650 : Nat := 381949732176658697945791

theorem tailTrace_1673650 : CollatzResearch.WordTrace tailWord_1673650 prefixEnd_1673650 381949732176658697945791 := by
  unfold tailWord_1673650
  simp only [CollatzResearch.WordTrace]
  refine ⟨15260757596664840377122601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40695353591106241005660269 15260757596664840377122601)
  ·
    refine ⟨11445568197498630282841951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15260757596664840377122601 11445568197498630282841951)
    ·
      refine ⟨17168352296247945424262927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11445568197498630282841951 17168352296247945424262927)
      ·
        refine ⟨25752528444371918136394391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17168352296247945424262927 25752528444371918136394391)
        ·
          refine ⟨38628792666557877204591587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25752528444371918136394391 38628792666557877204591587)
          ·
            refine ⟨57943188999836815806887381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38628792666557877204591587 57943188999836815806887381)
            ·
              refine ⟨1358043492183675370473923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57943188999836815806887381 1358043492183675370473923)
              ·
                refine ⟨2037065238275513055710885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358043492183675370473923 2037065238275513055710885)
                ·
                  refine ⟨381949732176658697945791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2037065238275513055710885 381949732176658697945791)
                  ·
                    rfl

theorem cell21_1673650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 4].length) (baseStart_1673650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673650 prefixEnd_1673650 := by exact prefixLift 1673650
  have htrace : WordTrace (prefixWord ++ tailWord_1673650) baseStart_1673650 baseEnd_1673650 := by
    simpa [prefixWord, tailWord_1673650, baseEnd_1673650] using wordTrace_append hprefix tailTrace_1673650
  have hstable : (prefixWord ++ tailWord_1673650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673650).length < 2 ^ (prefixWord ++ tailWord_1673650).sum := by decide
  have hdescent : baseEnd_1673650 < baseStart_1673650 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673695 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 5]
def baseStart_1673695 : Nat := 118140960795 + 1673695 * 2 ^ 59
def prefixEnd_1673695 : Nat := 4983230072969 + 3 ^ 40 * 1673695 * 2
def baseEnd_1673695 : Nat := 381960001789748619695699

theorem tailTrace_1673695 : CollatzResearch.WordTrace tailWord_1673695 prefixEnd_1673695 381960001789748619695699 := by
  unfold tailWord_1673695
  simp only [CollatzResearch.WordTrace]
  refine ⟨61044671671496334193878539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40696447780997556129252359 61044671671496334193878539)
  ·
    refine ⟨91567007507244501290817809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61044671671496334193878539 91567007507244501290817809)
    ·
      refine ⟨68675255630433375968113357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91567007507244501290817809 68675255630433375968113357)
      ·
        refine ⟨25753220861412515988042509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68675255630433375968113357 25753220861412515988042509)
        ·
          refine ⟨9657457823029693495515941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25753220861412515988042509 9657457823029693495515941)
          ·
            refine ⟨1810773341818067530409239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9657457823029693495515941 1810773341818067530409239)
            ·
              refine ⟨2716160012727101295613859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810773341818067530409239 2716160012727101295613859)
              ·
                refine ⟨4074240019090651943420789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716160012727101295613859 4074240019090651943420789)
                ·
                  refine ⟨381960001789748619695699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4074240019090651943420789 381960001789748619695699)
                  ·
                    rfl

theorem cell21_1673695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 5].length) (baseStart_1673695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673695 prefixEnd_1673695 := by exact prefixLift 1673695
  have htrace : WordTrace (prefixWord ++ tailWord_1673695) baseStart_1673695 baseEnd_1673695 := by
    simpa [prefixWord, tailWord_1673695, baseEnd_1673695] using wordTrace_append hprefix tailTrace_1673695
  have hstable : (prefixWord ++ tailWord_1673695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673695).length < 2 ^ (prefixWord ++ tailWord_1673695).sum := by decide
  have hdescent : baseEnd_1673695 < baseStart_1673695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673698 : List Nat := [3, 3, 3, 2, 1, 1, 2, 6]
def baseStart_1673698 : Nat := 118140960795 + 1673698 * 2 ^ 59
def prefixEnd_1673698 : Nat := 4983230072969 + 3 ^ 40 * 1673698 * 2
def baseEnd_1673698 : Nat := 127320228810207093715231

theorem tailTrace_1673698 : CollatzResearch.WordTrace tailWord_1673698 prefixEnd_1673698 127320228810207093715231 := by
  unfold tailWord_1673698
  simp only [CollatzResearch.WordTrace]
  refine ⟨15261195272621366426559437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40696520726990310470825165 15261195272621366426559437)
  ·
    refine ⟨5722948227233012409959789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15261195272621366426559437 5722948227233012409959789)
    ·
      refine ⟨2146105585212379653734921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5722948227233012409959789 2146105585212379653734921)
      ·
        refine ⟨1609579188909284740301191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2146105585212379653734921 1609579188909284740301191)
        ·
          refine ⟨2414368783363927110451787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609579188909284740301191 2414368783363927110451787)
          ·
            refine ⟨3621553175045890665677681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2414368783363927110451787 3621553175045890665677681)
            ·
              refine ⟨2716164881284417999258261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621553175045890665677681 2716164881284417999258261)
              ·
                refine ⟨127320228810207093715231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2716164881284417999258261 127320228810207093715231)
                ·
                  rfl

theorem cell21_1673698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 2, 6].length) (baseStart_1673698 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673698 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673698 prefixEnd_1673698 := by exact prefixLift 1673698
  have htrace : WordTrace (prefixWord ++ tailWord_1673698) baseStart_1673698 baseEnd_1673698 := by
    simpa [prefixWord, tailWord_1673698, baseEnd_1673698] using wordTrace_append hprefix tailTrace_1673698
  have hstable : (prefixWord ++ tailWord_1673698).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673698).length < 2 ^ (prefixWord ++ tailWord_1673698).sum := by decide
  have hdescent : baseEnd_1673698 < baseStart_1673698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673737 : List Nat := [1, 2, 1, 1, 3, 1, 2, 1, 9]
def baseStart_1673737 : Nat := 118140960795 + 1673737 * 2 ^ 59
def prefixEnd_1673737 : Nat := 4983230072969 + 3 ^ 40 * 1673737 * 2
def baseEnd_1673737 : Nat := 381969586761965879995613

theorem tailTrace_1673737 : CollatzResearch.WordTrace tailWord_1673737 prefixEnd_1673737 381969586761965879995613 := by
  unfold tailWord_1673737
  simp only [CollatzResearch.WordTrace]
  refine ⟨61046203537344175366907465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40697469024896116911271643 61046203537344175366907465)
  ·
    refine ⟨45784652653008131525180599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61046203537344175366907465 45784652653008131525180599)
    ·
      refine ⟨68676978979512197287770899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45784652653008131525180599 68676978979512197287770899)
      ·
        refine ⟨103015468469268295931656349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68676978979512197287770899 103015468469268295931656349)
        ·
          refine ⟨38630800675975610974371131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103015468469268295931656349 38630800675975610974371131)
          ·
            refine ⟨57946201013963416461556697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38630800675975610974371131 57946201013963416461556697)
            ·
              refine ⟨43459650760472562346167523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57946201013963416461556697 43459650760472562346167523)
              ·
                refine ⟨65189476140708843519251285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43459650760472562346167523 65189476140708843519251285)
                ·
                  refine ⟨381969586761965879995613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65189476140708843519251285 381969586761965879995613)
                  ·
                    rfl

theorem cell21_1673737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_1673737 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673737 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673737 prefixEnd_1673737 := by exact prefixLift 1673737
  have htrace : WordTrace (prefixWord ++ tailWord_1673737) baseStart_1673737 baseEnd_1673737 := by
    simpa [prefixWord, tailWord_1673737, baseEnd_1673737] using wordTrace_append hprefix tailTrace_1673737
  have hstable : (prefixWord ++ tailWord_1673737).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673737).length < 2 ^ (prefixWord ++ tailWord_1673737).sum := by decide
  have hdescent : baseEnd_1673737 < baseStart_1673737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673788 : List Nat := [2, 2, 2, 2, 3, 2, 2, 3, 3]
def baseStart_1673788 : Nat := 118140960795 + 1673788 * 2 ^ 59
def prefixEnd_1673788 : Nat := 4983230072969 + 3 ^ 40 * 1673788 * 2
def baseEnd_1673788 : Nat := 381981225656801124645509

theorem tailTrace_1673788 : CollatzResearch.WordTrace tailWord_1673788 prefixEnd_1673788 381981225656801124645509 := by
  unfold tailWord_1673788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30524031830079705538507009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40698709106772940718009345 30524031830079705538507009)
  ·
    refine ⟨22893023872559779153880257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30524031830079705538507009 22893023872559779153880257)
    ·
      refine ⟨17169767904419834365410193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22893023872559779153880257 17169767904419834365410193)
      ·
        refine ⟨12877325928314875774057645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17169767904419834365410193 12877325928314875774057645)
        ·
          refine ⟨4828997223118078415271617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12877325928314875774057645 4828997223118078415271617)
          ·
            refine ⟨3621747917338558811453713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4828997223118078415271617 3621747917338558811453713)
            ·
              refine ⟨2716310938003919108590285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621747917338558811453713 2716310938003919108590285)
              ·
                refine ⟨1018616601751469665721357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2716310938003919108590285 1018616601751469665721357)
                ·
                  refine ⟨381981225656801124645509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018616601751469665721357 381981225656801124645509)
                  ·
                    rfl

theorem cell21_1673788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 2, 3, 3].length) (baseStart_1673788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673788 prefixEnd_1673788 := by exact prefixLift 1673788
  have htrace : WordTrace (prefixWord ++ tailWord_1673788) baseStart_1673788 baseEnd_1673788 := by
    simpa [prefixWord, tailWord_1673788, baseEnd_1673788] using wordTrace_append hprefix tailTrace_1673788
  have hstable : (prefixWord ++ tailWord_1673788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673788).length < 2 ^ (prefixWord ++ tailWord_1673788).sum := by decide
  have hdescent : baseEnd_1673788 < baseStart_1673788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673799 : List Nat := [1, 1, 4, 1, 4, 2, 8]
def baseStart_1673799 : Nat := 118140960795 + 1673799 * 2 ^ 59
def prefixEnd_1673799 : Nat := 4983230072969 + 3 ^ 40 * 1673799 * 2
def baseEnd_1673799 : Nat := 42442637334074172218017

theorem tailTrace_1673799 : CollatzResearch.WordTrace tailWord_1673799 prefixEnd_1673799 42442637334074172218017 := by
  unfold tailWord_1673799
  simp only [CollatzResearch.WordTrace]
  refine ⟨61048464863119559955664451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40698976575413039970442967 61048464863119559955664451)
  ·
    refine ⟨91572697294679339933496677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61048464863119559955664451 91572697294679339933496677)
    ·
      refine ⟨17169880742752376237530627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91572697294679339933496677 17169880742752376237530627)
      ·
        refine ⟨25754821114128564356295941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17169880742752376237530627 25754821114128564356295941)
        ·
          refine ⟨4829028958899105816805489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25754821114128564356295941 4829028958899105816805489)
          ·
            refine ⟨3621771719174329362604117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829028958899105816805489 3621771719174329362604117)
            ·
              refine ⟨42442637334074172218017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3621771719174329362604117 42442637334074172218017)
              ·
                rfl

theorem cell21_1673799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 8].length) (baseStart_1673799 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673799 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673799 prefixEnd_1673799 := by exact prefixLift 1673799
  have htrace : WordTrace (prefixWord ++ tailWord_1673799) baseStart_1673799 baseEnd_1673799 := by
    simpa [prefixWord, tailWord_1673799, baseEnd_1673799] using wordTrace_append hprefix tailTrace_1673799
  have hstable : (prefixWord ++ tailWord_1673799).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673799).length < 2 ^ (prefixWord ++ tailWord_1673799).sum := by decide
  have hdescent : baseEnd_1673799 < baseStart_1673799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673802 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 4]
def baseStart_1673802 : Nat := 118140960795 + 1673802 * 2 ^ 59
def prefixEnd_1673802 : Nat := 4983230072969 + 3 ^ 40 * 1673802 * 2
def baseEnd_1673802 : Nat := 381984420647540211412147

theorem tailTrace_1673802 : CollatzResearch.WordTrace tailWord_1673802 prefixEnd_1673802 381984420647540211412147 := by
  unfold tailWord_1673802
  simp only [CollatzResearch.WordTrace]
  refine ⟨15262143570527172867005915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40699049521405794312015773 15262143570527172867005915)
  ·
    refine ⟨22893215355790759300508873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15262143570527172867005915 22893215355790759300508873)
    ·
      refine ⟨17169911516843069475381655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22893215355790759300508873 17169911516843069475381655)
      ·
        refine ⟨25754867275264604213072483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17169911516843069475381655 25754867275264604213072483)
        ·
          refine ⟨38632300912896906319608725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25754867275264604213072483 38632300912896906319608725)
          ·
            refine ⟨1810889105292042483731659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38632300912896906319608725 1810889105292042483731659)
            ·
              refine ⟨2716333657938063725597489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1810889105292042483731659 2716333657938063725597489)
              ·
                refine ⟨2037250243453547794198117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716333657938063725597489 2037250243453547794198117)
                ·
                  refine ⟨381984420647540211412147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2037250243453547794198117 381984420647540211412147)
                  ·
                    rfl

theorem cell21_1673802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 4].length) (baseStart_1673802 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673802 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673802 prefixEnd_1673802 := by exact prefixLift 1673802
  have htrace : WordTrace (prefixWord ++ tailWord_1673802) baseStart_1673802 baseEnd_1673802 := by
    simpa [prefixWord, tailWord_1673802, baseEnd_1673802] using wordTrace_append hprefix tailTrace_1673802
  have hstable : (prefixWord ++ tailWord_1673802).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673802).length < 2 ^ (prefixWord ++ tailWord_1673802).sum := by decide
  have hdescent : baseEnd_1673802 < baseStart_1673802 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1673847 : List Nat := [1, 1, 3, 1, 1, 3, 5, 3, 3]
def baseStart_1673847 : Nat := 118140960795 + 1673847 * 2 ^ 59
def prefixEnd_1673847 : Nat := 4983230072969 + 3 ^ 40 * 1673847 * 2
def baseEnd_1673847 : Nat := 381994690260630133162055

theorem tailTrace_1673847 : CollatzResearch.WordTrace tailWord_1673847 prefixEnd_1673847 381994690260630133162055 := by
  unfold tailWord_1673847
  simp only [CollatzResearch.WordTrace]
  refine ⟨61050215566945664153411795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40700143711297109435607863 61050215566945664153411795)
  ·
    refine ⟨91575323350418496230117693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61050215566945664153411795 91575323350418496230117693)
    ·
      refine ⟨34340746256406936086294135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91575323350418496230117693 34340746256406936086294135)
      ·
        refine ⟨51511119384610404129441203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34340746256406936086294135 51511119384610404129441203)
        ·
          refine ⟨77266679076915606194161805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51511119384610404129441203 77266679076915606194161805)
          ·
            refine ⟨28975004653843352322810677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77266679076915606194161805 28975004653843352322810677)
            ·
              refine ⟨2716406686297814280263501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28975004653843352322810677 2716406686297814280263501)
              ·
                refine ⟨1018652507361680355098813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2716406686297814280263501 1018652507361680355098813)
                ·
                  refine ⟨381994690260630133162055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018652507361680355098813 381994690260630133162055)
                  ·
                    rfl

theorem cell21_1673847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 3].length) (baseStart_1673847 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1673847 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1673847 prefixEnd_1673847 := by exact prefixLift 1673847
  have htrace : WordTrace (prefixWord ++ tailWord_1673847) baseStart_1673847 baseEnd_1673847 := by
    simpa [prefixWord, tailWord_1673847, baseEnd_1673847] using wordTrace_append hprefix tailTrace_1673847
  have hstable : (prefixWord ++ tailWord_1673847).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1673847).length < 2 ^ (prefixWord ++ tailWord_1673847).sum := by decide
  have hdescent : baseEnd_1673847 < baseStart_1673847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1673847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674002 : List Nat := [3, 2, 4, 1, 2, 2, 2, 5]
def baseStart_1674002 : Nat := 118140960795 + 1674002 * 2 ^ 59
def prefixEnd_1674002 : Nat := 4983230072969 + 3 ^ 40 * 1674002 * 2
def baseEnd_1674002 : Nat := 127343354457461436026135

theorem tailTrace_1674002 : CollatzResearch.WordTrace tailWord_1674002 prefixEnd_1674002 127343354457461436026135 := by
  unfold tailWord_1674002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263967220346031406326065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40703912587589417083536173 15263967220346031406326065)
  ·
    refine ⟨11447975415259523554744549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15263967220346031406326065 11447975415259523554744549)
    ·
      refine ⟨2146495390361160666514603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11447975415259523554744549 2146495390361160666514603)
      ·
        refine ⟨3219743085541740999771905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146495390361160666514603 3219743085541740999771905)
        ·
          refine ⟨2414807314156305749828929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3219743085541740999771905 2414807314156305749828929)
          ·
            refine ⟨1811105485617229312371697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414807314156305749828929 1811105485617229312371697)
            ·
              refine ⟨1358329114212921984278773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811105485617229312371697 1358329114212921984278773)
              ·
                refine ⟨127343354457461436026135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1358329114212921984278773 127343354457461436026135)
                ·
                  rfl

theorem cell21_1674002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_1674002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674002 prefixEnd_1674002 := by exact prefixLift 1674002
  have htrace : WordTrace (prefixWord ++ tailWord_1674002) baseStart_1674002 baseEnd_1674002 := by
    simpa [prefixWord, tailWord_1674002, baseEnd_1674002] using wordTrace_append hprefix tailTrace_1674002
  have hstable : (prefixWord ++ tailWord_1674002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674002).length < 2 ^ (prefixWord ++ tailWord_1674002).sum := by decide
  have hdescent : baseEnd_1674002 < baseStart_1674002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674016 : List Nat := [2, 1, 1, 5, 1, 4, 1, 3, 3]
def baseStart_1674016 : Nat := 118140960795 + 1674016 * 2 ^ 59
def prefixEnd_1674016 : Nat := 4983230072969 + 3 ^ 40 * 1674016 * 2
def baseEnd_1674016 : Nat := 382033258363123394845043

theorem tailTrace_1674016 : CollatzResearch.WordTrace tailWord_1674016 prefixEnd_1674016 382033258363123394845043 := by
  unfold tailWord_1674016
  simp only [CollatzResearch.WordTrace]
  refine ⟨30528189751666703008156951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40704253002222270677542601 30528189751666703008156951)
  ·
    refine ⟨45792284627500054512235427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30528189751666703008156951 45792284627500054512235427)
    ·
      refine ⟨68688426941250081768353141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45792284627500054512235427 68688426941250081768353141)
      ·
        refine ⟨6439540025742195165783107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68688426941250081768353141 6439540025742195165783107)
        ·
          refine ⟨9659310038613292748674661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439540025742195165783107 9659310038613292748674661)
          ·
            refine ⟨1811120632239992390376499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9659310038613292748674661 1811120632239992390376499)
            ·
              refine ⟨2716680948359988585564749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811120632239992390376499 2716680948359988585564749)
              ·
                refine ⟨1018755355634995719586781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2716680948359988585564749 1018755355634995719586781)
                ·
                  refine ⟨382033258363123394845043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1018755355634995719586781 382033258363123394845043)
                  ·
                    rfl

theorem cell21_1674016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 3].length) (baseStart_1674016 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674016 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674016 prefixEnd_1674016 := by exact prefixLift 1674016
  have htrace : WordTrace (prefixWord ++ tailWord_1674016) baseStart_1674016 baseEnd_1674016 := by
    simpa [prefixWord, tailWord_1674016, baseEnd_1674016] using wordTrace_append hprefix tailTrace_1674016
  have hstable : (prefixWord ++ tailWord_1674016).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674016).length < 2 ^ (prefixWord ++ tailWord_1674016).sum := by decide
  have hdescent : baseEnd_1674016 < baseStart_1674016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674117 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1674117 : Nat := 118140960795 + 1674117 * 2 ^ 59
def prefixEnd_1674117 : Nat := 4983230072969 + 3 ^ 40 * 1674117 * 2
def baseEnd_1674117 : Nat := 382056307939169663661503

theorem tailTrace_1674117 : CollatzResearch.WordTrace tailWord_1674117 prefixEnd_1674117 382056307939169663661503 := by
  unfold tailWord_1674117
  simp only [CollatzResearch.WordTrace]
  refine ⟨61060063275967500265740605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40706708850645000177160403 61060063275967500265740605)
  ·
    refine ⟨22897523728487812599652727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61060063275967500265740605 22897523728487812599652727)
    ·
      refine ⟨34346285592731718899479091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22897523728487812599652727 34346285592731718899479091)
      ·
        refine ⟨51519428389097578349218637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34346285592731718899479091 51519428389097578349218637)
        ·
          refine ⟨19319785645911591880956989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51519428389097578349218637 19319785645911591880956989)
          ·
            refine ⟨7244919617216846955358871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19319785645911591880956989 7244919617216846955358871)
            ·
              refine ⟨10867379425825270433038307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244919617216846955358871 10867379425825270433038307)
              ·
                refine ⟨16301069138737905649557461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10867379425825270433038307 16301069138737905649557461)
                ·
                  refine ⟨382056307939169663661503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16301069138737905649557461 382056307939169663661503)
                  ·
                    rfl

theorem cell21_1674117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1674117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674117 prefixEnd_1674117 := by exact prefixLift 1674117
  have htrace : WordTrace (prefixWord ++ tailWord_1674117) baseStart_1674117 baseEnd_1674117 := by
    simpa [prefixWord, tailWord_1674117, baseEnd_1674117] using wordTrace_append hprefix tailTrace_1674117
  have hstable : (prefixWord ++ tailWord_1674117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674117).length < 2 ^ (prefixWord ++ tailWord_1674117).sum := by decide
  have hdescent : baseEnd_1674117 < baseStart_1674117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674120 : List Nat := [2, 1, 3, 3, 2, 2, 3, 5]
def baseStart_1674120 : Nat := 118140960795 + 1674120 * 2 ^ 59
def prefixEnd_1674120 : Nat := 4983230072969 + 3 ^ 40 * 1674120 * 2
def baseEnd_1674120 : Nat := 127352330860014108370499

theorem tailTrace_1674120 : CollatzResearch.WordTrace tailWord_1674120 prefixEnd_1674120 127352330860014108370499 := by
  unfold tailWord_1674120
  simp only [CollatzResearch.WordTrace]
  refine ⟨30530086347478315889049907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40706781796637754518733209 30530086347478315889049907)
  ·
    refine ⟨45795129521217473833574861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30530086347478315889049907 45795129521217473833574861)
    ·
      refine ⟨17173173570456552687590573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45795129521217473833574861 17173173570456552687590573)
      ·
        refine ⟨6439940088921207257846465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17173173570456552687590573 6439940088921207257846465)
        ·
          refine ⟨4829955066690905443384849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6439940088921207257846465 4829955066690905443384849)
          ·
            refine ⟨3622466300018179082538637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829955066690905443384849 3622466300018179082538637)
            ·
              refine ⟨1358424862506817155951989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3622466300018179082538637 1358424862506817155951989)
              ·
                refine ⟨127352330860014108370499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1358424862506817155951989 127352330860014108370499)
                ·
                  rfl

theorem cell21_1674120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 3, 5].length) (baseStart_1674120 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674120 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674120 prefixEnd_1674120 := by exact prefixLift 1674120
  have htrace : WordTrace (prefixWord ++ tailWord_1674120) baseStart_1674120 baseEnd_1674120 := by
    simpa [prefixWord, tailWord_1674120, baseEnd_1674120] using wordTrace_append hprefix tailTrace_1674120
  have hstable : (prefixWord ++ tailWord_1674120).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674120).length < 2 ^ (prefixWord ++ tailWord_1674120).sum := by decide
  have hdescent : baseEnd_1674120 < baseStart_1674120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674148 : List Nat := [2, 3, 1, 2, 1, 2, 3, 1, 6]
def baseStart_1674148 : Nat := 118140960795 + 1674148 * 2 ^ 59
def prefixEnd_1674148 : Nat := 4983230072969 + 3 ^ 40 * 1674148 * 2
def baseEnd_1674148 : Nat := 382063382561520498644773

theorem tailTrace_1674148 : CollatzResearch.WordTrace tailWord_1674148 prefixEnd_1674148 382063382561520498644773 := by
  unfold tailWord_1674148
  simp only [CollatzResearch.WordTrace]
  refine ⟨30530596969427596280059549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40707462625903461706746065 30530596969427596280059549)
  ·
    refine ⟨11448973863535348605022331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30530596969427596280059549 11448973863535348605022331)
    ·
      refine ⟨17173460795303022907533497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11448973863535348605022331 17173460795303022907533497)
      ·
        refine ⟨12880095596477267180650123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17173460795303022907533497 12880095596477267180650123)
        ·
          refine ⟨19320143394715900770975185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12880095596477267180650123 19320143394715900770975185)
          ·
            refine ⟨14490107546036925578231389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19320143394715900770975185 14490107546036925578231389)
            ·
              refine ⟨5433790329763847091836771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14490107546036925578231389 5433790329763847091836771)
              ·
                refine ⟨8150685494645770637755157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433790329763847091836771 8150685494645770637755157)
                ·
                  refine ⟨382063382561520498644773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8150685494645770637755157 382063382561520498644773)
                  ·
                    rfl

theorem cell21_1674148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 3, 1, 6].length) (baseStart_1674148 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674148 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674148 prefixEnd_1674148 := by exact prefixLift 1674148
  have htrace : WordTrace (prefixWord ++ tailWord_1674148) baseStart_1674148 baseEnd_1674148 := by
    simpa [prefixWord, tailWord_1674148, baseEnd_1674148] using wordTrace_append hprefix tailTrace_1674148
  have hstable : (prefixWord ++ tailWord_1674148).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674148).length < 2 ^ (prefixWord ++ tailWord_1674148).sum := by decide
  have hdescent : baseEnd_1674148 < baseStart_1674148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674151 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 5]
def baseStart_1674151 : Nat := 118140960795 + 1674151 * 2 ^ 59
def prefixEnd_1674151 : Nat := 4983230072969 + 3 ^ 40 * 1674151 * 2
def baseEnd_1674151 : Nat := 382064067202393160094767

theorem tailTrace_1674151 : CollatzResearch.WordTrace tailWord_1674151 prefixEnd_1674151 382064067202393160094767 := by
  unfold tailWord_1674151
  simp only [CollatzResearch.WordTrace]
  refine ⟨61061303357844324072478307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40707535571896216048318871 61061303357844324072478307)
  ·
    refine ⟨91591955036766486108717461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61061303357844324072478307 91591955036766486108717461)
    ·
      refine ⟨4293372892348429036346131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91591955036766486108717461 4293372892348429036346131)
      ·
        refine ⟨6440059338522643554519197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293372892348429036346131 6440059338522643554519197)
        ·
          refine ⟨2415022251945991332944699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6440059338522643554519197 2415022251945991332944699)
          ·
            refine ⟨3622533377918986999417049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415022251945991332944699 3622533377918986999417049)
            ·
              refine ⟨2716900033439240249562787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3622533377918986999417049 2716900033439240249562787)
              ·
                refine ⟨4075350050158860374344181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716900033439240249562787 4075350050158860374344181)
                ·
                  refine ⟨382064067202393160094767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4075350050158860374344181 382064067202393160094767)
                  ·
                    rfl

theorem cell21_1674151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 5].length) (baseStart_1674151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674151 prefixEnd_1674151 := by exact prefixLift 1674151
  have htrace : WordTrace (prefixWord ++ tailWord_1674151) baseStart_1674151 baseEnd_1674151 := by
    simpa [prefixWord, tailWord_1674151, baseEnd_1674151] using wordTrace_append hprefix tailTrace_1674151
  have hstable : (prefixWord ++ tailWord_1674151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674151).length < 2 ^ (prefixWord ++ tailWord_1674151).sum := by decide
  have hdescent : baseEnd_1674151 < baseStart_1674151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674286 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 5]
def baseStart_1674286 : Nat := 118140960795 + 1674286 * 2 ^ 59
def prefixEnd_1674286 : Nat := 4983230072969 + 3 ^ 40 * 1674286 * 2
def baseEnd_1674286 : Nat := 382094876041662925344491

theorem tailTrace_1674286 : CollatzResearch.WordTrace tailWord_1674286 prefixEnd_1674286 382094876041662925344491 := by
  unfold tailWord_1674286
  simp only [CollatzResearch.WordTrace]
  refine ⟨7633278401544405266080339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40710818141570161419095141 7633278401544405266080339)
  ·
    refine ⟨11449917602316607899120509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7633278401544405266080339 11449917602316607899120509)
    ·
      refine ⟨4293719100868727962170191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11449917602316607899120509 4293719100868727962170191)
      ·
        refine ⟨6440578651303091943255287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293719100868727962170191 6440578651303091943255287)
        ·
          refine ⟨9660867976954637914882931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440578651303091943255287 9660867976954637914882931)
          ·
            refine ⟨14491301965431956872324397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9660867976954637914882931 14491301965431956872324397)
            ·
              refine ⟨5434238237036983827121649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14491301965431956872324397 5434238237036983827121649)
              ·
                refine ⟨4075678677777737870341237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434238237036983827121649 4075678677777737870341237)
                ·
                  refine ⟨382094876041662925344491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4075678677777737870341237 382094876041662925344491)
                  ·
                    rfl

theorem cell21_1674286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 5].length) (baseStart_1674286 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674286 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674286 prefixEnd_1674286 := by exact prefixLift 1674286
  have htrace : WordTrace (prefixWord ++ tailWord_1674286) baseStart_1674286 baseEnd_1674286 := by
    simpa [prefixWord, tailWord_1674286, baseEnd_1674286] using wordTrace_append hprefix tailTrace_1674286
  have hstable : (prefixWord ++ tailWord_1674286).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674286).length < 2 ^ (prefixWord ++ tailWord_1674286).sum := by decide
  have hdescent : baseEnd_1674286 < baseStart_1674286 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674317 : List Nat := [1, 6, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1674317 : Nat := 118140960795 + 1674317 * 2 ^ 59
def prefixEnd_1674317 : Nat := 4983230072969 + 3 ^ 40 * 1674317 * 2
def baseEnd_1674317 : Nat := 382101950664013760327761

theorem tailTrace_1674317 : CollatzResearch.WordTrace tailWord_1674317 prefixEnd_1674317 382101950664013760327761 := by
  unfold tailWord_1674317
  simp only [CollatzResearch.WordTrace]
  refine ⟨61067357875242934423021205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40711571916828622948680803 61067357875242934423021205)
  ·
    refine ⟨2862532400402012551079119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61067357875242934423021205 2862532400402012551079119)
    ·
      refine ⟨4293798600603018826618679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862532400402012551079119 4293798600603018826618679)
      ·
        refine ⟨6440697900904528239928019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293798600603018826618679 6440697900904528239928019)
        ·
          refine ⟨9661046851356792359892029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440697900904528239928019 9661046851356792359892029)
          ·
            refine ⟨3622892569258797134959511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9661046851356792359892029 3622892569258797134959511)
            ·
              refine ⟨5434338853888195702439267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622892569258797134959511 5434338853888195702439267)
              ·
                refine ⟨8151508280832293553658901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434338853888195702439267 8151508280832293553658901)
                ·
                  refine ⟨382101950664013760327761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8151508280832293553658901 382101950664013760327761)
                  ·
                    rfl

theorem cell21_1674317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1674317 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674317 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674317 prefixEnd_1674317 := by exact prefixLift 1674317
  have htrace : WordTrace (prefixWord ++ tailWord_1674317) baseStart_1674317 baseEnd_1674317 := by
    simpa [prefixWord, tailWord_1674317, baseEnd_1674317] using wordTrace_append hprefix tailTrace_1674317
  have hstable : (prefixWord ++ tailWord_1674317).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674317).length < 2 ^ (prefixWord ++ tailWord_1674317).sum := by decide
  have hdescent : baseEnd_1674317 < baseStart_1674317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674345 : List Nat := [1, 2, 1, 1, 1, 6, 2, 2, 5]
def baseStart_1674345 : Nat := 118140960795 + 1674345 * 2 ^ 59
def prefixEnd_1674345 : Nat := 4983230072969 + 3 ^ 40 * 1674345 * 2
def baseEnd_1674345 : Nat := 382108340645491933861037

theorem tailTrace_1674345 : CollatzResearch.WordTrace tailWord_1674345 prefixEnd_1674345 382108340645491933861037 := by
  unfold tailWord_1674345
  simp only [CollatzResearch.WordTrace]
  refine ⟨61068379119141495205040489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40712252746094330136693659 61068379119141495205040489)
  ·
    refine ⟨45801284339356121403780367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61068379119141495205040489 45801284339356121403780367)
    ·
      refine ⟨68701926509034182105670551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45801284339356121403780367 68701926509034182105670551)
      ·
        refine ⟨103052889763551273158505827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68701926509034182105670551 103052889763551273158505827)
        ·
          refine ⟨154579334645326909737758741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103052889763551273158505827 154579334645326909737758741)
          ·
            refine ⟨7245906311499698893957441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 154579334645326909737758741 7245906311499698893957441)
            ·
              refine ⟨5434429733624774170468081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7245906311499698893957441 5434429733624774170468081)
              ·
                refine ⟨4075822300218580627851061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434429733624774170468081 4075822300218580627851061)
                ·
                  refine ⟨382108340645491933861037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4075822300218580627851061 382108340645491933861037)
                  ·
                    rfl

theorem cell21_1674345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_1674345 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674345 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674345 prefixEnd_1674345 := by exact prefixLift 1674345
  have htrace : WordTrace (prefixWord ++ tailWord_1674345) baseStart_1674345 baseEnd_1674345 := by
    simpa [prefixWord, tailWord_1674345, baseEnd_1674345] using wordTrace_append hprefix tailTrace_1674345
  have hstable : (prefixWord ++ tailWord_1674345).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674345).length < 2 ^ (prefixWord ++ tailWord_1674345).sum := by decide
  have hdescent : baseEnd_1674345 < baseStart_1674345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674359 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 8]
def baseStart_1674359 : Nat := 118140960795 + 1674359 * 2 ^ 59
def prefixEnd_1674359 : Nat := 4983230072969 + 3 ^ 40 * 1674359 * 2
def baseEnd_1674359 : Nat := 382111535636231020627675

theorem tailTrace_1674359 : CollatzResearch.WordTrace tailWord_1674359 prefixEnd_1674359 382111535636231020627675 := by
  unfold tailWord_1674359
  simp only [CollatzResearch.WordTrace]
  refine ⟨61068889741090775596050131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40712593160727183730700087 61068889741090775596050131)
  ·
    refine ⟨91603334611636163394075197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61068889741090775596050131 91603334611636163394075197)
    ·
      refine ⟨34351250479363561272778199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91603334611636163394075197 34351250479363561272778199)
      ·
        refine ⟨51526875719045341909167299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34351250479363561272778199 51526875719045341909167299)
        ·
          refine ⟨77290313578568012863750949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51526875719045341909167299 77290313578568012863750949)
          ·
            refine ⟨14491933795981502411953303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77290313578568012863750949 14491933795981502411953303)
            ·
              refine ⟨21737900693972253617929955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14491933795981502411953303 21737900693972253617929955)
              ·
                refine ⟨32606851040958380426894933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21737900693972253617929955 32606851040958380426894933)
                ·
                  refine ⟨382111535636231020627675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32606851040958380426894933 382111535636231020627675)
                  ·
                    rfl

theorem cell21_1674359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_1674359 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674359 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674359 prefixEnd_1674359 := by exact prefixLift 1674359
  have htrace : WordTrace (prefixWord ++ tailWord_1674359) baseStart_1674359 baseEnd_1674359 := by
    simpa [prefixWord, tailWord_1674359, baseEnd_1674359] using wordTrace_append hprefix tailTrace_1674359
  have hstable : (prefixWord ++ tailWord_1674359).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674359).length < 2 ^ (prefixWord ++ tailWord_1674359).sum := by decide
  have hdescent : baseEnd_1674359 < baseStart_1674359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674407 : List Nat := [1, 1, 6, 2, 1, 1, 2, 7]
def baseStart_1674407 : Nat := 118140960795 + 1674407 * 2 ^ 59
def prefixEnd_1674407 : Nat := 4983230072969 + 3 ^ 40 * 1674407 * 2
def baseEnd_1674407 : Nat := 127374163296731201275859

theorem tailTrace_1674407 : CollatzResearch.WordTrace tailWord_1674407 prefixEnd_1674407 127374163296731201275859 := by
  unfold tailWord_1674407
  simp only [CollatzResearch.WordTrace]
  refine ⟨61070640444916879793797475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40713760296611253195864983 61070640444916879793797475)
  ·
    refine ⟨91605960667375319690696213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61070640444916879793797475 91605960667375319690696213)
    ·
      refine ⟨4294029406283218110501385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91605960667375319690696213 4294029406283218110501385)
      ·
        refine ⟨3220522054712413582876039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4294029406283218110501385 3220522054712413582876039)
        ·
          refine ⟨4830783082068620374314059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220522054712413582876039 4830783082068620374314059)
          ·
            refine ⟨7246174623102930561471089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830783082068620374314059 7246174623102930561471089)
            ·
              refine ⟨5434630967327197921103317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7246174623102930561471089 5434630967327197921103317)
              ·
                refine ⟨127374163296731201275859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5434630967327197921103317 127374163296731201275859)
                ·
                  rfl

theorem cell21_1674407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 7].length) (baseStart_1674407 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674407 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674407 prefixEnd_1674407 := by exact prefixLift 1674407
  have htrace : WordTrace (prefixWord ++ tailWord_1674407) baseStart_1674407 baseEnd_1674407 := by
    simpa [prefixWord, tailWord_1674407, baseEnd_1674407] using wordTrace_append hprefix tailTrace_1674407
  have hstable : (prefixWord ++ tailWord_1674407).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674407).length < 2 ^ (prefixWord ++ tailWord_1674407).sum := by decide
  have hdescent : baseEnd_1674407 < baseStart_1674407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674497 : List Nat := [1, 2, 4, 1, 1, 3, 1, 3, 5]
def baseStart_1674497 : Nat := 118140960795 + 1674497 * 2 ^ 59
def prefixEnd_1674497 : Nat := 4983230072969 + 3 ^ 40 * 1674497 * 2
def baseEnd_1674497 : Nat := 382143029116373447327393

theorem tailTrace_1674497 : CollatzResearch.WordTrace tailWord_1674497 prefixEnd_1674497 382143029116373447327393 := by
  unfold tailWord_1674497
  simp only [CollatzResearch.WordTrace]
  refine ⟨61073923014590825164573745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40715948676393883443049163 61073923014590825164573745)
  ·
    refine ⟨45805442260943118873430309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61073923014590825164573745 45805442260943118873430309)
    ·
      refine ⟨8588520423926834788768183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45805442260943118873430309 8588520423926834788768183)
      ·
        refine ⟨12882780635890252183152275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588520423926834788768183 12882780635890252183152275)
        ·
          refine ⟨19324170953835378274728413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12882780635890252183152275 19324170953835378274728413)
          ·
            refine ⟨7246564107688266853023155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19324170953835378274728413 7246564107688266853023155)
            ·
              refine ⟨10869846161532400279534733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7246564107688266853023155 10869846161532400279534733)
              ·
                refine ⟨4076192310574650104825525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10869846161532400279534733 4076192310574650104825525)
                ·
                  refine ⟨382143029116373447327393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4076192310574650104825525 382143029116373447327393)
                  ·
                    rfl

theorem cell21_1674497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_1674497 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674497 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674497 prefixEnd_1674497 := by exact prefixLift 1674497
  have htrace : WordTrace (prefixWord ++ tailWord_1674497) baseStart_1674497 baseEnd_1674497 := by
    simpa [prefixWord, tailWord_1674497, baseEnd_1674497] using wordTrace_append hprefix tailTrace_1674497
  have hstable : (prefixWord ++ tailWord_1674497).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674497).length < 2 ^ (prefixWord ++ tailWord_1674497).sum := by decide
  have hdescent : baseEnd_1674497 < baseStart_1674497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674531 : List Nat := [1, 1, 1, 4, 2, 5, 1, 3, 3]
def baseStart_1674531 : Nat := 118140960795 + 1674531 * 2 ^ 59
def prefixEnd_1674531 : Nat := 4983230072969 + 3 ^ 40 * 1674531 * 2
def baseEnd_1674531 : Nat := 382150788379596943760657

theorem tailTrace_1674531 : CollatzResearch.WordTrace tailWord_1674531 prefixEnd_1674531 382150788379596943760657 := by
  unfold tailWord_1674531
  simp only [CollatzResearch.WordTrace]
  refine ⟨61075163096467648971311447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40716775397645099314207631 61075163096467648971311447)
  ·
    refine ⟨91612744644701473456967171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61075163096467648971311447 91612744644701473456967171)
    ·
      refine ⟨137419116967052210185450757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91612744644701473456967171 137419116967052210185450757)
      ·
        refine ⟨25766084431322289409772017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137419116967052210185450757 25766084431322289409772017)
        ·
          refine ⟨19324563323491717057329013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25766084431322289409772017 19324563323491717057329013)
          ·
            refine ⟨1811677811577348474124595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19324563323491717057329013 1811677811577348474124595)
            ·
              refine ⟨2717516717366022711186893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811677811577348474124595 2717516717366022711186893)
              ·
                refine ⟨1019068769012258516695085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2717516717366022711186893 1019068769012258516695085)
                ·
                  refine ⟨382150788379596943760657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019068769012258516695085 382150788379596943760657)
                  ·
                    rfl

theorem cell21_1674531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 5, 1, 3, 3].length) (baseStart_1674531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674531 prefixEnd_1674531 := by exact prefixLift 1674531
  have htrace : WordTrace (prefixWord ++ tailWord_1674531) baseStart_1674531 baseEnd_1674531 := by
    simpa [prefixWord, tailWord_1674531, baseEnd_1674531] using wordTrace_append hprefix tailTrace_1674531
  have hstable : (prefixWord ++ tailWord_1674531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674531).length < 2 ^ (prefixWord ++ tailWord_1674531).sum := by decide
  have hdescent : baseEnd_1674531 < baseStart_1674531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674548 : List Nat := [2, 5, 1, 1, 1, 1, 5, 2, 3]
def baseStart_1674548 : Nat := 118140960795 + 1674548 * 2 ^ 59
def prefixEnd_1674548 : Nat := 4983230072969 + 3 ^ 40 * 1674548 * 2
def baseEnd_1674548 : Nat := 382154668011208691977289

theorem tailTrace_1674548 : CollatzResearch.WordTrace tailWord_1674548 prefixEnd_1674548 382154668011208691977289 := by
  unfold tailWord_1674548
  simp only [CollatzResearch.WordTrace]
  refine ⟨30537891568703030437340149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40717188758270707249786865 30537891568703030437340149)
  ·
    refine ⟨2862927334565909103500639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30537891568703030437340149 2862927334565909103500639)
    ·
      refine ⟨4294391001848863655250959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862927334565909103500639 4294391001848863655250959)
      ·
        refine ⟨6441586502773295482876439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294391001848863655250959 6441586502773295482876439)
        ·
          refine ⟨9662379754159943224314659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441586502773295482876439 9662379754159943224314659)
          ·
            refine ⟨14493569631239914836471989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662379754159943224314659 14493569631239914836471989)
            ·
              refine ⟨1358772152928742015919249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14493569631239914836471989 1358772152928742015919249)
              ·
                refine ⟨1019079114696556511939437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358772152928742015919249 1019079114696556511939437)
                ·
                  refine ⟨382154668011208691977289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019079114696556511939437 382154668011208691977289)
                  ·
                    rfl

theorem cell21_1674548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 5, 2, 3].length) (baseStart_1674548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674548 prefixEnd_1674548 := by exact prefixLift 1674548
  have htrace : WordTrace (prefixWord ++ tailWord_1674548) baseStart_1674548 baseEnd_1674548 := by
    simpa [prefixWord, tailWord_1674548, baseEnd_1674548] using wordTrace_append hprefix tailTrace_1674548
  have hstable : (prefixWord ++ tailWord_1674548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674548).length < 2 ^ (prefixWord ++ tailWord_1674548).sum := by decide
  have hdescent : baseEnd_1674548 < baseStart_1674548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674604 : List Nat := [2, 2, 1, 1, 5, 1, 1, 4, 4]
def baseStart_1674604 : Nat := 118140960795 + 1674604 * 2 ^ 59
def prefixEnd_1674604 : Nat := 4983230072969 + 3 ^ 40 * 1674604 * 2
def baseEnd_1674604 : Nat := 382167447974165039043841

theorem tailTrace_1674604 : CollatzResearch.WordTrace tailWord_1674604 prefixEnd_1674604 382167447974165039043841 := by
  unfold tailWord_1674604
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538912812601591219359433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40718550416802121625812577 30538912812601591219359433)
  ·
    refine ⟨22904184609451193414519575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30538912812601591219359433 22904184609451193414519575)
    ·
      refine ⟨34356276914176790121779363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22904184609451193414519575 34356276914176790121779363)
      ·
        refine ⟨51534415371265185182669045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34356276914176790121779363 51534415371265185182669045)
        ·
          refine ⟨4831351441056111110875223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51534415371265185182669045 4831351441056111110875223)
          ·
            refine ⟨7247027161584166666312835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831351441056111110875223 7247027161584166666312835)
            ·
              refine ⟨10870540742376249999469253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247027161584166666312835 10870540742376249999469253)
              ·
                refine ⟨2038226389195546874900485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10870540742376249999469253 2038226389195546874900485)
                ·
                  refine ⟨382167447974165039043841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2038226389195546874900485 382167447974165039043841)
                  ·
                    rfl

theorem cell21_1674604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 4].length) (baseStart_1674604 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674604 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674604 prefixEnd_1674604 := by exact prefixLift 1674604
  have htrace : WordTrace (prefixWord ++ tailWord_1674604) baseStart_1674604 baseEnd_1674604 := by
    simpa [prefixWord, tailWord_1674604, baseEnd_1674604] using wordTrace_append hprefix tailTrace_1674604
  have hstable : (prefixWord ++ tailWord_1674604).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674604).length < 2 ^ (prefixWord ++ tailWord_1674604).sum := by decide
  have hdescent : baseEnd_1674604 < baseStart_1674604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674776 : List Nat := [2, 1, 2, 3, 4, 2, 2, 2, 3]
def baseStart_1674776 : Nat := 118140960795 + 1674776 * 2 ^ 59
def prefixEnd_1674776 : Nat := 4983230072969 + 3 ^ 40 * 1674776 * 2
def baseEnd_1674776 : Nat := 382206700717530962176823

theorem tailTrace_1674776 : CollatzResearch.WordTrace tailWord_1674776 prefixEnd_1674776 382206700717530962176823 := by
  unfold tailWord_1674776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30542049490290027906990091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40722732653720037209320121 30542049490290027906990091)
  ·
    refine ⟨45813074235435041860485137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30542049490290027906990091 45813074235435041860485137)
    ·
      refine ⟨34359805676576281395363853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45813074235435041860485137 34359805676576281395363853)
      ·
        refine ⟨12884927128716105523261445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34359805676576281395363853 12884927128716105523261445)
        ·
          refine ⟨2415923836634269785611521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12884927128716105523261445 2415923836634269785611521)
          ·
            refine ⟨1811942877475702339208641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415923836634269785611521 1811942877475702339208641)
            ·
              refine ⟨1358957158106776754406481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811942877475702339208641 1358957158106776754406481)
              ·
                refine ⟨1019217868580082565804861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1358957158106776754406481 1019217868580082565804861)
                ·
                  refine ⟨382206700717530962176823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019217868580082565804861 382206700717530962176823)
                  ·
                    rfl

theorem cell21_1674776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 3].length) (baseStart_1674776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674776 prefixEnd_1674776 := by exact prefixLift 1674776
  have htrace : WordTrace (prefixWord ++ tailWord_1674776) baseStart_1674776 baseEnd_1674776 := by
    simpa [prefixWord, tailWord_1674776, baseEnd_1674776] using wordTrace_append hprefix tailTrace_1674776
  have hstable : (prefixWord ++ tailWord_1674776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674776).length < 2 ^ (prefixWord ++ tailWord_1674776).sum := by decide
  have hdescent : baseEnd_1674776 < baseStart_1674776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674787 : List Nat := [1, 1, 1, 4, 5, 2, 1, 6]
def baseStart_1674787 : Nat := 118140960795 + 1674787 * 2 ^ 59
def prefixEnd_1674787 : Nat := 4983230072969 + 3 ^ 40 * 1674787 * 2
def baseEnd_1674787 : Nat := 127403070355799129164489

theorem tailTrace_1674787 : CollatzResearch.WordTrace tailWord_1674787 prefixEnd_1674787 127403070355799129164489 := by
  unfold tailWord_1674787
  simp only [CollatzResearch.WordTrace]
  refine ⟨61084500183540204692630615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40723000122360136461753743 61084500183540204692630615)
  ·
    refine ⟨91626750275310307038945923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61084500183540204692630615 91626750275310307038945923)
    ·
      refine ⟨137440125412965460558418885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91626750275310307038945923 137440125412965460558418885)
      ·
        refine ⟨25770023514931023854703541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137440125412965460558418885 25770023514931023854703541)
        ·
          refine ⟨2415939704524783486378457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25770023514931023854703541 2415939704524783486378457)
          ·
            refine ⟨1811954778393587614783843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2415939704524783486378457 1811954778393587614783843)
            ·
              refine ⟨2717932167590381422175765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811954778393587614783843 2717932167590381422175765)
              ·
                refine ⟨127403070355799129164489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2717932167590381422175765 127403070355799129164489)
                ·
                  rfl

theorem cell21_1674787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 6].length) (baseStart_1674787 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674787 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674787 prefixEnd_1674787 := by exact prefixLift 1674787
  have htrace : WordTrace (prefixWord ++ tailWord_1674787) baseStart_1674787 baseEnd_1674787 := by
    simpa [prefixWord, tailWord_1674787, baseEnd_1674787] using wordTrace_append hprefix tailTrace_1674787
  have hstable : (prefixWord ++ tailWord_1674787).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674787).length < 2 ^ (prefixWord ++ tailWord_1674787).sum := by decide
  have hdescent : baseEnd_1674787 < baseStart_1674787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674891 : List Nat := [1, 1, 1, 1, 4, 1, 4, 4, 4]
def baseStart_1674891 : Nat := 118140960795 + 1674891 * 2 ^ 59
def prefixEnd_1674891 : Nat := 4983230072969 + 3 ^ 40 * 1674891 * 2
def baseEnd_1674891 : Nat := 382232945284316317759921

theorem tailTrace_1674891 : CollatzResearch.WordTrace tailWord_1674891 prefixEnd_1674891 382232945284316317759921 := by
  unfold tailWord_1674891
  simp only [CollatzResearch.WordTrace]
  refine ⟨61088293375163430454416527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40725528916775620302944351 61088293375163430454416527)
  ·
    refine ⟨91632440062745145681624791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61088293375163430454416527 91632440062745145681624791)
    ·
      refine ⟨137448660094117718522437187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91632440062745145681624791 137448660094117718522437187)
      ·
        refine ⟨206172990141176577783655781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137448660094117718522437187 206172990141176577783655781)
        ·
          refine ⟨38657435651470608334435459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206172990141176577783655781 38657435651470608334435459)
          ·
            refine ⟨57986153477205912501653189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38657435651470608334435459 57986153477205912501653189)
            ·
              refine ⟨10872403776976108594059973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57986153477205912501653189 10872403776976108594059973)
              ·
                refine ⟨2038575708183020361386245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10872403776976108594059973 2038575708183020361386245)
                ·
                  refine ⟨382232945284316317759921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2038575708183020361386245 382232945284316317759921)
                  ·
                    rfl

theorem cell21_1674891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 4, 4].length) (baseStart_1674891 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674891 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674891 prefixEnd_1674891 := by exact prefixLift 1674891
  have htrace : WordTrace (prefixWord ++ tailWord_1674891) baseStart_1674891 baseEnd_1674891 := by
    simpa [prefixWord, tailWord_1674891, baseEnd_1674891] using wordTrace_append hprefix tailTrace_1674891
  have hstable : (prefixWord ++ tailWord_1674891).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674891).length < 2 ^ (prefixWord ++ tailWord_1674891).sum := by decide
  have hdescent : baseEnd_1674891 < baseStart_1674891 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674894 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 5]
def baseStart_1674894 : Nat := 118140960795 + 1674894 * 2 ^ 59
def prefixEnd_1674894 : Nat := 4983230072969 + 3 ^ 40 * 1674894 * 2
def baseEnd_1674894 : Nat := 382233629925188979209915

theorem tailTrace_1674894 : CollatzResearch.WordTrace tailWord_1674894 prefixEnd_1674894 382233629925188979209915 := by
  unfold tailWord_1674894
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636050349269070245846967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40725601862768374644517157 7636050349269070245846967)
  ·
    refine ⟨11454075523903605368770451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7636050349269070245846967 11454075523903605368770451)
    ·
      refine ⟨17181113285855408053155677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11454075523903605368770451 17181113285855408053155677)
      ·
        refine ⟨6442917482195778019933379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17181113285855408053155677 6442917482195778019933379)
        ·
          refine ⟨9664376223293667029900069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6442917482195778019933379 9664376223293667029900069)
          ·
            refine ⟨1812070541867562568106263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9664376223293667029900069 1812070541867562568106263)
            ·
              refine ⟨2718105812801343852159395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812070541867562568106263 2718105812801343852159395)
              ·
                refine ⟨4077158719202015778239093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718105812801343852159395 4077158719202015778239093)
                ·
                  refine ⟨382233629925188979209915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4077158719202015778239093 382233629925188979209915)
                  ·
                    rfl

theorem cell21_1674894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 5].length) (baseStart_1674894 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674894 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674894 prefixEnd_1674894 := by exact prefixLift 1674894
  have htrace : WordTrace (prefixWord ++ tailWord_1674894) baseStart_1674894 baseEnd_1674894 := by
    simpa [prefixWord, tailWord_1674894, baseEnd_1674894] using wordTrace_append hprefix tailTrace_1674894
  have hstable : (prefixWord ++ tailWord_1674894).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674894).length < 2 ^ (prefixWord ++ tailWord_1674894).sum := by decide
  have hdescent : baseEnd_1674894 < baseStart_1674894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674956 : List Nat := [2, 2, 1, 5, 3, 1, 1, 6]
def baseStart_1674956 : Nat := 118140960795 + 1674956 * 2 ^ 59
def prefixEnd_1674956 : Nat := 4983230072969 + 3 ^ 40 * 1674956 * 2
def baseEnd_1674956 : Nat := 127415926389963549725485

theorem tailTrace_1674956 : CollatzResearch.WordTrace tailWord_1674956 prefixEnd_1674956 127415926389963549725485 := by
  unfold tailWord_1674956
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545332059963973277766361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40727109413285297703688481 30545332059963973277766361)
  ·
    refine ⟨22908999044972979958324771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30545332059963973277766361 22908999044972979958324771)
    ·
      refine ⟨34363498567459469937487157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22908999044972979958324771 34363498567459469937487157)
      ·
        refine ⟨3221577990699325306639421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34363498567459469937487157 3221577990699325306639421)
        ·
          refine ⟨1208091746512246989989783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3221577990699325306639421 1208091746512246989989783)
          ·
            refine ⟨1812137619768370484984675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208091746512246989989783 1812137619768370484984675)
            ·
              refine ⟨2718206429652555727477013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812137619768370484984675 2718206429652555727477013)
              ·
                refine ⟨127415926389963549725485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2718206429652555727477013 127415926389963549725485)
                ·
                  rfl

theorem cell21_1674956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 6].length) (baseStart_1674956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674956 prefixEnd_1674956 := by exact prefixLift 1674956
  have htrace : WordTrace (prefixWord ++ tailWord_1674956) baseStart_1674956 baseEnd_1674956 := by
    simpa [prefixWord, tailWord_1674956, baseEnd_1674956] using wordTrace_append hprefix tailTrace_1674956
  have hstable : (prefixWord ++ tailWord_1674956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674956).length < 2 ^ (prefixWord ++ tailWord_1674956).sum := by decide
  have hdescent : baseEnd_1674956 < baseStart_1674956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674967 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 4]
def baseStart_1674967 : Nat := 118140960795 + 1674967 * 2 ^ 59
def prefixEnd_1674967 : Nat := 4983230072969 + 3 ^ 40 * 1674967 * 2
def baseEnd_1674967 : Nat := 382250289519757074493099

theorem tailTrace_1674967 : CollatzResearch.WordTrace tailWord_1674967 prefixEnd_1674967 382250289519757074493099 := by
  unfold tailWord_1674967
  simp only [CollatzResearch.WordTrace]
  refine ⟨61091065322888095434183155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40727376881925396956122103 61091065322888095434183155)
  ·
    refine ⟨91636597984332143151274733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61091065322888095434183155 91636597984332143151274733)
    ·
      refine ⟨34363724244124553681728025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91636597984332143151274733 34363724244124553681728025)
      ·
        refine ⟨25772793183093415261296019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34363724244124553681728025 25772793183093415261296019)
        ·
          refine ⟨38659189774640122891944029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25772793183093415261296019 38659189774640122891944029)
          ·
            refine ⟨14497196165490046084479011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38659189774640122891944029 14497196165490046084479011)
            ·
              refine ⟨21745794248235069126718517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14497196165490046084479011 21745794248235069126718517)
              ·
                refine ⟨2038668210772037730629861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21745794248235069126718517 2038668210772037730629861)
                ·
                  refine ⟨382250289519757074493099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2038668210772037730629861 382250289519757074493099)
                  ·
                    rfl

theorem cell21_1674967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 4].length) (baseStart_1674967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674967 prefixEnd_1674967 := by exact prefixLift 1674967
  have htrace : WordTrace (prefixWord ++ tailWord_1674967) baseStart_1674967 baseEnd_1674967 := by
    simpa [prefixWord, tailWord_1674967, baseEnd_1674967] using wordTrace_append hprefix tailTrace_1674967
  have hstable : (prefixWord ++ tailWord_1674967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674967).length < 2 ^ (prefixWord ++ tailWord_1674967).sum := by decide
  have hdescent : baseEnd_1674967 < baseStart_1674967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1674998 : List Nat := [5, 1, 1, 1, 1, 4, 8]
def baseStart_1674998 : Nat := 118140960795 + 1674998 * 2 ^ 59
def prefixEnd_1674998 : Nat := 4983230072969 + 3 ^ 40 * 1674998 * 2
def baseEnd_1674998 : Nat := 42473040460234212164041

theorem tailTrace_1674998 : CollatzResearch.WordTrace tailWord_1674998 prefixEnd_1674998 42473040460234212164041 := by
  unfold tailWord_1674998
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818262249110986733035103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40728130657183858485707765 3818262249110986733035103)
  ·
    refine ⟨5727393373666480099552655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818262249110986733035103 5727393373666480099552655)
    ·
      refine ⟨8591090060499720149328983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727393373666480099552655 8591090060499720149328983)
      ·
        refine ⟨12886635090749580223993475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8591090060499720149328983 12886635090749580223993475)
        ·
          refine ⟨19329952636124370335990213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12886635090749580223993475 19329952636124370335990213)
          ·
            refine ⟨3624366119273319437998165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19329952636124370335990213 3624366119273319437998165)
            ·
              refine ⟨42473040460234212164041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3624366119273319437998165 42473040460234212164041)
              ·
                rfl

theorem cell21_1674998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 8].length) (baseStart_1674998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1674998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1674998 prefixEnd_1674998 := by exact prefixLift 1674998
  have htrace : WordTrace (prefixWord ++ tailWord_1674998) baseStart_1674998 baseEnd_1674998 := by
    simpa [prefixWord, tailWord_1674998, baseEnd_1674998] using wordTrace_append hprefix tailTrace_1674998
  have hstable : (prefixWord ++ tailWord_1674998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1674998).length < 2 ^ (prefixWord ++ tailWord_1674998).sum := by decide
  have hdescent : baseEnd_1674998 < baseStart_1674998 := by decide
  rcases family_descends (prefixWord ++ tailWord_1674998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675038 : List Nat := [4, 3, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1675038 : Nat := 118140960795 + 1675038 * 2 ^ 59
def prefixEnd_1675038 : Nat := 4983230072969 + 3 ^ 40 * 1675038 * 2
def baseEnd_1675038 : Nat := 382266492687076728809621

theorem tailTrace_1675038 : CollatzResearch.WordTrace tailWord_1675038 prefixEnd_1675038 382266492687076728809621 := by
  unfold tailWord_1675038
  simp only [CollatzResearch.WordTrace]
  refine ⟨7636706863203859320002221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40729103270420583040011845 7636706863203859320002221)
  ·
    refine ⟨2863765073701447245000833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7636706863203859320002221 2863765073701447245000833)
    ·
      refine ⟨2147823805276085433750625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2863765073701447245000833 2147823805276085433750625)
      ·
        refine ⟨1610867853957064075312969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2147823805276085433750625 1610867853957064075312969)
        ·
          refine ⟨1208150890467798056484727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1610867853957064075312969 1208150890467798056484727)
          ·
            refine ⟨1812226335701697084727091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208150890467798056484727 1812226335701697084727091)
            ·
              refine ⟨2718339503552545627090637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812226335701697084727091 2718339503552545627090637)
              ·
                refine ⟨1019377313832204610158989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2718339503552545627090637 1019377313832204610158989)
                ·
                  refine ⟨382266492687076728809621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019377313832204610158989 382266492687076728809621)
                  ·
                    rfl

theorem cell21_1675038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1675038 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675038 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675038 prefixEnd_1675038 := by exact prefixLift 1675038
  have htrace : WordTrace (prefixWord ++ tailWord_1675038) baseStart_1675038 baseEnd_1675038 := by
    simpa [prefixWord, tailWord_1675038, baseEnd_1675038] using wordTrace_append hprefix tailTrace_1675038
  have hstable : (prefixWord ++ tailWord_1675038).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675038).length < 2 ^ (prefixWord ++ tailWord_1675038).sum := by decide
  have hdescent : baseEnd_1675038 < baseStart_1675038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675057 : List Nat := [1, 2, 2, 3, 2, 2, 9]
def baseStart_1675057 : Nat := 118140960795 + 1675057 * 2 ^ 59
def prefixEnd_1675057 : Nat := 4983230072969 + 3 ^ 40 * 1675057 * 2
def baseEnd_1675057 : Nat := 42474536527326324221435

theorem tailTrace_1675057 : CollatzResearch.WordTrace tailWord_1675057 prefixEnd_1675057 42474536527326324221435 := by
  unfold tailWord_1675057
  simp only [CollatzResearch.WordTrace]
  refine ⟨61094347892562040804959425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40729565261708027203306283 61094347892562040804959425)
  ·
    refine ⟨45820760919421530603719569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61094347892562040804959425 45820760919421530603719569)
    ·
      refine ⟨34365570689566147952789677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45820760919421530603719569 34365570689566147952789677)
      ·
        refine ⟨12887089008587305482296129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34365570689566147952789677 12887089008587305482296129)
        ·
          refine ⟨9665316756440479111722097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12887089008587305482296129 9665316756440479111722097)
          ·
            refine ⟨7248987567330359333791573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9665316756440479111722097 7248987567330359333791573)
            ·
              refine ⟨42474536527326324221435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7248987567330359333791573 42474536527326324221435)
              ·
                rfl

theorem cell21_1675057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 9].length) (baseStart_1675057 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675057 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675057 prefixEnd_1675057 := by exact prefixLift 1675057
  have htrace : WordTrace (prefixWord ++ tailWord_1675057) baseStart_1675057 baseEnd_1675057 := by
    simpa [prefixWord, tailWord_1675057, baseEnd_1675057] using wordTrace_append hprefix tailTrace_1675057
  have hstable : (prefixWord ++ tailWord_1675057).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675057).length < 2 ^ (prefixWord ++ tailWord_1675057).sum := by decide
  have hdescent : baseEnd_1675057 < baseStart_1675057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675060 : List Nat := [2, 5, 1, 1, 2, 1, 2, 1, 6]
def baseStart_1675060 : Nat := 118140960795 + 1675060 * 2 ^ 59
def prefixEnd_1675060 : Nat := 4983230072969 + 3 ^ 40 * 1675060 * 2
def baseEnd_1675060 : Nat := 382271513386809579442909

theorem tailTrace_1675060 : CollatzResearch.WordTrace tailWord_1675060 prefixEnd_1675060 382271513386809579442909 := by
  unfold tailWord_1675060
  simp only [CollatzResearch.WordTrace]
  refine ⟨30547228655775586158659317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40729638207700781544879089 30547228655775586158659317)
  ·
    refine ⟨2863802686478961202374311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30547228655775586158659317 2863802686478961202374311)
    ·
      refine ⟨4295704029718441803561467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2863802686478961202374311 4295704029718441803561467)
      ·
        refine ⟨6443556044577662705342201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4295704029718441803561467 6443556044577662705342201)
        ·
          refine ⟨4832667033433247029006651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6443556044577662705342201 4832667033433247029006651)
          ·
            refine ⟨7249000550149870543509977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832667033433247029006651 7249000550149870543509977)
            ·
              refine ⟨5436750412612402907632483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7249000550149870543509977 5436750412612402907632483)
              ·
                refine ⟨8155125618918604361448725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436750412612402907632483 8155125618918604361448725)
                ·
                  refine ⟨382271513386809579442909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8155125618918604361448725 382271513386809579442909)
                  ·
                    rfl

theorem cell21_1675060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_1675060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675060 prefixEnd_1675060 := by exact prefixLift 1675060
  have htrace : WordTrace (prefixWord ++ tailWord_1675060) baseStart_1675060 baseEnd_1675060 := by
    simpa [prefixWord, tailWord_1675060, baseEnd_1675060] using wordTrace_append hprefix tailTrace_1675060
  have hstable : (prefixWord ++ tailWord_1675060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675060).length < 2 ^ (prefixWord ++ tailWord_1675060).sum := by decide
  have hdescent : baseEnd_1675060 < baseStart_1675060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675105 : List Nat := [1, 2, 3, 1, 1, 1, 4, 5, 3]
def baseStart_1675105 : Nat := 118140960795 + 1675105 * 2 ^ 59
def prefixEnd_1675105 : Nat := 4983230072969 + 3 ^ 40 * 1675105 * 2
def baseEnd_1675105 : Nat := 382281782999899501192817

theorem tailTrace_1675105 : CollatzResearch.WordTrace tailWord_1675105 prefixEnd_1675105 382281782999899501192817 := by
  unfold tailWord_1675105
  simp only [CollatzResearch.WordTrace]
  refine ⟨61096098596388145002706769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40730732397592096668471179 61096098596388145002706769)
  ·
    refine ⟨45822073947291108752030077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61096098596388145002706769 45822073947291108752030077)
    ·
      refine ⟨17183277730234165782011279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45822073947291108752030077 17183277730234165782011279)
      ·
        refine ⟨25774916595351248673016919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17183277730234165782011279 25774916595351248673016919)
        ·
          refine ⟨38662374893026873009525379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25774916595351248673016919 38662374893026873009525379)
          ·
            refine ⟨57993562339540309514288069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38662374893026873009525379 57993562339540309514288069)
            ·
              refine ⟨10873792938663808033929013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57993562339540309514288069 10873792938663808033929013)
              ·
                refine ⟨1019418087999732003180845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10873792938663808033929013 1019418087999732003180845)
                ·
                  refine ⟨382281782999899501192817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019418087999732003180845 382281782999899501192817)
                  ·
                    rfl

theorem cell21_1675105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 5, 3].length) (baseStart_1675105 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675105 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675105 prefixEnd_1675105 := by exact prefixLift 1675105
  have htrace : WordTrace (prefixWord ++ tailWord_1675105) baseStart_1675105 baseEnd_1675105 := by
    simpa [prefixWord, tailWord_1675105, baseEnd_1675105] using wordTrace_append hprefix tailTrace_1675105
  have hstable : (prefixWord ++ tailWord_1675105).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675105).length < 2 ^ (prefixWord ++ tailWord_1675105).sum := by decide
  have hdescent : baseEnd_1675105 < baseStart_1675105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675170 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 4]
def baseStart_1675170 : Nat := 118140960795 + 1675170 * 2 ^ 59
def prefixEnd_1675170 : Nat := 4983230072969 + 3 ^ 40 * 1675170 * 2
def baseEnd_1675170 : Nat := 382296616885473832609351

theorem tailTrace_1675170 : CollatzResearch.WordTrace tailWord_1675170 prefixEnd_1675170 382296616885473832609351 := by
  unfold tailWord_1675170
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274617335288165275955741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40732312894101774069215309 15274617335288165275955741)
  ·
    refine ⟨5727981500733061978483403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15274617335288165275955741 5727981500733061978483403)
    ·
      refine ⟨8591972251099592967725105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5727981500733061978483403 8591972251099592967725105)
      ·
        refine ⟨6443979188324694725793829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8591972251099592967725105 6443979188324694725793829)
        ·
          refine ⟨1208246097810880261086343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6443979188324694725793829 1208246097810880261086343)
          ·
            refine ⟨1812369146716320391629515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208246097810880261086343 1812369146716320391629515)
            ·
              refine ⟨2718553720074480587444273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812369146716320391629515 2718553720074480587444273)
              ·
                refine ⟨2038915290055860440583205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718553720074480587444273 2038915290055860440583205)
                ·
                  refine ⟨382296616885473832609351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2038915290055860440583205 382296616885473832609351)
                  ·
                    rfl

theorem cell21_1675170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_1675170 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675170 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675170 prefixEnd_1675170 := by exact prefixLift 1675170
  have htrace : WordTrace (prefixWord ++ tailWord_1675170) baseStart_1675170 baseEnd_1675170 := by
    simpa [prefixWord, tailWord_1675170, baseEnd_1675170] using wordTrace_append hprefix tailTrace_1675170
  have hstable : (prefixWord ++ tailWord_1675170).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675170).length < 2 ^ (prefixWord ++ tailWord_1675170).sum := by decide
  have hdescent : baseEnd_1675170 < baseStart_1675170 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675226 : List Nat := [3, 1, 1, 2, 5, 2, 7]
def baseStart_1675226 : Nat := 118140960795 + 1675226 * 2 ^ 59
def prefixEnd_1675226 : Nat := 4983230072969 + 3 ^ 40 * 1675226 * 2
def baseEnd_1675226 : Nat := 42478821872047797741767

theorem tailTrace_1675226 : CollatzResearch.WordTrace tailWord_1675226 prefixEnd_1675226 42478821872047797741767 := by
  unfold tailWord_1675226
  simp only [CollatzResearch.WordTrace]
  refine ⟨15275127957237445666965383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40733674552633188445241021 15275127957237445666965383)
  ·
    refine ⟨22912691935856168500448075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15275127957237445666965383 22912691935856168500448075)
    ·
      refine ⟨34369037903784252750672113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22912691935856168500448075 34369037903784252750672113)
      ·
        refine ⟨25776778427838189563004085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34369037903784252750672113 25776778427838189563004085)
        ·
          refine ⟨2416572977609830271531633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25776778427838189563004085 2416572977609830271531633)
          ·
            refine ⟨1812429733207372703648725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2416572977609830271531633 1812429733207372703648725)
            ·
              refine ⟨42478821872047797741767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1812429733207372703648725 42478821872047797741767)
              ·
                rfl

theorem cell21_1675226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 7].length) (baseStart_1675226 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675226 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675226 prefixEnd_1675226 := by exact prefixLift 1675226
  have htrace : WordTrace (prefixWord ++ tailWord_1675226) baseStart_1675226 baseEnd_1675226 := by
    simpa [prefixWord, tailWord_1675226, baseEnd_1675226] using wordTrace_append hprefix tailTrace_1675226
  have hstable : (prefixWord ++ tailWord_1675226).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675226).length < 2 ^ (prefixWord ++ tailWord_1675226).sum := by decide
  have hdescent : baseEnd_1675226 < baseStart_1675226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675285 : List Nat := [1, 3, 2, 1, 5, 9]
def baseStart_1675285 : Nat := 118140960795 + 1675285 * 2 ^ 59
def prefixEnd_1675285 : Nat := 4983230072969 + 3 ^ 40 * 1675285 * 2
def baseEnd_1675285 : Nat := 14160105979713303266387

theorem tailTrace_1675285 : CollatzResearch.WordTrace tailWord_1675285 prefixEnd_1675285 14160105979713303266387 := by
  unfold tailWord_1675285
  simp only [CollatzResearch.WordTrace]
  refine ⟨61102663735736035744259309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40735109157157357162839539 61102663735736035744259309)
  ·
    refine ⟨22913498900901013404097241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61102663735736035744259309 22913498900901013404097241)
    ·
      refine ⟨17185124175675760053072931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22913498900901013404097241 17185124175675760053072931)
      ·
        refine ⟨25777686263513640079609397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17185124175675760053072931 25777686263513640079609397)
        ·
          refine ⟨2416658087204403757463381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25777686263513640079609397 2416658087204403757463381)
          ·
            refine ⟨14160105979713303266387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2416658087204403757463381 14160105979713303266387)
            ·
              rfl

theorem cell21_1675285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 9].length) (baseStart_1675285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675285 prefixEnd_1675285 := by exact prefixLift 1675285
  have htrace : WordTrace (prefixWord ++ tailWord_1675285) baseStart_1675285 baseEnd_1675285 := by
    simpa [prefixWord, tailWord_1675285, baseEnd_1675285] using wordTrace_append hprefix tailTrace_1675285
  have hstable : (prefixWord ++ tailWord_1675285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675285).length < 2 ^ (prefixWord ++ tailWord_1675285).sum := by decide
  have hdescent : baseEnd_1675285 < baseStart_1675285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675350 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 5]
def baseStart_1675350 : Nat := 118140960795 + 1675350 * 2 ^ 59
def prefixEnd_1675350 : Nat := 4983230072969 + 3 ^ 40 * 1675350 * 2
def baseEnd_1675350 : Nat := 382337695337833519608983

theorem tailTrace_1675350 : CollatzResearch.WordTrace tailWord_1675350 prefixEnd_1675350 382337695337833519608983 := by
  unfold tailWord_1675350
  simp only [CollatzResearch.WordTrace]
  refine ⟨3819064655031284490335969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40736689653667034563583669 3819064655031284490335969)
  ·
    refine ⟨2864298491273463367751977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3819064655031284490335969 2864298491273463367751977)
    ·
      refine ⟨2148223868455097525813983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2864298491273463367751977 2148223868455097525813983)
      ·
        refine ⟨3222335802682646288720975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148223868455097525813983 3222335802682646288720975)
        ·
          refine ⟨4833503704023969433081463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222335802682646288720975 4833503704023969433081463)
          ·
            refine ⟨7250255556035954149622195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833503704023969433081463 7250255556035954149622195)
            ·
              refine ⟨10875383334053931224433293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250255556035954149622195 10875383334053931224433293)
              ·
                refine ⟨4078268750270224209162485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10875383334053931224433293 4078268750270224209162485)
                ·
                  refine ⟨382337695337833519608983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4078268750270224209162485 382337695337833519608983)
                  ·
                    rfl

theorem cell21_1675350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_1675350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675350 prefixEnd_1675350 := by exact prefixLift 1675350
  have htrace : WordTrace (prefixWord ++ tailWord_1675350) baseStart_1675350 baseEnd_1675350 := by
    simpa [prefixWord, tailWord_1675350, baseEnd_1675350] using wordTrace_append hprefix tailTrace_1675350
  have hstable : (prefixWord ++ tailWord_1675350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675350).length < 2 ^ (prefixWord ++ tailWord_1675350).sum := by decide
  have hdescent : baseEnd_1675350 < baseStart_1675350 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675378 : List Nat := [3, 2, 1, 2, 2, 2, 4, 5]
def baseStart_1675378 : Nat := 118140960795 + 1675378 * 2 ^ 59
def prefixEnd_1675378 : Nat := 4983230072969 + 3 ^ 40 * 1675378 * 2
def baseEnd_1675378 : Nat := 127448028439770564380753

theorem tailTrace_1675378 : CollatzResearch.WordTrace tailWord_1675378 prefixEnd_1675378 127448028439770564380753 := by
  unfold tailWord_1675378
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276513931099778156848697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40737370482932741751596525 15276513931099778156848697)
  ·
    refine ⟨11457385448324833617636523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15276513931099778156848697 11457385448324833617636523)
    ·
      refine ⟨17186078172487250426454785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11457385448324833617636523 17186078172487250426454785)
      ·
        refine ⟨12889558629365437819841089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17186078172487250426454785 12889558629365437819841089)
        ·
          refine ⟨9667168972024078364880817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12889558629365437819841089 9667168972024078364880817)
          ·
            refine ⟨7250376729018058773660613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9667168972024078364880817 7250376729018058773660613)
            ·
              refine ⟨1359445636690886020061365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7250376729018058773660613 1359445636690886020061365)
              ·
                refine ⟨127448028439770564380753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1359445636690886020061365 127448028439770564380753)
                ·
                  rfl

theorem cell21_1675378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_1675378 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675378 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675378 prefixEnd_1675378 := by exact prefixLift 1675378
  have htrace : WordTrace (prefixWord ++ tailWord_1675378) baseStart_1675378 baseEnd_1675378 := by
    simpa [prefixWord, tailWord_1675378, baseEnd_1675378] using wordTrace_append hprefix tailTrace_1675378
  have hstable : (prefixWord ++ tailWord_1675378).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675378).length < 2 ^ (prefixWord ++ tailWord_1675378).sum := by decide
  have hdescent : baseEnd_1675378 < baseStart_1675378 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675454 : List Nat := [4, 2, 1, 1, 5, 8]
def baseStart_1675454 : Nat := 118140960795 + 1675454 * 2 ^ 59
def prefixEnd_1675454 : Nat := 4983230072969 + 3 ^ 40 * 1675454 * 2
def baseEnd_1675454 : Nat := 14161534427953794439831

theorem tailTrace_1675454 : CollatzResearch.WordTrace tailWord_1675454 prefixEnd_1675454 14161534427953794439831 := by
  unfold tailWord_1675454
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638603459015472200895177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40739218448082518404774277 7638603459015472200895177)
  ·
    refine ⟨5728952594261604150671383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7638603459015472200895177 5728952594261604150671383)
    ·
      refine ⟨8593428891392406226007075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5728952594261604150671383 8593428891392406226007075)
      ·
        refine ⟨12890143337088609339010613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593428891392406226007075 12890143337088609339010613)
        ·
          refine ⟨1208450937852057125532245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12890143337088609339010613 1208450937852057125532245)
          ·
            refine ⟨14161534427953794439831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1208450937852057125532245 14161534427953794439831)
            ·
              rfl

theorem cell21_1675454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 8].length) (baseStart_1675454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675454 prefixEnd_1675454 := by exact prefixLift 1675454
  have htrace : WordTrace (prefixWord ++ tailWord_1675454) baseStart_1675454 baseEnd_1675454 := by
    simpa [prefixWord, tailWord_1675454, baseEnd_1675454] using wordTrace_append hprefix tailTrace_1675454
  have hstable : (prefixWord ++ tailWord_1675454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675454).length < 2 ^ (prefixWord ++ tailWord_1675454).sum := by decide
  have hdescent : baseEnd_1675454 < baseStart_1675454 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675457 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 4]
def baseStart_1675457 : Nat := 118140960795 + 1675457 * 2 ^ 59
def prefixEnd_1675457 : Nat := 4983230072969 + 3 ^ 40 * 1675457 * 2
def baseEnd_1675457 : Nat := 382362114195625111325431

theorem tailTrace_1675457 : CollatzResearch.WordTrace tailWord_1675457 prefixEnd_1675457 382362114195625111325431 := by
  unfold tailWord_1675457
  simp only [CollatzResearch.WordTrace]
  refine ⟨61108937091112909119520625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40739291394075272746347083 61108937091112909119520625)
  ·
    refine ⟨45831702818334681839640469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61108937091112909119520625 45831702818334681839640469)
    ·
      refine ⟨2148361069609438211233147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45831702818334681839640469 2148361069609438211233147)
      ·
        refine ⟨3222541604414157316849721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148361069609438211233147 3222541604414157316849721)
        ·
          refine ⟨2416906203310617987637291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222541604414157316849721 2416906203310617987637291)
          ·
            refine ⟨3625359304965926981455937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416906203310617987637291 3625359304965926981455937)
            ·
              refine ⟨2719019478724445236091953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625359304965926981455937 2719019478724445236091953)
              ·
                refine ⟨2039264609043333927068965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719019478724445236091953 2039264609043333927068965)
                ·
                  refine ⟨382362114195625111325431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039264609043333927068965 382362114195625111325431)
                  ·
                    rfl

theorem cell21_1675457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_1675457 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675457 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675457 prefixEnd_1675457 := by exact prefixLift 1675457
  have htrace : WordTrace (prefixWord ++ tailWord_1675457) baseStart_1675457 baseEnd_1675457 := by
    simpa [prefixWord, tailWord_1675457, baseEnd_1675457] using wordTrace_append hprefix tailTrace_1675457
  have hstable : (prefixWord ++ tailWord_1675457).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675457).length < 2 ^ (prefixWord ++ tailWord_1675457).sum := by decide
  have hdescent : baseEnd_1675457 < baseStart_1675457 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675485 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 5]
def baseStart_1675485 : Nat := 118140960795 + 1675485 * 2 ^ 59
def prefixEnd_1675485 : Nat := 4983230072969 + 3 ^ 40 * 1675485 * 2
def baseEnd_1675485 : Nat := 382368504177103284858707

theorem tailTrace_1675485 : CollatzResearch.WordTrace tailWord_1675485 prefixEnd_1675485 382368504177103284858707 := by
  unfold tailWord_1675485
  simp only [CollatzResearch.WordTrace]
  refine ⟨61109958335011469901539909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40739972223340979934359939 61109958335011469901539909)
  ·
    refine ⟨11458117187814650606538733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61109958335011469901539909 11458117187814650606538733)
    ·
      refine ⟨4296793945430493977452025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11458117187814650606538733 4296793945430493977452025)
      ·
        refine ⟨3222595459072870483089019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4296793945430493977452025 3222595459072870483089019)
        ·
          refine ⟨4833893188609305724633529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222595459072870483089019 4833893188609305724633529)
          ·
            refine ⟨3625419891456979293475147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4833893188609305724633529 3625419891456979293475147)
            ·
              refine ⟨5438129837185468940212721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625419891456979293475147 5438129837185468940212721)
              ·
                refine ⟨4078597377889101705159541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5438129837185468940212721 4078597377889101705159541)
                ·
                  refine ⟨382368504177103284858707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4078597377889101705159541 382368504177103284858707)
                  ·
                    rfl

theorem cell21_1675485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_1675485 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675485 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675485 prefixEnd_1675485 := by exact prefixLift 1675485
  have htrace : WordTrace (prefixWord ++ tailWord_1675485) baseStart_1675485 baseEnd_1675485 := by
    simpa [prefixWord, tailWord_1675485, baseEnd_1675485] using wordTrace_append hprefix tailTrace_1675485
  have hstable : (prefixWord ++ tailWord_1675485).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675485).length < 2 ^ (prefixWord ++ tailWord_1675485).sum := by decide
  have hdescent : baseEnd_1675485 < baseStart_1675485 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675516 : List Nat := [2, 2, 2, 1, 4, 3, 1, 2, 4]
def baseStart_1675516 : Nat := 118140960795 + 1675516 * 2 ^ 59
def prefixEnd_1675516 : Nat := 4983230072969 + 3 ^ 40 * 1675516 * 2
def baseEnd_1675516 : Nat := 382375578799454119841977

theorem tailTrace_1675516 : CollatzResearch.WordTrace tailWord_1675516 prefixEnd_1675516 382375578799454119841977 := by
  unfold tailWord_1675516
  simp only [CollatzResearch.WordTrace]
  refine ⟨30555544498949581097959201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40740725998599441463945601 30555544498949581097959201)
  ·
    refine ⟨22916658374212185823469401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30555544498949581097959201 22916658374212185823469401)
    ·
      refine ⟨17187493780659139367602051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22916658374212185823469401 17187493780659139367602051)
      ·
        refine ⟨25781240670988709051403077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17187493780659139367602051 25781240670988709051403077)
        ·
          refine ⟨4833982625810382947138077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25781240670988709051403077 4833982625810382947138077)
          ·
            refine ⟨1812743484678893605176779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4833982625810382947138077 1812743484678893605176779)
            ·
              refine ⟨2719115227018340407765169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1812743484678893605176779 2719115227018340407765169)
              ·
                refine ⟨2039336420263755305823877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719115227018340407765169 2039336420263755305823877)
                ·
                  refine ⟨382375578799454119841977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039336420263755305823877 382375578799454119841977)
                  ·
                    rfl

theorem cell21_1675516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 3, 1, 2, 4].length) (baseStart_1675516 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675516 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675516 prefixEnd_1675516 := by exact prefixLift 1675516
  have htrace : WordTrace (prefixWord ++ tailWord_1675516) baseStart_1675516 baseEnd_1675516 := by
    simpa [prefixWord, tailWord_1675516, baseEnd_1675516] using wordTrace_append hprefix tailTrace_1675516
  have hstable : (prefixWord ++ tailWord_1675516).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675516).length < 2 ^ (prefixWord ++ tailWord_1675516).sum := by decide
  have hdescent : baseEnd_1675516 < baseStart_1675516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675578 : List Nat := [3, 1, 1, 1, 4, 3, 3, 2, 3]
def baseStart_1675578 : Nat := 118140960795 + 1675578 * 2 ^ 59
def prefixEnd_1675578 : Nat := 4983230072969 + 3 ^ 40 * 1675578 * 2
def baseEnd_1675578 : Nat := 382389728044155789808517

theorem tailTrace_1675578 : CollatzResearch.WordTrace tailWord_1675578 prefixEnd_1675578 382389728044155789808517 := by
  unfold tailWord_1675578
  simp only [CollatzResearch.WordTrace]
  refine ⟨15278337580918636696168847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40742233549116364523116925 15278337580918636696168847)
  ·
    refine ⟨22917506371377955044253271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15278337580918636696168847 22917506371377955044253271)
    ·
      refine ⟨34376259557066932566379907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22917506371377955044253271 34376259557066932566379907)
      ·
        refine ⟨51564389335600398849569861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34376259557066932566379907 51564389335600398849569861)
        ·
          refine ⟨9668323000425074784294349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51564389335600398849569861 9668323000425074784294349)
          ·
            refine ⟨3625621125159403044110381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9668323000425074784294349 3625621125159403044110381)
            ·
              refine ⟨1359607921934776141541393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3625621125159403044110381 1359607921934776141541393)
              ·
                refine ⟨1019705941451082106156045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1359607921934776141541393 1019705941451082106156045)
                ·
                  refine ⟨382389728044155789808517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1019705941451082106156045 382389728044155789808517)
                  ·
                    rfl

theorem cell21_1675578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3, 2, 3].length) (baseStart_1675578 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675578 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675578 prefixEnd_1675578 := by exact prefixLift 1675578
  have htrace : WordTrace (prefixWord ++ tailWord_1675578) baseStart_1675578 baseEnd_1675578 := by
    simpa [prefixWord, tailWord_1675578, baseEnd_1675578] using wordTrace_append hprefix tailTrace_1675578
  have hstable : (prefixWord ++ tailWord_1675578).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675578).length < 2 ^ (prefixWord ++ tailWord_1675578).sum := by decide
  have hdescent : baseEnd_1675578 < baseStart_1675578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675679 : List Nat := [1, 1, 2, 5, 1, 1, 1, 2, 7]
def baseStart_1675679 : Nat := 118140960795 + 1675679 * 2 ^ 59
def prefixEnd_1675679 : Nat := 4983230072969 + 3 ^ 40 * 1675679 * 2
def baseEnd_1675679 : Nat := 382412777620202058624977

theorem tailTrace_1675679 : CollatzResearch.WordTrace tailWord_1675679 prefixEnd_1675679 382412777620202058624977 := by
  unfold tailWord_1675679
  simp only [CollatzResearch.WordTrace]
  refine ⟨61117034096308641034102091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40744689397539094022734727 61117034096308641034102091)
  ·
    refine ⟨91675551144462961551153137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61117034096308641034102091 91675551144462961551153137)
    ·
      refine ⟨68756663358347221163364853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91675551144462961551153137 68756663358347221163364853)
      ·
        refine ⟨6445937189845051984065455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68756663358347221163364853 6445937189845051984065455)
        ·
          refine ⟨9668905784767577976098183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6445937189845051984065455 9668905784767577976098183)
          ·
            refine ⟨14503358677151366964147275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9668905784767577976098183 14503358677151366964147275)
            ·
              refine ⟨21755038015727050446220913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14503358677151366964147275 21755038015727050446220913)
              ·
                refine ⟨16316278511795287834665685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21755038015727050446220913 16316278511795287834665685)
                ·
                  refine ⟨382412777620202058624977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16316278511795287834665685 382412777620202058624977)
                  ·
                    rfl

theorem cell21_1675679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 1, 2, 7].length) (baseStart_1675679 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675679 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675679 prefixEnd_1675679 := by exact prefixLift 1675679
  have htrace : WordTrace (prefixWord ++ tailWord_1675679) baseStart_1675679 baseEnd_1675679 := by
    simpa [prefixWord, tailWord_1675679, baseEnd_1675679] using wordTrace_append hprefix tailTrace_1675679
  have hstable : (prefixWord ++ tailWord_1675679).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675679).length < 2 ^ (prefixWord ++ tailWord_1675679).sum := by decide
  have hdescent : baseEnd_1675679 < baseStart_1675679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675716 : List Nat := [2, 3, 3, 2, 3, 1, 2, 5]
def baseStart_1675716 : Nat := 118140960795 + 1675716 * 2 ^ 59
def prefixEnd_1675716 : Nat := 4983230072969 + 3 ^ 40 * 1675716 * 2
def baseEnd_1675716 : Nat := 127473740508099405502745

theorem tailTrace_1675716 : CollatzResearch.WordTrace tailWord_1675716 prefixEnd_1675716 127473740508099405502745 := by
  unfold tailWord_1675716
  simp only [CollatzResearch.WordTrace]
  refine ⟨30559191798587298176599501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40745589064783064235466001 30559191798587298176599501)
  ·
    refine ⟨11459696924470236816224813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30559191798587298176599501 11459696924470236816224813)
    ·
      refine ⟨4297386346676338806084305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11459696924470236816224813 4297386346676338806084305)
      ·
        refine ⟨3223039760007254104563229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4297386346676338806084305 3223039760007254104563229)
        ·
          refine ⟨1208639910002720289211211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3223039760007254104563229 1208639910002720289211211)
          ·
            refine ⟨1812959865004080433816817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208639910002720289211211 1812959865004080433816817)
            ·
              refine ⟨1359719898753060325362613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812959865004080433816817 1359719898753060325362613)
              ·
                refine ⟨127473740508099405502745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1359719898753060325362613 127473740508099405502745)
                ·
                  rfl

theorem cell21_1675716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 3, 1, 2, 5].length) (baseStart_1675716 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675716 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675716 prefixEnd_1675716 := by exact prefixLift 1675716
  have htrace : WordTrace (prefixWord ++ tailWord_1675716) baseStart_1675716 baseEnd_1675716 := by
    simpa [prefixWord, tailWord_1675716, baseEnd_1675716] using wordTrace_append hprefix tailTrace_1675716
  have hstable : (prefixWord ++ tailWord_1675716).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675716).length < 2 ^ (prefixWord ++ tailWord_1675716).sum := by decide
  have hdescent : baseEnd_1675716 < baseStart_1675716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675800 : List Nat := [2, 1, 2, 3, 3, 10]
def baseStart_1675800 : Nat := 118140960795 + 1675800 * 2 ^ 59
def prefixEnd_1675800 : Nat := 4983230072969 + 3 ^ 40 * 1675800 * 2
def baseEnd_1675800 : Nat := 14164458943286397670669

theorem tailTrace_1675800 : CollatzResearch.WordTrace tailWord_1675800 prefixEnd_1675800 14164458943286397670669 := by
  unfold tailWord_1675800
  simp only [CollatzResearch.WordTrace]
  refine ⟨30560723664435139349628427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40747631552580185799504569 30560723664435139349628427)
  ·
    refine ⟨45841085496652709024442641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30560723664435139349628427 45841085496652709024442641)
    ·
      refine ⟨34380814122489531768331981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45841085496652709024442641 34380814122489531768331981)
      ·
        refine ⟨12892805295933574413124493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34380814122489531768331981 12892805295933574413124493)
        ·
          refine ⟨4834801985975090404921685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12892805295933574413124493 4834801985975090404921685)
          ·
            refine ⟨14164458943286397670669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4834801985975090404921685 14164458943286397670669)
            ·
              rfl

theorem cell21_1675800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 10].length) (baseStart_1675800 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675800 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675800 prefixEnd_1675800 := by exact prefixLift 1675800
  have htrace : WordTrace (prefixWord ++ tailWord_1675800) baseStart_1675800 baseEnd_1675800 := by
    simpa [prefixWord, tailWord_1675800, baseEnd_1675800] using wordTrace_append hprefix tailTrace_1675800
  have hstable : (prefixWord ++ tailWord_1675800).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675800).length < 2 ^ (prefixWord ++ tailWord_1675800).sum := by decide
  have hdescent : baseEnd_1675800 < baseStart_1675800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675831 : List Nat := [1, 1, 3, 1, 2, 3, 3, 2, 5]
def baseStart_1675831 : Nat := 118140960795 + 1675831 * 2 ^ 59
def prefixEnd_1675831 : Nat := 4983230072969 + 3 ^ 40 * 1675831 * 2
def baseEnd_1675831 : Nat := 382447466091083572091333

theorem tailTrace_1675831 : CollatzResearch.WordTrace tailWord_1675831 prefixEnd_1675831 382447466091083572091333 := by
  unfold tailWord_1675831
  simp only [CollatzResearch.WordTrace]
  refine ⟨61122577991757970993635347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40748385327838647329090231 61122577991757970993635347)
  ·
    refine ⟨91683866987636956490453021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61122577991757970993635347 91683866987636956490453021)
    ·
      refine ⟨34381450120363858683919883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91683866987636956490453021 34381450120363858683919883)
      ·
        refine ⟨51572175180545788025879825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34381450120363858683919883 51572175180545788025879825)
        ·
          refine ⟨38679131385409341019409869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51572175180545788025879825 38679131385409341019409869)
          ·
            refine ⟨14504674269528502882278701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38679131385409341019409869 14504674269528502882278701)
            ·
              refine ⟨5439252851073188580854513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14504674269528502882278701 5439252851073188580854513)
              ·
                refine ⟨4079439638304891435640885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5439252851073188580854513 4079439638304891435640885)
                ·
                  refine ⟨382447466091083572091333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4079439638304891435640885 382447466091083572091333)
                  ·
                    rfl

theorem cell21_1675831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 3, 2, 5].length) (baseStart_1675831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675831 prefixEnd_1675831 := by exact prefixLift 1675831
  have htrace : WordTrace (prefixWord ++ tailWord_1675831) baseStart_1675831 baseEnd_1675831 := by
    simpa [prefixWord, tailWord_1675831, baseEnd_1675831] using wordTrace_append hprefix tailTrace_1675831
  have hstable : (prefixWord ++ tailWord_1675831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675831).length < 2 ^ (prefixWord ++ tailWord_1675831).sum := by decide
  have hdescent : baseEnd_1675831 < baseStart_1675831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675876 : List Nat := [2, 3, 1, 1, 2, 2, 2, 8]
def baseStart_1675876 : Nat := 118140960795 + 1675876 * 2 ^ 59
def prefixEnd_1675876 : Nat := 4983230072969 + 3 ^ 40 * 1675876 * 2
def baseEnd_1675876 : Nat := 127485911901391164613747

theorem tailTrace_1675876 : CollatzResearch.WordTrace tailWord_1675876 prefixEnd_1675876 127485911901391164613747 := by
  unfold tailWord_1675876
  simp only [CollatzResearch.WordTrace]
  refine ⟨30562109638297471839511741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40749479517729962452682321 30562109638297471839511741)
  ·
    refine ⟨11460791114361551939816903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30562109638297471839511741 11460791114361551939816903)
    ·
      refine ⟨17191186671542327909725355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11460791114361551939816903 17191186671542327909725355)
      ·
        refine ⟨25786780007313491864588033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17191186671542327909725355 25786780007313491864588033)
        ·
          refine ⟨19340085005485118898441025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25786780007313491864588033 19340085005485118898441025)
          ·
            refine ⟨14505063754113839173830769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19340085005485118898441025 14505063754113839173830769)
            ·
              refine ⟨10878797815585379380373077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14505063754113839173830769 10878797815585379380373077)
              ·
                refine ⟨127485911901391164613747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10878797815585379380373077 127485911901391164613747)
                ·
                  rfl

theorem cell21_1675876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 8].length) (baseStart_1675876 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675876 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675876 prefixEnd_1675876 := by exact prefixLift 1675876
  have htrace : WordTrace (prefixWord ++ tailWord_1675876) baseStart_1675876 baseEnd_1675876 := by
    simpa [prefixWord, tailWord_1675876, baseEnd_1675876] using wordTrace_append hprefix tailTrace_1675876
  have hstable : (prefixWord ++ tailWord_1675876).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675876).length < 2 ^ (prefixWord ++ tailWord_1675876).sum := by decide
  have hdescent : baseEnd_1675876 < baseStart_1675876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675930 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 4]
def baseStart_1675930 : Nat := 118140960795 + 1675930 * 2 ^ 59
def prefixEnd_1675930 : Nat := 4983230072969 + 3 ^ 40 * 1675930 * 2
def baseEnd_1675930 : Nat := 382470059239881399941131

theorem tailTrace_1675930 : CollatzResearch.WordTrace tailWord_1675930 prefixEnd_1675930 382470059239881399941131 := by
  unfold tailWord_1675930
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281547204599827725372311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40750792545599540600992829 15281547204599827725372311)
  ·
    refine ⟨22922320806899741588058467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15281547204599827725372311 22922320806899741588058467)
    ·
      refine ⟨34383481210349612382087701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22922320806899741588058467 34383481210349612382087701)
      ·
        refine ⟨1611725681735138080410361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34383481210349612382087701 1611725681735138080410361)
        ·
          refine ⟨1208794261301353560307771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1611725681735138080410361 1208794261301353560307771)
          ·
            refine ⟨1813191391952030340461657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208794261301353560307771 1813191391952030340461657)
            ·
              refine ⟨1359893543964022755346243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813191391952030340461657 1359893543964022755346243)
              ·
                refine ⟨2039840315946034133019365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359893543964022755346243 2039840315946034133019365)
                ·
                  refine ⟨382470059239881399941131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2039840315946034133019365 382470059239881399941131)
                  ·
                    rfl

theorem cell21_1675930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 4].length) (baseStart_1675930 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675930 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675930 prefixEnd_1675930 := by exact prefixLift 1675930
  have htrace : WordTrace (prefixWord ++ tailWord_1675930) baseStart_1675930 baseEnd_1675930 := by
    simpa [prefixWord, tailWord_1675930, baseEnd_1675930] using wordTrace_append hprefix tailTrace_1675930
  have hstable : (prefixWord ++ tailWord_1675930).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675930).length < 2 ^ (prefixWord ++ tailWord_1675930).sum := by decide
  have hdescent : baseEnd_1675930 < baseStart_1675930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675969 : List Nat := [1, 2, 6, 2, 10]
def baseStart_1675969 : Nat := 118140960795 + 1675969 * 2 ^ 59
def prefixEnd_1675969 : Nat := 4983230072969 + 3 ^ 40 * 1675969 * 2
def baseEnd_1675969 : Nat := 4721962463842296281371

theorem tailTrace_1675969 : CollatzResearch.WordTrace tailWord_1675969 prefixEnd_1675969 4721962463842296281371 := by
  unfold tailWord_1675969
  simp only [CollatzResearch.WordTrace]
  refine ⟨61127611265258020562158961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40751740843505347041439307 61127611265258020562158961)
  ·
    refine ⟨45845708448943515421619221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61127611265258020562158961 45845708448943515421619221)
    ·
      refine ⟨2149017583544227285388401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45845708448943515421619221 2149017583544227285388401)
      ·
        refine ⟨1611763187658170464041301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2149017583544227285388401 1611763187658170464041301)
        ·
          refine ⟨4721962463842296281371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 1611763187658170464041301 4721962463842296281371)
          ·
            rfl

theorem cell21_1675969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 10].length) (baseStart_1675969 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675969 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675969 prefixEnd_1675969 := by exact prefixLift 1675969
  have htrace : WordTrace (prefixWord ++ tailWord_1675969) baseStart_1675969 baseEnd_1675969 := by
    simpa [prefixWord, tailWord_1675969, baseEnd_1675969] using wordTrace_append hprefix tailTrace_1675969
  have hstable : (prefixWord ++ tailWord_1675969).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675969).length < 2 ^ (prefixWord ++ tailWord_1675969).sum := by decide
  have hdescent : baseEnd_1675969 < baseStart_1675969 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1675986 : List Nat := [3, 2, 2, 2, 3, 2, 1, 6]
def baseStart_1675986 : Nat := 118140960795 + 1675986 * 2 ^ 59
def prefixEnd_1675986 : Nat := 4983230072969 + 3 ^ 40 * 1675986 * 2
def baseEnd_1675986 : Nat := 127494279734279249002561

theorem tailTrace_1675986 : CollatzResearch.WordTrace tailWord_1675986 prefixEnd_1675986 127494279734279249002561 := by
  unfold tailWord_1675986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15282057826549108116381953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40752154204130954977018541 15282057826549108116381953)
  ·
    refine ⟨11461543369911831087286465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15282057826549108116381953 11461543369911831087286465)
    ·
      refine ⟨8596157527433873315464849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11461543369911831087286465 8596157527433873315464849)
      ·
        refine ⟨6447118145575404986598637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8596157527433873315464849 6447118145575404986598637)
        ·
          refine ⟨2417669304590776869974489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6447118145575404986598637 2417669304590776869974489)
          ·
            refine ⟨1813251978443082652480867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417669304590776869974489 1813251978443082652480867)
            ·
              refine ⟨2719877967664623978721301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813251978443082652480867 2719877967664623978721301)
              ·
                refine ⟨127494279734279249002561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2719877967664623978721301 127494279734279249002561)
                ·
                  rfl

theorem cell21_1675986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 6].length) (baseStart_1675986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1675986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1675986 prefixEnd_1675986 := by exact prefixLift 1675986
  have htrace : WordTrace (prefixWord ++ tailWord_1675986) baseStart_1675986 baseEnd_1675986 := by
    simpa [prefixWord, tailWord_1675986, baseEnd_1675986] using wordTrace_append hprefix tailTrace_1675986
  have hstable : (prefixWord ++ tailWord_1675986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1675986).length < 2 ^ (prefixWord ++ tailWord_1675986).sum := by decide
  have hdescent : baseEnd_1675986 < baseStart_1675986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1675986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676028 : List Nat := [2, 2, 2, 1, 3, 3, 8]
def baseStart_1676028 : Nat := 118140960795 + 1676028 * 2 ^ 59
def prefixEnd_1676028 : Nat := 4983230072969 + 3 ^ 40 * 1676028 * 2
def baseEnd_1676028 : Nat := 42499158241672778589733

theorem tailTrace_1676028 : CollatzResearch.WordTrace tailWord_1676028 prefixEnd_1676028 42499158241672778589733 := by
  unfold tailWord_1676028
  simp only [CollatzResearch.WordTrace]
  refine ⟨30564881586022136819278369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40753175448029515759037825 30564881586022136819278369)
  ·
    refine ⟨22923661189516602614458777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30564881586022136819278369 22923661189516602614458777)
    ·
      refine ⟨17192745892137451960844083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22923661189516602614458777 17192745892137451960844083)
      ·
        refine ⟨25789118838206177941266125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17192745892137451960844083 25789118838206177941266125)
        ·
          refine ⟨9670919564327316727974797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25789118838206177941266125 9670919564327316727974797)
          ·
            refine ⟨3626594836622743772990549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9670919564327316727974797 3626594836622743772990549)
            ·
              refine ⟨42499158241672778589733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3626594836622743772990549 42499158241672778589733)
              ·
                rfl

theorem cell21_1676028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 3, 8].length) (baseStart_1676028 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676028 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676028 prefixEnd_1676028 := by exact prefixLift 1676028
  have htrace : WordTrace (prefixWord ++ tailWord_1676028) baseStart_1676028 baseEnd_1676028 := by
    simpa [prefixWord, tailWord_1676028, baseEnd_1676028] using wordTrace_append hprefix tailTrace_1676028
  have hstable : (prefixWord ++ tailWord_1676028).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676028).length < 2 ^ (prefixWord ++ tailWord_1676028).sum := by decide
  have hdescent : baseEnd_1676028 < baseStart_1676028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676093 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1676093 : Nat := 118140960795 + 1676093 * 2 ^ 59
def prefixEnd_1676093 : Nat := 4983230072969 + 3 ^ 40 * 1676093 * 2
def baseEnd_1676093 : Nat := 382507258060629338724131

theorem tailTrace_1676093 : CollatzResearch.WordTrace tailWord_1676093 prefixEnd_1676093 382507258060629338724131 := by
  unfold tailWord_1676093
  simp only [CollatzResearch.WordTrace]
  refine ⟨61132133916808789739672933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40754755944539193159781955 61132133916808789739672933)
  ·
    refine ⟨11462275109401648076188675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61132133916808789739672933 11462275109401648076188675)
    ·
      refine ⟨17193412664102472114283013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11462275109401648076188675 17193412664102472114283013)
      ·
        refine ⟨3223764874519213521428065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17193412664102472114283013 3223764874519213521428065)
        ·
          refine ⟨2417823655889410141071049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3223764874519213521428065 2417823655889410141071049)
          ·
            refine ⟨1813367741917057605803287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2417823655889410141071049 1813367741917057605803287)
            ·
              refine ⟨2720051612875586408704931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813367741917057605803287 2720051612875586408704931)
              ·
                refine ⟨4080077419313379613057397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720051612875586408704931 4080077419313379613057397)
                ·
                  refine ⟨382507258060629338724131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080077419313379613057397 382507258060629338724131)
                  ·
                    rfl

theorem cell21_1676093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1676093 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676093 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676093 prefixEnd_1676093 := by exact prefixLift 1676093
  have htrace : WordTrace (prefixWord ++ tailWord_1676093) baseStart_1676093 baseEnd_1676093 := by
    simpa [prefixWord, tailWord_1676093, baseEnd_1676093] using wordTrace_append hprefix tailTrace_1676093
  have hstable : (prefixWord ++ tailWord_1676093).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676093).length < 2 ^ (prefixWord ++ tailWord_1676093).sum := by decide
  have hdescent : baseEnd_1676093 < baseStart_1676093 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676104 : List Nat := [2, 1, 3, 1, 1, 3, 4, 6]
def baseStart_1676104 : Nat := 118140960795 + 1676104 * 2 ^ 59
def prefixEnd_1676104 : Nat := 4983230072969 + 3 ^ 40 * 1676104 * 2
def baseEnd_1676104 : Nat := 127503256136831921346925

theorem tailTrace_1676104 : CollatzResearch.WordTrace tailWord_1676104 prefixEnd_1676104 127503256136831921346925 := by
  unfold tailWord_1676104
  simp only [CollatzResearch.WordTrace]
  refine ⟨30566267559884469309161683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40755023413179292412215577 30566267559884469309161683)
  ·
    refine ⟨45849401339826703963742525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30566267559884469309161683 45849401339826703963742525)
    ·
      refine ⟨17193525502435013986403447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45849401339826703963742525 17193525502435013986403447)
      ·
        refine ⟨25790288253652520979605171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17193525502435013986403447 25790288253652520979605171)
        ·
          refine ⟨38685432380478781469407757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25790288253652520979605171 38685432380478781469407757)
          ·
            refine ⟨14507037142679543051027909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38685432380478781469407757 14507037142679543051027909)
            ·
              refine ⟨2720069464252414322067733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14507037142679543051027909 2720069464252414322067733)
              ·
                refine ⟨127503256136831921346925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2720069464252414322067733 127503256136831921346925)
                ·
                  rfl

theorem cell21_1676104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 6].length) (baseStart_1676104 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676104 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676104 prefixEnd_1676104 := by exact prefixLift 1676104
  have htrace : WordTrace (prefixWord ++ tailWord_1676104) baseStart_1676104 baseEnd_1676104 := by
    simpa [prefixWord, tailWord_1676104, baseEnd_1676104] using wordTrace_append hprefix tailTrace_1676104
  have hstable : (prefixWord ++ tailWord_1676104).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676104).length < 2 ^ (prefixWord ++ tailWord_1676104).sum := by decide
  have hdescent : baseEnd_1676104 < baseStart_1676104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676237 : List Nat := [1, 6, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1676237 : Nat := 118140960795 + 1676237 * 2 ^ 59
def prefixEnd_1676237 : Nat := 4983230072969 + 3 ^ 40 * 1676237 * 2
def baseEnd_1676237 : Nat := 382540120822517088323837

theorem tailTrace_1676237 : CollatzResearch.WordTrace tailWord_1676237 prefixEnd_1676237 382540120822517088323837 := by
  unfold tailWord_1676237
  simp only [CollatzResearch.WordTrace]
  refine ⟨61137386028287102332914965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40758257352191401555276643 61137386028287102332914965)
  ·
    refine ⟨2865814970075957921855389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61137386028287102332914965 2865814970075957921855389)
    ·
      refine ⟨1074680613778484220695771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2865814970075957921855389 1074680613778484220695771)
      ·
        refine ⟨1612020920667726331043657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1074680613778484220695771 1612020920667726331043657)
        ·
          refine ⟨1209015690500794748282743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1612020920667726331043657 1209015690500794748282743)
          ·
            refine ⟨1813523535751192122424115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209015690500794748282743 1813523535751192122424115)
            ·
              refine ⟨2720285303626788183636173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813523535751192122424115 2720285303626788183636173)
              ·
                refine ⟨1020106988860045568863565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2720285303626788183636173 1020106988860045568863565)
                ·
                  refine ⟨382540120822517088323837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020106988860045568863565 382540120822517088323837)
                  ·
                    rfl

theorem cell21_1676237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1676237 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676237 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676237 prefixEnd_1676237 := by exact prefixLift 1676237
  have htrace : WordTrace (prefixWord ++ tailWord_1676237) baseStart_1676237 baseEnd_1676237 := by
    simpa [prefixWord, tailWord_1676237, baseEnd_1676237] using wordTrace_append hprefix tailTrace_1676237
  have hstable : (prefixWord ++ tailWord_1676237).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676237).length < 2 ^ (prefixWord ++ tailWord_1676237).sum := by decide
  have hdescent : baseEnd_1676237 < baseStart_1676237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676242 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 6]
def baseStart_1676242 : Nat := 118140960795 + 1676242 * 2 ^ 59
def prefixEnd_1676242 : Nat := 4983230072969 + 3 ^ 40 * 1676242 * 2
def baseEnd_1676242 : Nat := 382541261890638190740493

theorem tailTrace_1676242 : CollatzResearch.WordTrace tailWord_1676242 prefixEnd_1676242 382541261890638190740493 := by
  unfold tailWord_1676242
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284392098317247046711745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40758378928845992124564653 15284392098317247046711745)
  ·
    refine ⟨11463294073737935285033809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15284392098317247046711745 11463294073737935285033809)
    ·
      refine ⟨8597470555303451463775357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11463294073737935285033809 8597470555303451463775357)
      ·
        refine ⟨3224051458238794298915759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8597470555303451463775357 3224051458238794298915759)
        ·
          refine ⟨4836077187358191448373639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224051458238794298915759 4836077187358191448373639)
          ·
            refine ⟨7254115781037287172560459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836077187358191448373639 7254115781037287172560459)
            ·
              refine ⟨10881173671555930758840689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7254115781037287172560459 10881173671555930758840689)
              ·
                refine ⟨8160880253666948069130517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10881173671555930758840689 8160880253666948069130517)
                ·
                  refine ⟨382541261890638190740493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8160880253666948069130517 382541261890638190740493)
                  ·
                    rfl

theorem cell21_1676242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 6].length) (baseStart_1676242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676242 prefixEnd_1676242 := by exact prefixLift 1676242
  have htrace : WordTrace (prefixWord ++ tailWord_1676242) baseStart_1676242 baseEnd_1676242 := by
    simpa [prefixWord, tailWord_1676242, baseEnd_1676242] using wordTrace_append hprefix tailTrace_1676242
  have hstable : (prefixWord ++ tailWord_1676242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676242).length < 2 ^ (prefixWord ++ tailWord_1676242).sum := by decide
  have hdescent : baseEnd_1676242 < baseStart_1676242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676321 : List Nat := [1, 2, 3, 2, 3, 1, 4, 2, 3]
def baseStart_1676321 : Nat := 118140960795 + 1676321 * 2 ^ 59
def prefixEnd_1676321 : Nat := 4983230072969 + 3 ^ 40 * 1676321 * 2
def baseEnd_1676321 : Nat := 382559290766951608923665

theorem tailTrace_1676321 : CollatzResearch.WordTrace tailWord_1676321 prefixEnd_1676321 382559290766951608923665 := by
  unfold tailWord_1676321
  simp only [CollatzResearch.WordTrace]
  refine ⟨61140449759982784678972817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40760299839988523119315211 61140449759982784678972817)
  ·
    refine ⟨45855337319987088509229613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61140449759982784678972817 45855337319987088509229613)
    ·
      refine ⟨17195751494995158190961105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45855337319987088509229613 17195751494995158190961105)
      ·
        refine ⟨12896813621246368643220829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17195751494995158190961105 12896813621246368643220829)
        ·
          refine ⟨4836305107967388241207811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12896813621246368643220829 4836305107967388241207811)
          ·
            refine ⟨7254457661951082361811717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836305107967388241207811 7254457661951082361811717)
            ·
              refine ⟨1360210811615827942839697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7254457661951082361811717 1360210811615827942839697)
              ·
                refine ⟨1020158108711870957129773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1360210811615827942839697 1020158108711870957129773)
                ·
                  refine ⟨382559290766951608923665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020158108711870957129773 382559290766951608923665)
                  ·
                    rfl

theorem cell21_1676321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 2, 3].length) (baseStart_1676321 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676321 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676321 prefixEnd_1676321 := by exact prefixLift 1676321
  have htrace : WordTrace (prefixWord ++ tailWord_1676321) baseStart_1676321 baseEnd_1676321 := by
    simpa [prefixWord, tailWord_1676321, baseEnd_1676321] using wordTrace_append hprefix tailTrace_1676321
  have hstable : (prefixWord ++ tailWord_1676321).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676321).length < 2 ^ (prefixWord ++ tailWord_1676321).sum := by decide
  have hdescent : baseEnd_1676321 < baseStart_1676321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676346 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 7]
def baseStart_1676346 : Nat := 118140960795 + 1676346 * 2 ^ 59
def prefixEnd_1676346 : Nat := 4983230072969 + 3 ^ 40 * 1676346 * 2
def baseEnd_1676346 : Nat := 382564996107557121006947

theorem tailTrace_1676346 : CollatzResearch.WordTrace tailWord_1676346 prefixEnd_1676346 382564996107557121006947 := by
  unfold tailWord_1676346
  simp only [CollatzResearch.WordTrace]
  refine ⟨15285340396223053487158223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40760907723261475965755261 15285340396223053487158223)
  ·
    refine ⟨22928010594334580230737335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15285340396223053487158223 22928010594334580230737335)
    ·
      refine ⟨34392015891501870346106003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22928010594334580230737335 34392015891501870346106003)
      ·
        refine ⟨51588023837252805519159005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34392015891501870346106003 51588023837252805519159005)
        ·
          refine ⟨19345508938969802069684627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51588023837252805519159005 19345508938969802069684627)
          ·
            refine ⟨29018263408454703104526941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19345508938969802069684627 29018263408454703104526941)
            ·
              refine ⟨10881848778170513664197603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29018263408454703104526941 10881848778170513664197603)
              ·
                refine ⟨16322773167255770496296405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10881848778170513664197603 16322773167255770496296405)
                ·
                  refine ⟨382564996107557121006947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16322773167255770496296405 382564996107557121006947)
                  ·
                    rfl

theorem cell21_1676346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 7].length) (baseStart_1676346 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676346 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676346 prefixEnd_1676346 := by exact prefixLift 1676346
  have htrace : WordTrace (prefixWord ++ tailWord_1676346) baseStart_1676346 baseEnd_1676346 := by
    simpa [prefixWord, tailWord_1676346, baseEnd_1676346] using wordTrace_append hprefix tailTrace_1676346
  have hstable : (prefixWord ++ tailWord_1676346).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676346).length < 2 ^ (prefixWord ++ tailWord_1676346).sum := by decide
  have hdescent : baseEnd_1676346 < baseStart_1676346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676349 : List Nat := [1, 4, 1, 3, 1, 3, 3, 5]
def baseStart_1676349 : Nat := 118140960795 + 1676349 * 2 ^ 59
def prefixEnd_1676349 : Nat := 4983230072969 + 3 ^ 40 * 1676349 * 2
def baseEnd_1676349 : Nat := 127521893582809927485647

theorem tailTrace_1676349 : CollatzResearch.WordTrace tailWord_1676349 prefixEnd_1676349 127521893582809927485647 := by
  unfold tailWord_1676349
  simp only [CollatzResearch.WordTrace]
  refine ⟨61141471003881345460992101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40760980669254230307328067 61141471003881345460992101)
  ·
    refine ⟨11464025813227752273936019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61141471003881345460992101 11464025813227752273936019)
    ·
      refine ⟨17196038719841628410904029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11464025813227752273936019 17196038719841628410904029)
      ·
        refine ⟨6448514519940610654089011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17196038719841628410904029 6448514519940610654089011)
        ·
          refine ⟨9672771779910915981133517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448514519940610654089011 9672771779910915981133517)
          ·
            refine ⟨3627289417466593492925069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9672771779910915981133517 3627289417466593492925069)
            ·
              refine ⟨1360233531549972559846901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3627289417466593492925069 1360233531549972559846901)
              ·
                refine ⟨127521893582809927485647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1360233531549972559846901 127521893582809927485647)
                ·
                  rfl

theorem cell21_1676349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 3, 5].length) (baseStart_1676349 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676349 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676349 prefixEnd_1676349 := by exact prefixLift 1676349
  have htrace : WordTrace (prefixWord ++ tailWord_1676349) baseStart_1676349 baseEnd_1676349 := by
    simpa [prefixWord, tailWord_1676349, baseEnd_1676349] using wordTrace_append hprefix tailTrace_1676349
  have hstable : (prefixWord ++ tailWord_1676349).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676349).length < 2 ^ (prefixWord ++ tailWord_1676349).sum := by decide
  have hdescent : baseEnd_1676349 < baseStart_1676349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676377 : List Nat := [1, 2, 1, 2, 2, 1, 2, 6, 4]
def baseStart_1676377 : Nat := 118140960795 + 1676377 * 2 ^ 59
def prefixEnd_1676377 : Nat := 4983230072969 + 3 ^ 40 * 1676377 * 2
def baseEnd_1676377 : Nat := 382572070729907955990217

theorem tailTrace_1676377 : CollatzResearch.WordTrace tailWord_1676377 prefixEnd_1676377 382572070729907955990217 := by
  unfold tailWord_1676377
  simp only [CollatzResearch.WordTrace]
  refine ⟨61142492247779906243011385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40761661498519937495340923 61142492247779906243011385)
  ·
    refine ⟨45856869185834929682258539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61142492247779906243011385 45856869185834929682258539)
    ·
      refine ⟨68785303778752394523387809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45856869185834929682258539 68785303778752394523387809)
      ·
        refine ⟨51588977834064295892540857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68785303778752394523387809 51588977834064295892540857)
        ·
          refine ⟨38691733375548221919405643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51588977834064295892540857 38691733375548221919405643)
          ·
            refine ⟨58037600063322332879108465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38691733375548221919405643 58037600063322332879108465)
            ·
              refine ⟨43528200047491749659331349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58037600063322332879108465 43528200047491749659331349)
              ·
                refine ⟨2040384377226175765281157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43528200047491749659331349 2040384377226175765281157)
                ·
                  refine ⟨382572070729907955990217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2040384377226175765281157 382572070729907955990217)
                  ·
                    rfl

theorem cell21_1676377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_1676377 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676377 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676377 prefixEnd_1676377 := by exact prefixLift 1676377
  have htrace : WordTrace (prefixWord ++ tailWord_1676377) baseStart_1676377 baseEnd_1676377 := by
    simpa [prefixWord, tailWord_1676377, baseEnd_1676377] using wordTrace_append hprefix tailTrace_1676377
  have hstable : (prefixWord ++ tailWord_1676377).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676377).length < 2 ^ (prefixWord ++ tailWord_1676377).sum := by decide
  have hdescent : baseEnd_1676377 < baseStart_1676377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676380 : List Nat := [2, 2, 4, 1, 1, 1, 1, 6, 3]
def baseStart_1676380 : Nat := 118140960795 + 1676380 * 2 ^ 59
def prefixEnd_1676380 : Nat := 4983230072969 + 3 ^ 40 * 1676380 * 2
def baseEnd_1676380 : Nat := 382572755370780617440211

theorem tailTrace_1676380 : CollatzResearch.WordTrace tailWord_1676380 prefixEnd_1676380 382572755370780617440211 := by
  unfold tailWord_1676380
  simp only [CollatzResearch.WordTrace]
  refine ⟨30571300833384518877685297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40761734444512691836913729 30571300833384518877685297)
  ·
    refine ⟨22928475625038389158263973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30571300833384518877685297 22928475625038389158263973)
    ·
      refine ⟨4299089179694697967174495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22928475625038389158263973 4299089179694697967174495)
      ·
        refine ⟨6448633769542046950761743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299089179694697967174495 6448633769542046950761743)
        ·
          refine ⟨9672950654313070426142615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6448633769542046950761743 9672950654313070426142615)
          ·
            refine ⟨14509425981469605639213923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9672950654313070426142615 14509425981469605639213923)
            ·
              refine ⟨21764138972204408458820885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14509425981469605639213923 21764138972204408458820885)
              ·
                refine ⟨1020194014322081646507229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21764138972204408458820885 1020194014322081646507229)
                ·
                  refine ⟨382572755370780617440211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020194014322081646507229 382572755370780617440211)
                  ·
                    rfl

theorem cell21_1676380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 3].length) (baseStart_1676380 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676380 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676380 prefixEnd_1676380 := by exact prefixLift 1676380
  have htrace : WordTrace (prefixWord ++ tailWord_1676380) baseStart_1676380 baseEnd_1676380 := by
    simpa [prefixWord, tailWord_1676380, baseEnd_1676380] using wordTrace_append hprefix tailTrace_1676380
  have hstable : (prefixWord ++ tailWord_1676380).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676380).length < 2 ^ (prefixWord ++ tailWord_1676380).sum := by decide
  have hdescent : baseEnd_1676380 < baseStart_1676380 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676408 : List Nat := [2, 1, 2, 1, 1, 1, 8, 5]
def baseStart_1676408 : Nat := 118140960795 + 1676408 * 2 ^ 59
def prefixEnd_1676408 : Nat := 4983230072969 + 3 ^ 40 * 1676408 * 2
def baseEnd_1676408 : Nat := 127526381784086263657829

theorem tailTrace_1676408 : CollatzResearch.WordTrace tailWord_1676408 prefixEnd_1676408 127526381784086263657829 := by
  unfold tailWord_1676408
  simp only [CollatzResearch.WordTrace]
  refine ⟨30571811455333799268694939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40762415273778399024926585 30571811455333799268694939)
  ·
    refine ⟨45857717183000698903042409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30571811455333799268694939 45857717183000698903042409)
    ·
      refine ⟨34393287887250524177281807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45857717183000698903042409 34393287887250524177281807)
      ·
        refine ⟨51589931830875786265922711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34393287887250524177281807 51589931830875786265922711)
        ·
          refine ⟨77384897746313679398884067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51589931830875786265922711 77384897746313679398884067)
          ·
            refine ⟨116077346619470519098326101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77384897746313679398884067 116077346619470519098326101)
            ·
              refine ⟨1360281405696920145683509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 116077346619470519098326101 1360281405696920145683509)
              ·
                refine ⟨127526381784086263657829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1360281405696920145683509 127526381784086263657829)
                ·
                  rfl

theorem cell21_1676408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 5].length) (baseStart_1676408 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676408 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676408 prefixEnd_1676408 := by exact prefixLift 1676408
  have htrace : WordTrace (prefixWord ++ tailWord_1676408) baseStart_1676408 baseEnd_1676408 := by
    simpa [prefixWord, tailWord_1676408, baseEnd_1676408] using wordTrace_append hprefix tailTrace_1676408
  have hstable : (prefixWord ++ tailWord_1676408).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676408).length < 2 ^ (prefixWord ++ tailWord_1676408).sum := by decide
  have hdescent : baseEnd_1676408 < baseStart_1676408 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676439 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 5]
def baseStart_1676439 : Nat := 118140960795 + 1676439 * 2 ^ 59
def prefixEnd_1676439 : Nat := 4983230072969 + 3 ^ 40 * 1676439 * 2
def baseEnd_1676439 : Nat := 382586219974609625956757

theorem tailTrace_1676439 : CollatzResearch.WordTrace tailWord_1676439 prefixEnd_1676439 382586219974609625956757 := by
  unfold tailWord_1676439
  simp only [CollatzResearch.WordTrace]
  refine ⟨61144753573555290831768371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40763169049036860554512247 61144753573555290831768371)
  ·
    refine ⟨91717130360332936247652557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61144753573555290831768371 91717130360332936247652557)
    ·
      refine ⟨34393923885124851092869709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91717130360332936247652557 34393923885124851092869709)
      ·
        refine ⟨12897721456921819159826141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34393923885124851092869709 12897721456921819159826141)
        ·
          refine ⟨4836645546345682184934803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12897721456921819159826141 4836645546345682184934803)
          ·
            refine ⟨7254968319518523277402205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4836645546345682184934803 7254968319518523277402205)
            ·
              refine ⟨2720613119819446229025827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7254968319518523277402205 2720613119819446229025827)
              ·
                refine ⟨4080919679729169343538741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2720613119819446229025827 4080919679729169343538741)
                ·
                  refine ⟨382586219974609625956757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4080919679729169343538741 382586219974609625956757)
                  ·
                    rfl

theorem cell21_1676439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 5].length) (baseStart_1676439 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676439 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676439 prefixEnd_1676439 := by exact prefixLift 1676439
  have htrace : WordTrace (prefixWord ++ tailWord_1676439) baseStart_1676439 baseEnd_1676439 := by
    simpa [prefixWord, tailWord_1676439, baseEnd_1676439] using wordTrace_append hprefix tailTrace_1676439
  have hstable : (prefixWord ++ tailWord_1676439).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676439).length < 2 ^ (prefixWord ++ tailWord_1676439).sum := by decide
  have hdescent : baseEnd_1676439 < baseStart_1676439 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676467 : List Nat := [1, 1, 1, 2, 3, 2, 4, 7]
def baseStart_1676467 : Nat := 118140960795 + 1676467 * 2 ^ 59
def prefixEnd_1676467 : Nat := 4983230072969 + 3 ^ 40 * 1676467 * 2
def baseEnd_1676467 : Nat := 127530869985362599830011

theorem tailTrace_1676467 : CollatzResearch.WordTrace tailWord_1676467 prefixEnd_1676467 127530869985362599830011 := by
  unfold tailWord_1676467
  simp only [CollatzResearch.WordTrace]
  refine ⟨61145774817453851613787655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40763849878302567742525103 61145774817453851613787655)
  ·
    refine ⟨91718662226180777420681483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61145774817453851613787655 91718662226180777420681483)
    ·
      refine ⟨137577993339271166131022225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91718662226180777420681483 137577993339271166131022225)
      ·
        refine ⟨103183495004453374598266669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137577993339271166131022225 103183495004453374598266669)
        ·
          refine ⟨38693810626670015474350001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103183495004453374598266669 38693810626670015474350001)
          ·
            refine ⟨29020357970002511605762501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38693810626670015474350001 29020357970002511605762501)
            ·
              refine ⟨5441317119375470926080469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29020357970002511605762501 5441317119375470926080469)
              ·
                refine ⟨127530869985362599830011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5441317119375470926080469 127530869985362599830011)
                ·
                  rfl

theorem cell21_1676467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 7].length) (baseStart_1676467 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676467 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676467 prefixEnd_1676467 := by exact prefixLift 1676467
  have htrace : WordTrace (prefixWord ++ tailWord_1676467) baseStart_1676467 baseEnd_1676467 := by
    simpa [prefixWord, tailWord_1676467, baseEnd_1676467] using wordTrace_append hprefix tailTrace_1676467
  have hstable : (prefixWord ++ tailWord_1676467).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676467).length < 2 ^ (prefixWord ++ tailWord_1676467).sum := by decide
  have hdescent : baseEnd_1676467 < baseStart_1676467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676484 : List Nat := [2, 3, 3, 1, 3, 9]
def baseStart_1676484 : Nat := 118140960795 + 1676484 * 2 ^ 59
def prefixEnd_1676484 : Nat := 4983230072969 + 3 ^ 40 * 1676484 * 2
def baseEnd_1676484 : Nat := 14170240355099983248395

theorem tailTrace_1676484 : CollatzResearch.WordTrace tailWord_1676484 prefixEnd_1676484 14170240355099983248395 := by
  unfold tailWord_1676484
  simp only [CollatzResearch.WordTrace]
  refine ⟨30573197429196131758578253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40764263238928175678104337 30573197429196131758578253)
  ·
    refine ⟨11464949035948549409466845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30573197429196131758578253 11464949035948549409466845)
    ·
      refine ⟨4299355888480706028550067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11464949035948549409466845 4299355888480706028550067)
      ·
        refine ⟨6449033832721059042825101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4299355888480706028550067 6449033832721059042825101)
        ·
          refine ⟨2418387687270397141059413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6449033832721059042825101 2418387687270397141059413)
          ·
            refine ⟨14170240355099983248395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 2418387687270397141059413 14170240355099983248395)
            ·
              rfl

theorem cell21_1676484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 9].length) (baseStart_1676484 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676484 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676484 prefixEnd_1676484 := by exact prefixLift 1676484
  have htrace : WordTrace (prefixWord ++ tailWord_1676484) baseStart_1676484 baseEnd_1676484 := by
    simpa [prefixWord, tailWord_1676484, baseEnd_1676484] using wordTrace_append hprefix tailTrace_1676484
  have hstable : (prefixWord ++ tailWord_1676484).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676484).length < 2 ^ (prefixWord ++ tailWord_1676484).sum := by decide
  have hdescent : baseEnd_1676484 < baseStart_1676484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676501 : List Nat := [1, 3, 2, 4, 1, 3, 1, 6]
def baseStart_1676501 : Nat := 118140960795 + 1676501 * 2 ^ 59
def prefixEnd_1676501 : Nat := 4983230072969 + 3 ^ 40 * 1676501 * 2
def baseEnd_1676501 : Nat := 127533456406437098641099

theorem tailTrace_1676501 : CollatzResearch.WordTrace tailWord_1676501 prefixEnd_1676501 127533456406437098641099 := by
  unfold tailWord_1676501
  simp only [CollatzResearch.WordTrace]
  refine ⟨61147014899330675420525357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40764676599553783613683571 61147014899330675420525357)
  ·
    refine ⟨22930130587249003282697009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61147014899330675420525357 22930130587249003282697009)
    ·
      refine ⟨17197597940436752462022757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22930130587249003282697009 17197597940436752462022757)
      ·
        refine ⟨3224549613831891086629267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17197597940436752462022757 3224549613831891086629267)
        ·
          refine ⟨4836824420747836629943901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3224549613831891086629267 4836824420747836629943901)
          ·
            refine ⟨1813809157780438736228963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4836824420747836629943901 1813809157780438736228963)
            ·
              refine ⟨2720713736670658104343445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1813809157780438736228963 2720713736670658104343445)
              ·
                refine ⟨127533456406437098641099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2720713736670658104343445 127533456406437098641099)
                ·
                  rfl

theorem cell21_1676501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 6].length) (baseStart_1676501 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676501 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676501 prefixEnd_1676501 := by exact prefixLift 1676501
  have htrace : WordTrace (prefixWord ++ tailWord_1676501) baseStart_1676501 baseEnd_1676501 := by
    simpa [prefixWord, tailWord_1676501, baseEnd_1676501] using wordTrace_append hprefix tailTrace_1676501
  have hstable : (prefixWord ++ tailWord_1676501).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676501).length < 2 ^ (prefixWord ++ tailWord_1676501).sum := by decide
  have hdescent : baseEnd_1676501 < baseStart_1676501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676543 : List Nat := [1, 1, 2, 2, 1, 6, 8]
def baseStart_1676543 : Nat := 118140960795 + 1676543 * 2 ^ 59
def prefixEnd_1676543 : Nat := 4983230072969 + 3 ^ 40 * 1676543 * 2
def baseEnd_1676543 : Nat := 42512217132392061802579

theorem tailTrace_1676543 : CollatzResearch.WordTrace tailWord_1676543 prefixEnd_1676543 42512217132392061802579 := by
  unfold tailWord_1676543
  simp only [CollatzResearch.WordTrace]
  refine ⟨61148546765178516593554283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40765697843452344395702855 61148546765178516593554283)
  ·
    refine ⟨91722820147767774890331425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61148546765178516593554283 91722820147767774890331425)
    ·
      refine ⟨68792115110825831167748569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91722820147767774890331425 68792115110825831167748569)
      ·
        refine ⟨51594086333119373375811427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68792115110825831167748569 51594086333119373375811427)
        ·
          refine ⟨77391129499679060063717141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51594086333119373375811427 77391129499679060063717141)
          ·
            refine ⟨3627709195297455940486741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77391129499679060063717141 3627709195297455940486741)
            ·
              refine ⟨42512217132392061802579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 3627709195297455940486741 42512217132392061802579)
              ·
                rfl

theorem cell21_1676543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 6, 8].length) (baseStart_1676543 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676543 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676543 prefixEnd_1676543 := by exact prefixLift 1676543
  have htrace : WordTrace (prefixWord ++ tailWord_1676543) baseStart_1676543 baseEnd_1676543 := by
    simpa [prefixWord, tailWord_1676543, baseEnd_1676543] using wordTrace_append hprefix tailTrace_1676543
  have hstable : (prefixWord ++ tailWord_1676543).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676543).length < 2 ^ (prefixWord ++ tailWord_1676543).sum := by decide
  have hdescent : baseEnd_1676543 < baseStart_1676543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676608 : List Nat := [2, 1, 1, 2, 2, 1, 7, 2, 3]
def baseStart_1676608 : Nat := 118140960795 + 1676608 * 2 ^ 59
def prefixEnd_1676608 : Nat := 4983230072969 + 3 ^ 40 * 1676608 * 2
def baseEnd_1676608 : Nat := 382624788077102887639745

theorem tailTrace_1676608 : CollatzResearch.WordTrace tailWord_1676608 prefixEnd_1676608 382624788077102887639745 := by
  unfold tailWord_1676608
  simp only [CollatzResearch.WordTrace]
  refine ⟨30575458754971516347335239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40767278339962021796446985 30575458754971516347335239)
  ·
    refine ⟨45863188132457274521002859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30575458754971516347335239 45863188132457274521002859)
    ·
      refine ⟨68794782198685911781504289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45863188132457274521002859 68794782198685911781504289)
      ·
        refine ⟨51596086649014433836128217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68794782198685911781504289 51596086649014433836128217)
        ·
          refine ⟨38697064986760825377096163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51596086649014433836128217 38697064986760825377096163)
          ·
            refine ⟨58045597480141238065644245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38697064986760825377096163 58045597480141238065644245)
            ·
              refine ⟨1360443690940810267163537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58045597480141238065644245 1360443690940810267163537)
              ·
                refine ⟨1020332768205607700372653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1360443690940810267163537 1020332768205607700372653)
                ·
                  refine ⟨382624788077102887639745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020332768205607700372653 382624788077102887639745)
                  ·
                    rfl

theorem cell21_1676608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 2, 3].length) (baseStart_1676608 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676608 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676608 prefixEnd_1676608 := by exact prefixLift 1676608
  have htrace : WordTrace (prefixWord ++ tailWord_1676608) baseStart_1676608 baseEnd_1676608 := by
    simpa [prefixWord, tailWord_1676608, baseEnd_1676608] using wordTrace_append hprefix tailTrace_1676608
  have hstable : (prefixWord ++ tailWord_1676608).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676608).length < 2 ^ (prefixWord ++ tailWord_1676608).sum := by decide
  have hdescent : baseEnd_1676608 < baseStart_1676608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676614 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 4]
def baseStart_1676614 : Nat := 118140960795 + 1676614 * 2 ^ 59
def prefixEnd_1676614 : Nat := 4983230072969 + 3 ^ 40 * 1676614 * 2
def baseEnd_1676614 : Nat := 382626157358848210539733

theorem tailTrace_1676614 : CollatzResearch.WordTrace tailWord_1676614 prefixEnd_1676614 382626157358848210539733 := by
  unfold tailWord_1676614
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910973010872540491230903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40767424231947530479592597 1910973010872540491230903)
  ·
    refine ⟨2866459516308810736846355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1910973010872540491230903 2866459516308810736846355)
    ·
      refine ⟨4299689274463216105269533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2866459516308810736846355 4299689274463216105269533)
      ·
        refine ⟨1612383477923706039476075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4299689274463216105269533 1612383477923706039476075)
        ·
          refine ⟨2418575216885559059214113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612383477923706039476075 2418575216885559059214113)
          ·
            refine ⟨1813931412664169294410585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2418575216885559059214113 1813931412664169294410585)
            ·
              refine ⟨1360448559498126970807939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1813931412664169294410585 1360448559498126970807939)
              ·
                refine ⟨2040672839247190456211909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1360448559498126970807939 2040672839247190456211909)
                ·
                  refine ⟨382626157358848210539733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2040672839247190456211909 382626157358848210539733)
                  ·
                    rfl

theorem cell21_1676614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 4].length) (baseStart_1676614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676614 prefixEnd_1676614 := by exact prefixLift 1676614
  have htrace : WordTrace (prefixWord ++ tailWord_1676614) baseStart_1676614 baseEnd_1676614 := by
    simpa [prefixWord, tailWord_1676614, baseEnd_1676614] using wordTrace_append hprefix tailTrace_1676614
  have hstable : (prefixWord ++ tailWord_1676614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676614).length < 2 ^ (prefixWord ++ tailWord_1676614).sum := by decide
  have hdescent : baseEnd_1676614 < baseStart_1676614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676667 : List Nat := [1, 1, 1, 1, 1, 6, 3, 4, 3]
def baseStart_1676667 : Nat := 118140960795 + 1676667 * 2 ^ 59
def prefixEnd_1676667 : Nat := 4983230072969 + 3 ^ 40 * 1676667 * 2
def baseEnd_1676667 : Nat := 382638252680931896156291

theorem tailTrace_1676667 : CollatzResearch.WordTrace tailWord_1676667 prefixEnd_1676667 382638252680931896156291 := by
  unfold tailWord_1676667
  simp only [CollatzResearch.WordTrace]
  refine ⟨61153069416729285771068255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40768712944486190514045503 61153069416729285771068255)
  ·
    refine ⟨91729604125093928656602383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61153069416729285771068255 91729604125093928656602383)
    ·
      refine ⟨137594406187640892984903575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91729604125093928656602383 137594406187640892984903575)
      ·
        refine ⟨206391609281461339477355363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137594406187640892984903575 206391609281461339477355363)
        ·
          refine ⟨309587413922192009216033045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206391609281461339477355363 309587413922192009216033045)
          ·
            refine ⟨14511910027602750432001549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 309587413922192009216033045 14511910027602750432001549)
            ·
              refine ⟨5441966260351031412000581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14511910027602750432001549 5441966260351031412000581)
              ·
                refine ⟨1020368673815818389750109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5441966260351031412000581 1020368673815818389750109)
                ·
                  refine ⟨382638252680931896156291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020368673815818389750109 382638252680931896156291)
                  ·
                    rfl

theorem cell21_1676667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 3].length) (baseStart_1676667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676667 prefixEnd_1676667 := by exact prefixLift 1676667
  have htrace : WordTrace (prefixWord ++ tailWord_1676667) baseStart_1676667 baseEnd_1676667 := by
    simpa [prefixWord, tailWord_1676667, baseEnd_1676667] using wordTrace_append hprefix tailTrace_1676667
  have hstable : (prefixWord ++ tailWord_1676667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676667).length < 2 ^ (prefixWord ++ tailWord_1676667).sum := by decide
  have hdescent : baseEnd_1676667 < baseStart_1676667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676771 : List Nat := [1, 1, 1, 6, 2, 1, 9]
def baseStart_1676771 : Nat := 118140960795 + 1676771 * 2 ^ 59
def prefixEnd_1676771 : Nat := 4983230072969 + 3 ^ 40 * 1676771 * 2
def baseEnd_1676771 : Nat := 42517998544205647380305

theorem tailTrace_1676771 : CollatzResearch.WordTrace tailWord_1676771 prefixEnd_1676771 42517998544205647380305 := by
  unfold tailWord_1676771
  simp only [CollatzResearch.WordTrace]
  refine ⟨61156862608352511532854167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40771241738901674355236111 61156862608352511532854167)
  ·
    refine ⟨91735293912528767299281251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61156862608352511532854167 91735293912528767299281251)
    ·
      refine ⟨137602940868793150948921877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91735293912528767299281251 137602940868793150948921877)
      ·
        refine ⟨6450137853224678950730713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 137602940868793150948921877 6450137853224678950730713)
        ·
          refine ⟨4837603389918509213048035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6450137853224678950730713 4837603389918509213048035)
          ·
            refine ⟨7256405084877763819572053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4837603389918509213048035 7256405084877763819572053)
            ·
              refine ⟨42517998544205647380305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7256405084877763819572053 42517998544205647380305)
              ·
                rfl

theorem cell21_1676771_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 9].length) (baseStart_1676771 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676771 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676771 prefixEnd_1676771 := by exact prefixLift 1676771
  have htrace : WordTrace (prefixWord ++ tailWord_1676771) baseStart_1676771 baseEnd_1676771 := by
    simpa [prefixWord, tailWord_1676771, baseEnd_1676771] using wordTrace_append hprefix tailTrace_1676771
  have hstable : (prefixWord ++ tailWord_1676771).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676771).length < 2 ^ (prefixWord ++ tailWord_1676771).sum := by decide
  have hdescent : baseEnd_1676771 < baseStart_1676771 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676771) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676833 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 4]
def baseStart_1676833 : Nat := 118140960795 + 1676833 * 2 ^ 59
def prefixEnd_1676833 : Nat := 4983230072969 + 3 ^ 40 * 1676833 * 2
def baseEnd_1676833 : Nat := 382676136142552496389285

theorem tailTrace_1676833 : CollatzResearch.WordTrace tailWord_1676833 prefixEnd_1676833 382676136142552496389285 := by
  unfold tailWord_1676833
  simp only [CollatzResearch.WordTrace]
  refine ⟨61159123934127896121611153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40772749289418597414407435 61159123934127896121611153)
  ·
    refine ⟨45869342950595922091208365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61159123934127896121611153 45869342950595922091208365)
    ·
      refine ⟨17201003606473470784203137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45869342950595922091208365 17201003606473470784203137)
      ·
        refine ⟨12900752704855103088152353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17201003606473470784203137 12900752704855103088152353)
        ·
          refine ⟨9675564528641327316114265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12900752704855103088152353 9675564528641327316114265)
          ·
            refine ⟨7256673396480995487085699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9675564528641327316114265 7256673396480995487085699)
            ·
              refine ⟨10885010094721493230628549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7256673396480995487085699 10885010094721493230628549)
              ·
                refine ⟨2040939392760279980742853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10885010094721493230628549 2040939392760279980742853)
                ·
                  refine ⟨382676136142552496389285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2040939392760279980742853 382676136142552496389285)
                  ·
                    rfl

theorem cell21_1676833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 4].length) (baseStart_1676833 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676833 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676833 prefixEnd_1676833 := by exact prefixLift 1676833
  have htrace : WordTrace (prefixWord ++ tailWord_1676833) baseStart_1676833 baseEnd_1676833 := by
    simpa [prefixWord, tailWord_1676833, baseEnd_1676833] using wordTrace_append hprefix tailTrace_1676833
  have hstable : (prefixWord ++ tailWord_1676833).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676833).length < 2 ^ (prefixWord ++ tailWord_1676833).sum := by decide
  have hdescent : baseEnd_1676833 < baseStart_1676833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676870 : List Nat := [6, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1676870 : Nat := 118140960795 + 1676870 * 2 ^ 59
def prefixEnd_1676870 : Nat := 4983230072969 + 3 ^ 40 * 1676870 * 2
def baseEnd_1676870 : Nat := 382684580046648654272543

theorem tailTrace_1676870 : CollatzResearch.WordTrace tailWord_1676870 prefixEnd_1676870 382684580046648654272543 := by
  unfold tailWord_1676870
  simp only [CollatzResearch.WordTrace]
  refine ⟨1911264794843557857522127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 40773648956662567627138709 1911264794843557857522127)
  ·
    refine ⟨2866897192265336786283191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1911264794843557857522127 2866897192265336786283191)
    ·
      refine ⟨4300345788398005179424787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2866897192265336786283191 4300345788398005179424787)
      ·
        refine ⟨6450518682597007769137181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4300345788398005179424787 6450518682597007769137181)
        ·
          refine ⟨2418944505973877913426443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6450518682597007769137181 2418944505973877913426443)
          ·
            refine ⟨3628416758960816870139665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2418944505973877913426443 3628416758960816870139665)
            ·
              refine ⟨2721312569220612652604749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628416758960816870139665 2721312569220612652604749)
              ·
                refine ⟨1020492213457729744726781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2721312569220612652604749 1020492213457729744726781)
                ·
                  refine ⟨382684580046648654272543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020492213457729744726781 382684580046648654272543)
                  ·
                    rfl

theorem cell21_1676870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1676870 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676870 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676870 prefixEnd_1676870 := by exact prefixLift 1676870
  have htrace : WordTrace (prefixWord ++ tailWord_1676870) baseStart_1676870 baseEnd_1676870 := by
    simpa [prefixWord, tailWord_1676870, baseEnd_1676870] using wordTrace_append hprefix tailTrace_1676870
  have hstable : (prefixWord ++ tailWord_1676870).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676870).length < 2 ^ (prefixWord ++ tailWord_1676870).sum := by decide
  have hdescent : baseEnd_1676870 < baseStart_1676870 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1676937 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 7]
def baseStart_1676937 : Nat := 118140960795 + 1676937 * 2 ^ 59
def prefixEnd_1676937 : Nat := 4983230072969 + 3 ^ 40 * 1676937 * 2
def baseEnd_1676937 : Nat := 382699870359471426655739

theorem tailTrace_1676937 : CollatzResearch.WordTrace tailWord_1676937 prefixEnd_1676937 382699870359471426655739 := by
  unfold tailWord_1676937
  simp only [CollatzResearch.WordTrace]
  refine ⟨61162917125751121883397065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40775278083834081255598043 61162917125751121883397065)
  ·
    refine ⟨45872187844313341412547799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61162917125751121883397065 45872187844313341412547799)
    ·
      refine ⟨68808281766470012118821699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45872187844313341412547799 68808281766470012118821699)
      ·
        refine ⟨103212422649705018178232549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68808281766470012118821699 103212422649705018178232549)
        ·
          refine ⟨19352329246819690908418603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103212422649705018178232549 19352329246819690908418603)
          ·
            refine ⟨29028493870229536362627905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19352329246819690908418603 29028493870229536362627905)
            ·
              refine ⟨21771370402672152271970929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29028493870229536362627905 21771370402672152271970929)
              ·
                refine ⟨16328527802004114203978197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21771370402672152271970929 16328527802004114203978197)
                ·
                  refine ⟨382699870359471426655739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16328527802004114203978197 382699870359471426655739)
                  ·
                    rfl

theorem cell21_1676937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_1676937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1676937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1676937 prefixEnd_1676937 := by exact prefixLift 1676937
  have htrace : WordTrace (prefixWord ++ tailWord_1676937) baseStart_1676937 baseEnd_1676937 := by
    simpa [prefixWord, tailWord_1676937, baseEnd_1676937] using wordTrace_append hprefix tailTrace_1676937
  have hstable : (prefixWord ++ tailWord_1676937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1676937).length < 2 ^ (prefixWord ++ tailWord_1676937).sum := by decide
  have hdescent : baseEnd_1676937 < baseStart_1676937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1676937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677002 : List Nat := [3, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1677002 : Nat := 118140960795 + 1677002 * 2 ^ 59
def prefixEnd_1677002 : Nat := 4983230072969 + 3 ^ 40 * 1677002 * 2
def baseEnd_1677002 : Nat := 382714704245045758072273

theorem tailTrace_1677002 : CollatzResearch.WordTrace tailWord_1677002 prefixEnd_1677002 382714704245045758072273 := by
  unfold tailWord_1677002
  simp only [CollatzResearch.WordTrace]
  refine ⟨15291321967628909496128315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40776858580343758656342173 15291321967628909496128315)
  ·
    refine ⟨22936982951443364244192473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15291321967628909496128315 22936982951443364244192473)
    ·
      refine ⟨17202737213582523183144355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22936982951443364244192473 17202737213582523183144355)
      ·
        refine ⟨25804105820373784774716533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17202737213582523183144355 25804105820373784774716533)
        ·
          refine ⟨2419134920660042322629675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25804105820373784774716533 2419134920660042322629675)
          ·
            refine ⟨3628702380990063483944513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2419134920660042322629675 3628702380990063483944513)
            ·
              refine ⟨2721526785742547612958385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3628702380990063483944513 2721526785742547612958385)
              ·
                refine ⟨2041145089306910709718789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2721526785742547612958385 2041145089306910709718789)
                ·
                  refine ⟨382714704245045758072273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041145089306910709718789 382714704245045758072273)
                  ·
                    rfl

theorem cell21_1677002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1677002 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677002 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677002 prefixEnd_1677002 := by exact prefixLift 1677002
  have htrace : WordTrace (prefixWord ++ tailWord_1677002) baseStart_1677002 baseEnd_1677002 := by
    simpa [prefixWord, tailWord_1677002, baseEnd_1677002] using wordTrace_append hprefix tailTrace_1677002
  have hstable : (prefixWord ++ tailWord_1677002).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677002).length < 2 ^ (prefixWord ++ tailWord_1677002).sum := by decide
  have hdescent : baseEnd_1677002 < baseStart_1677002 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677005 : List Nat := [1, 6, 2, 1, 1, 2, 1, 4, 3]
def baseStart_1677005 : Nat := 118140960795 + 1677005 * 2 ^ 59
def prefixEnd_1677005 : Nat := 4983230072969 + 3 ^ 40 * 1677005 * 2
def baseEnd_1677005 : Nat := 382715388885918419522267

theorem tailTrace_1677005 : CollatzResearch.WordTrace tailWord_1677005 prefixEnd_1677005 382715388885918419522267 := by
  unfold tailWord_1677005
  simp only [CollatzResearch.WordTrace]
  refine ⟨61165397289504769496872469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40776931526336512997914979 61165397289504769496872469)
  ·
    refine ⟨2867127997945536070165897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61165397289504769496872469 2867127997945536070165897)
    ·
      refine ⟨2150345998459152052624423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2867127997945536070165897 2150345998459152052624423)
      ·
        refine ⟨3225518997688728078936635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2150345998459152052624423 3225518997688728078936635)
        ·
          refine ⟨4838278496533092118404953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3225518997688728078936635 4838278496533092118404953)
          ·
            refine ⟨3628708872399819088803715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4838278496533092118404953 3628708872399819088803715)
            ·
              refine ⟨5443063308599728633205573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3628708872399819088803715 5443063308599728633205573)
              ·
                refine ⟨1020574370362449118726045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5443063308599728633205573 1020574370362449118726045)
                ·
                  refine ⟨382715388885918419522267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020574370362449118726045 382715388885918419522267)
                  ·
                    rfl

theorem cell21_1677005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 3].length) (baseStart_1677005 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677005 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677005 prefixEnd_1677005 := by exact prefixLift 1677005
  have htrace : WordTrace (prefixWord ++ tailWord_1677005) baseStart_1677005 baseEnd_1677005 := by
    simpa [prefixWord, tailWord_1677005, baseEnd_1677005] using wordTrace_append hprefix tailTrace_1677005
  have hstable : (prefixWord ++ tailWord_1677005).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677005).length < 2 ^ (prefixWord ++ tailWord_1677005).sum := by decide
  have hdescent : baseEnd_1677005 < baseStart_1677005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677092 : List Nat := [2, 3, 1, 3, 2, 1, 4, 5]
def baseStart_1677092 : Nat := 118140960795 + 1677092 * 2 ^ 59
def prefixEnd_1677092 : Nat := 4983230072969 + 3 ^ 40 * 1677092 * 2
def baseEnd_1677092 : Nat := 127578414490408533857363

theorem tailTrace_1677092 : CollatzResearch.WordTrace tailWord_1677092 prefixEnd_1677092 127578414490408533857363 := by
  unfold tailWord_1677092
  simp only [CollatzResearch.WordTrace]
  refine ⟨30584285220094791677644765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40779046960126388903526353 30584285220094791677644765)
  ·
    refine ⟨11469106957535546879116787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30584285220094791677644765 11469106957535546879116787)
    ·
      refine ⟨17203660436303320318675181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11469106957535546879116787 17203660436303320318675181)
      ·
        refine ⟨6451372663613745119503193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17203660436303320318675181 6451372663613745119503193)
        ·
          refine ⟨4838529497710308839627395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6451372663613745119503193 4838529497710308839627395)
          ·
            refine ⟨7257794246565463259441093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4838529497710308839627395 7257794246565463259441093)
            ·
              refine ⟨1360836421231024361145205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7257794246565463259441093 1360836421231024361145205)
              ·
                refine ⟨127578414490408533857363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1360836421231024361145205 127578414490408533857363)
                ·
                  rfl

theorem cell21_1677092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 5].length) (baseStart_1677092 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677092 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677092 prefixEnd_1677092 := by exact prefixLift 1677092
  have htrace : WordTrace (prefixWord ++ tailWord_1677092) baseStart_1677092 baseEnd_1677092 := by
    simpa [prefixWord, tailWord_1677092, baseEnd_1677092] using wordTrace_append hprefix tailTrace_1677092
  have hstable : (prefixWord ++ tailWord_1677092).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677092).length < 2 ^ (prefixWord ++ tailWord_1677092).sum := by decide
  have hdescent : baseEnd_1677092 < baseStart_1677092 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677137 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 4]
def baseStart_1677137 : Nat := 118140960795 + 1677137 * 2 ^ 59
def prefixEnd_1677137 : Nat := 4983230072969 + 3 ^ 40 * 1677137 * 2
def baseEnd_1677137 : Nat := 382745513084315523321997

theorem tailTrace_1677137 : CollatzResearch.WordTrace tailWord_1677137 prefixEnd_1677137 382745513084315523321997 := by
  unfold tailWord_1677137
  simp only [CollatzResearch.WordTrace]
  refine ⟨61170211725026556040677665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40780141150017704027118443 61170211725026556040677665)
  ·
    refine ⟨45877658793769917030508249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61170211725026556040677665 45877658793769917030508249)
    ·
      refine ⟨34408244095327437772881187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45877658793769917030508249 34408244095327437772881187)
      ·
        refine ⟨51612366142991156659321781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34408244095327437772881187 51612366142991156659321781)
        ·
          refine ⟨4838659325905420936811417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51612366142991156659321781 4838659325905420936811417)
          ·
            refine ⟨3628994494429065702608563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4838659325905420936811417 3628994494429065702608563)
            ·
              refine ⟨5443491741643598553912845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3628994494429065702608563 5443491741643598553912845)
              ·
                refine ⟨2041309403116349457717317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5443491741643598553912845 2041309403116349457717317)
                ·
                  refine ⟨382745513084315523321997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2041309403116349457717317 382745513084315523321997)
                  ·
                    rfl

theorem cell21_1677137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 4].length) (baseStart_1677137 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677137 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677137 prefixEnd_1677137 := by exact prefixLift 1677137
  have htrace : WordTrace (prefixWord ++ tailWord_1677137) baseStart_1677137 baseEnd_1677137 := by
    simpa [prefixWord, tailWord_1677137, baseEnd_1677137] using wordTrace_append hprefix tailTrace_1677137
  have hstable : (prefixWord ++ tailWord_1677137).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677137).length < 2 ^ (prefixWord ++ tailWord_1677137).sum := by decide
  have hdescent : baseEnd_1677137 < baseStart_1677137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677174 : List Nat := [5, 1, 1, 3, 2, 2, 2, 2, 3]
def baseStart_1677174 : Nat := 118140960795 + 1677174 * 2 ^ 59
def prefixEnd_1677174 : Nat := 4983230072969 + 3 ^ 40 * 1677174 * 2
def baseEnd_1677174 : Nat := 382753956988411681205255

theorem tailTrace_1677174 : CollatzResearch.WordTrace tailWord_1677174 prefixEnd_1677174 382753956988411681205255 := by
  unfold tailWord_1677174
  simp only [CollatzResearch.WordTrace]
  refine ⟨3823222576618281959985911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40781040817261674239849717 3823222576618281959985911)
  ·
    refine ⟨5734833864927422939978867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3823222576618281959985911 5734833864927422939978867)
    ·
      refine ⟨8602250797391134409968301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5734833864927422939978867 8602250797391134409968301)
      ·
        refine ⟨3225844049021675403738113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8602250797391134409968301 3225844049021675403738113)
        ·
          refine ⟨2419383036766256552803585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3225844049021675403738113 2419383036766256552803585)
          ·
            refine ⟨1814537277574692414602689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419383036766256552803585 1814537277574692414602689)
            ·
              refine ⟨1360902958181019310952017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1814537277574692414602689 1360902958181019310952017)
              ·
                refine ⟨1020677218635764483214013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1360902958181019310952017 1020677218635764483214013)
                ·
                  refine ⟨382753956988411681205255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020677218635764483214013 382753956988411681205255)
                  ·
                    rfl

theorem cell21_1677174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 3].length) (baseStart_1677174 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677174 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677174 prefixEnd_1677174 := by exact prefixLift 1677174
  have htrace : WordTrace (prefixWord ++ tailWord_1677174) baseStart_1677174 baseEnd_1677174 := by
    simpa [prefixWord, tailWord_1677174, baseEnd_1677174] using wordTrace_append hprefix tailTrace_1677174
  have hstable : (prefixWord ++ tailWord_1677174).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677174).length < 2 ^ (prefixWord ++ tailWord_1677174).sum := by decide
  have hdescent : baseEnd_1677174 < baseStart_1677174 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677185 : List Nat := [1, 2, 4, 4, 1, 2, 1, 6]
def baseStart_1677185 : Nat := 118140960795 + 1677185 * 2 ^ 59
def prefixEnd_1677185 : Nat := 4983230072969 + 3 ^ 40 * 1677185 * 2
def baseEnd_1677185 : Nat := 127585489112759368840633

theorem tailTrace_1677185 : CollatzResearch.WordTrace tailWord_1677185 prefixEnd_1677185 127585489112759368840633 := by
  unfold tailWord_1677185
  simp only [CollatzResearch.WordTrace]
  refine ⟨61171962428852660238425009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40781308285901773492283339 61171962428852660238425009)
  ·
    refine ⟨45878971821639495178818757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61171962428852660238425009 45878971821639495178818757)
    ·
      refine ⟨8602307216557405346028517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45878971821639495178818757 8602307216557405346028517)
      ·
        refine ⟨1612932603104513502380347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8602307216557405346028517 1612932603104513502380347)
        ·
          refine ⟨2419398904656770253570521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1612932603104513502380347 2419398904656770253570521)
          ·
            refine ⟨1814549178492577690177891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2419398904656770253570521 1814549178492577690177891)
            ·
              refine ⟨2721823767738866535266837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1814549178492577690177891 2721823767738866535266837)
              ·
                refine ⟨127585489112759368840633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2721823767738866535266837 127585489112759368840633)
                ·
                  rfl

theorem cell21_1677185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 6].length) (baseStart_1677185 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677185 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677185 prefixEnd_1677185 := by exact prefixLift 1677185
  have htrace : WordTrace (prefixWord ++ tailWord_1677185) baseStart_1677185 baseEnd_1677185 := by
    simpa [prefixWord, tailWord_1677185, baseEnd_1677185] using wordTrace_append hprefix tailTrace_1677185
  have hstable : (prefixWord ++ tailWord_1677185).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677185).length < 2 ^ (prefixWord ++ tailWord_1677185).sum := by decide
  have hdescent : baseEnd_1677185 < baseStart_1677185 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677331 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 8]
def baseStart_1677331 : Nat := 118140960795 + 1677331 * 2 ^ 59
def prefixEnd_1677331 : Nat := 4983230072969 + 3 ^ 40 * 1677331 * 2
def baseEnd_1677331 : Nat := 382789786527414297088267

theorem tailTrace_1677331 : CollatzResearch.WordTrace tailWord_1677331 prefixEnd_1677331 382789786527414297088267 := by
  unfold tailWord_1677331
  simp only [CollatzResearch.WordTrace]
  refine ⟨61177287486323727173239847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40784858324215818115493231 61177287486323727173239847)
  ·
    refine ⟨91765931229485590759859771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61177287486323727173239847 91765931229485590759859771)
    ·
      refine ⟨137648896844228386139789657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91765931229485590759859771 137648896844228386139789657)
      ·
        refine ⟨103236672633171289604842243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137648896844228386139789657 103236672633171289604842243)
        ·
          refine ⟨154855008949756934407263365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103236672633171289604842243 154855008949756934407263365)
          ·
            refine ⟨29035314178079425201361881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154855008949756934407263365 29035314178079425201361881)
            ·
              refine ⟨21776485633559568901021411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29035314178079425201361881 21776485633559568901021411)
              ·
                refine ⟨32664728450339353351532117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21776485633559568901021411 32664728450339353351532117)
                ·
                  refine ⟨382789786527414297088267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32664728450339353351532117 382789786527414297088267)
                  ·
                    rfl

theorem cell21_1677331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_1677331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677331 prefixEnd_1677331 := by exact prefixLift 1677331
  have htrace : WordTrace (prefixWord ++ tailWord_1677331) baseStart_1677331 baseEnd_1677331 := by
    simpa [prefixWord, tailWord_1677331, baseEnd_1677331] using wordTrace_append hprefix tailTrace_1677331
  have hstable : (prefixWord ++ tailWord_1677331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677331).length < 2 ^ (prefixWord ++ tailWord_1677331).sum := by decide
  have hdescent : baseEnd_1677331 < baseStart_1677331 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677562 : List Nat := [3, 1, 1, 1, 1, 5, 1, 5, 3]
def baseStart_1677562 : Nat := 118140960795 + 1677562 * 2 ^ 59
def prefixEnd_1677562 : Nat := 4983230072969 + 3 ^ 40 * 1677562 * 2
def baseEnd_1677562 : Nat := 382842503874609228737795

theorem tailTrace_1677562 : CollatzResearch.WordTrace tailWord_1677562 prefixEnd_1677562 382842503874609228737795 := by
  unfold tailWord_1677562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296428187121713406224735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40790475165657902416599293 15296428187121713406224735)
  ·
    refine ⟨22944642280682570109337103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15296428187121713406224735 22944642280682570109337103)
    ·
      refine ⟨34416963421023855164005655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22944642280682570109337103 34416963421023855164005655)
      ·
        refine ⟨51625445131535782746008483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34416963421023855164005655 51625445131535782746008483)
        ·
          refine ⟨77438167697303674119012725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51625445131535782746008483 77438167697303674119012725)
          ·
            refine ⟨7259828221622219448657443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77438167697303674119012725 7259828221622219448657443)
            ·
              refine ⟨10889742332433329172986165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7259828221622219448657443 10889742332433329172986165)
              ·
                refine ⟨1020913343665624609967453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10889742332433329172986165 1020913343665624609967453)
                ·
                  refine ⟨382842503874609228737795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020913343665624609967453 382842503874609228737795)
                  ·
                    rfl

theorem cell21_1677562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 3].length) (baseStart_1677562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677562 prefixEnd_1677562 := by exact prefixLift 1677562
  have htrace : WordTrace (prefixWord ++ tailWord_1677562) baseStart_1677562 baseEnd_1677562 := by
    simpa [prefixWord, tailWord_1677562, baseEnd_1677562] using wordTrace_append hprefix tailTrace_1677562
  have hstable : (prefixWord ++ tailWord_1677562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677562).length < 2 ^ (prefixWord ++ tailWord_1677562).sum := by decide
  have hdescent : baseEnd_1677562 < baseStart_1677562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677576 : List Nat := [2, 1, 3, 2, 3, 2, 1, 1, 6]
def baseStart_1677576 : Nat := 118140960795 + 1677576 * 2 ^ 59
def prefixEnd_1677576 : Nat := 4983230072969 + 3 ^ 40 * 1677576 * 2
def baseEnd_1677576 : Nat := 382845698865348315504433

theorem tailTrace_1677576 : CollatzResearch.WordTrace tailWord_1677576 prefixEnd_1677576 382845698865348315504433 := by
  unfold tailWord_1677576
  simp only [CollatzResearch.WordTrace]
  refine ⟨30593111685218067007954291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40790815580290756010605721 30593111685218067007954291)
  ·
    refine ⟨45889667527827100511931437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30593111685218067007954291 45889667527827100511931437)
    ·
      refine ⟨17208625322935162691974289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45889667527827100511931437 17208625322935162691974289)
      ·
        refine ⟨12906468992201372018980717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17208625322935162691974289 12906468992201372018980717)
        ·
          refine ⟨4839925872075514507117769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12906468992201372018980717 4839925872075514507117769)
          ·
            refine ⟨3629944404056635880338327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4839925872075514507117769 3629944404056635880338327)
            ·
              refine ⟨5444916606084953820507491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3629944404056635880338327 5444916606084953820507491)
              ·
                refine ⟨8167374909127430730761237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5444916606084953820507491 8167374909127430730761237)
                ·
                  refine ⟨382845698865348315504433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8167374909127430730761237 382845698865348315504433)
                  ·
                    rfl

theorem cell21_1677576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 1, 6].length) (baseStart_1677576 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677576 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677576 prefixEnd_1677576 := by exact prefixLift 1677576
  have htrace : WordTrace (prefixWord ++ tailWord_1677576) baseStart_1677576 baseEnd_1677576 := by
    simpa [prefixWord, tailWord_1677576, baseEnd_1677576] using wordTrace_append hprefix tailTrace_1677576
  have hstable : (prefixWord ++ tailWord_1677576).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677576).length < 2 ^ (prefixWord ++ tailWord_1677576).sum := by decide
  have hdescent : baseEnd_1677576 < baseStart_1677576 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677613 : List Nat := [1, 5, 3, 1, 2, 2, 1, 3, 3]
def baseStart_1677613 : Nat := 118140960795 + 1677613 * 2 ^ 59
def prefixEnd_1677613 : Nat := 4983230072969 + 3 ^ 40 * 1677613 * 2
def baseEnd_1677613 : Nat := 382854142769444473387691

theorem tailTrace_1677613 : CollatzResearch.WordTrace tailWord_1677613 prefixEnd_1677613 382854142769444473387691 := by
  unfold tailWord_1677613
  simp only [CollatzResearch.WordTrace]
  refine ⟨61187572871302089335005493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40791715247534726223336995 61187572871302089335005493)
  ·
    refine ⟨5736334956684570875156765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61187572871302089335005493 5736334956684570875156765)
    ·
      refine ⟨2151125608756714078183787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5736334956684570875156765 2151125608756714078183787)
      ·
        refine ⟨3226688413135071117275681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2151125608756714078183787 3226688413135071117275681)
        ·
          refine ⟨2420016309851303337956761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3226688413135071117275681 2420016309851303337956761)
          ·
            refine ⟨1815012232388477503467571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2420016309851303337956761 1815012232388477503467571)
            ·
              refine ⟨2722518348582716255201357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815012232388477503467571 2722518348582716255201357)
              ·
                refine ⟨1020944380718518595700509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2722518348582716255201357 1020944380718518595700509)
                ·
                  refine ⟨382854142769444473387691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020944380718518595700509 382854142769444473387691)
                  ·
                    rfl

theorem cell21_1677613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_1677613 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677613 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677613 prefixEnd_1677613 := by exact prefixLift 1677613
  have htrace : WordTrace (prefixWord ++ tailWord_1677613) baseStart_1677613 baseEnd_1677613 := by
    simpa [prefixWord, tailWord_1677613, baseEnd_1677613] using wordTrace_append hprefix tailTrace_1677613
  have hstable : (prefixWord ++ tailWord_1677613).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677613).length < 2 ^ (prefixWord ++ tailWord_1677613).sum := by decide
  have hdescent : baseEnd_1677613 < baseStart_1677613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677635 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 6]
def baseStart_1677635 : Nat := 118140960795 + 1677635 * 2 ^ 59
def prefixEnd_1677635 : Nat := 4983230072969 + 3 ^ 40 * 1677635 * 2
def baseEnd_1677635 : Nat := 382859163469177324020979

theorem tailTrace_1677635 : CollatzResearch.WordTrace tailWord_1677635 prefixEnd_1677635 382859163469177324020979 := by
  unfold tailWord_1677635
  simp only [CollatzResearch.WordTrace]
  refine ⟨61188375277222387092306359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40792250184814924728204239 61188375277222387092306359)
  ·
    refine ⟨91782562915833580638459539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61188375277222387092306359 91782562915833580638459539)
    ·
      refine ⟨137673844373750370957689309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91782562915833580638459539 137673844373750370957689309)
      ·
        refine ⟨51627691640156389109133491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137673844373750370957689309 51627691640156389109133491)
        ·
          refine ⟨77441537460234583663700237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51627691640156389109133491 77441537460234583663700237)
          ·
            refine ⟨29040576547587968873887589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77441537460234583663700237 29040576547587968873887589)
            ·
              refine ⟨5445108102672744163853923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29040576547587968873887589 5445108102672744163853923)
              ·
                refine ⟨8167662154009116245780885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5445108102672744163853923 8167662154009116245780885)
                ·
                  refine ⟨382859163469177324020979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8167662154009116245780885 382859163469177324020979)
                  ·
                    rfl

theorem cell21_1677635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 6].length) (baseStart_1677635 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677635 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677635 prefixEnd_1677635 := by exact prefixLift 1677635
  have htrace : WordTrace (prefixWord ++ tailWord_1677635) baseStart_1677635 baseEnd_1677635 := by
    simpa [prefixWord, tailWord_1677635, baseEnd_1677635] using wordTrace_append hprefix tailTrace_1677635
  have hstable : (prefixWord ++ tailWord_1677635).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677635).length < 2 ^ (prefixWord ++ tailWord_1677635).sum := by decide
  have hdescent : baseEnd_1677635 < baseStart_1677635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677745 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 4]
def baseStart_1677745 : Nat := 118140960795 + 1677745 * 2 ^ 59
def prefixEnd_1677745 : Nat := 4983230072969 + 3 ^ 40 * 1677745 * 2
def baseEnd_1677745 : Nat := 382884266967841577187421

theorem tailTrace_1677745 : CollatzResearch.WordTrace tailWord_1677745 prefixEnd_1677745 382884266967841577187421 := by
  unfold tailWord_1677745
  simp only [CollatzResearch.WordTrace]
  refine ⟨61192387306823875878810689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40794924871215917252540459 61192387306823875878810689)
  ·
    refine ⟨45894290480117906909108017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61192387306823875878810689 45894290480117906909108017)
    ·
      refine ⟨34420717860088430181831013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45894290480117906909108017 34420717860088430181831013)
      ·
        refine ⟨6453884598766580659093315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34420717860088430181831013 6453884598766580659093315)
        ·
          refine ⟨9680826898149870988639973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6453884598766580659093315 9680826898149870988639973)
          ·
            refine ⟨1815155043403100810369995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9680826898149870988639973 1815155043403100810369995)
            ·
              refine ⟨2722732565104651215554993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815155043403100810369995 2722732565104651215554993)
              ·
                refine ⟨2042049423828488411666245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2722732565104651215554993 2042049423828488411666245)
                ·
                  refine ⟨382884266967841577187421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2042049423828488411666245 382884266967841577187421)
                  ·
                    rfl

theorem cell21_1677745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_1677745 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677745 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677745 prefixEnd_1677745 := by exact prefixLift 1677745
  have htrace : WordTrace (prefixWord ++ tailWord_1677745) baseStart_1677745 baseEnd_1677745 := by
    simpa [prefixWord, tailWord_1677745, baseEnd_1677745] using wordTrace_append hprefix tailTrace_1677745
  have hstable : (prefixWord ++ tailWord_1677745).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677745).length < 2 ^ (prefixWord ++ tailWord_1677745).sum := by decide
  have hdescent : baseEnd_1677745 < baseStart_1677745 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677748 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 5]
def baseStart_1677748 : Nat := 118140960795 + 1677748 * 2 ^ 59
def prefixEnd_1677748 : Nat := 4983230072969 + 3 ^ 40 * 1677748 * 2
def baseEnd_1677748 : Nat := 382884951608714238637415

theorem tailTrace_1677748 : CollatzResearch.WordTrace tailWord_1677748 prefixEnd_1677748 382884951608714238637415 := by
  unfold tailWord_1677748
  simp only [CollatzResearch.WordTrace]
  refine ⟨30596248362906503695584949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40794997817208671594113265 30596248362906503695584949)
  ·
    refine ⟨2868398284022484721461089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30596248362906503695584949 2868398284022484721461089)
    ·
      refine ⟨2151298713016863541095817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2868398284022484721461089 2151298713016863541095817)
      ·
        refine ⟨1613474034762647655821863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2151298713016863541095817 1613474034762647655821863)
        ·
          refine ⟨2420211052143971483732795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613474034762647655821863 2420211052143971483732795)
          ·
            refine ⟨3630316578215957225599193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420211052143971483732795 3630316578215957225599193)
            ·
              refine ⟨2722737433661967919199395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3630316578215957225599193 2722737433661967919199395)
              ·
                refine ⟨4084106150492951878799093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2722737433661967919199395 4084106150492951878799093)
                ·
                  refine ⟨382884951608714238637415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4084106150492951878799093 382884951608714238637415)
                  ·
                    rfl

theorem cell21_1677748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_1677748 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677748 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677748 prefixEnd_1677748 := by exact prefixLift 1677748
  have htrace : WordTrace (prefixWord ++ tailWord_1677748) baseStart_1677748 baseEnd_1677748 := by
    simpa [prefixWord, tailWord_1677748, baseEnd_1677748] using wordTrace_append hprefix tailTrace_1677748
  have hstable : (prefixWord ++ tailWord_1677748).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677748).length < 2 ^ (prefixWord ++ tailWord_1677748).sum := by decide
  have hdescent : baseEnd_1677748 < baseStart_1677748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677832 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 7]
def baseStart_1677832 : Nat := 118140960795 + 1677832 * 2 ^ 59
def prefixEnd_1677832 : Nat := 4983230072969 + 3 ^ 40 * 1677832 * 2
def baseEnd_1677832 : Nat := 382904121553148759237243

theorem tailTrace_1677832 : CollatzResearch.WordTrace tailWord_1677832 prefixEnd_1677832 382904121553148759237243 := by
  unfold tailWord_1677832
  simp only [CollatzResearch.WordTrace]
  refine ⟨30597780228754344868613875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40797040305005793158151833 30597780228754344868613875)
  ·
    refine ⟨45896670343131517302920813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30597780228754344868613875 45896670343131517302920813)
    ·
      refine ⟨17211251378674318988595305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45896670343131517302920813 17211251378674318988595305)
      ·
        refine ⟨12908438534005739241446479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17211251378674318988595305 12908438534005739241446479)
        ·
          refine ⟨19362657801008608862169719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12908438534005739241446479 19362657801008608862169719)
          ·
            refine ⟨29043986701512913293254579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19362657801008608862169719 29043986701512913293254579)
            ·
              refine ⟨43565980052269369939881869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29043986701512913293254579 43565980052269369939881869)
              ·
                refine ⟨16337242519601013727455701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43565980052269369939881869 16337242519601013727455701)
                ·
                  refine ⟨382904121553148759237243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16337242519601013727455701 382904121553148759237243)
                  ·
                    rfl

theorem cell21_1677832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 7].length) (baseStart_1677832 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677832 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677832 prefixEnd_1677832 := by exact prefixLift 1677832
  have htrace : WordTrace (prefixWord ++ tailWord_1677832) baseStart_1677832 baseEnd_1677832 := by
    simpa [prefixWord, tailWord_1677832, baseEnd_1677832] using wordTrace_append hprefix tailTrace_1677832
  have hstable : (prefixWord ++ tailWord_1677832).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677832).length < 2 ^ (prefixWord ++ tailWord_1677832).sum := by decide
  have hdescent : baseEnd_1677832 < baseStart_1677832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1677970 : List Nat := [3, 2, 3, 1, 2, 1, 9]
def baseStart_1677970 : Nat := 118140960795 + 1677970 * 2 ^ 59
def prefixEnd_1677970 : Nat := 4983230072969 + 3 ^ 40 * 1677970 * 2
def baseEnd_1677970 : Nat := 42548401670365687326329

theorem tailTrace_1677970 : CollatzResearch.WordTrace tailWord_1677970 prefixEnd_1677970 42548401670365687326329 := by
  unfold tailWord_1677970
  simp only [CollatzResearch.WordTrace]
  refine ⟨15300148432752184826437841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40800395820672492870500909 15300148432752184826437841)
  ·
    refine ⟨11475111324564138619828381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15300148432752184826437841 11475111324564138619828381)
    ·
      refine ⟨4303166746711551982435643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11475111324564138619828381 4303166746711551982435643)
      ·
        refine ⟨6454750120067327973653465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4303166746711551982435643 6454750120067327973653465)
        ·
          refine ⟨4841062590050495980240099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6454750120067327973653465 4841062590050495980240099)
          ·
            refine ⟨7261593885075743970360149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4841062590050495980240099 7261593885075743970360149)
            ·
              refine ⟨42548401670365687326329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7261593885075743970360149 42548401670365687326329)
              ·
                rfl

theorem cell21_1677970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 9].length) (baseStart_1677970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1677970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1677970 prefixEnd_1677970 := by exact prefixLift 1677970
  have htrace : WordTrace (prefixWord ++ tailWord_1677970) baseStart_1677970 baseEnd_1677970 := by
    simpa [prefixWord, tailWord_1677970, baseEnd_1677970] using wordTrace_append hprefix tailTrace_1677970
  have hstable : (prefixWord ++ tailWord_1677970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1677970).length < 2 ^ (prefixWord ++ tailWord_1677970).sum := by decide
  have hdescent : baseEnd_1677970 < baseStart_1677970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1677970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678069 : List Nat := [1, 3, 6, 1, 1, 1, 2, 3, 3]
def baseStart_1678069 : Nat := 118140960795 + 1678069 * 2 ^ 59
def prefixEnd_1678069 : Nat := 4983230072969 + 3 ^ 40 * 1678069 * 2
def baseEnd_1678069 : Nat := 382958208182089013786759

theorem tailTrace_1678069 : CollatzResearch.WordTrace tailWord_1678069 prefixEnd_1678069 382958208182089013786759 := by
  unfold tailWord_1678069
  simp only [CollatzResearch.WordTrace]
  refine ⟨61204204557650079213605261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40802803038433386142403507 61204204557650079213605261)
  ·
    refine ⟨22951576709118779705101973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61204204557650079213605261 22951576709118779705101973)
    ·
      refine ⟨1075855158239942798676655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22951576709118779705101973 1075855158239942798676655)
      ·
        refine ⟨1613782737359914198014983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075855158239942798676655 1613782737359914198014983)
        ·
          refine ⟨2420674106039871297022475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613782737359914198014983 2420674106039871297022475)
          ·
            refine ⟨3631011159059806945533713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420674106039871297022475 3631011159059806945533713)
            ·
              refine ⟨2723258369294855209150285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631011159059806945533713 2723258369294855209150285)
              ·
                refine ⟨1021221888485570703431357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2723258369294855209150285 1021221888485570703431357)
                ·
                  refine ⟨382958208182089013786759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021221888485570703431357 382958208182089013786759)
                  ·
                    rfl

theorem cell21_1678069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_1678069 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678069 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678069 prefixEnd_1678069 := by exact prefixLift 1678069
  have htrace : WordTrace (prefixWord ++ tailWord_1678069) baseStart_1678069 baseEnd_1678069 := by
    simpa [prefixWord, tailWord_1678069, baseEnd_1678069] using wordTrace_append hprefix tailTrace_1678069
  have hstable : (prefixWord ++ tailWord_1678069).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678069).length < 2 ^ (prefixWord ++ tailWord_1678069).sum := by decide
  have hdescent : baseEnd_1678069 < baseStart_1678069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678153 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 5]
def baseStart_1678153 : Nat := 118140960795 + 1678153 * 2 ^ 59
def prefixEnd_1678153 : Nat := 4983230072969 + 3 ^ 40 * 1678153 * 2
def baseEnd_1678153 : Nat := 382977378126523534386587

theorem tailTrace_1678153 : CollatzResearch.WordTrace tailWord_1678153 prefixEnd_1678153 382977378126523534386587 := by
  unfold tailWord_1678153
  simp only [CollatzResearch.WordTrace]
  refine ⟨61207268289345761559663113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40804845526230507706442075 61207268289345761559663113)
  ·
    refine ⟨45905451217009321169747335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61207268289345761559663113 45905451217009321169747335)
    ·
      refine ⟨68858176825513981754621003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45905451217009321169747335 68858176825513981754621003)
      ·
        refine ⟨103287265238270972631931505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68858176825513981754621003 103287265238270972631931505)
        ·
          refine ⟨77465448928703229473948629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103287265238270972631931505 77465448928703229473948629)
          ·
            refine ⟨1815596459266481940795671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 77465448928703229473948629 1815596459266481940795671)
            ·
              refine ⟨2723394688899722911193507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815596459266481940795671 2723394688899722911193507)
              ·
                refine ⟨4085092033349584366790261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723394688899722911193507 4085092033349584366790261)
                ·
                  refine ⟨382977378126523534386587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4085092033349584366790261 382977378126523534386587)
                  ·
                    rfl

theorem cell21_1678153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_1678153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678153 prefixEnd_1678153 := by exact prefixLift 1678153
  have htrace : WordTrace (prefixWord ++ tailWord_1678153) baseStart_1678153 baseEnd_1678153 := by
    simpa [prefixWord, tailWord_1678153, baseEnd_1678153] using wordTrace_append hprefix tailTrace_1678153
  have hstable : (prefixWord ++ tailWord_1678153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678153).length < 2 ^ (prefixWord ++ tailWord_1678153).sum := by decide
  have hdescent : baseEnd_1678153 < baseStart_1678153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678181 : List Nat := [1, 3, 1, 3, 1, 1, 4, 7]
def baseStart_1678181 : Nat := 118140960795 + 1678181 * 2 ^ 59
def prefixEnd_1678181 : Nat := 4983230072969 + 3 ^ 40 * 1678181 * 2
def baseEnd_1678181 : Nat := 127661256036000569306621

theorem tailTrace_1678181 : CollatzResearch.WordTrace tailWord_1678181 prefixEnd_1678181 127661256036000569306621 := by
  unfold tailWord_1678181
  simp only [CollatzResearch.WordTrace]
  refine ⟨61208289533244322341682397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40805526355496214894454931 61208289533244322341682397)
  ·
    refine ⟨22953108574966620878130899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61208289533244322341682397 22953108574966620878130899)
    ·
      refine ⟨34429662862449931317196349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22953108574966620878130899 34429662862449931317196349)
      ·
        refine ⟨12911123573418724243948631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34429662862449931317196349 12911123573418724243948631)
        ·
          refine ⟨19366685360128086365922947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12911123573418724243948631 19366685360128086365922947)
          ·
            refine ⟨29050028040192129548884421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19366685360128086365922947 29050028040192129548884421)
            ·
              refine ⟨5446880257536024290415829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29050028040192129548884421 5446880257536024290415829)
              ·
                refine ⟨127661256036000569306621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5446880257536024290415829 127661256036000569306621)
                ·
                  rfl

theorem cell21_1678181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 7].length) (baseStart_1678181 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678181 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678181 prefixEnd_1678181 := by exact prefixLift 1678181
  have htrace : WordTrace (prefixWord ++ tailWord_1678181) baseStart_1678181 baseEnd_1678181 := by
    simpa [prefixWord, tailWord_1678181, baseEnd_1678181] using wordTrace_append hprefix tailTrace_1678181
  have hstable : (prefixWord ++ tailWord_1678181).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678181).length < 2 ^ (prefixWord ++ tailWord_1678181).sum := by decide
  have hdescent : baseEnd_1678181 < baseStart_1678181 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678198 : List Nat := [5, 1, 1, 3, 1, 10]
def baseStart_1678198 : Nat := 118140960795 + 1678198 * 2 ^ 59
def prefixEnd_1678198 : Nat := 4983230072969 + 3 ^ 40 * 1678198 * 2
def baseEnd_1678198 : Nat := 14184727694059757634685

theorem tailTrace_1678198 : CollatzResearch.WordTrace tailWord_1678198 prefixEnd_1678198 14184727694059757634685 := by
  unfold tailWord_1678198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3825556848386420890315703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40805939716121822830034165 3825556848386420890315703)
  ·
    refine ⟨5738335272579631335473555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3825556848386420890315703 5738335272579631335473555)
    ·
      refine ⟨8607502908869447003210333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5738335272579631335473555 8607502908869447003210333)
      ·
        refine ⟨3227813590826042626203875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8607502908869447003210333 3227813590826042626203875)
        ·
          refine ⟨4841720386239063939305813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3227813590826042626203875 4841720386239063939305813)
          ·
            refine ⟨14184727694059757634685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4841720386239063939305813 14184727694059757634685)
            ·
              rfl

theorem cell21_1678198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 10].length) (baseStart_1678198 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678198 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678198 prefixEnd_1678198 := by exact prefixLift 1678198
  have htrace : WordTrace (prefixWord ++ tailWord_1678198) baseStart_1678198 baseEnd_1678198 := by
    simpa [prefixWord, tailWord_1678198, baseEnd_1678198] using wordTrace_append hprefix tailTrace_1678198
  have hstable : (prefixWord ++ tailWord_1678198).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678198).length < 2 ^ (prefixWord ++ tailWord_1678198).sum := by decide
  have hdescent : baseEnd_1678198 < baseStart_1678198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678212 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1678212 : Nat := 118140960795 + 1678212 * 2 ^ 59
def prefixEnd_1678212 : Nat := 4983230072969 + 3 ^ 40 * 1678212 * 2
def baseEnd_1678212 : Nat := 382990842730352542903133

theorem tailTrace_1678212 : CollatzResearch.WordTrace tailWord_1678212 prefixEnd_1678212 382990842730352542903133 := by
  unfold tailWord_1678212
  simp only [CollatzResearch.WordTrace]
  refine ⟨30604710098066007318030445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40806280130754676424040593 30604710098066007318030445)
  ·
    refine ⟨11476766286774752744261417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30604710098066007318030445 11476766286774752744261417)
    ·
      refine ⟨8607574715081064558196063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11476766286774752744261417 8607574715081064558196063)
      ·
        refine ⟨12911362072621596837294095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8607574715081064558196063 12911362072621596837294095)
        ·
          refine ⟨19367043108932395255941143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12911362072621596837294095 19367043108932395255941143)
          ·
            refine ⟨29050564663398592883911715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19367043108932395255941143 29050564663398592883911715)
            ·
              refine ⟨43575846995097889325867573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29050564663398592883911715 43575846995097889325867573)
              ·
                refine ⟨4085235655790427124300085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43575846995097889325867573 4085235655790427124300085)
                ·
                  refine ⟨382990842730352542903133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4085235655790427124300085 382990842730352542903133)
                  ·
                    rfl

theorem cell21_1678212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1678212 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678212 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678212 prefixEnd_1678212 := by exact prefixLift 1678212
  have htrace : WordTrace (prefixWord ++ tailWord_1678212) baseStart_1678212 baseEnd_1678212 := by
    simpa [prefixWord, tailWord_1678212, baseEnd_1678212] using wordTrace_append hprefix tailTrace_1678212
  have hstable : (prefixWord ++ tailWord_1678212).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678212).length < 2 ^ (prefixWord ++ tailWord_1678212).sum := by decide
  have hdescent : baseEnd_1678212 < baseStart_1678212 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678423 : List Nat := [1, 1, 3, 2, 2, 1, 1, 1, 9]
def baseStart_1678423 : Nat := 118140960795 + 1678423 * 2 ^ 59
def prefixEnd_1678423 : Nat := 4983230072969 + 3 ^ 40 * 1678423 * 2
def baseEnd_1678423 : Nat := 383038995805063064886035

theorem tailTrace_1678423 : CollatzResearch.WordTrace tailWord_1678423 prefixEnd_1678423 383038995805063064886035 := by
  unfold tailWord_1678423
  simp only [CollatzResearch.WordTrace]
  refine ⟨61217115998367597671991923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40811410665578398447994615 61217115998367597671991923)
  ·
    refine ⟨91825673997551396507987885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61217115998367597671991923 91825673997551396507987885)
    ·
      refine ⟨34434627749081773690495457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91825673997551396507987885 34434627749081773690495457)
      ·
        refine ⟨25825970811811330267871593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34434627749081773690495457 25825970811811330267871593)
        ·
          refine ⟨19369478108858497700903695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25825970811811330267871593 19369478108858497700903695)
          ·
            refine ⟨29054217163287746551355543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19369478108858497700903695 29054217163287746551355543)
            ·
              refine ⟨43581325744931619827033315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29054217163287746551355543 43581325744931619827033315)
              ·
                refine ⟨65371988617397429740549973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43581325744931619827033315 65371988617397429740549973)
                ·
                  refine ⟨383038995805063064886035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 65371988617397429740549973 383038995805063064886035)
                  ·
                    rfl

theorem cell21_1678423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 1, 9].length) (baseStart_1678423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678423 prefixEnd_1678423 := by exact prefixLift 1678423
  have htrace : WordTrace (prefixWord ++ tailWord_1678423) baseStart_1678423 baseEnd_1678423 := by
    simpa [prefixWord, tailWord_1678423, baseEnd_1678423] using wordTrace_append hprefix tailTrace_1678423
  have hstable : (prefixWord ++ tailWord_1678423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678423).length < 2 ^ (prefixWord ++ tailWord_1678423).sum := by decide
  have hdescent : baseEnd_1678423 < baseStart_1678423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678561 : List Nat := [1, 2, 3, 1, 3, 2, 3, 6]
def baseStart_1678561 : Nat := 118140960795 + 1678561 * 2 ^ 59
def prefixEnd_1678561 : Nat := 4983230072969 + 3 ^ 40 * 1678561 * 2
def baseEnd_1678561 : Nat := 127690163095068497195251

theorem tailTrace_1678561 : CollatzResearch.WordTrace tailWord_1678561 prefixEnd_1678561 127690163095068497195251 := by
  unfold tailWord_1678561
  simp only [CollatzResearch.WordTrace]
  refine ⟨61222149271867647240515537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40814766181245098160343691 61222149271867647240515537)
  ·
    refine ⟨45916611953900735430386653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61222149271867647240515537 45916611953900735430386653)
    ·
      refine ⟨17218729482712775786394995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45916611953900735430386653 17218729482712775786394995)
      ·
        refine ⟨25828094224069163679592493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17218729482712775786394995 25828094224069163679592493)
        ·
          refine ⟨9685535334025936379847185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25828094224069163679592493 9685535334025936379847185)
          ·
            refine ⟨7264151500519452284885389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9685535334025936379847185 7264151500519452284885389)
            ·
              refine ⟨2724056812694794606832021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7264151500519452284885389 2724056812694794606832021)
              ·
                refine ⟨127690163095068497195251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2724056812694794606832021 127690163095068497195251)
                ·
                  rfl

theorem cell21_1678561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 6].length) (baseStart_1678561 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678561 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678561 prefixEnd_1678561 := by exact prefixLift 1678561
  have htrace : WordTrace (prefixWord ++ tailWord_1678561) baseStart_1678561 baseEnd_1678561 := by
    simpa [prefixWord, tailWord_1678561, baseEnd_1678561] using wordTrace_append hprefix tailTrace_1678561
  have hstable : (prefixWord ++ tailWord_1678561).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678561).length < 2 ^ (prefixWord ++ tailWord_1678561).sum := by decide
  have hdescent : baseEnd_1678561 < baseStart_1678561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678668 : List Nat := [2, 2, 1, 3, 2, 2, 3, 1, 5]
def baseStart_1678668 : Nat := 118140960795 + 1678668 * 2 ^ 59
def prefixEnd_1678668 : Nat := 4983230072969 + 3 ^ 40 * 1678668 * 2
def baseEnd_1678668 : Nat := 383094908142997083302201

theorem tailTrace_1678668 : CollatzResearch.WordTrace tailWord_1678668 prefixEnd_1678668 383094908142997083302201 := by
  unfold tailWord_1678668
  simp only [CollatzResearch.WordTrace]
  refine ⟨30613025941240002257330329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40817367921653336343107105 30613025941240002257330329)
  ·
    refine ⟨22959769455930001692997747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30613025941240002257330329 22959769455930001692997747)
    ·
      refine ⟨34439654183895002539496621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22959769455930001692997747 34439654183895002539496621)
      ·
        refine ⟨12914870318960625952311233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34439654183895002539496621 12914870318960625952311233)
        ·
          refine ⟨9686152739220469464233425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12914870318960625952311233 9686152739220469464233425)
          ·
            refine ⟨7264614554415352098175069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9686152739220469464233425 7264614554415352098175069)
            ·
              refine ⟨2724230457905757036815651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7264614554415352098175069 2724230457905757036815651)
              ·
                refine ⟨4086345686858635555223477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724230457905757036815651 4086345686858635555223477)
                ·
                  refine ⟨383094908142997083302201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4086345686858635555223477 383094908142997083302201)
                  ·
                    rfl

theorem cell21_1678668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 1, 5].length) (baseStart_1678668 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678668 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678668 prefixEnd_1678668 := by exact prefixLift 1678668
  have htrace : WordTrace (prefixWord ++ tailWord_1678668) baseStart_1678668 baseEnd_1678668 := by
    simpa [prefixWord, tailWord_1678668, baseEnd_1678668] using wordTrace_append hprefix tailTrace_1678668
  have hstable : (prefixWord ++ tailWord_1678668).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678668).length < 2 ^ (prefixWord ++ tailWord_1678668).sum := by decide
  have hdescent : baseEnd_1678668 < baseStart_1678668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678806 : List Nat := [5, 2, 1, 1, 1, 3, 1, 7]
def baseStart_1678806 : Nat := 118140960795 + 1678806 * 2 ^ 59
def prefixEnd_1678806 : Nat := 4983230072969 + 3 ^ 40 * 1678806 * 2
def baseEnd_1678806 : Nat := 127708800541046503333973

theorem tailTrace_1678806 : CollatzResearch.WordTrace tailWord_1678806 prefixEnd_1678806 127708800541046503333973 := by
  unfold tailWord_1678806
  simp only [CollatzResearch.WordTrace]
  refine ⟨3826942822248753380199017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40820723437320036055456181 3826942822248753380199017)
  ·
    refine ⟨2870207116686565035149263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3826942822248753380199017 2870207116686565035149263)
    ·
      refine ⟨4305310675029847552723895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2870207116686565035149263 4305310675029847552723895)
      ·
        refine ⟨6457966012544771329085843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4305310675029847552723895 6457966012544771329085843)
        ·
          refine ⟨9686949018817156993628765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6457966012544771329085843 9686949018817156993628765)
          ·
            refine ⟨3632605882056433872610787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9686949018817156993628765 3632605882056433872610787)
            ·
              refine ⟨5448908823084650808916181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3632605882056433872610787 5448908823084650808916181)
              ·
                refine ⟨127708800541046503333973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5448908823084650808916181 127708800541046503333973)
                ·
                  rfl

theorem cell21_1678806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 7].length) (baseStart_1678806 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678806 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678806 prefixEnd_1678806 := by exact prefixLift 1678806
  have htrace : WordTrace (prefixWord ++ tailWord_1678806) baseStart_1678806 baseEnd_1678806 := by
    simpa [prefixWord, tailWord_1678806, baseEnd_1678806] using wordTrace_append hprefix tailTrace_1678806
  have hstable : (prefixWord ++ tailWord_1678806).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678806).length < 2 ^ (prefixWord ++ tailWord_1678806).sum := by decide
  have hdescent : baseEnd_1678806 < baseStart_1678806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678837 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 5]
def baseStart_1678837 : Nat := 118140960795 + 1678837 * 2 ^ 59
def prefixEnd_1678837 : Nat := 4983230072969 + 3 ^ 40 * 1678837 * 2
def baseEnd_1678837 : Nat := 383133476245490344985189

theorem tailTrace_1678837 : CollatzResearch.WordTrace tailWord_1678837 prefixEnd_1678837 383133476245490344985189 := by
  unfold tailWord_1678837
  simp only [CollatzResearch.WordTrace]
  refine ⟨61232215818867746377562765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40821477212578497585041843 61232215818867746377562765)
  ·
    refine ⟨22962080932075404891586037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61232215818867746377562765 22962080932075404891586037)
    ·
      refine ⟨2152695087382069208586191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22962080932075404891586037 2152695087382069208586191)
      ·
        refine ⟨3229042631073103812879287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152695087382069208586191 3229042631073103812879287)
        ·
          refine ⟨4843563946609655719318931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229042631073103812879287 4843563946609655719318931)
          ·
            refine ⟨7265345919914483578978397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843563946609655719318931 7265345919914483578978397)
            ·
              refine ⟨2724504719967931342116899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7265345919914483578978397 2724504719967931342116899)
              ·
                refine ⟨4086757079951897013175349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2724504719967931342116899 4086757079951897013175349)
                ·
                  refine ⟨383133476245490344985189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4086757079951897013175349 383133476245490344985189)
                  ·
                    rfl

theorem cell21_1678837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_1678837 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678837 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678837 prefixEnd_1678837 := by exact prefixLift 1678837
  have htrace : WordTrace (prefixWord ++ tailWord_1678837) baseStart_1678837 baseEnd_1678837 := by
    simpa [prefixWord, tailWord_1678837, baseEnd_1678837] using wordTrace_append hprefix tailTrace_1678837
  have hstable : (prefixWord ++ tailWord_1678837).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678837).length < 2 ^ (prefixWord ++ tailWord_1678837).sum := by decide
  have hdescent : baseEnd_1678837 < baseStart_1678837 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678888 : List Nat := [2, 1, 5, 2, 3, 1, 2, 2, 3]
def baseStart_1678888 : Nat := 118140960795 + 1678888 * 2 ^ 59
def prefixEnd_1678888 : Nat := 4983230072969 + 3 ^ 40 * 1678888 * 2
def baseEnd_1678888 : Nat := 383145115140325589635085

theorem tailTrace_1678888 : CollatzResearch.WordTrace tailWord_1678888 prefixEnd_1678888 383145115140325589635085 := by
  unfold tailWord_1678888
  simp only [CollatzResearch.WordTrace]
  refine ⟨30617037970841491043834659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40822717294455321391779545 30617037970841491043834659)
  ·
    refine ⟨45925556956262236565751989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30617037970841491043834659 45925556956262236565751989)
    ·
      refine ⟨4305520964649584678039249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45925556956262236565751989 4305520964649584678039249)
      ·
        refine ⟨3229140723487188508529437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4305520964649584678039249 3229140723487188508529437)
        ·
          refine ⟨1210927771307695690698539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3229140723487188508529437 1210927771307695690698539)
          ·
            refine ⟨1816391656961543536047809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210927771307695690698539 1816391656961543536047809)
            ·
              refine ⟨1362293742721157652035857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1816391656961543536047809 1362293742721157652035857)
              ·
                refine ⟨1021720307040868239026893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362293742721157652035857 1021720307040868239026893)
                ·
                  refine ⟨383145115140325589635085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021720307040868239026893 383145115140325589635085)
                  ·
                    rfl

theorem cell21_1678888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 3].length) (baseStart_1678888 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678888 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678888 prefixEnd_1678888 := by exact prefixLift 1678888
  have htrace : WordTrace (prefixWord ++ tailWord_1678888) baseStart_1678888 baseEnd_1678888 := by
    simpa [prefixWord, tailWord_1678888, baseEnd_1678888] using wordTrace_append hprefix tailTrace_1678888
  have hstable : (prefixWord ++ tailWord_1678888).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678888).length < 2 ^ (prefixWord ++ tailWord_1678888).sum := by decide
  have hdescent : baseEnd_1678888 < baseStart_1678888 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1678986 : List Nat := [3, 1, 2, 3, 2, 1, 1, 2, 6]
def baseStart_1678986 : Nat := 118140960795 + 1678986 * 2 ^ 59
def prefixEnd_1678986 : Nat := 4983230072969 + 3 ^ 40 * 1678986 * 2
def baseEnd_1678986 : Nat := 383167480075499197001551

theorem tailTrace_1678986 : CollatzResearch.WordTrace tailWord_1678986 prefixEnd_1678986 383167480075499197001551 := by
  unfold tailWord_1678986
  simp only [CollatzResearch.WordTrace]
  refine ⟨15309412573831986206184203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40825100196885296549824541 15309412573831986206184203)
  ·
    refine ⟨22964118860747979309276305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15309412573831986206184203 22964118860747979309276305)
    ·
      refine ⟨17223089145560984481957229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22964118860747979309276305 17223089145560984481957229)
      ·
        refine ⟨6458658429585369180733961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17223089145560984481957229 6458658429585369180733961)
        ·
          refine ⟨4843993822189026885550471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6458658429585369180733961 4843993822189026885550471)
          ·
            refine ⟨7265990733283540328325707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4843993822189026885550471 7265990733283540328325707)
            ·
              refine ⟨10898986099925310492488561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265990733283540328325707 10898986099925310492488561)
              ·
                refine ⟨8174239574943982869366421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10898986099925310492488561 8174239574943982869366421)
                ·
                  refine ⟨383167480075499197001551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8174239574943982869366421 383167480075499197001551)
                  ·
                    rfl

theorem cell21_1678986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 2, 6].length) (baseStart_1678986 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1678986 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1678986 prefixEnd_1678986 := by exact prefixLift 1678986
  have htrace : WordTrace (prefixWord ++ tailWord_1678986) baseStart_1678986 baseEnd_1678986 := by
    simpa [prefixWord, tailWord_1678986, baseEnd_1678986] using wordTrace_append hprefix tailTrace_1678986
  have hstable : (prefixWord ++ tailWord_1678986).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1678986).length < 2 ^ (prefixWord ++ tailWord_1678986).sum := by decide
  have hdescent : baseEnd_1678986 < baseStart_1678986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1678986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679000 : List Nat := [2, 1, 2, 4, 1, 2, 9]
def baseStart_1679000 : Nat := 118140960795 + 1679000 * 2 ^ 59
def prefixEnd_1679000 : Nat := 4983230072969 + 3 ^ 40 * 1679000 * 2
def baseEnd_1679000 : Nat := 42574519451804253752021

theorem tailTrace_1679000 : CollatzResearch.WordTrace tailWord_1679000 prefixEnd_1679000 42574519451804253752021 := by
  unfold tailWord_1679000
  simp only [CollatzResearch.WordTrace]
  refine ⟨30619080458638612607873227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40825440611518150143830969 30619080458638612607873227)
  ·
    refine ⟨45928620687957918911809841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30619080458638612607873227 45928620687957918911809841)
    ·
      refine ⟨34446465515968439183857381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45928620687957918911809841 34446465515968439183857381)
      ·
        refine ⟨6458712284244082346973259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34446465515968439183857381 6458712284244082346973259)
        ·
          refine ⟨9688068426366123520459889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6458712284244082346973259 9688068426366123520459889)
          ·
            refine ⟨7266051319774592640344917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9688068426366123520459889 7266051319774592640344917)
            ·
              refine ⟨42574519451804253752021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7266051319774592640344917 42574519451804253752021)
              ·
                rfl

theorem cell21_1679000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 9].length) (baseStart_1679000 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679000 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679000 prefixEnd_1679000 := by exact prefixLift 1679000
  have htrace : WordTrace (prefixWord ++ tailWord_1679000) baseStart_1679000 baseEnd_1679000 := by
    simpa [prefixWord, tailWord_1679000, baseEnd_1679000] using wordTrace_append hprefix tailTrace_1679000
  have hstable : (prefixWord ++ tailWord_1679000).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679000).length < 2 ^ (prefixWord ++ tailWord_1679000).sum := by decide
  have hdescent : baseEnd_1679000 < baseStart_1679000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679048 : List Nat := [2, 1, 3, 1, 2, 2, 2, 5, 3]
def baseStart_1679048 : Nat := 118140960795 + 1679048 * 2 ^ 59
def prefixEnd_1679048 : Nat := 4983230072969 + 3 ^ 40 * 1679048 * 2
def baseEnd_1679048 : Nat := 383181629320200866968091

theorem tailTrace_1679048 : CollatzResearch.WordTrace tailWord_1679048 prefixEnd_1679048 383181629320200866968091 := by
  unfold tailWord_1679048
  simp only [CollatzResearch.WordTrace]
  refine ⟨30619955810551664706746899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40826607747402219608995865 30619955810551664706746899)
  ·
    refine ⟨45929933715827497060120349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30619955810551664706746899 45929933715827497060120349)
    ·
      refine ⟨17223725143435311397545131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45929933715827497060120349 17223725143435311397545131)
      ·
        refine ⟨25835587715152967096317697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17223725143435311397545131 25835587715152967096317697)
        ·
          refine ⟨19376690786364725322238273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25835587715152967096317697 19376690786364725322238273)
          ·
            refine ⟨14532518089773543991678705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19376690786364725322238273 14532518089773543991678705)
            ·
              refine ⟨10899388567330157993759029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14532518089773543991678705 10899388567330157993759029)
              ·
                refine ⟨1021817678187202311914909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10899388567330157993759029 1021817678187202311914909)
                ·
                  refine ⟨383181629320200866968091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021817678187202311914909 383181629320200866968091)
                  ·
                    rfl

theorem cell21_1679048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 5, 3].length) (baseStart_1679048 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679048 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679048 prefixEnd_1679048 := by exact prefixLift 1679048
  have htrace : WordTrace (prefixWord ++ tailWord_1679048) baseStart_1679048 baseEnd_1679048 := by
    simpa [prefixWord, tailWord_1679048, baseEnd_1679048] using wordTrace_append hprefix tailTrace_1679048
  have hstable : (prefixWord ++ tailWord_1679048).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679048).length < 2 ^ (prefixWord ++ tailWord_1679048).sum := by decide
  have hdescent : baseEnd_1679048 < baseStart_1679048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679065 : List Nat := [1, 2, 1, 2, 3, 3, 4, 2, 3]
def baseStart_1679065 : Nat := 118140960795 + 1679065 * 2 ^ 59
def prefixEnd_1679065 : Nat := 4983230072969 + 3 ^ 40 * 1679065 * 2
def baseEnd_1679065 : Nat := 383185508951812615184723

theorem tailTrace_1679065 : CollatzResearch.WordTrace tailWord_1679065 prefixEnd_1679065 383185508951812615184723 := by
  unfold tailWord_1679065
  simp only [CollatzResearch.WordTrace]
  refine ⟨61240531662041741316862649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40827021108027827544575099 61240531662041741316862649)
  ·
    refine ⟨45930398746531305987646987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61240531662041741316862649 45930398746531305987646987)
    ·
      refine ⟨68895598119796958981470481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45930398746531305987646987 68895598119796958981470481)
      ·
        refine ⟨51671698589847719236102861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68895598119796958981470481 51671698589847719236102861)
        ·
          refine ⟨19376886971192894713538573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51671698589847719236102861 19376886971192894713538573)
          ·
            refine ⟨7266332614197335517576965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19376886971192894713538573 7266332614197335517576965)
            ·
              refine ⟨1362437365162000409545681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7266332614197335517576965 1362437365162000409545681)
              ·
                refine ⟨1021828023871500307159261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362437365162000409545681 1021828023871500307159261)
                ·
                  refine ⟨383185508951812615184723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021828023871500307159261 383185508951812615184723)
                  ·
                    rfl

theorem cell21_1679065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 4, 2, 3].length) (baseStart_1679065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679065 prefixEnd_1679065 := by exact prefixLift 1679065
  have htrace : WordTrace (prefixWord ++ tailWord_1679065) baseStart_1679065 baseEnd_1679065 := by
    simpa [prefixWord, tailWord_1679065, baseEnd_1679065] using wordTrace_append hprefix tailTrace_1679065
  have hstable : (prefixWord ++ tailWord_1679065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679065).length < 2 ^ (prefixWord ++ tailWord_1679065).sum := by decide
  have hdescent : baseEnd_1679065 < baseStart_1679065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679158 : List Nat := [5, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_1679158 : Nat := 118140960795 + 1679158 * 2 ^ 59
def prefixEnd_1679158 : Nat := 4983230072969 + 3 ^ 40 * 1679158 * 2
def baseEnd_1679158 : Nat := 383206732818865120134533

theorem tailTrace_1679158 : CollatzResearch.WordTrace tailWord_1679158 prefixEnd_1679158 383206732818865120134533 := by
  unfold tailWord_1679158
  simp only [CollatzResearch.WordTrace]
  refine ⟨3827745228169051137499883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40829282433803212133332085 3827745228169051137499883)
  ·
    refine ⟨5741617842253576706249825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3827745228169051137499883 5741617842253576706249825)
    ·
      refine ⟨4306213381690182529687369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5741617842253576706249825 4306213381690182529687369)
      ·
        refine ⟨3229660036267636897265527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4306213381690182529687369 3229660036267636897265527)
        ·
          refine ⟨4844490054401455345898291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3229660036267636897265527 4844490054401455345898291)
          ·
            refine ⟨7266735081602183018847437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4844490054401455345898291 7266735081602183018847437)
            ·
              refine ⟨2725025655600818632067789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7266735081602183018847437 2725025655600818632067789)
              ·
                refine ⟨1021884620850306987025421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725025655600818632067789 1021884620850306987025421)
                ·
                  refine ⟨383206732818865120134533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021884620850306987025421 383206732818865120134533)
                  ·
                    rfl

theorem cell21_1679158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_1679158 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679158 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679158 prefixEnd_1679158 := by exact prefixLift 1679158
  have htrace : WordTrace (prefixWord ++ tailWord_1679158) baseStart_1679158 baseEnd_1679158 := by
    simpa [prefixWord, tailWord_1679158, baseEnd_1679158] using wordTrace_append hprefix tailTrace_1679158
  have hstable : (prefixWord ++ tailWord_1679158).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679158).length < 2 ^ (prefixWord ++ tailWord_1679158).sum := by decide
  have hdescent : baseEnd_1679158 < baseStart_1679158 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679400 : List Nat := [2, 1, 5, 3, 1, 1, 2, 2, 4]
def baseStart_1679400 : Nat := 118140960795 + 1679400 * 2 ^ 59
def prefixEnd_1679400 : Nat := 4983230072969 + 3 ^ 40 * 1679400 * 2
def baseEnd_1679400 : Nat := 383261960515926477100705

theorem tailTrace_1679400 : CollatzResearch.WordTrace tailWord_1679400 prefixEnd_1679400 383261960515926477100705 := by
  unfold tailWord_1679400
  simp only [CollatzResearch.WordTrace]
  refine ⟨30626375057914046765153827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40835166743885395686871769 30626375057914046765153827)
  ·
    refine ⟨45939562586871070147730741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30626375057914046765153827 45939562586871070147730741)
    ·
      refine ⟨4306833992519162826349757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45939562586871070147730741 4306833992519162826349757)
      ·
        refine ⟨1615062747194686059881159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4306833992519162826349757 1615062747194686059881159)
        ·
          refine ⟨2422594120792029089821739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615062747194686059881159 2422594120792029089821739)
          ·
            refine ⟨3633891181188043634732609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422594120792029089821739 3633891181188043634732609)
            ·
              refine ⟨2725418385891032726049457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3633891181188043634732609 2725418385891032726049457)
              ·
                refine ⟨2044063789418274544537093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2725418385891032726049457 2044063789418274544537093)
                ·
                  refine ⟨383261960515926477100705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044063789418274544537093 383261960515926477100705)
                  ·
                    rfl

theorem cell21_1679400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 2, 2, 4].length) (baseStart_1679400 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679400 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679400 prefixEnd_1679400 := by exact prefixLift 1679400
  have htrace : WordTrace (prefixWord ++ tailWord_1679400) baseStart_1679400 baseEnd_1679400 := by
    simpa [prefixWord, tailWord_1679400, baseEnd_1679400] using wordTrace_append hprefix tailTrace_1679400
  have hstable : (prefixWord ++ tailWord_1679400).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679400).length < 2 ^ (prefixWord ++ tailWord_1679400).sum := by decide
  have hdescent : baseEnd_1679400 < baseStart_1679400 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679521 : List Nat := [1, 2, 3, 3, 1, 3, 3, 2, 3]
def baseStart_1679521 : Nat := 118140960795 + 1679521 * 2 ^ 59
def prefixEnd_1679521 : Nat := 4983230072969 + 3 ^ 40 * 1679521 * 2
def baseEnd_1679521 : Nat := 383289574364457155583791

theorem tailTrace_1679521 : CollatzResearch.WordTrace tailWord_1679521 prefixEnd_1679521 383289574364457155583791 := by
  unfold tailWord_1679521
  simp only [CollatzResearch.WordTrace]
  refine ⟨61257163348389731195462417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40838108898926487463641611 61257163348389731195462417)
  ·
    refine ⟨45942872511292298396596813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61257163348389731195462417 45942872511292298396596813)
    ·
      refine ⟨17228577191734611898723805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45942872511292298396596813 17228577191734611898723805)
      ·
        refine ⟨6460716446900479462021427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17228577191734611898723805 6460716446900479462021427)
        ·
          refine ⟨9691074670350719193032141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460716446900479462021427 9691074670350719193032141)
          ·
            refine ⟨3634153001381519697387053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9691074670350719193032141 3634153001381519697387053)
            ·
              refine ⟨1362807375518069886520145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3634153001381519697387053 1362807375518069886520145)
              ·
                refine ⟨1022105531638552414890109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362807375518069886520145 1022105531638552414890109)
                ·
                  refine ⟨383289574364457155583791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022105531638552414890109 383289574364457155583791)
                  ·
                    rfl

theorem cell21_1679521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_1679521 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679521 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679521 prefixEnd_1679521 := by exact prefixLift 1679521
  have htrace : WordTrace (prefixWord ++ tailWord_1679521) baseStart_1679521 baseEnd_1679521 := by
    simpa [prefixWord, tailWord_1679521, baseEnd_1679521] using wordTrace_append hprefix tailTrace_1679521
  have hstable : (prefixWord ++ tailWord_1679521).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679521).length < 2 ^ (prefixWord ++ tailWord_1679521).sum := by decide
  have hdescent : baseEnd_1679521 < baseStart_1679521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679546 : List Nat := [3, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_1679546 : Nat := 118140960795 + 1679546 * 2 ^ 59
def prefixEnd_1679546 : Nat := 4983230072969 + 3 ^ 40 * 1679546 * 2
def baseEnd_1679546 : Nat := 383295279705062667667073

theorem tailTrace_1679546 : CollatzResearch.WordTrace tailWord_1679546 prefixEnd_1679546 383295279705062667667073 := by
  unfold tailWord_1679546
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314518793324790116280623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40838716782199440310081661 15314518793324790116280623)
  ·
    refine ⟨22971778189987185174420935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15314518793324790116280623 22971778189987185174420935)
    ·
      refine ⟨34457667284980777761631403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22971778189987185174420935 34457667284980777761631403)
      ·
        refine ⟨51686500927471166642447105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34457667284980777761631403 51686500927471166642447105)
        ·
          refine ⟨38764875695603374981835329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51686500927471166642447105 38764875695603374981835329)
          ·
            refine ⟨29073656771702531236376497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38764875695603374981835329 29073656771702531236376497)
            ·
              refine ⟨21805242578776898427282373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29073656771702531236376497 21805242578776898427282373)
              ·
                refine ⟨4088482983520668455115445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21805242578776898427282373 4088482983520668455115445)
                ·
                  refine ⟨383295279705062667667073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4088482983520668455115445 383295279705062667667073)
                  ·
                    rfl

theorem cell21_1679546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_1679546 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679546 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679546 prefixEnd_1679546 := by exact prefixLift 1679546
  have htrace : WordTrace (prefixWord ++ tailWord_1679546) baseStart_1679546 baseEnd_1679546 := by
    simpa [prefixWord, tailWord_1679546, baseEnd_1679546] using wordTrace_append hprefix tailTrace_1679546
  have hstable : (prefixWord ++ tailWord_1679546).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679546).length < 2 ^ (prefixWord ++ tailWord_1679546).sum := by decide
  have hdescent : baseEnd_1679546 < baseStart_1679546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679563 : List Nat := [1, 1, 1, 1, 3, 2, 4, 5, 3]
def baseStart_1679563 : Nat := 118140960795 + 1679563 * 2 ^ 59
def prefixEnd_1679563 : Nat := 4983230072969 + 3 ^ 40 * 1679563 * 2
def baseEnd_1679563 : Nat := 383299159336674415883705

theorem tailTrace_1679563 : CollatzResearch.WordTrace tailWord_1679563 prefixEnd_1679563 383299159336674415883705 := by
  unfold tailWord_1679563
  simp only [CollatzResearch.WordTrace]
  refine ⟨61258695214237572368491343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40839130142825048245660895 61258695214237572368491343)
  ·
    refine ⟨91888042821356358552737015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61258695214237572368491343 91888042821356358552737015)
    ·
      refine ⟨137832064232034537829105523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91888042821356358552737015 137832064232034537829105523)
      ·
        refine ⟨206748096348051806743658285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137832064232034537829105523 206748096348051806743658285)
        ·
          refine ⟨77530536130519427528871857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206748096348051806743658285 77530536130519427528871857)
          ·
            refine ⟨58147902097889570646653893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77530536130519427528871857 58147902097889570646653893)
            ·
              refine ⟨10902731643354294496247605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58147902097889570646653893 10902731643354294496247605)
              ·
                refine ⟨1022131091564465109023213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10902731643354294496247605 1022131091564465109023213)
                ·
                  refine ⟨383299159336674415883705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022131091564465109023213 383299159336674415883705)
                  ·
                    rfl

theorem cell21_1679563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 5, 3].length) (baseStart_1679563 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679563 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679563 prefixEnd_1679563 := by exact prefixLift 1679563
  have htrace : WordTrace (prefixWord ++ tailWord_1679563) baseStart_1679563 baseEnd_1679563 := by
    simpa [prefixWord, tailWord_1679563, baseEnd_1679563] using wordTrace_append hprefix tailTrace_1679563
  have hstable : (prefixWord ++ tailWord_1679563).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679563).length < 2 ^ (prefixWord ++ tailWord_1679563).sum := by decide
  have hdescent : baseEnd_1679563 < baseStart_1679563 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679577 : List Nat := [1, 2, 1, 2, 3, 1, 3, 4, 4]
def baseStart_1679577 : Nat := 118140960795 + 1679577 * 2 ^ 59
def prefixEnd_1679577 : Nat := 4983230072969 + 3 ^ 40 * 1679577 * 2
def baseEnd_1679577 : Nat := 383302354327413502650343

theorem tailTrace_1679577 : CollatzResearch.WordTrace tailWord_1679577 prefixEnd_1679577 383302354327413502650343 := by
  unfold tailWord_1679577
  simp only [CollatzResearch.WordTrace]
  refine ⟨61259205836186852759500985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40839470557457901839667323 61259205836186852759500985)
  ·
    refine ⟨45944404377140139569625739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61259205836186852759500985 45944404377140139569625739)
    ·
      refine ⟨68916606565710209354438609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45944404377140139569625739 68916606565710209354438609)
      ·
        refine ⟨51687454924282657015828957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68916606565710209354438609 51687454924282657015828957)
        ·
          refine ⟨19382795596605996380935859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51687454924282657015828957 19382795596605996380935859)
          ·
            refine ⟨29074193394908994571403789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19382795596605996380935859 29074193394908994571403789)
            ·
              refine ⟨10902822523090872964276421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29074193394908994571403789 10902822523090872964276421)
              ·
                refine ⟨2044279223079538680801829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10902822523090872964276421 2044279223079538680801829)
                ·
                  refine ⟨383302354327413502650343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044279223079538680801829 383302354327413502650343)
                  ·
                    rfl

theorem cell21_1679577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 4, 4].length) (baseStart_1679577 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679577 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679577 prefixEnd_1679577 := by exact prefixLift 1679577
  have htrace : WordTrace (prefixWord ++ tailWord_1679577) baseStart_1679577 baseEnd_1679577 := by
    simpa [prefixWord, tailWord_1679577, baseEnd_1679577] using wordTrace_append hprefix tailTrace_1679577
  have hstable : (prefixWord ++ tailWord_1679577).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679577).length < 2 ^ (prefixWord ++ tailWord_1679577).sum := by decide
  have hdescent : baseEnd_1679577 < baseStart_1679577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679639 : List Nat := [1, 1, 3, 4, 1, 3, 2, 1, 5]
def baseStart_1679639 : Nat := 118140960795 + 1679639 * 2 ^ 59
def prefixEnd_1679639 : Nat := 4983230072969 + 3 ^ 40 * 1679639 * 2
def baseEnd_1679639 : Nat := 383316503572115172616883

theorem tailTrace_1679639 : CollatzResearch.WordTrace tailWord_1679639 prefixEnd_1679639 383316503572115172616883 := by
  unfold tailWord_1679639
  simp only [CollatzResearch.WordTrace]
  refine ⟨61261467161962237348257971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40840978107974824898838647 61261467161962237348257971)
  ·
    refine ⟨91892200742943356022386957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61261467161962237348257971 91892200742943356022386957)
    ·
      refine ⟨34459575278603758508395109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91892200742943356022386957 34459575278603758508395109)
      ·
        refine ⟨6461170364738204720324083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34459575278603758508395109 6461170364738204720324083)
        ·
          refine ⟨9691755547107307080486125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461170364738204720324083 9691755547107307080486125)
          ·
            refine ⟨3634408330165240155182297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9691755547107307080486125 3634408330165240155182297)
            ·
              refine ⟨2725806247623930116386723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3634408330165240155182297 2725806247623930116386723)
              ·
                refine ⟨4088709371435895174580085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2725806247623930116386723 4088709371435895174580085)
                ·
                  refine ⟨383316503572115172616883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4088709371435895174580085 383316503572115172616883)
                  ·
                    rfl

theorem cell21_1679639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 5].length) (baseStart_1679639 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679639 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679639 prefixEnd_1679639 := by exact prefixLift 1679639
  have htrace : WordTrace (prefixWord ++ tailWord_1679639) baseStart_1679639 baseEnd_1679639 := by
    simpa [prefixWord, tailWord_1679639, baseEnd_1679639] using wordTrace_append hprefix tailTrace_1679639
  have hstable : (prefixWord ++ tailWord_1679639).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679639).length < 2 ^ (prefixWord ++ tailWord_1679639).sum := by decide
  have hdescent : baseEnd_1679639 < baseStart_1679639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679667 : List Nat := [1, 1, 1, 2, 5, 1, 3, 7]
def baseStart_1679667 : Nat := 118140960795 + 1679667 * 2 ^ 59
def prefixEnd_1679667 : Nat := 4983230072969 + 3 ^ 40 * 1679667 * 2
def baseEnd_1679667 : Nat := 127774297851197782050053

theorem tailTrace_1679667 : CollatzResearch.WordTrace tailWord_1679667 prefixEnd_1679667 127774297851197782050053 := by
  unfold tailWord_1679667
  simp only [CollatzResearch.WordTrace]
  refine ⟨61262488405860798130277255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40841658937240532086851503 61262488405860798130277255)
  ·
    refine ⟨91893732608791197195415883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61262488405860798130277255 91893732608791197195415883)
    ·
      refine ⟨137840598913186795793123825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91893732608791197195415883 137840598913186795793123825)
      ·
        refine ⟨103380449184890096844842869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137840598913186795793123825 103380449184890096844842869)
        ·
          refine ⟨9691917111083446579204019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103380449184890096844842869 9691917111083446579204019)
          ·
            refine ⟨14537875666625169868806029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9691917111083446579204019 14537875666625169868806029)
            ·
              refine ⟨5451703374984438700802261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14537875666625169868806029 5451703374984438700802261)
              ·
                refine ⟨127774297851197782050053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5451703374984438700802261 127774297851197782050053)
                ·
                  rfl

theorem cell21_1679667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 7].length) (baseStart_1679667 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679667 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679667 prefixEnd_1679667 := by exact prefixLift 1679667
  have htrace : WordTrace (prefixWord ++ tailWord_1679667) baseStart_1679667 baseEnd_1679667 := by
    simpa [prefixWord, tailWord_1679667, baseEnd_1679667] using wordTrace_append hprefix tailTrace_1679667
  have hstable : (prefixWord ++ tailWord_1679667).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679667).length < 2 ^ (prefixWord ++ tailWord_1679667).sum := by decide
  have hdescent : baseEnd_1679667 < baseStart_1679667 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679673 : List Nat := [1, 2, 1, 6, 1, 3, 1, 3, 3]
def baseStart_1679673 : Nat := 118140960795 + 1679673 * 2 ^ 59
def prefixEnd_1679673 : Nat := 4983230072969 + 3 ^ 40 * 1679673 * 2
def baseEnd_1679673 : Nat := 383324262835338669050147

theorem tailTrace_1679673 : CollatzResearch.WordTrace tailWord_1679673 prefixEnd_1679673 383324262835338669050147 := by
  unfold tailWord_1679673
  simp only [CollatzResearch.WordTrace]
  refine ⟨61262707243839061154995673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40841804829226040769997115 61262707243839061154995673)
  ·
    refine ⟨45947030432879295866246755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61262707243839061154995673 45947030432879295866246755)
    ·
      refine ⟨68920545649318943799370133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45947030432879295866246755 68920545649318943799370133)
      ·
        refine ⟨3230650577311825490595475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68920545649318943799370133 3230650577311825490595475)
        ·
          refine ⟨4845975865967738235893213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3230650577311825490595475 4845975865967738235893213)
          ·
            refine ⟨1817240949737901838459955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4845975865967738235893213 1817240949737901838459955)
            ·
              refine ⟨2725861424606852757689933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817240949737901838459955 2725861424606852757689933)
              ·
                refine ⟨1022198034227569784133725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2725861424606852757689933 1022198034227569784133725)
                ·
                  refine ⟨383324262835338669050147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022198034227569784133725 383324262835338669050147)
                  ·
                    rfl

theorem cell21_1679673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 3, 3].length) (baseStart_1679673 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679673 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679673 prefixEnd_1679673 := by exact prefixLift 1679673
  have htrace : WordTrace (prefixWord ++ tailWord_1679673) baseStart_1679673 baseEnd_1679673 := by
    simpa [prefixWord, tailWord_1679673, baseEnd_1679673] using wordTrace_append hprefix tailTrace_1679673
  have hstable : (prefixWord ++ tailWord_1679673).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679673).length < 2 ^ (prefixWord ++ tailWord_1679673).sum := by decide
  have hdescent : baseEnd_1679673 < baseStart_1679673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679766 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 5]
def baseStart_1679766 : Nat := 118140960795 + 1679766 * 2 ^ 59
def prefixEnd_1679766 : Nat := 4983230072969 + 3 ^ 40 * 1679766 * 2
def baseEnd_1679766 : Nat := 383345486702391173999957

theorem tailTrace_1679766 : CollatzResearch.WordTrace tailWord_1679766 prefixEnd_1679766 383345486702391173999957 := by
  unfold tailWord_1679766
  simp only [CollatzResearch.WordTrace]
  refine ⟨3829131202031383627383197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40844066155001425358754101 3829131202031383627383197)
  ·
    refine ⟨1435924200761768860268699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3829131202031383627383197 1435924200761768860268699)
    ·
      refine ⟨2153886301142653290403049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1435924200761768860268699 2153886301142653290403049)
      ·
        refine ⟨1615414725856989967802287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2153886301142653290403049 1615414725856989967802287)
        ·
          refine ⟨2423122088785484951703431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615414725856989967802287 2423122088785484951703431)
          ·
            refine ⟨3634683133178227427555147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423122088785484951703431 3634683133178227427555147)
            ·
              refine ⟨5452024699767341141332721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634683133178227427555147 5452024699767341141332721)
              ·
                refine ⟨4089018524825505855999541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5452024699767341141332721 4089018524825505855999541)
                ·
                  refine ⟨383345486702391173999957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4089018524825505855999541 383345486702391173999957)
                  ·
                    rfl

theorem cell21_1679766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 5].length) (baseStart_1679766 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679766 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679766 prefixEnd_1679766 := by exact prefixLift 1679766
  have htrace : WordTrace (prefixWord ++ tailWord_1679766) baseStart_1679766 baseEnd_1679766 := by
    simpa [prefixWord, tailWord_1679766, baseEnd_1679766] using wordTrace_append hprefix tailTrace_1679766
  have hstable : (prefixWord ++ tailWord_1679766).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679766).length < 2 ^ (prefixWord ++ tailWord_1679766).sum := by decide
  have hdescent : baseEnd_1679766 < baseStart_1679766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679788 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 6]
def baseStart_1679788 : Nat := 118140960795 + 1679788 * 2 ^ 59
def prefixEnd_1679788 : Nat := 4983230072969 + 3 ^ 40 * 1679788 * 2
def baseEnd_1679788 : Nat := 383350507402124024633245

theorem tailTrace_1679788 : CollatzResearch.WordTrace tailWord_1679788 prefixEnd_1679788 383350507402124024633245 := by
  unfold tailWord_1679788
  simp only [CollatzResearch.WordTrace]
  refine ⟨30633450819211217897716009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40844601092281623863621345 30633450819211217897716009)
  ·
    refine ⟨22975088114408413423287007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30633450819211217897716009 22975088114408413423287007)
    ·
      refine ⟨34462632171612620134930511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22975088114408413423287007 34462632171612620134930511)
      ·
        refine ⟨51693948257418930202395767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34462632171612620134930511 51693948257418930202395767)
        ·
          refine ⟨77540922386128395303593651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51693948257418930202395767 77540922386128395303593651)
          ·
            refine ⟨116311383579192592955390477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77540922386128395303593651 116311383579192592955390477)
            ·
              refine ⟨43616768842197222358271429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116311383579192592955390477 43616768842197222358271429)
              ·
                refine ⟨8178144157911979192175893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43616768842197222358271429 8178144157911979192175893)
                ·
                  refine ⟨383350507402124024633245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8178144157911979192175893 383350507402124024633245)
                  ·
                    rfl

theorem cell21_1679788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 6].length) (baseStart_1679788 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679788 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679788 prefixEnd_1679788 := by exact prefixLift 1679788
  have htrace : WordTrace (prefixWord ++ tailWord_1679788) baseStart_1679788 baseEnd_1679788 := by
    simpa [prefixWord, tailWord_1679788, baseEnd_1679788] using wordTrace_append hprefix tailTrace_1679788
  have hstable : (prefixWord ++ tailWord_1679788).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679788).length < 2 ^ (prefixWord ++ tailWord_1679788).sum := by decide
  have hdescent : baseEnd_1679788 < baseStart_1679788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679805 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 6]
def baseStart_1679805 : Nat := 118140960795 + 1679805 * 2 ^ 59
def prefixEnd_1679805 : Nat := 4983230072969 + 3 ^ 40 * 1679805 * 2
def baseEnd_1679805 : Nat := 383354387033735772849877

theorem tailTrace_1679805 : CollatzResearch.WordTrace tailWord_1679805 prefixEnd_1679805 383354387033735772849877 := by
  unfold tailWord_1679805
  simp only [CollatzResearch.WordTrace]
  refine ⟨61267521679360847698800869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40845014452907231799200579 61267521679360847698800869)
  ·
    refine ⟨11487660314880158943525163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61267521679360847698800869 11487660314880158943525163)
    ·
      refine ⟨17231490472320238415287745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11487660314880158943525163 17231490472320238415287745)
      ·
        refine ⟨12923617854240178811465809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17231490472320238415287745 12923617854240178811465809)
        ·
          refine ⟨9692713390680134108599357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12923617854240178811465809 9692713390680134108599357)
          ·
            refine ⟨3634767521505050290724759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9692713390680134108599357 3634767521505050290724759)
            ·
              refine ⟨5452151282257575436087139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3634767521505050290724759 5452151282257575436087139)
              ·
                refine ⟨8178226923386363154130709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5452151282257575436087139 8178226923386363154130709)
                ·
                  refine ⟨383354387033735772849877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8178226923386363154130709 383354387033735772849877)
                  ·
                    rfl

theorem cell21_1679805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_1679805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679805 prefixEnd_1679805 := by exact prefixLift 1679805
  have htrace : WordTrace (prefixWord ++ tailWord_1679805) baseStart_1679805 baseEnd_1679805 := by
    simpa [prefixWord, tailWord_1679805, baseEnd_1679805] using wordTrace_append hprefix tailTrace_1679805
  have hstable : (prefixWord ++ tailWord_1679805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679805).length < 2 ^ (prefixWord ++ tailWord_1679805).sum := by decide
  have hdescent : baseEnd_1679805 < baseStart_1679805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679864 : List Nat := [2, 1, 2, 1, 1, 4, 1, 3, 6]
def baseStart_1679864 : Nat := 118140960795 + 1679864 * 2 ^ 59
def prefixEnd_1679864 : Nat := 4983230072969 + 3 ^ 40 * 1679864 * 2
def baseEnd_1679864 : Nat := 383367851637564781366423

theorem tailTrace_1679864 : CollatzResearch.WordTrace tailWord_1679864 prefixEnd_1679864 383367851637564781366423 := by
  unfold tailWord_1679864
  simp only [CollatzResearch.WordTrace]
  refine ⟨30634836793073550387599323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40846449057431400516799097 30634836793073550387599323)
  ·
    refine ⟨45952255189610325581398985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30634836793073550387599323 45952255189610325581398985)
    ·
      refine ⟨34464191392207744186049239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45952255189610325581398985 34464191392207744186049239)
      ·
        refine ⟨51696287088311616279073859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34464191392207744186049239 51696287088311616279073859)
        ·
          refine ⟨77544430632467424418610789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51696287088311616279073859 77544430632467424418610789)
          ·
            refine ⟨14539580743587642078489523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77544430632467424418610789 14539580743587642078489523)
            ·
              refine ⟨21809371115381463117734285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14539580743587642078489523 21809371115381463117734285)
              ·
                refine ⟨8178514168268048669150357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21809371115381463117734285 8178514168268048669150357)
                ·
                  refine ⟨383367851637564781366423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8178514168268048669150357 383367851637564781366423)
                  ·
                    rfl

theorem cell21_1679864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 6].length) (baseStart_1679864 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679864 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679864 prefixEnd_1679864 := by exact prefixLift 1679864
  have htrace : WordTrace (prefixWord ++ tailWord_1679864) baseStart_1679864 baseEnd_1679864 := by
    simpa [prefixWord, tailWord_1679864, baseEnd_1679864] using wordTrace_append hprefix tailTrace_1679864
  have hstable : (prefixWord ++ tailWord_1679864).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679864).length < 2 ^ (prefixWord ++ tailWord_1679864).sum := by decide
  have hdescent : baseEnd_1679864 < baseStart_1679864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679918 : List Nat := [4, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_1679918 : Nat := 118140960795 + 1679918 * 2 ^ 59
def prefixEnd_1679918 : Nat := 4983230072969 + 3 ^ 40 * 1679918 * 2
def baseEnd_1679918 : Nat := 383380175173272687466313

theorem tailTrace_1679918 : CollatzResearch.WordTrace tailWord_1679918 prefixEnd_1679918 383380175173272687466313 := by
  unfold tailWord_1679918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658955390993933499708051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40847762085300978665109605 7658955390993933499708051)
  ·
    refine ⟨11488433086490900249562077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658955390993933499708051 11488433086490900249562077)
    ·
      refine ⟨4308162407434087593585779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11488433086490900249562077 4308162407434087593585779)
      ·
        refine ⟨6462243611151131390378669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308162407434087593585779 6462243611151131390378669)
        ·
          refine ⟨2423341354181674271392001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6462243611151131390378669 2423341354181674271392001)
          ·
            refine ⟨1817506015636255703544001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423341354181674271392001 1817506015636255703544001)
            ·
              refine ⟨1363129511727191777658001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817506015636255703544001 1363129511727191777658001)
              ·
                refine ⟨1022347133795393833243501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363129511727191777658001 1022347133795393833243501)
                ·
                  refine ⟨383380175173272687466313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022347133795393833243501 383380175173272687466313)
                  ·
                    rfl

theorem cell21_1679918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_1679918 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679918 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679918 prefixEnd_1679918 := by exact prefixLift 1679918
  have htrace : WordTrace (prefixWord ++ tailWord_1679918) baseStart_1679918 baseEnd_1679918 := by
    simpa [prefixWord, tailWord_1679918, baseEnd_1679918] using wordTrace_append hprefix tailTrace_1679918
  have hstable : (prefixWord ++ tailWord_1679918).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679918).length < 2 ^ (prefixWord ++ tailWord_1679918).sum := by decide
  have hdescent : baseEnd_1679918 < baseStart_1679918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1679966 : List Nat := [4, 4, 1, 2, 2, 1, 1, 2, 4]
def baseStart_1679966 : Nat := 118140960795 + 1679966 * 2 ^ 59
def prefixEnd_1679966 : Nat := 4983230072969 + 3 ^ 40 * 1679966 * 2
def baseEnd_1679966 : Nat := 383391129427235270666215

theorem tailTrace_1679966 : CollatzResearch.WordTrace tailWord_1679966 prefixEnd_1679966 383391129427235270666215 := by
  unfold tailWord_1679966
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659174228972196524426469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40848929221185048130274501 7659174228972196524426469)
  ·
    refine ⟨1436095167932286848329963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7659174228972196524426469 1436095167932286848329963)
    ·
      refine ⟨2154142751898430272494945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436095167932286848329963 2154142751898430272494945)
      ·
        refine ⟨1615607063923822704371209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2154142751898430272494945 1615607063923822704371209)
        ·
          refine ⟨1211705297942867028278407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615607063923822704371209 1211705297942867028278407)
          ·
            refine ⟨1817557946914300542417611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211705297942867028278407 1817557946914300542417611)
            ·
              refine ⟨2726336920371450813626417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817557946914300542417611 2726336920371450813626417)
              ·
                refine ⟨2044752690278588110219813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726336920371450813626417 2044752690278588110219813)
                ·
                  refine ⟨383391129427235270666215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044752690278588110219813 383391129427235270666215)
                  ·
                    rfl

theorem cell21_1679966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_1679966 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1679966 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1679966 prefixEnd_1679966 := by exact prefixLift 1679966
  have htrace : WordTrace (prefixWord ++ tailWord_1679966) baseStart_1679966 baseEnd_1679966 := by
    simpa [prefixWord, tailWord_1679966, baseEnd_1679966] using wordTrace_append hprefix tailTrace_1679966
  have hstable : (prefixWord ++ tailWord_1679966).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1679966).length < 2 ^ (prefixWord ++ tailWord_1679966).sum := by decide
  have hdescent : baseEnd_1679966 < baseStart_1679966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1679966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680036 : List Nat := [2, 3, 1, 2, 2, 1, 5, 2, 3]
def baseStart_1680036 : Nat := 118140960795 + 1680036 * 2 ^ 59
def prefixEnd_1680036 : Nat := 4983230072969 + 3 ^ 40 * 1680036 * 2
def baseEnd_1680036 : Nat := 383407104380930704499405

theorem tailTrace_1680036 : CollatzResearch.WordTrace tailWord_1680036 prefixEnd_1680036 383407104380930704499405 := by
  unfold tailWord_1680036
  simp only [CollatzResearch.WordTrace]
  refine ⟨30637973470761987075229981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40850631294349316100306641 30637973470761987075229981)
  ·
    refine ⟨11489240051535745153211243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30637973470761987075229981 11489240051535745153211243)
    ·
      refine ⟨17233860077303617729816865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11489240051535745153211243 17233860077303617729816865)
      ·
        refine ⟨12925395057977713297362649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17233860077303617729816865 12925395057977713297362649)
        ·
          refine ⟨9694046293483284973021987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12925395057977713297362649 9694046293483284973021987)
          ·
            refine ⟨14541069440224927459532981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9694046293483284973021987 14541069440224927459532981)
            ·
              refine ⟨1363225260021086949331217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14541069440224927459532981 1363225260021086949331217)
              ·
                refine ⟨1022418945015815211998413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363225260021086949331217 1022418945015815211998413)
                ·
                  refine ⟨383407104380930704499405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022418945015815211998413 383407104380930704499405)
                  ·
                    rfl

theorem cell21_1680036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_1680036 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680036 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680036 prefixEnd_1680036 := by exact prefixLift 1680036
  have htrace : WordTrace (prefixWord ++ tailWord_1680036) baseStart_1680036 baseEnd_1680036 := by
    simpa [prefixWord, tailWord_1680036, baseEnd_1680036] using wordTrace_append hprefix tailTrace_1680036
  have hstable : (prefixWord ++ tailWord_1680036).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680036).length < 2 ^ (prefixWord ++ tailWord_1680036).sum := by decide
  have hdescent : baseEnd_1680036 < baseStart_1680036 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680047 : List Nat := [1, 1, 2, 1, 2, 6, 2, 6]
def baseStart_1680047 : Nat := 118140960795 + 1680047 * 2 ^ 59
def prefixEnd_1680047 : Nat := 4983230072969 + 3 ^ 40 * 1680047 * 2
def baseEnd_1680047 : Nat := 127803204910265709938683

theorem tailTrace_1680047 : CollatzResearch.WordTrace tailWord_1680047 prefixEnd_1680047 127803204910265709938683 := by
  unfold tailWord_1680047
  simp only [CollatzResearch.WordTrace]
  refine ⟨61276348144484123029110395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40850898762989415352740263 61276348144484123029110395)
  ·
    refine ⟨91914522216726184543665593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61276348144484123029110395 91914522216726184543665593)
    ·
      refine ⟨68935891662544638407749195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91914522216726184543665593 68935891662544638407749195)
      ·
        refine ⟨103403837493816957611623793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68935891662544638407749195 103403837493816957611623793)
        ·
          refine ⟨77552878120362718208717845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103403837493816957611623793 77552878120362718208717845)
          ·
            refine ⟨3635291161892002416033649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77552878120362718208717845 3635291161892002416033649)
            ·
              refine ⟨2726468371419001812025237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635291161892002416033649 2726468371419001812025237)
              ·
                refine ⟨127803204910265709938683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2726468371419001812025237 127803204910265709938683)
                ·
                  rfl

theorem cell21_1680047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 6].length) (baseStart_1680047 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680047 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680047 prefixEnd_1680047 := by exact prefixLift 1680047
  have htrace : WordTrace (prefixWord ++ tailWord_1680047) baseStart_1680047 baseEnd_1680047 := by
    simpa [prefixWord, tailWord_1680047, baseEnd_1680047] using wordTrace_append hprefix tailTrace_1680047
  have hstable : (prefixWord ++ tailWord_1680047).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680047).length < 2 ^ (prefixWord ++ tailWord_1680047).sum := by decide
  have hdescent : baseEnd_1680047 < baseStart_1680047 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680095 : List Nat := [1, 1, 2, 3, 2, 4, 1, 4, 3]
def baseStart_1680095 : Nat := 118140960795 + 1680095 * 2 ^ 59
def prefixEnd_1680095 : Nat := 4983230072969 + 3 ^ 40 * 1680095 * 2
def baseEnd_1680095 : Nat := 383420568984759713015951

theorem tailTrace_1680095 : CollatzResearch.WordTrace tailWord_1680095 prefixEnd_1680095 383420568984759713015951 := by
  unfold tailWord_1680095
  simp only [CollatzResearch.WordTrace]
  refine ⟨61278098848310227226857739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40852065898873484817905159 61278098848310227226857739)
  ·
    refine ⟨91917148272465340840286609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61278098848310227226857739 91917148272465340840286609)
    ·
      refine ⟨68937861204349005630214957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91917148272465340840286609 68937861204349005630214957)
      ·
        refine ⟨25851697951630877111330609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68937861204349005630214957 25851697951630877111330609)
        ·
          refine ⟨19388773463723157833497957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25851697951630877111330609 19388773463723157833497957)
          ·
            refine ⟨3635395024448092093780867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19388773463723157833497957 3635395024448092093780867)
            ·
              refine ⟨5453092536672138140671301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635395024448092093780867 5453092536672138140671301)
              ·
                refine ⟨1022454850626025901375869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5453092536672138140671301 1022454850626025901375869)
                ·
                  refine ⟨383420568984759713015951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022454850626025901375869 383420568984759713015951)
                  ·
                    rfl

theorem cell21_1680095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 3].length) (baseStart_1680095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680095 prefixEnd_1680095 := by exact prefixLift 1680095
  have htrace : WordTrace (prefixWord ++ tailWord_1680095) baseStart_1680095 baseEnd_1680095 := by
    simpa [prefixWord, tailWord_1680095, baseEnd_1680095] using wordTrace_append hprefix tailTrace_1680095
  have hstable : (prefixWord ++ tailWord_1680095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680095).length < 2 ^ (prefixWord ++ tailWord_1680095).sum := by decide
  have hdescent : baseEnd_1680095 < baseStart_1680095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680109 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 4]
def baseStart_1680109 : Nat := 118140960795 + 1680109 * 2 ^ 59
def prefixEnd_1680109 : Nat := 4983230072969 + 3 ^ 40 * 1680109 * 2
def baseEnd_1680109 : Nat := 383423763975498799782589

theorem tailTrace_1680109 : CollatzResearch.WordTrace tailWord_1680109 prefixEnd_1680109 383423763975498799782589 := by
  unfold tailWord_1680109
  simp only [CollatzResearch.WordTrace]
  refine ⟨61278609470259507617867381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40852406313506338411911587 61278609470259507617867381)
  ·
    refine ⟨5744869637836828839175067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61278609470259507617867381 5744869637836828839175067)
    ·
      refine ⟨8617304456755243258762601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5744869637836828839175067 8617304456755243258762601)
      ·
        refine ⟨6462978342566432444071951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8617304456755243258762601 6462978342566432444071951)
        ·
          refine ⟨9694467513849648666107927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462978342566432444071951 9694467513849648666107927)
          ·
            refine ⟨14541701270774472999161891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9694467513849648666107927 14541701270774472999161891)
            ·
              refine ⟨21812551906161709498742837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14541701270774472999161891 21812551906161709498742837)
              ·
                refine ⟨2044926741202660265507141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21812551906161709498742837 2044926741202660265507141)
                ·
                  refine ⟨383423763975498799782589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2044926741202660265507141 383423763975498799782589)
                  ·
                    rfl

theorem cell21_1680109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 4].length) (baseStart_1680109 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680109 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680109 prefixEnd_1680109 := by exact prefixLift 1680109
  have htrace : WordTrace (prefixWord ++ tailWord_1680109) baseStart_1680109 baseEnd_1680109 := by
    simpa [prefixWord, tailWord_1680109, baseEnd_1680109] using wordTrace_append hprefix tailTrace_1680109
  have hstable : (prefixWord ++ tailWord_1680109).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680109).length < 2 ^ (prefixWord ++ tailWord_1680109).sum := by decide
  have hdescent : baseEnd_1680109 < baseStart_1680109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680154 : List Nat := [3, 1, 1, 3, 2, 1, 4, 1, 5]
def baseStart_1680154 : Nat := 118140960795 + 1680154 * 2 ^ 59
def prefixEnd_1680154 : Nat := 4983230072969 + 3 ^ 40 * 1680154 * 2
def baseEnd_1680154 : Nat := 383434033588588721532497

theorem tailTrace_1680154 : CollatzResearch.WordTrace tailWord_1680154 prefixEnd_1680154 383434033588588721532497 := by
  unfold tailWord_1680154
  simp only [CollatzResearch.WordTrace]
  refine ⟨15320062688774120075813879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40853500503397653535503677 15320062688774120075813879)
  ·
    refine ⟨22980094033161180113720819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15320062688774120075813879 22980094033161180113720819)
    ·
      refine ⟨34470141049741770170581229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22980094033161180113720819 34470141049741770170581229)
      ·
        refine ⟨12926302893653163813967961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34470141049741770170581229 12926302893653163813967961)
        ·
          refine ⟨9694727170239872860475971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12926302893653163813967961 9694727170239872860475971)
          ·
            refine ⟨14542090755359809290713957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9694727170239872860475971 14542090755359809290713957)
            ·
              refine ⟨2726642016629964242008867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14542090755359809290713957 2726642016629964242008867)
              ·
                refine ⟨4089963024944946363013301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726642016629964242008867 4089963024944946363013301)
                ·
                  refine ⟨383434033588588721532497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4089963024944946363013301 383434033588588721532497)
                  ·
                    rfl

theorem cell21_1680154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 1, 5].length) (baseStart_1680154 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680154 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680154 prefixEnd_1680154 := by exact prefixLift 1680154
  have htrace : WordTrace (prefixWord ++ tailWord_1680154) baseStart_1680154 baseEnd_1680154 := by
    simpa [prefixWord, tailWord_1680154, baseEnd_1680154] using wordTrace_append hprefix tailTrace_1680154
  have hstable : (prefixWord ++ tailWord_1680154).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680154).length < 2 ^ (prefixWord ++ tailWord_1680154).sum := by decide
  have hdescent : baseEnd_1680154 < baseStart_1680154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680205 : List Nat := [1, 6, 1, 2, 3, 1, 1, 1, 5]
def baseStart_1680205 : Nat := 118140960795 + 1680205 * 2 ^ 59
def prefixEnd_1680205 : Nat := 4983230072969 + 3 ^ 40 * 1680205 * 2
def baseEnd_1680205 : Nat := 383445672483423966182393

theorem tailTrace_1680205 : CollatzResearch.WordTrace tailWord_1680205 prefixEnd_1680205 383445672483423966182393 := by
  unfold tailWord_1680205
  simp only [CollatzResearch.WordTrace]
  refine ⟨61282110877911716013362069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40854740585274477342241379 61282110877911716013362069)
  ·
    refine ⟨2872598947402111688126347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61282110877911716013362069 2872598947402111688126347)
    ·
      refine ⟨4308898421103167532189521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2872598947402111688126347 4308898421103167532189521)
      ·
        refine ⟨3231673815827375649142141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4308898421103167532189521 3231673815827375649142141)
        ·
          refine ⟨1211877680935265868428303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3231673815827375649142141 1211877680935265868428303)
          ·
            refine ⟨1817816521402898802642455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211877680935265868428303 1817816521402898802642455)
            ·
              refine ⟨2726724782104348203963683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817816521402898802642455 2726724782104348203963683)
              ·
                refine ⟨4090087173156522305945525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2726724782104348203963683 4090087173156522305945525)
                ·
                  refine ⟨383445672483423966182393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4090087173156522305945525 383445672483423966182393)
                  ·
                    rfl

theorem cell21_1680205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_1680205 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680205 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680205 prefixEnd_1680205 := by exact prefixLift 1680205
  have htrace : WordTrace (prefixWord ++ tailWord_1680205) baseStart_1680205 baseEnd_1680205 := by
    simpa [prefixWord, tailWord_1680205, baseEnd_1680205] using wordTrace_append hprefix tailTrace_1680205
  have hstable : (prefixWord ++ tailWord_1680205).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680205).length < 2 ^ (prefixWord ++ tailWord_1680205).sum := by decide
  have hdescent : baseEnd_1680205 < baseStart_1680205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680261 : List Nat := [1, 3, 1, 1, 3, 4, 2, 2, 4]
def baseStart_1680261 : Nat := 118140960795 + 1680261 * 2 ^ 59
def prefixEnd_1680261 : Nat := 4983230072969 + 3 ^ 40 * 1680261 * 2
def baseEnd_1680261 : Nat := 383458452446380313248945

theorem tailTrace_1680261 : CollatzResearch.WordTrace tailWord_1680261 prefixEnd_1680261 383458452446380313248945 := by
  unfold tailWord_1680261
  simp only [CollatzResearch.WordTrace]
  refine ⟨61284153365708837577400637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40856102243805891718267091 61284153365708837577400637)
  ·
    refine ⟨22981557512140814091525239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61284153365708837577400637 22981557512140814091525239)
    ·
      refine ⟨34472336268211221137287859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22981557512140814091525239 34472336268211221137287859)
      ·
        refine ⟨51708504402316831705931789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34472336268211221137287859 51708504402316831705931789)
        ·
          refine ⟨19390689150868811889724421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51708504402316831705931789 19390689150868811889724421)
          ·
            refine ⟨3635754215787902229323329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19390689150868811889724421 3635754215787902229323329)
            ·
              refine ⟨2726815661840926671992497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3635754215787902229323329 2726815661840926671992497)
              ·
                refine ⟨2045111746380695003994373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726815661840926671992497 2045111746380695003994373)
                ·
                  refine ⟨383458452446380313248945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045111746380695003994373 383458452446380313248945)
                  ·
                    rfl

theorem cell21_1680261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_1680261 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680261 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680261 prefixEnd_1680261 := by exact prefixLift 1680261
  have htrace : WordTrace (prefixWord ++ tailWord_1680261) baseStart_1680261 baseEnd_1680261 := by
    simpa [prefixWord, tailWord_1680261, baseEnd_1680261] using wordTrace_append hprefix tailTrace_1680261
  have hstable : (prefixWord ++ tailWord_1680261).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680261).length < 2 ^ (prefixWord ++ tailWord_1680261).sum := by decide
  have hdescent : baseEnd_1680261 < baseStart_1680261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680264 : List Nat := [2, 1, 3, 3, 2, 1, 4, 2, 3]
def baseStart_1680264 : Nat := 118140960795 + 1680264 * 2 ^ 59
def prefixEnd_1680264 : Nat := 4983230072969 + 3 ^ 40 * 1680264 * 2
def baseEnd_1680264 : Nat := 383459137087252974698939

theorem tailTrace_1680264 : CollatzResearch.WordTrace tailWord_1680264 prefixEnd_1680264 383459137087252974698939 := by
  unfold tailWord_1680264
  simp only [CollatzResearch.WordTrace]
  refine ⟨30642131392348984544879923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40856175189798646059839897 30642131392348984544879923)
  ·
    refine ⟨45963197088523476817319885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30642131392348984544879923 45963197088523476817319885)
    ·
      refine ⟨17236198908196303806494957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45963197088523476817319885 17236198908196303806494957)
      ·
        refine ⟨6463574590573613927435609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17236198908196303806494957 6463574590573613927435609)
        ·
          refine ⟨4847680942930210445576707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6463574590573613927435609 4847680942930210445576707)
          ·
            refine ⟨7271521414395315668365061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4847680942930210445576707 7271521414395315668365061)
            ·
              refine ⟨1363410265199121687818449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7271521414395315668365061 1363410265199121687818449)
              ·
                refine ⟨1022557698899341265863837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363410265199121687818449 1022557698899341265863837)
                ·
                  refine ⟨383459137087252974698939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022557698899341265863837 383459137087252974698939)
                  ·
                    rfl

theorem cell21_1680264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 4, 2, 3].length) (baseStart_1680264 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680264 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680264 prefixEnd_1680264 := by exact prefixLift 1680264
  have htrace : WordTrace (prefixWord ++ tailWord_1680264) baseStart_1680264 baseEnd_1680264 := by
    simpa [prefixWord, tailWord_1680264, baseEnd_1680264] using wordTrace_append hprefix tailTrace_1680264
  have hstable : (prefixWord ++ tailWord_1680264).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680264).length < 2 ^ (prefixWord ++ tailWord_1680264).sum := by decide
  have hdescent : baseEnd_1680264 < baseStart_1680264 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680320 : List Nat := [2, 1, 1, 2, 3, 4, 1, 1, 6]
def baseStart_1680320 : Nat := 118140960795 + 1680320 * 2 ^ 59
def prefixEnd_1680320 : Nat := 4983230072969 + 3 ^ 40 * 1680320 * 2
def baseEnd_1680320 : Nat := 383471917050209321765491

theorem tailTrace_1680320 : CollatzResearch.WordTrace tailWord_1680320 prefixEnd_1680320 383471917050209321765491 := by
  unfold tailWord_1680320
  simp only [CollatzResearch.WordTrace]
  refine ⟨30643152636247545326899207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40857536848330060435865609 30643152636247545326899207)
  ·
    refine ⟨45964728954371317990348811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30643152636247545326899207 45964728954371317990348811)
    ·
      refine ⟨68947093431556976985523217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45964728954371317990348811 68947093431556976985523217)
      ·
        refine ⟨51710320073667732739142413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68947093431556976985523217 51710320073667732739142413)
        ·
          refine ⟨19391370027625399777178405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51710320073667732739142413 19391370027625399777178405)
          ·
            refine ⟨3635881880179762458220951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19391370027625399777178405 3635881880179762458220951)
            ·
              refine ⟨5453822820269643687331427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635881880179762458220951 5453822820269643687331427)
              ·
                refine ⟨8180734230404465530997141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5453822820269643687331427 8180734230404465530997141)
                ·
                  refine ⟨383471917050209321765491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8180734230404465530997141 383471917050209321765491)
                  ·
                    rfl

theorem cell21_1680320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 6].length) (baseStart_1680320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680320 prefixEnd_1680320 := by exact prefixLift 1680320
  have htrace : WordTrace (prefixWord ++ tailWord_1680320) baseStart_1680320 baseEnd_1680320 := by
    simpa [prefixWord, tailWord_1680320, baseEnd_1680320] using wordTrace_append hprefix tailTrace_1680320
  have hstable : (prefixWord ++ tailWord_1680320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680320).length < 2 ^ (prefixWord ++ tailWord_1680320).sum := by decide
  have hdescent : baseEnd_1680320 < baseStart_1680320 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680337 : List Nat := [1, 2, 2, 1, 2, 1, 7, 1, 4]
def baseStart_1680337 : Nat := 118140960795 + 1680337 * 2 ^ 59
def prefixEnd_1680337 : Nat := 4983230072969 + 3 ^ 40 * 1680337 * 2
def baseEnd_1680337 : Nat := 383475796681821069982123

theorem tailTrace_1680337 : CollatzResearch.WordTrace tailWord_1680337 prefixEnd_1680337 383475796681821069982123 := by
  unfold tailWord_1680337
  simp only [CollatzResearch.WordTrace]
  refine ⟨61286925313433502557167265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40857950208955668371444843 61286925313433502557167265)
  ·
    refine ⟨45965193985075126917875449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61286925313433502557167265 45965193985075126917875449)
    ·
      refine ⟨34473895488806345188406587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45965193985075126917875449 34473895488806345188406587)
      ·
        refine ⟨51710843233209517782609881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34473895488806345188406587 51710843233209517782609881)
        ·
          refine ⟨38783132424907138336957411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51710843233209517782609881 38783132424907138336957411)
          ·
            refine ⟨58174698637360707505436117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38783132424907138336957411 58174698637360707505436117)
            ·
              refine ⟨1363469499313141582158659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58174698637360707505436117 1363469499313141582158659)
              ·
                refine ⟨2045204248969712373237989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363469499313141582158659 2045204248969712373237989)
                ·
                  refine ⟨383475796681821069982123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045204248969712373237989 383475796681821069982123)
                  ·
                    rfl

theorem cell21_1680337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_1680337 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680337 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680337 prefixEnd_1680337 := by exact prefixLift 1680337
  have htrace : WordTrace (prefixWord ++ tailWord_1680337) baseStart_1680337 baseEnd_1680337 := by
    simpa [prefixWord, tailWord_1680337, baseEnd_1680337] using wordTrace_append hprefix tailTrace_1680337
  have hstable : (prefixWord ++ tailWord_1680337).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680337).length < 2 ^ (prefixWord ++ tailWord_1680337).sum := by decide
  have hdescent : baseEnd_1680337 < baseStart_1680337 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680351 : List Nat := [1, 1, 2, 3, 5, 1, 1, 7]
def baseStart_1680351 : Nat := 118140960795 + 1680351 * 2 ^ 59
def prefixEnd_1680351 : Nat := 4983230072969 + 3 ^ 40 * 1680351 * 2
def baseEnd_1680351 : Nat := 127826330557520052249587

theorem tailTrace_1680351 : CollatzResearch.WordTrace tailWord_1680351 prefixEnd_1680351 127826330557520052249587 := by
  unfold tailWord_1680351
  simp only [CollatzResearch.WordTrace]
  refine ⟨61287435935382782948176907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40858290623588521965451271 61287435935382782948176907)
  ·
    refine ⟨91931153903074174422265361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61287435935382782948176907 91931153903074174422265361)
    ·
      refine ⟨68948365427305630816699021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91931153903074174422265361 68948365427305630816699021)
      ·
        refine ⟨25855637035239611556262133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68948365427305630816699021 25855637035239611556262133)
        ·
          refine ⟨2423965972053713583399575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25855637035239611556262133 2423965972053713583399575)
          ·
            refine ⟨3635948958080570375099363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2423965972053713583399575 3635948958080570375099363)
            ·
              refine ⟨5453923437120855562649045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635948958080570375099363 5453923437120855562649045)
              ·
                refine ⟨127826330557520052249587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5453923437120855562649045 127826330557520052249587)
                ·
                  rfl

theorem cell21_1680351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 7].length) (baseStart_1680351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680351 prefixEnd_1680351 := by exact prefixLift 1680351
  have htrace : WordTrace (prefixWord ++ tailWord_1680351) baseStart_1680351 baseEnd_1680351 := by
    simpa [prefixWord, tailWord_1680351, baseEnd_1680351] using wordTrace_append hprefix tailTrace_1680351
  have hstable : (prefixWord ++ tailWord_1680351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680351).length < 2 ^ (prefixWord ++ tailWord_1680351).sum := by decide
  have hdescent : baseEnd_1680351 < baseStart_1680351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680357 : List Nat := [1, 3, 1, 6, 1, 2, 1, 3, 3]
def baseStart_1680357 : Nat := 118140960795 + 1680357 * 2 ^ 59
def prefixEnd_1680357 : Nat := 4983230072969 + 3 ^ 40 * 1680357 * 2
def baseEnd_1680357 : Nat := 383480360954305479648749

theorem tailTrace_1680357 : CollatzResearch.WordTrace tailWord_1680357 prefixEnd_1680357 383480360954305479648749 := by
  unfold tailWord_1680357
  simp only [CollatzResearch.WordTrace]
  refine ⟨61287654773361045972895325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40858436515574030648596883 61287654773361045972895325)
  ·
    refine ⟨22982870540010392239835747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61287654773361045972895325 22982870540010392239835747)
    ·
      refine ⟨34474305810015588359753621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22982870540010392239835747 34474305810015588359753621)
      ·
        refine ⟨1615983084844480704363451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 34474305810015588359753621 1615983084844480704363451)
        ·
          refine ⟨2423974627266721056545177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615983084844480704363451 2423974627266721056545177)
          ·
            refine ⟨1817980970450040792408883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2423974627266721056545177 1817980970450040792408883)
            ·
              refine ⟨2726971455675061188613325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817980970450040792408883 2726971455675061188613325)
              ·
                refine ⟨1022614295878147945729997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2726971455675061188613325 1022614295878147945729997)
                ·
                  refine ⟨383480360954305479648749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022614295878147945729997 383480360954305479648749)
                  ·
                    rfl

theorem cell21_1680357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_1680357 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680357 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680357 prefixEnd_1680357 := by exact prefixLift 1680357
  have htrace : WordTrace (prefixWord ++ tailWord_1680357) baseStart_1680357 baseEnd_1680357 := by
    simpa [prefixWord, tailWord_1680357, baseEnd_1680357] using wordTrace_append hprefix tailTrace_1680357
  have hstable : (prefixWord ++ tailWord_1680357).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680357).length < 2 ^ (prefixWord ++ tailWord_1680357).sum := by decide
  have hdescent : baseEnd_1680357 < baseStart_1680357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680410 : List Nat := [3, 1, 1, 3, 1, 2, 1, 9]
def baseStart_1680410 : Nat := 118140960795 + 1680410 * 2 ^ 59
def prefixEnd_1680410 : Nat := 4983230072969 + 3 ^ 40 * 1680410 * 2
def baseEnd_1680410 : Nat := 127830818758796388421769

theorem tailTrace_1680410 : CollatzResearch.WordTrace tailWord_1680410 prefixEnd_1680410 127830818758796388421769 := by
  unfold tailWord_1680410
  simp only [CollatzResearch.WordTrace]
  refine ⟨15322396960542259006143671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40859725228112690683049789 15322396960542259006143671)
  ·
    refine ⟨22983595440813388509215507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15322396960542259006143671 22983595440813388509215507)
    ·
      refine ⟨34475393161220082763823261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22983595440813388509215507 34475393161220082763823261)
      ·
        refine ⟨12928272435457531036433723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34475393161220082763823261 12928272435457531036433723)
        ·
          refine ⟨19392408653186296554650585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12928272435457531036433723 19392408653186296554650585)
          ·
            refine ⟨14544306489889722415987939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19392408653186296554650585 14544306489889722415987939)
            ·
              refine ⟨21816459734834583623981909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14544306489889722415987939 21816459734834583623981909)
              ·
                refine ⟨127830818758796388421769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21816459734834583623981909 127830818758796388421769)
                ·
                  rfl

theorem cell21_1680410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 9].length) (baseStart_1680410 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680410 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680410 prefixEnd_1680410 := by exact prefixLift 1680410
  have htrace : WordTrace (prefixWord ++ tailWord_1680410) baseStart_1680410 baseEnd_1680410 := by
    simpa [prefixWord, tailWord_1680410, baseEnd_1680410] using wordTrace_append hprefix tailTrace_1680410
  have hstable : (prefixWord ++ tailWord_1680410).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680410).length < 2 ^ (prefixWord ++ tailWord_1680410).sum := by decide
  have hdescent : baseEnd_1680410 < baseStart_1680410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680489 : List Nat := [1, 2, 1, 1, 1, 8, 1, 2, 4]
def baseStart_1680489 : Nat := 118140960795 + 1680489 * 2 ^ 59
def prefixEnd_1680489 : Nat := 4983230072969 + 3 ^ 40 * 1680489 * 2
def baseEnd_1680489 : Nat := 383510485152702583448479

theorem tailTrace_1680489 : CollatzResearch.WordTrace tailWord_1680489 prefixEnd_1680489 383510485152702583448479 := by
  unfold tailWord_1680489
  simp only [CollatzResearch.WordTrace]
  refine ⟨61292469208882832516700521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40861646139255221677800347 61292469208882832516700521)
  ·
    refine ⟨45969351906662124387525391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61292469208882832516700521 45969351906662124387525391)
    ·
      refine ⟨68954027859993186581288087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45969351906662124387525391 68954027859993186581288087)
      ·
        refine ⟨103431041789989779871932131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68954027859993186581288087 103431041789989779871932131)
        ·
          refine ⟨155146562684984669807898197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103431041789989779871932131 155146562684984669807898197)
          ·
            refine ⟨1818123781464664099311307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 155146562684984669807898197 1818123781464664099311307)
            ·
              refine ⟨2727185672196996148966961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818123781464664099311307 2727185672196996148966961)
              ·
                refine ⟨2045389254147747111725221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2727185672196996148966961 2045389254147747111725221)
                ·
                  refine ⟨383510485152702583448479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045389254147747111725221 383510485152702583448479)
                  ·
                    rfl

theorem cell21_1680489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 2, 4].length) (baseStart_1680489 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680489 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680489 prefixEnd_1680489 := by exact prefixLift 1680489
  have htrace : WordTrace (prefixWord ++ tailWord_1680489) baseStart_1680489 baseEnd_1680489 := by
    simpa [prefixWord, tailWord_1680489, baseEnd_1680489] using wordTrace_append hprefix tailTrace_1680489
  have hstable : (prefixWord ++ tailWord_1680489).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680489).length < 2 ^ (prefixWord ++ tailWord_1680489).sum := by decide
  have hdescent : baseEnd_1680489 < baseStart_1680489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680531 : List Nat := [1, 1, 1, 2, 1, 2, 5, 2, 6]
def baseStart_1680531 : Nat := 118140960795 + 1680531 * 2 ^ 59
def prefixEnd_1680531 : Nat := 4983230072969 + 3 ^ 40 * 1680531 * 2
def baseEnd_1680531 : Nat := 383520070124919843748393

theorem tailTrace_1680531 : CollatzResearch.WordTrace tailWord_1680531 prefixEnd_1680531 383520070124919843748393 := by
  unfold tailWord_1680531
  simp only [CollatzResearch.WordTrace]
  refine ⟨61294001074730673689729447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40862667383153782459819631 61294001074730673689729447)
  ·
    refine ⟨91941001612096010534594171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61294001074730673689729447 91941001612096010534594171)
    ·
      refine ⟨137911502418144015801891257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91941001612096010534594171 137911502418144015801891257)
      ·
        refine ⟨103433626813608011851418443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137911502418144015801891257 103433626813608011851418443)
        ·
          refine ⟨155150440220412017777127665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103433626813608011851418443 155150440220412017777127665)
          ·
            refine ⟨116362830165309013332845749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155150440220412017777127665 116362830165309013332845749)
            ·
              refine ⟨10909015327997719999954289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116362830165309013332845749 10909015327997719999954289)
              ·
                refine ⟨8181761495998289999965717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10909015327997719999954289 8181761495998289999965717)
                ·
                  refine ⟨383520070124919843748393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8181761495998289999965717 383520070124919843748393)
                  ·
                    rfl

theorem cell21_1680531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 2, 6].length) (baseStart_1680531 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680531 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680531 prefixEnd_1680531 := by exact prefixLift 1680531
  have htrace : WordTrace (prefixWord ++ tailWord_1680531) baseStart_1680531 baseEnd_1680531 := by
    simpa [prefixWord, tailWord_1680531, baseEnd_1680531] using wordTrace_append hprefix tailTrace_1680531
  have hstable : (prefixWord ++ tailWord_1680531).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680531).length < 2 ^ (prefixWord ++ tailWord_1680531).sum := by decide
  have hdescent : baseEnd_1680531 < baseStart_1680531 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680548 : List Nat := [2, 3, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1680548 : Nat := 118140960795 + 1680548 * 2 ^ 59
def prefixEnd_1680548 : Nat := 4983230072969 + 3 ^ 40 * 1680548 * 2
def baseEnd_1680548 : Nat := 383523949756531591965025

theorem tailTrace_1680548 : CollatzResearch.WordTrace tailWord_1680548 prefixEnd_1680548 383523949756531591965025 := by
  unfold tailWord_1680548
  simp only [CollatzResearch.WordTrace]
  refine ⟨30647310557834542796549149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40863080743779390395398865 30647310557834542796549149)
  ·
    refine ⟨11492741459187953548705931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30647310557834542796549149 11492741459187953548705931)
    ·
      refine ⟨17239112188781930323058897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11492741459187953548705931 17239112188781930323058897)
      ·
        refine ⟨12929334141586447742294173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17239112188781930323058897 12929334141586447742294173)
        ·
          refine ⟨4848500303094917903360315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12929334141586447742294173 4848500303094917903360315)
          ·
            refine ⟨7272750454642376855040473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4848500303094917903360315 7272750454642376855040473)
            ·
              refine ⟨5454562840981782641280355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7272750454642376855040473 5454562840981782641280355)
              ·
                refine ⟨8181844261472673961920533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454562840981782641280355 8181844261472673961920533)
                ·
                  refine ⟨383523949756531591965025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8181844261472673961920533 383523949756531591965025)
                  ·
                    rfl

theorem cell21_1680548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1680548 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680548 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680548 prefixEnd_1680548 := by exact prefixLift 1680548
  have htrace : WordTrace (prefixWord ++ tailWord_1680548) baseStart_1680548 baseEnd_1680548 := by
    simpa [prefixWord, tailWord_1680548, baseEnd_1680548] using wordTrace_append hprefix tailTrace_1680548
  have hstable : (prefixWord ++ tailWord_1680548).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680548).length < 2 ^ (prefixWord ++ tailWord_1680548).sum := by decide
  have hdescent : baseEnd_1680548 < baseStart_1680548 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680551 : List Nat := [1, 1, 6, 2, 1, 3, 1, 1, 5]
def baseStart_1680551 : Nat := 118140960795 + 1680551 * 2 ^ 59
def prefixEnd_1680551 : Nat := 4983230072969 + 3 ^ 40 * 1680551 * 2
def baseEnd_1680551 : Nat := 383524634397404253415019

theorem tailTrace_1680551 : CollatzResearch.WordTrace tailWord_1680551 prefixEnd_1680551 383524634397404253415019 := by
  unfold tailWord_1680551
  simp only [CollatzResearch.WordTrace]
  refine ⟨61294730534658217105457507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40863153689772144736971671 61294730534658217105457507)
  ·
    refine ⟨91942095801987325658186261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61294730534658217105457507 91942095801987325658186261)
    ·
      refine ⟨4309785740718155890227481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91942095801987325658186261 4309785740718155890227481)
      ·
        refine ⟨3232339305538616917670611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4309785740718155890227481 3232339305538616917670611)
        ·
          refine ⟨4848508958307925376505917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232339305538616917670611 4848508958307925376505917)
          ·
            refine ⟨1818190859365472016189719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4848508958307925376505917 1818190859365472016189719)
            ·
              refine ⟨2727286289048208024284579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818190859365472016189719 2727286289048208024284579)
              ·
                refine ⟨4090929433572312036426869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2727286289048208024284579 4090929433572312036426869)
                ·
                  refine ⟨383524634397404253415019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4090929433572312036426869 383524634397404253415019)
                  ·
                    rfl

theorem cell21_1680551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 5].length) (baseStart_1680551 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680551 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680551 prefixEnd_1680551 := by exact prefixLift 1680551
  have htrace : WordTrace (prefixWord ++ tailWord_1680551) baseStart_1680551 baseEnd_1680551 := by
    simpa [prefixWord, tailWord_1680551, baseEnd_1680551] using wordTrace_append hprefix tailTrace_1680551
  have hstable : (prefixWord ++ tailWord_1680551).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680551).length < 2 ^ (prefixWord ++ tailWord_1680551).sum := by decide
  have hdescent : baseEnd_1680551 < baseStart_1680551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680562 : List Nat := [3, 2, 1, 1, 1, 4, 1, 8]
def baseStart_1680562 : Nat := 118140960795 + 1680562 * 2 ^ 59
def prefixEnd_1680562 : Nat := 4983230072969 + 3 ^ 40 * 1680562 * 2
def baseEnd_1680562 : Nat := 127842381582423559577221

theorem tailTrace_1680562 : CollatzResearch.WordTrace tailWord_1680562 prefixEnd_1680562 127842381582423559577221 := by
  unfold tailWord_1680562
  simp only [CollatzResearch.WordTrace]
  refine ⟨15323782934404591496026985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40863421158412243989405293 15323782934404591496026985)
  ·
    refine ⟨11492837200803443622020239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15323782934404591496026985 11492837200803443622020239)
    ·
      refine ⟨17239255801205165433030359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11492837200803443622020239 17239255801205165433030359)
      ·
        refine ⟨25858883701807748149545539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17239255801205165433030359 25858883701807748149545539)
        ·
          refine ⟨38788325552711622224318309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25858883701807748149545539 38788325552711622224318309)
          ·
            refine ⟨7272811041133429167059683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38788325552711622224318309 7272811041133429167059683)
            ·
              refine ⟨10909216561700143750589525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7272811041133429167059683 10909216561700143750589525)
              ·
                refine ⟨127842381582423559577221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10909216561700143750589525 127842381582423559577221)
                ·
                  rfl

theorem cell21_1680562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_1680562 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680562 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680562 prefixEnd_1680562 := by exact prefixLift 1680562
  have htrace : WordTrace (prefixWord ++ tailWord_1680562) baseStart_1680562 baseEnd_1680562 := by
    simpa [prefixWord, tailWord_1680562, baseEnd_1680562] using wordTrace_append hprefix tailTrace_1680562
  have hstable : (prefixWord ++ tailWord_1680562).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680562).length < 2 ^ (prefixWord ++ tailWord_1680562).sum := by decide
  have hdescent : baseEnd_1680562 < baseStart_1680562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680596 : List Nat := [2, 4, 1, 4, 2, 8]
def baseStart_1680596 : Nat := 118140960795 + 1680596 * 2 ^ 59
def prefixEnd_1680596 : Nat := 4983230072969 + 3 ^ 40 * 1680596 * 2
def baseEnd_1680596 : Nat := 14204996444833117598701

theorem tailTrace_1680596 : CollatzResearch.WordTrace tailWord_1680596 prefixEnd_1680596 14204996444833117598701 := by
  unfold tailWord_1680596
  simp only [CollatzResearch.WordTrace]
  refine ⟨30648185909747594895422821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40864247879663459860563761 30648185909747594895422821)
  ·
    refine ⟨5746534858077674042891779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30648185909747594895422821 5746534858077674042891779)
    ·
      refine ⟨8619802287116511064337669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5746534858077674042891779 8619802287116511064337669)
      ·
        refine ⟨1616212928834345824563313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8619802287116511064337669 1616212928834345824563313)
        ·
          refine ⟨1212159696625759368422485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1616212928834345824563313 1212159696625759368422485)
          ·
            refine ⟨14204996444833117598701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 1212159696625759368422485 14204996444833117598701)
            ·
              rfl

theorem cell21_1680596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 2, 8].length) (baseStart_1680596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680596 prefixEnd_1680596 := by exact prefixLift 1680596
  have htrace : WordTrace (prefixWord ++ tailWord_1680596) baseStart_1680596 baseEnd_1680596 := by
    simpa [prefixWord, tailWord_1680596, baseEnd_1680596] using wordTrace_append hprefix tailTrace_1680596
  have hstable : (prefixWord ++ tailWord_1680596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680596).length < 2 ^ (prefixWord ++ tailWord_1680596).sum := by decide
  have hdescent : baseEnd_1680596 < baseStart_1680596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680607 : List Nat := [1, 1, 2, 3, 2, 1, 2, 3, 6]
def baseStart_1680607 : Nat := 118140960795 + 1680607 * 2 ^ 59
def prefixEnd_1680607 : Nat := 4983230072969 + 3 ^ 40 * 1680607 * 2
def baseEnd_1680607 : Nat := 383537414360360600481571

theorem tailTrace_1680607 : CollatzResearch.WordTrace tailWord_1680607 prefixEnd_1680607 383537414360360600481571 := by
  unfold tailWord_1680607
  simp only [CollatzResearch.WordTrace]
  refine ⟨61296773022455338669496075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40864515348303559112997383 61296773022455338669496075)
  ·
    refine ⟨91945159533683008004244113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61296773022455338669496075 91945159533683008004244113)
    ·
      refine ⟨68958869650262256003183085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91945159533683008004244113 68958869650262256003183085)
      ·
        refine ⟨25859576118848346001193657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68958869650262256003183085 25859576118848346001193657)
        ·
          refine ⟨19394682089136259500895243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25859576118848346001193657 19394682089136259500895243)
          ·
            refine ⟨29092023133704389251342865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19394682089136259500895243 29092023133704389251342865)
            ·
              refine ⟨21819017350278291938507149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29092023133704389251342865 21819017350278291938507149)
              ·
                refine ⟨8182131506354359476940181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21819017350278291938507149 8182131506354359476940181)
                ·
                  refine ⟨383537414360360600481571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8182131506354359476940181 383537414360360600481571)
                  ·
                    rfl

theorem cell21_1680607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 2, 3, 6].length) (baseStart_1680607 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680607 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680607 prefixEnd_1680607 := by exact prefixLift 1680607
  have htrace : WordTrace (prefixWord ++ tailWord_1680607) baseStart_1680607 baseEnd_1680607 := by
    simpa [prefixWord, tailWord_1680607, baseEnd_1680607] using wordTrace_append hprefix tailTrace_1680607
  have hstable : (prefixWord ++ tailWord_1680607).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680607).length < 2 ^ (prefixWord ++ tailWord_1680607).sum := by decide
  have hdescent : baseEnd_1680607 < baseStart_1680607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680658 : List Nat := [3, 2, 4, 2, 1, 1, 1, 1, 6]
def baseStart_1680658 : Nat := 118140960795 + 1680658 * 2 ^ 59
def prefixEnd_1680658 : Nat := 4983230072969 + 3 ^ 40 * 1680658 * 2
def baseEnd_1680658 : Nat := 383549053255195845131467

theorem tailTrace_1680658 : CollatzResearch.WordTrace tailWord_1680658 prefixEnd_1680658 383549053255195845131467 := by
  unfold tailWord_1680658
  simp only [CollatzResearch.WordTrace]
  refine ⟨15324658286317643594900657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40865755430180382919735085 15324658286317643594900657)
  ·
    refine ⟨11493493714738232696175493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15324658286317643594900657 11493493714738232696175493)
    ·
      refine ⟨2155030071513418630532905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11493493714738232696175493 2155030071513418630532905)
      ·
        refine ⟨1616272553635063972899679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2155030071513418630532905 1616272553635063972899679)
        ·
          refine ⟨2424408830452595959349519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616272553635063972899679 2424408830452595959349519)
          ·
            refine ⟨3636613245678893939024279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2424408830452595959349519 3636613245678893939024279)
            ·
              refine ⟨5454919868518340908536419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3636613245678893939024279 5454919868518340908536419)
              ·
                refine ⟨8182379802777511362804629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5454919868518340908536419 8182379802777511362804629)
                ·
                  refine ⟨383549053255195845131467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8182379802777511362804629 383549053255195845131467)
                  ·
                    rfl

theorem cell21_1680658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 1, 1, 1, 6].length) (baseStart_1680658 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680658 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680658 prefixEnd_1680658 := by exact prefixLift 1680658
  have htrace : WordTrace (prefixWord ++ tailWord_1680658) baseStart_1680658 baseEnd_1680658 := by
    simpa [prefixWord, tailWord_1680658, baseEnd_1680658] using wordTrace_append hprefix tailTrace_1680658
  have hstable : (prefixWord ++ tailWord_1680658).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680658).length < 2 ^ (prefixWord ++ tailWord_1680658).sum := by decide
  have hdescent : baseEnd_1680658 < baseStart_1680658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680703 : List Nat := [1, 1, 2, 2, 4, 4, 1, 3, 3]
def baseStart_1680703 : Nat := 118140960795 + 1680703 * 2 ^ 59
def prefixEnd_1680703 : Nat := 4983230072969 + 3 ^ 40 * 1680703 * 2
def baseEnd_1680703 : Nat := 383559322868285766881375

theorem tailTrace_1680703 : CollatzResearch.WordTrace tailWord_1680703 prefixEnd_1680703 383559322868285766881375 := by
  unfold tailWord_1680703
  simp only [CollatzResearch.WordTrace]
  refine ⟨61300274430107547064990763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40866849620071698043327175 61300274430107547064990763)
  ·
    refine ⟨91950411645161320597486145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61300274430107547064990763 91950411645161320597486145)
    ·
      refine ⟨68962808733870990448114609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91950411645161320597486145 68962808733870990448114609)
      ·
        refine ⟨51722106550403242836085957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68962808733870990448114609 51722106550403242836085957)
        ·
          refine ⟨9697894978200608031766117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51722106550403242836085957 9697894978200608031766117)
          ·
            refine ⟨1818355308412614005956147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9697894978200608031766117 1818355308412614005956147)
            ·
              refine ⟨2727532962618921008934221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818355308412614005956147 2727532962618921008934221)
              ·
                refine ⟨1022824860982095378350333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2727532962618921008934221 1022824860982095378350333)
                ·
                  refine ⟨383559322868285766881375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1022824860982095378350333 383559322868285766881375)
                  ·
                    rfl

theorem cell21_1680703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 4, 1, 3, 3].length) (baseStart_1680703 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680703 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680703 prefixEnd_1680703 := by exact prefixLift 1680703
  have htrace : WordTrace (prefixWord ++ tailWord_1680703) baseStart_1680703 baseEnd_1680703 := by
    simpa [prefixWord, tailWord_1680703, baseEnd_1680703] using wordTrace_append hprefix tailTrace_1680703
  have hstable : (prefixWord ++ tailWord_1680703).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680703).length < 2 ^ (prefixWord ++ tailWord_1680703).sum := by decide
  have hdescent : baseEnd_1680703 < baseStart_1680703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680726 : List Nat := [5, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_1680726 : Nat := 118140960795 + 1680726 * 2 ^ 59
def prefixEnd_1680726 : Nat := 4983230072969 + 3 ^ 40 * 1680726 * 2
def baseEnd_1680726 : Nat := 383564571781642837997995

theorem tailTrace_1680726 : CollatzResearch.WordTrace tailWord_1680726 prefixEnd_1680726 383564571781642837997995 := by
  unfold tailWord_1680726
  simp only [CollatzResearch.WordTrace]
  refine ⟨3831319581814013874567377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40867408872682814662052021 3831319581814013874567377)
  ·
    refine ⟨2873489686360510405925533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3831319581814013874567377 2873489686360510405925533)
    ·
      refine ⟨1077558632385191402222075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2873489686360510405925533 1077558632385191402222075)
      ·
        refine ⟨1616337948577787103333113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077558632385191402222075 1616337948577787103333113)
        ·
          refine ⟨1212253461433340327499835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1616337948577787103333113 1212253461433340327499835)
          ·
            refine ⟨1818380192150010491249753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212253461433340327499835 1818380192150010491249753)
            ·
              refine ⟨1363785144112507868437315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818380192150010491249753 1363785144112507868437315)
              ·
                refine ⟨2045677716168761802655973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363785144112507868437315 2045677716168761802655973)
                ·
                  refine ⟨383564571781642837997995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045677716168761802655973 383564571781642837997995)
                  ·
                    rfl

theorem cell21_1680726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_1680726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680726 prefixEnd_1680726 := by exact prefixLift 1680726
  have htrace : WordTrace (prefixWord ++ tailWord_1680726) baseStart_1680726 baseEnd_1680726 := by
    simpa [prefixWord, tailWord_1680726, baseEnd_1680726] using wordTrace_append hprefix tailTrace_1680726
  have hstable : (prefixWord ++ tailWord_1680726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680726).length < 2 ^ (prefixWord ++ tailWord_1680726).sum := by decide
  have hdescent : baseEnd_1680726 < baseStart_1680726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680776 : List Nat := [2, 1, 3, 3, 1, 2, 1, 4, 4]
def baseStart_1680776 : Nat := 118140960795 + 1680776 * 2 ^ 59
def prefixEnd_1680776 : Nat := 4983230072969 + 3 ^ 40 * 1680776 * 2
def baseEnd_1680776 : Nat := 383575982462853862164559

theorem tailTrace_1680776 : CollatzResearch.WordTrace tailWord_1680776 prefixEnd_1680776 383575982462853862164559 := by
  unfold tailWord_1680776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30651468479421540266199091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40868624639228720354932121 30651468479421540266199091)
  ·
    refine ⟨45977202719132310399298637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30651468479421540266199091 45977202719132310399298637)
    ·
      refine ⟨17241451019674616399736989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45977202719132310399298637 17241451019674616399736989)
      ·
        refine ⟨6465544132377981149901371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17241451019674616399736989 6465544132377981149901371)
        ·
          refine ⟨9698316198566971724852057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465544132377981149901371 9698316198566971724852057)
          ·
            refine ⟨7273737148925228793639043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9698316198566971724852057 7273737148925228793639043)
            ·
              refine ⟨10910605723387843190458565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7273737148925228793639043 10910605723387843190458565)
              ·
                refine ⟨2045738573135220598210981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10910605723387843190458565 2045738573135220598210981)
                ·
                  refine ⟨383575982462853862164559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2045738573135220598210981 383575982462853862164559)
                  ·
                    rfl

theorem cell21_1680776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 4].length) (baseStart_1680776 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680776 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680776 prefixEnd_1680776 := by exact prefixLift 1680776
  have htrace : WordTrace (prefixWord ++ tailWord_1680776) baseStart_1680776 baseEnd_1680776 := by
    simpa [prefixWord, tailWord_1680776, baseEnd_1680776] using wordTrace_append hprefix tailTrace_1680776
  have hstable : (prefixWord ++ tailWord_1680776).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680776).length < 2 ^ (prefixWord ++ tailWord_1680776).sum := by decide
  have hdescent : baseEnd_1680776 < baseStart_1680776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680807 : List Nat := [1, 1, 6, 1, 1, 1, 5, 5]
def baseStart_1680807 : Nat := 118140960795 + 1680807 * 2 ^ 59
def prefixEnd_1680807 : Nat := 4983230072969 + 3 ^ 40 * 1680807 * 2
def baseEnd_1680807 : Nat := 127861019028401565715943

theorem tailTrace_1680807 : CollatzResearch.WordTrace tailWord_1680807 prefixEnd_1680807 127861019028401565715943 := by
  unfold tailWord_1680807
  simp only [CollatzResearch.WordTrace]
  refine ⟨61304067621730772826776675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40869378414487181884517783 61304067621730772826776675)
  ·
    refine ⟨91956101432596159240165013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61304067621730772826776675 91956101432596159240165013)
    ·
      refine ⟨4310442254652944964382735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91956101432596159240165013 4310442254652944964382735)
      ·
        refine ⟨6465663381979417446574103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310442254652944964382735 6465663381979417446574103)
        ·
          refine ⟨9698495072969126169861155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465663381979417446574103 9698495072969126169861155)
          ·
            refine ⟨14547742609453689254791733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9698495072969126169861155 14547742609453689254791733)
            ·
              refine ⟨1363850869636283367636725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14547742609453689254791733 1363850869636283367636725)
              ·
                refine ⟨127861019028401565715943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1363850869636283367636725 127861019028401565715943)
                ·
                  rfl

theorem cell21_1680807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 5, 5].length) (baseStart_1680807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680807 prefixEnd_1680807 := by exact prefixLift 1680807
  have htrace : WordTrace (prefixWord ++ tailWord_1680807) baseStart_1680807 baseEnd_1680807 := by
    simpa [prefixWord, tailWord_1680807, baseEnd_1680807] using wordTrace_append hprefix tailTrace_1680807
  have hstable : (prefixWord ++ tailWord_1680807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680807).length < 2 ^ (prefixWord ++ tailWord_1680807).sum := by decide
  have hdescent : baseEnd_1680807 < baseStart_1680807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1680942 : List Nat := [4, 1, 3, 1, 2, 10]
def baseStart_1680942 : Nat := 118140960795 + 1680942 * 2 ^ 59
def prefixEnd_1680942 : Nat := 4983230072969 + 3 ^ 40 * 1680942 * 2
def baseEnd_1680942 : Nat := 14207920960165720829539

theorem tailTrace_1680942 : CollatzResearch.WordTrace tailWord_1680942 prefixEnd_1680942 14207920960165720829539 := by
  unfold tailWord_1680942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663623934530211360367635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40872660984161127255294053 7663623934530211360367635)
  ·
    refine ⟨11495435901795317040551453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7663623934530211360367635 11495435901795317040551453)
    ·
      refine ⟨4310788463173243890206795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11495435901795317040551453 4310788463173243890206795)
      ·
        refine ⟨6466182694759865835310193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310788463173243890206795 6466182694759865835310193)
        ·
          refine ⟨4849637021069899376482645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6466182694759865835310193 4849637021069899376482645)
          ·
            refine ⟨14207920960165720829539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 4849637021069899376482645 14207920960165720829539)
            ·
              rfl

theorem cell21_1680942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 10].length) (baseStart_1680942 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1680942 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1680942 prefixEnd_1680942 := by exact prefixLift 1680942
  have htrace : WordTrace (prefixWord ++ tailWord_1680942) baseStart_1680942 baseEnd_1680942 := by
    simpa [prefixWord, tailWord_1680942, baseEnd_1680942] using wordTrace_append hprefix tailTrace_1680942
  have hstable : (prefixWord ++ tailWord_1680942).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1680942).length < 2 ^ (prefixWord ++ tailWord_1680942).sum := by decide
  have hdescent : baseEnd_1680942 < baseStart_1680942 := by decide
  rcases family_descends (prefixWord ++ tailWord_1680942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681021 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 4]
def baseStart_1681021 : Nat := 118140960795 + 1681021 * 2 ^ 59
def prefixEnd_1681021 : Nat := 4983230072969 + 3 ^ 40 * 1681021 * 2
def baseEnd_1681021 : Nat := 383631894800787880580725

theorem tailTrace_1681021 : CollatzResearch.WordTrace tailWord_1681021 prefixEnd_1681021 383631894800787880580725 := by
  unfold tailWord_1681021
  simp only [CollatzResearch.WordTrace]
  refine ⟨61311872842955487375066917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40874581895303658250044611 61311872842955487375066917)
  ·
    refine ⟨11495976158054153882825047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61311872842955487375066917 11495976158054153882825047)
    ·
      refine ⟨17243964237081230824237571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11495976158054153882825047 17243964237081230824237571)
      ·
        refine ⟨25865946355621846236356357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17243964237081230824237571 25865946355621846236356357)
        ·
          refine ⟨4849864941679096169316817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25865946355621846236356357 4849864941679096169316817)
          ·
            refine ⟨3637398706259322126987613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4849864941679096169316817 3637398706259322126987613)
            ·
              refine ⟨1364024514847245797620355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3637398706259322126987613 1364024514847245797620355)
              ·
                refine ⟨2046036772270868696430533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364024514847245797620355 2046036772270868696430533)
                ·
                  refine ⟨383631894800787880580725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046036772270868696430533 383631894800787880580725)
                  ·
                    rfl

theorem cell21_1681021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_1681021 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681021 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681021 prefixEnd_1681021 := by exact prefixLift 1681021
  have htrace : WordTrace (prefixWord ++ tailWord_1681021) baseStart_1681021 baseEnd_1681021 := by
    simpa [prefixWord, tailWord_1681021, baseEnd_1681021] using wordTrace_append hprefix tailTrace_1681021
  have hstable : (prefixWord ++ tailWord_1681021).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681021).length < 2 ^ (prefixWord ++ tailWord_1681021).sum := by decide
  have hdescent : baseEnd_1681021 < baseStart_1681021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681049 : List Nat := [1, 2, 1, 2, 1, 2, 2, 7, 3]
def baseStart_1681049 : Nat := 118140960795 + 1681049 * 2 ^ 59
def prefixEnd_1681049 : Nat := 4983230072969 + 3 ^ 40 * 1681049 * 2
def baseEnd_1681049 : Nat := 383638284782266054114001

theorem tailTrace_1681049 : CollatzResearch.WordTrace tailWord_1681049 prefixEnd_1681049 383638284782266054114001 := by
  unfold tailWord_1681049
  simp only [CollatzResearch.WordTrace]
  refine ⟨61312894086854048157086201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40875262724569365438057467 61312894086854048157086201)
  ·
    refine ⟨45984670565140536117814651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61312894086854048157086201 45984670565140536117814651)
    ·
      refine ⟨68977005847710804176721977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45984670565140536117814651 68977005847710804176721977)
      ·
        refine ⟨51732754385783103132541483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68977005847710804176721977 51732754385783103132541483)
        ·
          refine ⟨77599131578674654698812225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51732754385783103132541483 77599131578674654698812225)
          ·
            refine ⟨58199348684005991024109169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77599131578674654698812225 58199348684005991024109169)
            ·
              refine ⟨43649511513004493268081877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58199348684005991024109169 43649511513004493268081877)
              ·
                refine ⟨1023035426086042810970669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43649511513004493268081877 1023035426086042810970669)
                ·
                  refine ⟨383638284782266054114001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023035426086042810970669 383638284782266054114001)
                  ·
                    rfl

theorem cell21_1681049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_1681049 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681049 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681049 prefixEnd_1681049 := by exact prefixLift 1681049
  have htrace : WordTrace (prefixWord ++ tailWord_1681049) baseStart_1681049 baseEnd_1681049 := by
    simpa [prefixWord, tailWord_1681049, baseEnd_1681049] using wordTrace_append hprefix tailTrace_1681049
  have hstable : (prefixWord ++ tailWord_1681049).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681049).length < 2 ^ (prefixWord ++ tailWord_1681049).sum := by decide
  have hdescent : baseEnd_1681049 < baseStart_1681049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681117 : List Nat := [1, 4, 3, 3, 1, 2, 2, 2, 3]
def baseStart_1681117 : Nat := 118140960795 + 1681117 * 2 ^ 59
def prefixEnd_1681117 : Nat := 4983230072969 + 3 ^ 40 * 1681117 * 2
def baseEnd_1681117 : Nat := 383653803308713046980529

theorem tailTrace_1681117 : CollatzResearch.WordTrace tailWord_1681117 prefixEnd_1681117 383653803308713046980529 := by
  unfold tailWord_1681117
  simp only [CollatzResearch.WordTrace]
  refine ⟨61315374250607695770561605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40876916167071797180374403 61315374250607695770561605)
  ·
    refine ⟨11496632671988942956980301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61315374250607695770561605 11496632671988942956980301)
    ·
      refine ⟨4311237251995853608867613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11496632671988942956980301 4311237251995853608867613)
      ·
        refine ⟨1616713969498445103325355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4311237251995853608867613 1616713969498445103325355)
        ·
          refine ⟨2425070954247667654988033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616713969498445103325355 2425070954247667654988033)
          ·
            refine ⟨1818803215685750741241025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425070954247667654988033 1818803215685750741241025)
            ·
              refine ⟨1364102411764313055930769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818803215685750741241025 1364102411764313055930769)
              ·
                refine ⟨1023076808823234791948077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364102411764313055930769 1023076808823234791948077)
                ·
                  refine ⟨383653803308713046980529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023076808823234791948077 383653803308713046980529)
                  ·
                    rfl

theorem cell21_1681117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 2, 2, 2, 3].length) (baseStart_1681117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681117 prefixEnd_1681117 := by exact prefixLift 1681117
  have htrace : WordTrace (prefixWord ++ tailWord_1681117) baseStart_1681117 baseEnd_1681117 := by
    simpa [prefixWord, tailWord_1681117, baseEnd_1681117] using wordTrace_append hprefix tailTrace_1681117
  have hstable : (prefixWord ++ tailWord_1681117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681117).length < 2 ^ (prefixWord ++ tailWord_1681117).sum := by decide
  have hdescent : baseEnd_1681117 < baseStart_1681117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681139 : List Nat := [1, 1, 1, 2, 2, 3, 4, 3, 4]
def baseStart_1681139 : Nat := 118140960795 + 1681139 * 2 ^ 59
def prefixEnd_1681139 : Nat := 4983230072969 + 3 ^ 40 * 1681139 * 2
def baseEnd_1681139 : Nat := 383658824008445897613817

theorem tailTrace_1681139 : CollatzResearch.WordTrace tailWord_1681139 prefixEnd_1681139 383658824008445897613817 := by
  unfold tailWord_1681139
  simp only [CollatzResearch.WordTrace]
  refine ⟨61316176656527993527862471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40877451104351995685241647 61316176656527993527862471)
  ·
    refine ⟨91974264984791990291793707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61316176656527993527862471 91974264984791990291793707)
    ·
      refine ⟨137961397477187985437690561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91974264984791990291793707 137961397477187985437690561)
      ·
        refine ⟨103471048107890989078267921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137961397477187985437690561 103471048107890989078267921)
        ·
          refine ⟨77603286080918241808700941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103471048107890989078267921 77603286080918241808700941)
          ·
            refine ⟨29101232280344340678262853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77603286080918241808700941 29101232280344340678262853)
            ·
              refine ⟨5456481052564563877174285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29101232280344340678262853 5456481052564563877174285)
              ·
                refine ⟨2046180394711711453940357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5456481052564563877174285 2046180394711711453940357)
                ·
                  refine ⟨383658824008445897613817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046180394711711453940357 383658824008445897613817)
                  ·
                    rfl

theorem cell21_1681139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 3, 4].length) (baseStart_1681139 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681139 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681139 prefixEnd_1681139 := by exact prefixLift 1681139
  have htrace : WordTrace (prefixWord ++ tailWord_1681139) baseStart_1681139 baseEnd_1681139 := by
    simpa [prefixWord, tailWord_1681139, baseEnd_1681139] using wordTrace_append hprefix tailTrace_1681139
  have hstable : (prefixWord ++ tailWord_1681139).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681139).length < 2 ^ (prefixWord ++ tailWord_1681139).sum := by decide
  have hdescent : baseEnd_1681139 < baseStart_1681139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681153 : List Nat := [1, 2, 4, 1, 1, 1, 2, 9]
def baseStart_1681153 : Nat := 118140960795 + 1681153 * 2 ^ 59
def prefixEnd_1681153 : Nat := 4983230072969 + 3 ^ 40 * 1681153 * 2
def baseEnd_1681153 : Nat := 127887339666394994793485

theorem tailTrace_1681153 : CollatzResearch.WordTrace tailWord_1681153 prefixEnd_1681153 127887339666394994793485 := by
  unfold tailWord_1681153
  simp only [CollatzResearch.WordTrace]
  refine ⟨61316687278477273918872113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40877791518984849279248075 61316687278477273918872113)
  ·
    refine ⟨45987515458857955439154085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61316687278477273918872113 45987515458857955439154085)
    ·
      refine ⟨8622659148535866644841391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45987515458857955439154085 8622659148535866644841391)
      ·
        refine ⟨12933988722803799967262087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8622659148535866644841391 12933988722803799967262087)
        ·
          refine ⟨19400983084205699950893131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12933988722803799967262087 19400983084205699950893131)
          ·
            refine ⟨29101474626308549926339697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19400983084205699950893131 29101474626308549926339697)
            ·
              refine ⟨21826105969731412444754773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29101474626308549926339697 21826105969731412444754773)
              ·
                refine ⟨127887339666394994793485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 21826105969731412444754773 127887339666394994793485)
                ·
                  rfl

theorem cell21_1681153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 9].length) (baseStart_1681153 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681153 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681153 prefixEnd_1681153 := by exact prefixLift 1681153
  have htrace : WordTrace (prefixWord ++ tailWord_1681153) baseStart_1681153 baseEnd_1681153 := by
    simpa [prefixWord, tailWord_1681153, baseEnd_1681153] using wordTrace_append hprefix tailTrace_1681153
  have hstable : (prefixWord ++ tailWord_1681153).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681153).length < 2 ^ (prefixWord ++ tailWord_1681153).sum := by decide
  have hdescent : baseEnd_1681153 < baseStart_1681153 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681159 : List Nat := [1, 1, 4, 4, 2, 1, 2, 3, 3]
def baseStart_1681159 : Nat := 118140960795 + 1681159 * 2 ^ 59
def prefixEnd_1681159 : Nat := 4983230072969 + 3 ^ 40 * 1681159 * 2
def baseEnd_1681159 : Nat := 383663388280930307280443

theorem tailTrace_1681159 : CollatzResearch.WordTrace tailWord_1681159 prefixEnd_1681159 383663388280930307280443 := by
  unfold tailWord_1681159
  simp only [CollatzResearch.WordTrace]
  refine ⟨61316906116455536943590531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40877937410970357962393687 61316906116455536943590531)
  ·
    refine ⟨91975359174683305415385797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61316906116455536943590531 91975359174683305415385797)
    ·
      refine ⟨17245379845253119765384837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91975359174683305415385797 17245379845253119765384837)
      ·
        refine ⟨3233508720984959956009657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17245379845253119765384837 3233508720984959956009657)
        ·
          refine ⟨2425131540738719967007243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3233508720984959956009657 2425131540738719967007243)
          ·
            refine ⟨3637697311108079950510865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425131540738719967007243 3637697311108079950510865)
            ·
              refine ⟨2728272983331059962883149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3637697311108079950510865 2728272983331059962883149)
              ·
                refine ⟨1023102368749147486081181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2728272983331059962883149 1023102368749147486081181)
                ·
                  refine ⟨383663388280930307280443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023102368749147486081181 383663388280930307280443)
                  ·
                    rfl

theorem cell21_1681159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 3, 3].length) (baseStart_1681159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681159 prefixEnd_1681159 := by exact prefixLift 1681159
  have htrace : WordTrace (prefixWord ++ tailWord_1681159) baseStart_1681159 baseEnd_1681159 := by
    simpa [prefixWord, tailWord_1681159, baseEnd_1681159] using wordTrace_append hprefix tailTrace_1681159
  have hstable : (prefixWord ++ tailWord_1681159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681159).length < 2 ^ (prefixWord ++ tailWord_1681159).sum := by decide
  have hdescent : baseEnd_1681159 < baseStart_1681159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681165 : List Nat := [1, 7, 2, 1, 2, 1, 1, 2, 4]
def baseStart_1681165 : Nat := 118140960795 + 1681165 * 2 ^ 59
def prefixEnd_1681165 : Nat := 4983230072969 + 3 ^ 40 * 1681165 * 2
def baseEnd_1681165 : Nat := 383664757562675630180431

theorem tailTrace_1681165 : CollatzResearch.WordTrace tailWord_1681165 prefixEnd_1681165 383664757562675630180431 := by
  unfold tailWord_1681165
  simp only [CollatzResearch.WordTrace]
  refine ⟨61317124954433799968308949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40878083302955866645539299 61317124954433799968308949)
  ·
    refine ⟨1437120116119542186757241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 61317124954433799968308949 1437120116119542186757241)
    ·
      refine ⟨1077840087089656640067931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1437120116119542186757241 1077840087089656640067931)
      ·
        refine ⟨1616760130634484960101897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077840087089656640067931 1616760130634484960101897)
        ·
          refine ⟨1212570097975863720076423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1616760130634484960101897 1212570097975863720076423)
          ·
            refine ⟨1818855146963795580114635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212570097975863720076423 1818855146963795580114635)
            ·
              refine ⟨2728282720445693370171953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1818855146963795580114635 2728282720445693370171953)
              ·
                refine ⟨2046212040334270027628965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728282720445693370171953 2046212040334270027628965)
                ·
                  refine ⟨383664757562675630180431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046212040334270027628965 383664757562675630180431)
                  ·
                    rfl

theorem cell21_1681165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_1681165 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681165 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681165 prefixEnd_1681165 := by exact prefixLift 1681165
  have htrace : WordTrace (prefixWord ++ tailWord_1681165) baseStart_1681165 baseEnd_1681165 := by
    simpa [prefixWord, tailWord_1681165, baseEnd_1681165] using wordTrace_append hprefix tailTrace_1681165
  have hstable : (prefixWord ++ tailWord_1681165).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681165).length < 2 ^ (prefixWord ++ tailWord_1681165).sum := by decide
  have hdescent : baseEnd_1681165 < baseStart_1681165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681204 : List Nat := [2, 5, 1, 1, 2, 3, 2, 5]
def baseStart_1681204 : Nat := 118140960795 + 1681204 * 2 ^ 59
def prefixEnd_1681204 : Nat := 4983230072969 + 3 ^ 40 * 1681204 * 2
def baseEnd_1681204 : Nat := 127891219298006743010117

theorem tailTrace_1681204 : CollatzResearch.WordTrace tailWord_1681204 prefixEnd_1681204 127891219298006743010117 := by
  unfold tailWord_1681204
  simp only [CollatzResearch.WordTrace]
  refine ⟨30659273700646254814489333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40879031600861673085985777 30659273700646254814489333)
  ·
    refine ⟨2874306909435586388858375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30659273700646254814489333 2874306909435586388858375)
    ·
      refine ⟨4311460364153379583287563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2874306909435586388858375 4311460364153379583287563)
      ·
        refine ⟨6467190546230069374931345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311460364153379583287563 6467190546230069374931345)
        ·
          refine ⟨4850392909672552031198509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6467190546230069374931345 4850392909672552031198509)
          ·
            refine ⟨1818897341127207011699441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4850392909672552031198509 1818897341127207011699441)
            ·
              refine ⟨1364173005845405258774581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818897341127207011699441 1364173005845405258774581)
              ·
                refine ⟨127891219298006743010117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1364173005845405258774581 127891219298006743010117)
                ·
                  rfl

theorem cell21_1681204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 5].length) (baseStart_1681204 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681204 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681204 prefixEnd_1681204 := by exact prefixLift 1681204
  have htrace : WordTrace (prefixWord ++ tailWord_1681204) baseStart_1681204 baseEnd_1681204 := by
    simpa [prefixWord, tailWord_1681204, baseEnd_1681204] using wordTrace_append hprefix tailTrace_1681204
  have hstable : (prefixWord ++ tailWord_1681204).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681204).length < 2 ^ (prefixWord ++ tailWord_1681204).sum := by decide
  have hdescent : baseEnd_1681204 < baseStart_1681204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681274 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 8]
def baseStart_1681274 : Nat := 118140960795 + 1681274 * 2 ^ 59
def prefixEnd_1681274 : Nat := 4983230072969 + 3 ^ 40 * 1681274 * 2
def baseEnd_1681274 : Nat := 383689632847715662863541

theorem tailTrace_1681274 : CollatzResearch.WordTrace tailWord_1681274 prefixEnd_1681274 383689632847715662863541 := by
  unfold tailWord_1681274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330275127759727896006719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40880733674025941056017917 15330275127759727896006719)
  ·
    refine ⟨22995412691639591844010079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15330275127759727896006719 22995412691639591844010079)
    ·
      refine ⟨34493119037459387766015119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22995412691639591844010079 34493119037459387766015119)
      ·
        refine ⟨51739678556189081649022679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34493119037459387766015119 51739678556189081649022679)
        ·
          refine ⟨77609517834283622473534019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51739678556189081649022679 77609517834283622473534019)
          ·
            refine ⟨116414276751425433710301029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77609517834283622473534019 116414276751425433710301029)
            ·
              refine ⟨21827676890892268820681443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 116414276751425433710301029 21827676890892268820681443)
              ·
                refine ⟨32741515336338403231022165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21827676890892268820681443 32741515336338403231022165)
                ·
                  refine ⟨383689632847715662863541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 32741515336338403231022165 383689632847715662863541)
                  ·
                    rfl

theorem cell21_1681274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 8].length) (baseStart_1681274 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681274 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681274 prefixEnd_1681274 := by exact prefixLift 1681274
  have htrace : WordTrace (prefixWord ++ tailWord_1681274) baseStart_1681274 baseEnd_1681274 := by
    simpa [prefixWord, tailWord_1681274, baseEnd_1681274] using wordTrace_append hprefix tailTrace_1681274
  have hstable : (prefixWord ++ tailWord_1681274).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681274).length < 2 ^ (prefixWord ++ tailWord_1681274).sum := by decide
  have hdescent : baseEnd_1681274 < baseStart_1681274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681277 : List Nat := [1, 4, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1681277 : Nat := 118140960795 + 1681277 * 2 ^ 59
def prefixEnd_1681277 : Nat := 4983230072969 + 3 ^ 40 * 1681277 * 2
def baseEnd_1681277 : Nat := 383690317488588324313535

theorem tailTrace_1681277 : CollatzResearch.WordTrace tailWord_1681277 prefixEnd_1681277 383690317488588324313535 := by
  unfold tailWord_1681277
  simp only [CollatzResearch.WordTrace]
  refine ⟨61321209930028043096386085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40880806620018695397590723 61321209930028043096386085)
  ·
    refine ⟨11497726861880258080572391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61321209930028043096386085 11497726861880258080572391)
    ·
      refine ⟨17246590292820387120858587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11497726861880258080572391 17246590292820387120858587)
      ·
        refine ⟨25869885439230580681287881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17246590292820387120858587 25869885439230580681287881)
        ·
          refine ⟨19402414079422935510965911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25869885439230580681287881 19402414079422935510965911)
          ·
            refine ⟨29103621119134403266448867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19402414079422935510965911 29103621119134403266448867)
            ·
              refine ⟨43655431678701604899673301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29103621119134403266448867 43655431678701604899673301)
              ·
                refine ⟨1023174179969568864836093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43655431678701604899673301 1023174179969568864836093)
                ·
                  refine ⟨383690317488588324313535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023174179969568864836093 383690317488588324313535)
                  ·
                    rfl

theorem cell21_1681277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1681277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681277 prefixEnd_1681277 := by exact prefixLift 1681277
  have htrace : WordTrace (prefixWord ++ tailWord_1681277) baseStart_1681277 baseEnd_1681277 := by
    simpa [prefixWord, tailWord_1681277, baseEnd_1681277] using wordTrace_append hprefix tailTrace_1681277
  have hstable : (prefixWord ++ tailWord_1681277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681277).length < 2 ^ (prefixWord ++ tailWord_1681277).sum := by decide
  have hdescent : baseEnd_1681277 < baseStart_1681277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681305 : List Nat := [1, 2, 1, 2, 1, 3, 5, 6]
def baseStart_1681305 : Nat := 118140960795 + 1681305 * 2 ^ 59
def prefixEnd_1681305 : Nat := 4983230072969 + 3 ^ 40 * 1681305 * 2
def baseEnd_1681305 : Nat := 127898902490022165948937

theorem tailTrace_1681305 : CollatzResearch.WordTrace tailWord_1681305 prefixEnd_1681305 127898902490022165948937 := by
  unfold tailWord_1681305
  simp only [CollatzResearch.WordTrace]
  refine ⟨61322231173926603878405369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40881487449284402585603579 61322231173926603878405369)
  ·
    refine ⟨45991673380444952908804027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61322231173926603878405369 45991673380444952908804027)
    ·
      refine ⟨68987510070667429363206041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45991673380444952908804027 68987510070667429363206041)
      ·
        refine ⟨51740632553000572022404531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68987510070667429363206041 51740632553000572022404531)
        ·
          refine ⟨77610948829500858033606797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51740632553000572022404531 77610948829500858033606797)
          ·
            refine ⟨29104105811062821762602549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77610948829500858033606797 29104105811062821762602549)
            ·
              refine ⟨2728509919787139540243989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29104105811062821762602549 2728509919787139540243989)
              ·
                refine ⟨127898902490022165948937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2728509919787139540243989 127898902490022165948937)
                ·
                  rfl

theorem cell21_1681305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 6].length) (baseStart_1681305 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681305 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681305 prefixEnd_1681305 := by exact prefixLift 1681305
  have htrace : WordTrace (prefixWord ++ tailWord_1681305) baseStart_1681305 baseEnd_1681305 := by
    simpa [prefixWord, tailWord_1681305, baseEnd_1681305] using wordTrace_append hprefix tailTrace_1681305
  have hstable : (prefixWord ++ tailWord_1681305).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681305).length < 2 ^ (prefixWord ++ tailWord_1681305).sum := by decide
  have hdescent : baseEnd_1681305 < baseStart_1681305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681308 : List Nat := [2, 2, 3, 3, 1, 1, 2, 3, 4]
def baseStart_1681308 : Nat := 118140960795 + 1681308 * 2 ^ 59
def prefixEnd_1681308 : Nat := 4983230072969 + 3 ^ 40 * 1681308 * 2
def baseEnd_1681308 : Nat := 383697392110939159296805

theorem tailTrace_1681308 : CollatzResearch.WordTrace tailWord_1681308 prefixEnd_1681308 383697392110939159296805 := by
  unfold tailWord_1681308
  simp only [CollatzResearch.WordTrace]
  refine ⟨30661170296457867695382289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40881560395277156927176385 30661170296457867695382289)
  ·
    refine ⟨22995877722343400771536717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30661170296457867695382289 22995877722343400771536717)
    ·
      refine ⟨8623454145878775289326269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22995877722343400771536717 8623454145878775289326269)
      ·
        refine ⟨3233795304704540733497351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8623454145878775289326269 3233795304704540733497351)
        ·
          refine ⟨4850692957056811100246027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3233795304704540733497351 4850692957056811100246027)
          ·
            refine ⟨7276039435585216650369041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4850692957056811100246027 7276039435585216650369041)
            ·
              refine ⟨5457029576688912487776781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7276039435585216650369041 5457029576688912487776781)
              ·
                refine ⟨2046386091258342182916293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5457029576688912487776781 2046386091258342182916293)
                ·
                  refine ⟨383697392110939159296805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046386091258342182916293 383697392110939159296805)
                  ·
                    rfl

theorem cell21_1681308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 2, 3, 4].length) (baseStart_1681308 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681308 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681308 prefixEnd_1681308 := by exact prefixLift 1681308
  have htrace : WordTrace (prefixWord ++ tailWord_1681308) baseStart_1681308 baseEnd_1681308 := by
    simpa [prefixWord, tailWord_1681308, baseEnd_1681308] using wordTrace_append hprefix tailTrace_1681308
  have hstable : (prefixWord ++ tailWord_1681308).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681308).length < 2 ^ (prefixWord ++ tailWord_1681308).sum := by decide
  have hdescent : baseEnd_1681308 < baseStart_1681308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681395 : List Nat := [1, 1, 1, 2, 2, 2, 1, 4, 7]
def baseStart_1681395 : Nat := 118140960795 + 1681395 * 2 ^ 59
def prefixEnd_1681395 : Nat := 4983230072969 + 3 ^ 40 * 1681395 * 2
def baseEnd_1681395 : Nat := 383717246696246341346627

theorem tailTrace_1681395 : CollatzResearch.WordTrace tailWord_1681395 prefixEnd_1681395 383717246696246341346627 := by
  unfold tailWord_1681395
  simp only [CollatzResearch.WordTrace]
  refine ⟨61325513743600549249181639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40883675829067032832787759 61325513743600549249181639)
  ·
    refine ⟨91988270615400823873772459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61325513743600549249181639 91988270615400823873772459)
    ·
      refine ⟨137982405923101235810658689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91988270615400823873772459 137982405923101235810658689)
      ·
        refine ⟨103486804442325926857994017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137982405923101235810658689 103486804442325926857994017)
        ·
          refine ⟨77615103331744445143495513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103486804442325926857994017 77615103331744445143495513)
          ·
            refine ⟨58211327498808333857621635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77615103331744445143495513 58211327498808333857621635)
            ·
              refine ⟨87316991248212500786432453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58211327498808333857621635 87316991248212500786432453)
              ·
                refine ⟨16371935859039843897456085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87316991248212500786432453 16371935859039843897456085)
                ·
                  refine ⟨383717246696246341346627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16371935859039843897456085 383717246696246341346627)
                  ·
                    rfl

theorem cell21_1681395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 4, 7].length) (baseStart_1681395 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681395 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681395 prefixEnd_1681395 := by exact prefixLift 1681395
  have htrace : WordTrace (prefixWord ++ tailWord_1681395) baseStart_1681395 baseEnd_1681395 := by
    simpa [prefixWord, tailWord_1681395, baseEnd_1681395] using wordTrace_append hprefix tailTrace_1681395
  have hstable : (prefixWord ++ tailWord_1681395).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681395).length < 2 ^ (prefixWord ++ tailWord_1681395).sum := by decide
  have hdescent : baseEnd_1681395 < baseStart_1681395 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681418 : List Nat := [3, 1, 2, 2, 5, 1, 2, 1, 4]
def baseStart_1681418 : Nat := 118140960795 + 1681418 * 2 ^ 59
def prefixEnd_1681418 : Nat := 4983230072969 + 3 ^ 40 * 1681418 * 2
def baseEnd_1681418 : Nat := 383722495609603412463247

theorem tailTrace_1681418 : CollatzResearch.WordTrace tailWord_1681418 prefixEnd_1681418 383722495609603412463247 := by
  unfold tailWord_1681418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15331588155629306044317227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40884235081678149451512605 15331588155629306044317227)
  ·
    refine ⟨22997382233443959066475841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15331588155629306044317227 22997382233443959066475841)
    ·
      refine ⟨17248036675082969299856881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22997382233443959066475841 17248036675082969299856881)
      ·
        refine ⟨12936027506312226974892661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17248036675082969299856881 12936027506312226974892661)
        ·
          refine ⟨1212752578716771278896187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12936027506312226974892661 1212752578716771278896187)
          ·
            refine ⟨1819128868075156918344281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1212752578716771278896187 1819128868075156918344281)
            ·
              refine ⟨1364346651056367688758211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819128868075156918344281 1364346651056367688758211)
              ·
                refine ⟨2046519976584551533137317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364346651056367688758211 2046519976584551533137317)
                ·
                  refine ⟨383722495609603412463247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046519976584551533137317 383722495609603412463247)
                  ·
                    rfl

theorem cell21_1681418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 4].length) (baseStart_1681418 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681418 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681418 prefixEnd_1681418 := by exact prefixLift 1681418
  have htrace : WordTrace (prefixWord ++ tailWord_1681418) baseStart_1681418 baseEnd_1681418 := by
    simpa [prefixWord, tailWord_1681418, baseEnd_1681418] using wordTrace_append hprefix tailTrace_1681418
  have hstable : (prefixWord ++ tailWord_1681418).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681418).length < 2 ^ (prefixWord ++ tailWord_1681418).sum := by decide
  have hdescent : baseEnd_1681418 < baseStart_1681418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681519 : List Nat := [1, 1, 2, 1, 3, 4, 3, 2, 4]
def baseStart_1681519 : Nat := 118140960795 + 1681519 * 2 ^ 59
def prefixEnd_1681519 : Nat := 4983230072969 + 3 ^ 40 * 1681519 * 2
def baseEnd_1681519 : Nat := 383745545185649681279707

theorem tailTrace_1681519 : CollatzResearch.WordTrace tailWord_1681519 prefixEnd_1681519 383745545185649681279707 := by
  unfold tailWord_1681519
  simp only [CollatzResearch.WordTrace]
  refine ⟨61330036395151318426695611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40886690930100878951130407 61330036395151318426695611)
  ·
    refine ⟨91995054592726977640043417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61330036395151318426695611 91995054592726977640043417)
    ·
      refine ⟨68996290944545233230032563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91995054592726977640043417 68996290944545233230032563)
      ·
        refine ⟨103494436416817849845048845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68996290944545233230032563 103494436416817849845048845)
        ·
          refine ⟨38810413656306693691893317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103494436416817849845048845 38810413656306693691893317)
          ·
            refine ⟨7276952560557505067229997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38810413656306693691893317 7276952560557505067229997)
            ·
              refine ⟨2728857210209064400211249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7276952560557505067229997 2728857210209064400211249)
              ·
                refine ⟨2046642907656798300158437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2728857210209064400211249 2046642907656798300158437)
                ·
                  refine ⟨383745545185649681279707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2046642907656798300158437 383745545185649681279707)
                  ·
                    rfl

theorem cell21_1681519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 2, 4].length) (baseStart_1681519 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681519 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681519 prefixEnd_1681519 := by exact prefixLift 1681519
  have htrace : WordTrace (prefixWord ++ tailWord_1681519) baseStart_1681519 baseEnd_1681519 := by
    simpa [prefixWord, tailWord_1681519, baseEnd_1681519] using wordTrace_append hprefix tailTrace_1681519
  have hstable : (prefixWord ++ tailWord_1681519).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681519).length < 2 ^ (prefixWord ++ tailWord_1681519).sum := by decide
  have hdescent : baseEnd_1681519 < baseStart_1681519 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681550 : List Nat := [4, 1, 1, 3, 3, 1, 1, 7]
def baseStart_1681550 : Nat := 118140960795 + 1681550 * 2 ^ 59
def prefixEnd_1681550 : Nat := 4983230072969 + 3 ^ 40 * 1681550 * 2
def baseEnd_1681550 : Nat := 127917539936000172087659

theorem tailTrace_1681550 : CollatzResearch.WordTrace tailWord_1681550 prefixEnd_1681550 127917539936000172087659 := by
  unfold tailWord_1681550
  simp only [CollatzResearch.WordTrace]
  refine ⟨7666395882254876340134263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40887444705359340480716069 7666395882254876340134263)
  ·
    refine ⟨11499593823382314510201395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7666395882254876340134263 11499593823382314510201395)
    ·
      refine ⟨17249390735073471765302093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11499593823382314510201395 17249390735073471765302093)
      ·
        refine ⟨6468521525652551911988285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17249390735073471765302093 6468521525652551911988285)
        ·
          refine ⟨2425695572119706966995607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6468521525652551911988285 2425695572119706966995607)
          ·
            refine ⟨3638543358179560450493411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2425695572119706966995607 3638543358179560450493411)
            ·
              refine ⟨5457815037269340675740117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3638543358179560450493411 5457815037269340675740117)
              ·
                refine ⟨127917539936000172087659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5457815037269340675740117 127917539936000172087659)
                ·
                  rfl

theorem cell21_1681550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 7].length) (baseStart_1681550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681550 prefixEnd_1681550 := by exact prefixLift 1681550
  have htrace : WordTrace (prefixWord ++ tailWord_1681550) baseStart_1681550 baseEnd_1681550 := by
    simpa [prefixWord, tailWord_1681550, baseEnd_1681550] using wordTrace_append hprefix tailTrace_1681550
  have hstable : (prefixWord ++ tailWord_1681550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681550).length < 2 ^ (prefixWord ++ tailWord_1681550).sum := by decide
  have hdescent : baseEnd_1681550 < baseStart_1681550 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681556 : List Nat := [2, 4, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1681556 : Nat := 118140960795 + 1681556 * 2 ^ 59
def prefixEnd_1681556 : Nat := 4983230072969 + 3 ^ 40 * 1681556 * 2
def baseEnd_1681556 : Nat := 383753989089745839162965

theorem tailTrace_1681556 : CollatzResearch.WordTrace tailWord_1681556 prefixEnd_1681556 383753989089745839162965 := by
  unfold tailWord_1681556
  simp only [CollatzResearch.WordTrace]
  refine ⟨30665692948008636872896261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40887590597344849163861681 30665692948008636872896261)
  ·
    refine ⟨5749817427751619413668049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30665692948008636872896261 5749817427751619413668049)
    ·
      refine ⟨4312363070813714560251037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5749817427751619413668049 4312363070813714560251037)
      ·
        refine ⟨1617136151555142960094139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4312363070813714560251037 1617136151555142960094139)
        ·
          refine ⟨2425704227332714440141209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617136151555142960094139 2425704227332714440141209)
          ·
            refine ⟨1819278170499535830105907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2425704227332714440141209 1819278170499535830105907)
            ·
              refine ⟨2728917255749303745158861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819278170499535830105907 2728917255749303745158861)
              ·
                refine ⟨1023343970905988904434573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2728917255749303745158861 1023343970905988904434573)
                ·
                  refine ⟨383753989089745839162965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023343970905988904434573 383753989089745839162965)
                  ·
                    rfl

theorem cell21_1681556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1681556 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681556 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681556 prefixEnd_1681556 := by exact prefixLift 1681556
  have htrace : WordTrace (prefixWord ++ tailWord_1681556) baseStart_1681556 baseEnd_1681556 := by
    simpa [prefixWord, tailWord_1681556, baseEnd_1681556] using wordTrace_append hprefix tailTrace_1681556
  have hstable : (prefixWord ++ tailWord_1681556).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681556).length < 2 ^ (prefixWord ++ tailWord_1681556).sum := by decide
  have hdescent : baseEnd_1681556 < baseStart_1681556 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681581 : List Nat := [1, 5, 2, 1, 2, 1, 3, 1, 5]
def baseStart_1681581 : Nat := 118140960795 + 1681581 * 2 ^ 59
def prefixEnd_1681581 : Nat := 4983230072969 + 3 ^ 40 * 1681581 * 2
def baseEnd_1681581 : Nat := 383759694430351351246247

theorem tailTrace_1681581 : CollatzResearch.WordTrace tailWord_1681581 prefixEnd_1681581 383759694430351351246247 := by
  unfold tailWord_1681581
  simp only [CollatzResearch.WordTrace]
  refine ⟨61332297720926703015452597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40888198480617802010301731 61332297720926703015452597)
  ·
    refine ⟨5749902911336878407698681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61332297720926703015452597 5749902911336878407698681)
    ·
      refine ⟨4312427183502658805774011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5749902911336878407698681 4312427183502658805774011)
      ·
        refine ⟨6468640775253988208661017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4312427183502658805774011 6468640775253988208661017)
        ·
          refine ⟨4851480581440491156495763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6468640775253988208661017 4851480581440491156495763)
          ·
            refine ⟨7277220872160736734743645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4851480581440491156495763 7277220872160736734743645)
            ·
              refine ⟨2728957827060276275528867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7277220872160736734743645 2728957827060276275528867)
              ·
                refine ⟨4093436740590414413293301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728957827060276275528867 4093436740590414413293301)
                ·
                  refine ⟨383759694430351351246247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4093436740590414413293301 383759694430351351246247)
                  ·
                    rfl

theorem cell21_1681581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_1681581 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681581 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681581 prefixEnd_1681581 := by exact prefixLift 1681581
  have htrace : WordTrace (prefixWord ++ tailWord_1681581) baseStart_1681581 baseEnd_1681581 := by
    simpa [prefixWord, tailWord_1681581, baseEnd_1681581] using wordTrace_append hprefix tailTrace_1681581
  have hstable : (prefixWord ++ tailWord_1681581).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681581).length < 2 ^ (prefixWord ++ tailWord_1681581).sum := by decide
  have hdescent : baseEnd_1681581 < baseStart_1681581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681744 : List Nat := [2, 1, 1, 1, 1, 6, 9]
def baseStart_1681744 : Nat := 118140960795 + 1681744 * 2 ^ 59
def prefixEnd_1681744 : Nat := 4983230072969 + 3 ^ 40 * 1681744 * 2
def baseEnd_1681744 : Nat := 42644099250122143336583

theorem tailTrace_1681744 : CollatzResearch.WordTrace tailWord_1681744 prefixEnd_1681744 42644099250122143336583 := by
  unfold tailWord_1681744
  simp only [CollatzResearch.WordTrace]
  refine ⟨30669121409668090926818143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40892161879557454569090857 30669121409668090926818143)
  ·
    refine ⟨46003682114502136390227215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30669121409668090926818143 46003682114502136390227215)
    ·
      refine ⟨69005523171753204585340823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46003682114502136390227215 69005523171753204585340823)
      ·
        refine ⟨103508284757629806878011235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69005523171753204585340823 103508284757629806878011235)
        ·
          refine ⟨155262427136444710317016853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103508284757629806878011235 155262427136444710317016853)
          ·
            refine ⟨7277926272020845796110165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 155262427136444710317016853 7277926272020845796110165)
            ·
              refine ⟨42644099250122143336583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7277926272020845796110165 42644099250122143336583)
              ·
                rfl

theorem cell21_1681744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 9].length) (baseStart_1681744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681744 prefixEnd_1681744 := by exact prefixLift 1681744
  have htrace : WordTrace (prefixWord ++ tailWord_1681744) baseStart_1681744 baseEnd_1681744 := by
    simpa [prefixWord, tailWord_1681744, baseEnd_1681744] using wordTrace_append hprefix tailTrace_1681744
  have hstable : (prefixWord ++ tailWord_1681744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681744).length < 2 ^ (prefixWord ++ tailWord_1681744).sum := by decide
  have hdescent : baseEnd_1681744 < baseStart_1681744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681857 : List Nat := [1, 2, 7, 1, 1, 1, 1, 1, 6]
def baseStart_1681857 : Nat := 118140960795 + 1681857 * 2 ^ 59
def prefixEnd_1681857 : Nat := 4983230072969 + 3 ^ 40 * 1681857 * 2
def baseEnd_1681857 : Nat := 383822681390636204645683

theorem tailTrace_1681857 : CollatzResearch.WordTrace tailWord_1681857 prefixEnd_1681857 383822681390636204645683 := by
  unfold tailWord_1681857
  simp only [CollatzResearch.WordTrace]
  refine ⟨61342364267926802152499825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40894909511951201434999883 61342364267926802152499825)
  ·
    refine ⟨46006773200945101614374869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61342364267926802152499825 46006773200945101614374869)
    ·
      refine ⟨1078283746897150819086911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 46006773200945101614374869 1078283746897150819086911)
      ·
        refine ⟨1617425620345726228630367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078283746897150819086911 1617425620345726228630367)
        ·
          refine ⟨2426138430518589342945551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617425620345726228630367 2426138430518589342945551)
          ·
            refine ⟨3639207645777884014418327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426138430518589342945551 3639207645777884014418327)
            ·
              refine ⟨5458811468666826021627491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639207645777884014418327 5458811468666826021627491)
              ·
                refine ⟨8188217203000239032441237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5458811468666826021627491 8188217203000239032441237)
                ·
                  refine ⟨383822681390636204645683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8188217203000239032441237 383822681390636204645683)
                  ·
                    rfl

theorem cell21_1681857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 1, 1, 1, 6].length) (baseStart_1681857 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681857 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681857 prefixEnd_1681857 := by exact prefixLift 1681857
  have htrace : WordTrace (prefixWord ++ tailWord_1681857) baseStart_1681857 baseEnd_1681857 := by
    simpa [prefixWord, tailWord_1681857, baseEnd_1681857] using wordTrace_append hprefix tailTrace_1681857
  have hstable : (prefixWord ++ tailWord_1681857).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681857).length < 2 ^ (prefixWord ++ tailWord_1681857).sum := by decide
  have hdescent : baseEnd_1681857 < baseStart_1681857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681902 : List Nat := [4, 1, 2, 1, 2, 4, 1, 3, 3]
def baseStart_1681902 : Nat := 118140960795 + 1681902 * 2 ^ 59
def prefixEnd_1681902 : Nat := 4983230072969 + 3 ^ 40 * 1681902 * 2
def baseEnd_1681902 : Nat := 383832951003726126395591

theorem tailTrace_1681902 : CollatzResearch.WordTrace tailWord_1681902 prefixEnd_1681902 383832951003726126395591 := by
  unfold tailWord_1681902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7668000694095471854735995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40896003701842516558591973 7668000694095471854735995)
  ·
    refine ⟨11502001041143207782103993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7668000694095471854735995 11502001041143207782103993)
    ·
      refine ⟨8626500780857405836577995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11502001041143207782103993 8626500780857405836577995)
      ·
        refine ⟨12939751171286108754866993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8626500780857405836577995 12939751171286108754866993)
        ·
          refine ⟨9704813378464581566150245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12939751171286108754866993 9704813378464581566150245)
          ·
            refine ⟨1819652508462109043653171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9704813378464581566150245 1819652508462109043653171)
            ·
              refine ⟨2729478762693163565479757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819652508462109043653171 2729478762693163565479757)
              ·
                refine ⟨1023554536009936337054909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2729478762693163565479757 1023554536009936337054909)
                ·
                  refine ⟨383832951003726126395591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023554536009936337054909 383832951003726126395591)
                  ·
                    rfl

theorem cell21_1681902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 4, 1, 3, 3].length) (baseStart_1681902 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681902 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681902 prefixEnd_1681902 := by exact prefixLift 1681902
  have htrace : WordTrace (prefixWord ++ tailWord_1681902) baseStart_1681902 baseEnd_1681902 := by
    simpa [prefixWord, tailWord_1681902, baseEnd_1681902] using wordTrace_append hprefix tailTrace_1681902
  have hstable : (prefixWord ++ tailWord_1681902).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681902).length < 2 ^ (prefixWord ++ tailWord_1681902).sum := by decide
  have hdescent : baseEnd_1681902 < baseStart_1681902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681933 : List Nat := [1, 7, 1, 1, 1, 2, 1, 3, 4]
def baseStart_1681933 : Nat := 118140960795 + 1681933 * 2 ^ 59
def prefixEnd_1681933 : Nat := 4983230072969 + 3 ^ 40 * 1681933 * 2
def baseEnd_1681933 : Nat := 383840025626076961378861

theorem tailTrace_1681933 : CollatzResearch.WordTrace tailWord_1681933 prefixEnd_1681933 383840025626076961378861 := by
  unfold tailWord_1681933
  simp only [CollatzResearch.WordTrace]
  refine ⟨61345136215651467132266453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40896757477100978088177635 61345136215651467132266453)
  ·
    refine ⟨1437776630054331260912495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 61345136215651467132266453 1437776630054331260912495)
    ·
      refine ⟨2156664945081496891368743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1437776630054331260912495 2156664945081496891368743)
      ·
        refine ⟨3234997417622245337053115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156664945081496891368743 3234997417622245337053115)
        ·
          refine ⟨4852496126433368005579673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3234997417622245337053115 4852496126433368005579673)
          ·
            refine ⟨3639372094825026004184755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4852496126433368005579673 3639372094825026004184755)
            ·
              refine ⟨5459058142237539006277133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3639372094825026004184755 5459058142237539006277133)
              ·
                refine ⟨2047146803339077127353925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5459058142237539006277133 2047146803339077127353925)
                ·
                  refine ⟨383840025626076961378861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2047146803339077127353925 383840025626076961378861)
                  ·
                    rfl

theorem cell21_1681933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_1681933 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681933 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681933 prefixEnd_1681933 := by exact prefixLift 1681933
  have htrace : WordTrace (prefixWord ++ tailWord_1681933) baseStart_1681933 baseEnd_1681933 := by
    simpa [prefixWord, tailWord_1681933, baseEnd_1681933] using wordTrace_append hprefix tailTrace_1681933
  have hstable : (prefixWord ++ tailWord_1681933).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681933).length < 2 ^ (prefixWord ++ tailWord_1681933).sum := by decide
  have hdescent : baseEnd_1681933 < baseStart_1681933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681978 : List Nat := [3, 1, 1, 1, 3, 5, 2, 2, 3]
def baseStart_1681978 : Nat := 118140960795 + 1681978 * 2 ^ 59
def prefixEnd_1681978 : Nat := 4983230072969 + 3 ^ 40 * 1681978 * 2
def baseEnd_1681978 : Nat := 383850295239166883128769

theorem tailTrace_1681978 : CollatzResearch.WordTrace tailWord_1681978 prefixEnd_1681978 383850295239166883128769 := by
  unfold tailWord_1681978
  simp only [CollatzResearch.WordTrace]
  refine ⟨15336694375122109954413647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40897851666992293211769725 15336694375122109954413647)
  ·
    refine ⟨23005041562683164931620471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15336694375122109954413647 23005041562683164931620471)
    ·
      refine ⟨34507562344024747397430707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005041562683164931620471 34507562344024747397430707)
      ·
        refine ⟨51761343516037121096146061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34507562344024747397430707 51761343516037121096146061)
        ·
          refine ⟨19410503818513920411054773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51761343516037121096146061 19410503818513920411054773)
          ·
            refine ⟨1819734732985680038536385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19410503818513920411054773 1819734732985680038536385)
            ·
              refine ⟨1364801049739260028902289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819734732985680038536385 1364801049739260028902289)
              ·
                refine ⟨1023600787304445021676717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364801049739260028902289 1023600787304445021676717)
                ·
                  refine ⟨383850295239166883128769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023600787304445021676717 383850295239166883128769)
                  ·
                    rfl

theorem cell21_1681978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 5, 2, 2, 3].length) (baseStart_1681978 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681978 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681978 prefixEnd_1681978 := by exact prefixLift 1681978
  have htrace : WordTrace (prefixWord ++ tailWord_1681978) baseStart_1681978 baseEnd_1681978 := by
    simpa [prefixWord, tailWord_1681978, baseEnd_1681978] using wordTrace_append hprefix tailTrace_1681978
  have hstable : (prefixWord ++ tailWord_1681978).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681978).length < 2 ^ (prefixWord ++ tailWord_1681978).sum := by decide
  have hdescent : baseEnd_1681978 < baseStart_1681978 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1681989 : List Nat := [1, 3, 1, 1, 1, 7, 1, 6]
def baseStart_1681989 : Nat := 118140960795 + 1681989 * 2 ^ 59
def prefixEnd_1681989 : Nat := 4983230072969 + 3 ^ 40 * 1681989 * 2
def baseEnd_1681989 : Nat := 127950935196344436148471

theorem tailTrace_1681989 : CollatzResearch.WordTrace tailWord_1681989 prefixEnd_1681989 127950935196344436148471 := by
  unfold tailWord_1681989
  simp only [CollatzResearch.WordTrace]
  refine ⟨61347178703448588696305021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40898119135632392464203347 61347178703448588696305021)
  ·
    refine ⟨23005192013793220761114383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61347178703448588696305021 23005192013793220761114383)
    ·
      refine ⟨34507788020689831141671575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23005192013793220761114383 34507788020689831141671575)
      ·
        refine ⟨51761682031034746712507363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34507788020689831141671575 51761682031034746712507363)
        ·
          refine ⟨77642523046552120068761045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51761682031034746712507363 77642523046552120068761045)
          ·
            refine ⟨1819746633903565314111587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 77642523046552120068761045 1819746633903565314111587)
            ·
              refine ⟨2729619950855347971167381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1819746633903565314111587 2729619950855347971167381)
              ·
                refine ⟨127950935196344436148471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 2729619950855347971167381 127950935196344436148471)
                ·
                  rfl

theorem cell21_1681989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 7, 1, 6].length) (baseStart_1681989 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1681989 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1681989 prefixEnd_1681989 := by exact prefixLift 1681989
  have htrace : WordTrace (prefixWord ++ tailWord_1681989) baseStart_1681989 baseEnd_1681989 := by
    simpa [prefixWord, tailWord_1681989, baseEnd_1681989] using wordTrace_append hprefix tailTrace_1681989
  have hstable : (prefixWord ++ tailWord_1681989).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1681989).length < 2 ^ (prefixWord ++ tailWord_1681989).sum := by decide
  have hdescent : baseEnd_1681989 < baseStart_1681989 := by decide
  rcases family_descends (prefixWord ++ tailWord_1681989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682037 : List Nat := [1, 3, 4, 2, 2, 1, 2, 1, 5]
def baseStart_1682037 : Nat := 118140960795 + 1682037 * 2 ^ 59
def prefixEnd_1682037 : Nat := 4983230072969 + 3 ^ 40 * 1682037 * 2
def baseEnd_1682037 : Nat := 383863759842995891645315

theorem tailTrace_1682037 : CollatzResearch.WordTrace tailWord_1682037 prefixEnd_1682037 383863759842995891645315 := by
  unfold tailWord_1682037
  simp only [CollatzResearch.WordTrace]
  refine ⟨61348929407274692894052365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40899286271516461929368243 61348929407274692894052365)
  ·
    refine ⟨23005848527728009835269637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61348929407274692894052365 23005848527728009835269637)
    ·
      refine ⟨4313596598949001844113057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23005848527728009835269637 4313596598949001844113057)
      ·
        refine ⟨3235197449211751383084793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4313596598949001844113057 3235197449211751383084793)
        ·
          refine ⟨2426398086908813537313595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3235197449211751383084793 2426398086908813537313595)
          ·
            refine ⟨3639597130363220305970393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2426398086908813537313595 3639597130363220305970393)
            ·
              refine ⟨2729697847772415229477795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3639597130363220305970393 2729697847772415229477795)
              ·
                refine ⟨4094546771658622844216693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2729697847772415229477795 4094546771658622844216693)
                ·
                  refine ⟨383863759842995891645315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4094546771658622844216693 383863759842995891645315)
                  ·
                    rfl

theorem cell21_1682037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_1682037 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682037 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682037 prefixEnd_1682037 := by exact prefixLift 1682037
  have htrace : WordTrace (prefixWord ++ tailWord_1682037) baseStart_1682037 baseEnd_1682037 := by
    simpa [prefixWord, tailWord_1682037, baseEnd_1682037] using wordTrace_append hprefix tailTrace_1682037
  have hstable : (prefixWord ++ tailWord_1682037).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682037).length < 2 ^ (prefixWord ++ tailWord_1682037).sum := by decide
  have hdescent : baseEnd_1682037 < baseStart_1682037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682102 : List Nat := [5, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_1682102 : Nat := 118140960795 + 1682102 * 2 ^ 59
def prefixEnd_1682102 : Nat := 4983230072969 + 3 ^ 40 * 1682102 * 2
def baseEnd_1682102 : Nat := 383878593728570223061849

theorem tailTrace_1682102 : CollatzResearch.WordTrace tailWord_1682102 prefixEnd_1682102 383878593728570223061849 := by
  unfold tailWord_1682102
  simp only [CollatzResearch.WordTrace]
  refine ⟨3834456259502450562198035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 40900866768026139330112373 3834456259502450562198035)
  ·
    refine ⟨5751684389253675843297053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3834456259502450562198035 5751684389253675843297053)
    ·
      refine ⟨2156881645970128441236395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5751684389253675843297053 2156881645970128441236395)
      ·
        refine ⟨3235322468955192661854593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2156881645970128441236395 3235322468955192661854593)
        ·
          refine ⟨2426491851716394496390945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3235322468955192661854593 2426491851716394496390945)
          ·
            refine ⟨1819868888787295872293209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426491851716394496390945 1819868888787295872293209)
            ·
              refine ⟨1364901666590471904219907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1819868888787295872293209 1364901666590471904219907)
              ·
                refine ⟨2047352499885707856329861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364901666590471904219907 2047352499885707856329861)
                ·
                  refine ⟨383878593728570223061849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2047352499885707856329861 383878593728570223061849)
                  ·
                    rfl

theorem cell21_1682102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_1682102 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682102 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682102 prefixEnd_1682102 := by exact prefixLift 1682102
  have htrace : WordTrace (prefixWord ++ tailWord_1682102) baseStart_1682102 baseEnd_1682102 := by
    simpa [prefixWord, tailWord_1682102, baseEnd_1682102] using wordTrace_append hprefix tailTrace_1682102
  have hstable : (prefixWord ++ tailWord_1682102).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682102).length < 2 ^ (prefixWord ++ tailWord_1682102).sum := by decide
  have hdescent : baseEnd_1682102 < baseStart_1682102 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682234 : List Nat := [3, 1, 1, 1, 6, 2, 2, 5]
def baseStart_1682234 : Nat := 118140960795 + 1682234 * 2 ^ 59
def prefixEnd_1682234 : Nat := 4983230072969 + 3 ^ 40 * 1682234 * 2
def baseEnd_1682234 : Nat := 127969572642322442287193

theorem tailTrace_1682234 : CollatzResearch.WordTrace tailWord_1682234 prefixEnd_1682234 127969572642322442287193 := by
  unfold tailWord_1682234
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339028646890248884743439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40904076391707330359315837 15339028646890248884743439)
  ·
    refine ⟨23008542970335373327115159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15339028646890248884743439 23008542970335373327115159)
    ·
      refine ⟨34512814455503059990672739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23008542970335373327115159 34512814455503059990672739)
      ·
        refine ⟨51769221683254589986009109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34512814455503059990672739 51769221683254589986009109)
        ·
          refine ⟨2426682266402558905594177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51769221683254589986009109 2426682266402558905594177)
          ·
            refine ⟨1820011699801919179195633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426682266402558905594177 1820011699801919179195633)
            ·
              refine ⟨1365008774851439384396725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820011699801919179195633 1365008774851439384396725)
              ·
                refine ⟨127969572642322442287193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1365008774851439384396725 127969572642322442287193)
                ·
                  rfl

theorem cell21_1682234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 5].length) (baseStart_1682234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682234 prefixEnd_1682234 := by exact prefixLift 1682234
  have htrace : WordTrace (prefixWord ++ tailWord_1682234) baseStart_1682234 baseEnd_1682234 := by
    simpa [prefixWord, tailWord_1682234, baseEnd_1682234] using wordTrace_append hprefix tailTrace_1682234
  have hstable : (prefixWord ++ tailWord_1682234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682234).length < 2 ^ (prefixWord ++ tailWord_1682234).sum := by decide
  have hdescent : baseEnd_1682234 < baseStart_1682234 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682265 : List Nat := [1, 2, 1, 2, 2, 5, 3, 2, 3]
def baseStart_1682265 : Nat := 118140960795 + 1682265 * 2 ^ 59
def prefixEnd_1682265 : Nat := 4983230072969 + 3 ^ 40 * 1682265 * 2
def baseEnd_1682265 : Nat := 383915792549318161844849

theorem tailTrace_1682265 : CollatzResearch.WordTrace tailWord_1682265 prefixEnd_1682265 383915792549318161844849 := by
  unfold tailWord_1682265
  simp only [CollatzResearch.WordTrace]
  refine ⟨61357245250448687833352249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40904830166965791888901499 61357245250448687833352249)
  ·
    refine ⟨46017933937836515875014187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61357245250448687833352249 46017933937836515875014187)
    ·
      refine ⟨69026900906754773812521281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46017933937836515875014187 69026900906754773812521281)
      ·
        refine ⟨51770175680066080359390961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69026900906754773812521281 51770175680066080359390961)
        ·
          refine ⟨38827631760049560269543221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51770175680066080359390961 38827631760049560269543221)
          ·
            refine ⟨3640090477504646275269677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38827631760049560269543221 3640090477504646275269677)
            ·
              refine ⟨1365033929064242353226129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3640090477504646275269677 1365033929064242353226129)
              ·
                refine ⟨1023775446798181764919597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365033929064242353226129 1023775446798181764919597)
                ·
                  refine ⟨383915792549318161844849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023775446798181764919597 383915792549318161844849)
                  ·
                    rfl

theorem cell21_1682265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 5, 3, 2, 3].length) (baseStart_1682265 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682265 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682265 prefixEnd_1682265 := by exact prefixLift 1682265
  have htrace : WordTrace (prefixWord ++ tailWord_1682265) baseStart_1682265 baseEnd_1682265 := by
    simpa [prefixWord, tailWord_1682265, baseEnd_1682265] using wordTrace_append hprefix tailTrace_1682265
  have hstable : (prefixWord ++ tailWord_1682265).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682265).length < 2 ^ (prefixWord ++ tailWord_1682265).sum := by decide
  have hdescent : baseEnd_1682265 < baseStart_1682265 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682276 : List Nat := [2, 3, 1, 1, 4, 1, 1, 8]
def baseStart_1682276 : Nat := 118140960795 + 1682276 * 2 ^ 59
def prefixEnd_1682276 : Nat := 4983230072969 + 3 ^ 40 * 1682276 * 2
def baseEnd_1682276 : Nat := 127972767633061529053831

theorem tailTrace_1682276 : CollatzResearch.WordTrace tailWord_1682276 prefixEnd_1682276 127972767633061529053831 := by
  unfold tailWord_1682276
  simp only [CollatzResearch.WordTrace]
  refine ⟨30678823226704418356001341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40905097635605891141335121 30678823226704418356001341)
  ·
    refine ⟨11504558710014156883500503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30678823226704418356001341 11504558710014156883500503)
    ·
      refine ⟨17256838065021235325250755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11504558710014156883500503 17256838065021235325250755)
      ·
        refine ⟨25885257097531852987876133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17256838065021235325250755 25885257097531852987876133)
        ·
          refine ⟨4853485705787222435226775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25885257097531852987876133 4853485705787222435226775)
          ·
            refine ⟨7280228558680833652840163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4853485705787222435226775 7280228558680833652840163)
            ·
              refine ⟨10920342838021250479260245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7280228558680833652840163 10920342838021250479260245)
              ·
                refine ⟨127972767633061529053831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10920342838021250479260245 127972767633061529053831)
                ·
                  rfl

theorem cell21_1682276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 8].length) (baseStart_1682276 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682276 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682276 prefixEnd_1682276 := by exact prefixLift 1682276
  have htrace : WordTrace (prefixWord ++ tailWord_1682276) baseStart_1682276 baseEnd_1682276 := by
    simpa [prefixWord, tailWord_1682276, baseEnd_1682276] using wordTrace_append hprefix tailTrace_1682276
  have hstable : (prefixWord ++ tailWord_1682276).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682276).length < 2 ^ (prefixWord ++ tailWord_1682276).sum := by decide
  have hdescent : baseEnd_1682276 < baseStart_1682276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682279 : List Nat := [1, 1, 5, 1, 2, 2, 4, 1, 4]
def baseStart_1682279 : Nat := 118140960795 + 1682279 * 2 ^ 59
def prefixEnd_1682279 : Nat := 4983230072969 + 3 ^ 40 * 1682279 * 2
def baseEnd_1682279 : Nat := 383918987540057248611487

theorem tailTrace_1682279 : CollatzResearch.WordTrace tailWord_1682279 prefixEnd_1682279 383918987540057248611487 := by
  unfold tailWord_1682279
  simp only [CollatzResearch.WordTrace]
  refine ⟨61357755872397968224361891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40905170581598645482907927 61357755872397968224361891)
  ·
    refine ⟨92036633808596952336542837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61357755872397968224361891 92036633808596952336542837)
    ·
      refine ⟨8628434419555964281550891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92036633808596952336542837 8628434419555964281550891)
      ·
        refine ⟨12942651629333946422326337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8628434419555964281550891 12942651629333946422326337)
        ·
          refine ⟨9706988722000459816744753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12942651629333946422326337 9706988722000459816744753)
          ·
            refine ⟨7280241541500344862558565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9706988722000459816744753 7280241541500344862558565)
            ·
              refine ⟨1365045289031314661729731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7280241541500344862558565 1365045289031314661729731)
              ·
                refine ⟨2047567933546971992594597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365045289031314661729731 2047567933546971992594597)
                ·
                  refine ⟨383918987540057248611487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2047567933546971992594597 383918987540057248611487)
                  ·
                    rfl

theorem cell21_1682279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 4].length) (baseStart_1682279 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682279 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682279 prefixEnd_1682279 := by exact prefixLift 1682279
  have htrace : WordTrace (prefixWord ++ tailWord_1682279) baseStart_1682279 baseEnd_1682279 := by
    simpa [prefixWord, tailWord_1682279, baseEnd_1682279] using wordTrace_append hprefix tailTrace_1682279
  have hstable : (prefixWord ++ tailWord_1682279).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682279).length < 2 ^ (prefixWord ++ tailWord_1682279).sum := by decide
  have hdescent : baseEnd_1682279 < baseStart_1682279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682383 : List Nat := [1, 1, 2, 1, 1, 7, 2, 1, 5]
def baseStart_1682383 : Nat := 118140960795 + 1682383 * 2 ^ 59
def prefixEnd_1682383 : Nat := 4983230072969 + 3 ^ 40 * 1682383 * 2
def baseEnd_1682383 : Nat := 383942721756976178877941

theorem tailTrace_1682383 : CollatzResearch.WordTrace tailWord_1682383 prefixEnd_1682383 383942721756976178877941 := by
  unfold tailWord_1682383
  simp only [CollatzResearch.WordTrace]
  refine ⟨61361549064021193986147803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40907699376014129324098535 61361549064021193986147803)
  ·
    refine ⟨92042323596031790979221705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61361549064021193986147803 92042323596031790979221705)
    ·
      refine ⟨69031742697023843234416279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92042323596031790979221705 69031742697023843234416279)
      ·
        refine ⟨103547614045535764851624419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69031742697023843234416279 103547614045535764851624419)
        ·
          refine ⟨155321421068303647277436629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103547614045535764851624419 155321421068303647277436629)
          ·
            refine ⟨3640345806288366733064921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 155321421068303647277436629 3640345806288366733064921)
            ·
              refine ⟨2730259354716275049798691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3640345806288366733064921 2730259354716275049798691)
              ·
                refine ⟨4095389032074412574698037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730259354716275049798691 4095389032074412574698037)
                ·
                  refine ⟨383942721756976178877941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4095389032074412574698037 383942721756976178877941)
                  ·
                    rfl

theorem cell21_1682383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 2, 1, 5].length) (baseStart_1682383 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682383 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682383 prefixEnd_1682383 := by exact prefixLift 1682383
  have htrace : WordTrace (prefixWord ++ tailWord_1682383) baseStart_1682383 baseEnd_1682383 := by
    simpa [prefixWord, tailWord_1682383, baseEnd_1682383] using wordTrace_append hprefix tailTrace_1682383
  have hstable : (prefixWord ++ tailWord_1682383).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682383).length < 2 ^ (prefixWord ++ tailWord_1682383).sum := by decide
  have hdescent : baseEnd_1682383 < baseStart_1682383 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682417 : List Nat := [1, 2, 2, 2, 4, 3, 1, 3, 3]
def baseStart_1682417 : Nat := 118140960795 + 1682417 * 2 ^ 59
def prefixEnd_1682417 : Nat := 4983230072969 + 3 ^ 40 * 1682417 * 2
def baseEnd_1682417 : Nat := 383950481020199675311205

theorem tailTrace_1682417 : CollatzResearch.WordTrace tailWord_1682417 prefixEnd_1682417 383950481020199675311205 := by
  unfold tailWord_1682417
  simp only [CollatzResearch.WordTrace]
  refine ⟨61362789145898017792885505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40908526097265345195257003 61362789145898017792885505)
  ·
    refine ⟨46022091859423513344664129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61362789145898017792885505 46022091859423513344664129)
    ·
      refine ⟨34516568894567635008498097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46022091859423513344664129 34516568894567635008498097)
      ·
        refine ⟨25887426670925726256373573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34516568894567635008498097 25887426670925726256373573)
        ·
          refine ⟨4853892500798573673070045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25887426670925726256373573 4853892500798573673070045)
          ·
            refine ⟨1820209687799465127401267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4853892500798573673070045 1820209687799465127401267)
            ·
              refine ⟨2730314531699197691101901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820209687799465127401267 2730314531699197691101901)
              ·
                refine ⟨1023867949387199134163213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2730314531699197691101901 1023867949387199134163213)
                ·
                  refine ⟨383950481020199675311205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023867949387199134163213 383950481020199675311205)
                  ·
                    rfl

theorem cell21_1682417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 3, 1, 3, 3].length) (baseStart_1682417 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682417 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682417 prefixEnd_1682417 := by exact prefixLift 1682417
  have htrace : WordTrace (prefixWord ++ tailWord_1682417) baseStart_1682417 baseEnd_1682417 := by
    simpa [prefixWord, tailWord_1682417, baseEnd_1682417] using wordTrace_append hprefix tailTrace_1682417
  have hstable : (prefixWord ++ tailWord_1682417).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682417).length < 2 ^ (prefixWord ++ tailWord_1682417).sum := by decide
  have hdescent : baseEnd_1682417 < baseStart_1682417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682420 : List Nat := [2, 6, 2, 1, 1, 2, 7]
def baseStart_1682420 : Nat := 118140960795 + 1682420 * 2 ^ 59
def prefixEnd_1682420 : Nat := 4983230072969 + 3 ^ 40 * 1682420 * 2
def baseEnd_1682420 : Nat := 42661240629008037417911

theorem tailTrace_1682420 : CollatzResearch.WordTrace tailWord_1682420 prefixEnd_1682420 42661240629008037417911 := by
  unfold tailWord_1682420
  simp only [CollatzResearch.WordTrace]
  refine ⟨30681449282443574652622357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40908599043258099536829809 30681449282443574652622357)
  ·
    refine ⟨1438192935114542561841673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 30681449282443574652622357 1438192935114542561841673)
    ·
      refine ⟨1078644701335906921381255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1438192935114542561841673 1078644701335906921381255)
      ·
        refine ⟨1617967052003860382071883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078644701335906921381255 1617967052003860382071883)
        ·
          refine ⟨2426950578005790573107825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617967052003860382071883 2426950578005790573107825)
          ·
            refine ⟨1820212933504342929830869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426950578005790573107825 1820212933504342929830869)
            ·
              refine ⟨42661240629008037417911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1820212933504342929830869 42661240629008037417911)
              ·
                rfl

theorem cell21_1682420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 7].length) (baseStart_1682420 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682420 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682420 prefixEnd_1682420 := by exact prefixLift 1682420
  have htrace : WordTrace (prefixWord ++ tailWord_1682420) baseStart_1682420 baseEnd_1682420 := by
    simpa [prefixWord, tailWord_1682420, baseEnd_1682420] using wordTrace_append hprefix tailTrace_1682420
  have hstable : (prefixWord ++ tailWord_1682420).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682420).length < 2 ^ (prefixWord ++ tailWord_1682420).sum := by decide
  have hdescent : baseEnd_1682420 < baseStart_1682420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682428 : List Nat := [2, 2, 2, 1, 2, 5, 7]
def baseStart_1682428 : Nat := 118140960795 + 1682428 * 2 ^ 59
def prefixEnd_1682428 : Nat := 4983230072969 + 3 ^ 40 * 1682428 * 2
def baseEnd_1682428 : Nat := 42661443485562900069761

theorem tailTrace_1682428 : CollatzResearch.WordTrace tailWord_1682428 prefixEnd_1682428 42661443485562900069761 := by
  unfold tailWord_1682428
  simp only [CollatzResearch.WordTrace]
  refine ⟨30681595174429083335767969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40908793565905444447690625 30681595174429083335767969)
  ·
    refine ⟨23011196380821812501825977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30681595174429083335767969 23011196380821812501825977)
    ·
      refine ⟨17258397285616359376369483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23011196380821812501825977 17258397285616359376369483)
      ·
        refine ⟨25887595928424539064554225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17258397285616359376369483 25887595928424539064554225)
        ·
          refine ⟨19415696946318404298415669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25887595928424539064554225 19415696946318404298415669)
          ·
            refine ⟨1820221588717350402976469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19415696946318404298415669 1820221588717350402976469)
            ·
              refine ⟨42661443485562900069761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 1820221588717350402976469 42661443485562900069761)
              ·
                rfl

theorem cell21_1682428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 7].length) (baseStart_1682428 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682428 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682428 prefixEnd_1682428 := by exact prefixLift 1682428
  have htrace : WordTrace (prefixWord ++ tailWord_1682428) baseStart_1682428 baseEnd_1682428 := by
    simpa [prefixWord, tailWord_1682428, baseEnd_1682428] using wordTrace_append hprefix tailTrace_1682428
  have hstable : (prefixWord ++ tailWord_1682428).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682428).length < 2 ^ (prefixWord ++ tailWord_1682428).sum := by decide
  have hdescent : baseEnd_1682428 < baseStart_1682428 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682434 : List Nat := [3, 4, 1, 3, 1, 2, 1, 1, 5]
def baseStart_1682434 : Nat := 118140960795 + 1682434 * 2 ^ 59
def prefixEnd_1682434 : Nat := 4983230072969 + 3 ^ 40 * 1682434 * 2
def baseEnd_1682434 : Nat := 383954360651811423527837

theorem tailTrace_1682434 : CollatzResearch.WordTrace tailWord_1682434 prefixEnd_1682434 383954360651811423527837 := by
  unfold tailWord_1682434
  simp only [CollatzResearch.WordTrace]
  refine ⟨15340852296709107424063589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40908939457890953130836237 15340852296709107424063589)
  ·
    refine ⟨2876409805632957642011923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15340852296709107424063589 2876409805632957642011923)
    ·
      refine ⟨4314614708449436463017885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876409805632957642011923 4314614708449436463017885)
      ·
        refine ⟨1617980515668538673631707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4314614708449436463017885 1617980515668538673631707)
        ·
          refine ⟨2426970773502808010447561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1617980515668538673631707 2426970773502808010447561)
          ·
            refine ⟨1820228080127106007835671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2426970773502808010447561 1820228080127106007835671)
            ·
              refine ⟨2730342120190659011753507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1820228080127106007835671 2730342120190659011753507)
              ·
                refine ⟨4095513180285988517630261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2730342120190659011753507 4095513180285988517630261)
                ·
                  refine ⟨383954360651811423527837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4095513180285988517630261 383954360651811423527837)
                  ·
                    rfl

theorem cell21_1682434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_1682434 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682434 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682434 prefixEnd_1682434 := by exact prefixLift 1682434
  have htrace : WordTrace (prefixWord ++ tailWord_1682434) baseStart_1682434 baseEnd_1682434 := by
    simpa [prefixWord, tailWord_1682434, baseEnd_1682434] using wordTrace_append hprefix tailTrace_1682434
  have hstable : (prefixWord ++ tailWord_1682434).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682434).length < 2 ^ (prefixWord ++ tailWord_1682434).sum := by decide
  have hdescent : baseEnd_1682434 < baseStart_1682434 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682493 : List Nat := [1, 4, 1, 3, 1, 2, 4, 2, 3]
def baseStart_1682493 : Nat := 118140960795 + 1682493 * 2 ^ 59
def prefixEnd_1682493 : Nat := 4983230072969 + 3 ^ 40 * 1682493 * 2
def baseEnd_1682493 : Nat := 383967825255640432044383

theorem tailTrace_1682493 : CollatzResearch.WordTrace tailWord_1682493 prefixEnd_1682493 383967825255640432044383 := by
  unfold tailWord_1682493
  simp only [CollatzResearch.WordTrace]
  refine ⟨61365561093622682772652133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40910374062415121848434755 61365561093622682772652133)
  ·
    refine ⟨11506042705054253019872275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61365561093622682772652133 11506042705054253019872275)
    ·
      refine ⟨17259064057581379529808413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11506042705054253019872275 17259064057581379529808413)
      ·
        refine ⟨6472149021593017323678155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17259064057581379529808413 6472149021593017323678155)
        ·
          refine ⟨9708223532389525985517233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6472149021593017323678155 9708223532389525985517233)
          ·
            refine ⟨7281167649292144489137925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9708223532389525985517233 7281167649292144489137925)
            ·
              refine ⟨1365218934242277091713361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7281167649292144489137925 1365218934242277091713361)
              ·
                refine ⟨1023914200681707818785021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365218934242277091713361 1023914200681707818785021)
                ·
                  refine ⟨383967825255640432044383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023914200681707818785021 383967825255640432044383)
                  ·
                    rfl

theorem cell21_1682493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_1682493 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682493 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682493 prefixEnd_1682493 := by exact prefixLift 1682493
  have htrace : WordTrace (prefixWord ++ tailWord_1682493) baseStart_1682493 baseEnd_1682493 := by
    simpa [prefixWord, tailWord_1682493, baseEnd_1682493] using wordTrace_append hprefix tailTrace_1682493
  have hstable : (prefixWord ++ tailWord_1682493).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682493).length < 2 ^ (prefixWord ++ tailWord_1682493).sum := by decide
  have hdescent : baseEnd_1682493 < baseStart_1682493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1682558 : List Nat := [4, 2, 4, 1, 1, 1, 3, 1, 4]
def baseStart_1682558 : Nat := 118140960795 + 1682558 * 2 ^ 59
def prefixEnd_1682558 : Nat := 4983230072969 + 3 ^ 40 * 1682558 * 2
def baseEnd_1682558 : Nat := 383982659141214763460917

theorem tailTrace_1682558 : CollatzResearch.WordTrace tailWord_1682558 prefixEnd_1682558 383982659141214763460917 := by
  unfold tailWord_1682558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7670991479798399859221041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40911954558924799249178885 7670991479798399859221041)
  ·
    refine ⟨5753243609848799894415781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7670991479798399859221041 5753243609848799894415781)
    ·
      refine ⟨1078733176846649980202959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5753243609848799894415781 1078733176846649980202959)
      ·
        refine ⟨1618099765269974970304439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1078733176846649980202959 1618099765269974970304439)
        ·
          refine ⟨2427149647904962455456659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1618099765269974970304439 2427149647904962455456659)
          ·
            refine ⟨3640724471857443683184989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2427149647904962455456659 3640724471857443683184989)
            ·
              refine ⟨1365271676946541381194371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3640724471857443683184989 1365271676946541381194371)
              ·
                refine ⟨2047907515419812071791557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1365271676946541381194371 2047907515419812071791557)
                ·
                  refine ⟨383982659141214763460917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2047907515419812071791557 383982659141214763460917)
                  ·
                    rfl

theorem cell21_1682558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_1682558 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_1682558 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_1682558 prefixEnd_1682558 := by exact prefixLift 1682558
  have htrace : WordTrace (prefixWord ++ tailWord_1682558) baseStart_1682558 baseEnd_1682558 := by
    simpa [prefixWord, tailWord_1682558, baseEnd_1682558] using wordTrace_append hprefix tailTrace_1682558
  have hstable : (prefixWord ++ tailWord_1682558).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1682558).length < 2 ^ (prefixWord ++ tailWord_1682558).sum := by decide
  have hdescent : baseEnd_1682558 < baseStart_1682558 := by decide
  rcases family_descends (prefixWord ++ tailWord_1682558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
