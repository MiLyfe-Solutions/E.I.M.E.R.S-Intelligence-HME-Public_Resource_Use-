import V185TrunkScan23Chunk0916

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5427902 : List Nat := [4, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3]
def baseStart_5427902 : Nat := 118140960795 + 5427902 * 2 ^ 59
def prefixEnd_5427902 : Nat := 4983230072969 + 3 ^ 40 * 5427902 * 2
def baseEnd_5427902 : Nat := 2787122671500727542162539

theorem tailTrace_5427902 : CollatzResearch.WordTrace tailWord_5427902 prefixEnd_5427902 2787122671500727542162539 := by
  unfold tailWord_5427902
  simp only [CollatzResearch.WordTrace]
  refine ⟨24746481247705692587940745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 131981233321097027135683973 24746481247705692587940745)
  ·
    refine ⟨18559860935779269440955559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24746481247705692587940745 18559860935779269440955559)
    ·
      refine ⟨27839791403668904161433339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18559860935779269440955559 27839791403668904161433339)
      ·
        refine ⟨41759687105503356242150009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27839791403668904161433339 41759687105503356242150009)
        ·
          refine ⟨31319765329127517181612507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41759687105503356242150009 31319765329127517181612507)
          ·
            refine ⟨46979647993691275772418761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31319765329127517181612507 46979647993691275772418761)
            ·
              refine ⟨35234735995268456829314071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46979647993691275772418761 35234735995268456829314071)
              ·
                refine ⟨52852103992902685243971107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35234735995268456829314071 52852103992902685243971107)
                ·
                  refine ⟨79278155989354027865956661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52852103992902685243971107 79278155989354027865956661)
                  ·
                    refine ⟨7432327124001940112433437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79278155989354027865956661 7432327124001940112433437)
                    ·
                      refine ⟨2787122671500727542162539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432327124001940112433437 2787122671500727542162539)
                      ·
                        rfl

theorem cell23_5427902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_5427902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427902 prefixEnd_5427902 := by exact prefixLift 5427902
  have htrace : WordTrace (prefixWord ++ tailWord_5427902) baseStart_5427902 baseEnd_5427902 := by
    simpa [prefixWord, tailWord_5427902, baseEnd_5427902] using wordTrace_append hprefix tailTrace_5427902
  have hstable : (prefixWord ++ tailWord_5427902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427902).length < 2 ^ (prefixWord ++ tailWord_5427902).sum := by decide
  have hdescent : baseEnd_5427902 < baseStart_5427902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427903 : List Nat := [1, 1, 2, 2, 2, 6, 2, 1, 2, 2, 2]
def baseStart_5427903 : Nat := 118140960795 + 5427903 * 2 ^ 59
def prefixEnd_5427903 : Nat := 4983230072969 + 3 ^ 40 * 5427903 * 2
def baseEnd_5427903 : Nat := 2787123184981382038250035

theorem tailTrace_5427903 : CollatzResearch.WordTrace tailWord_5427903 prefixEnd_5427903 2787123184981382038250035 := by
  unfold tailWord_5427903
  simp only [CollatzResearch.WordTrace]
  refine ⟨197971886454641917874312363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131981257636427945249541575 197971886454641917874312363)
  ·
    refine ⟨296957829681962876811468545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197971886454641917874312363 296957829681962876811468545)
    ·
      refine ⟨222718372261472157608601409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296957829681962876811468545 222718372261472157608601409)
      ·
        refine ⟨167038779196104118206451057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222718372261472157608601409 167038779196104118206451057)
        ·
          refine ⟨125279084397078088654838293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167038779196104118206451057 125279084397078088654838293)
          ·
            refine ⟨5872457081113035405695545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125279084397078088654838293 5872457081113035405695545)
            ·
              refine ⟨4404342810834776554271659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872457081113035405695545 4404342810834776554271659)
              ·
                refine ⟨6606514216252164831407489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404342810834776554271659 6606514216252164831407489)
                ·
                  refine ⟨4954885662189123623555617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6606514216252164831407489 4954885662189123623555617)
                  ·
                    refine ⟨3716164246641842717666713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4954885662189123623555617 3716164246641842717666713)
                    ·
                      refine ⟨2787123184981382038250035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716164246641842717666713 2787123184981382038250035)
                      ·
                        rfl

theorem cell23_5427903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_5427903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427903 prefixEnd_5427903 := by exact prefixLift 5427903
  have htrace : WordTrace (prefixWord ++ tailWord_5427903) baseStart_5427903 baseEnd_5427903 := by
    simpa [prefixWord, tailWord_5427903, baseEnd_5427903] using wordTrace_append hprefix tailTrace_5427903
  have hstable : (prefixWord ++ tailWord_5427903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427903).length < 2 ^ (prefixWord ++ tailWord_5427903).sum := by decide
  have hdescent : baseEnd_5427903 < baseStart_5427903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427952 : List Nat := [2, 1, 1, 1, 3, 1, 4, 3, 3, 4]
def baseStart_5427952 : Nat := 118140960795 + 5427952 * 2 ^ 59
def prefixEnd_5427952 : Nat := 4983230072969 + 3 ^ 40 * 5427952 * 2
def baseEnd_5427952 : Nat := 929049448511150782179103

theorem tailTrace_5427952 : CollatzResearch.WordTrace tailWord_5427952 prefixEnd_5427952 929049448511150782179103 := by
  unfold tailWord_5427952
  simp only [CollatzResearch.WordTrace]
  refine ⟨98986836815732199621423055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131982449087642932828564073 98986836815732199621423055)
  ·
    refine ⟨148480255223598299432134583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98986836815732199621423055 148480255223598299432134583)
    ·
      refine ⟨222720382835397449148201875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148480255223598299432134583 222720382835397449148201875)
      ·
        refine ⟨334080574253096173722302813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222720382835397449148201875 334080574253096173722302813)
        ·
          refine ⟨125280215344911065145863555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334080574253096173722302813 125280215344911065145863555)
          ·
            refine ⟨187920323017366597718795333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125280215344911065145863555 187920323017366597718795333)
            ·
              refine ⟨35235060565756237072274125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 187920323017366597718795333 35235060565756237072274125)
              ·
                refine ⟨13213147712158588902102797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35235060565756237072274125 13213147712158588902102797)
                ·
                  refine ⟨4954930392059470838288549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13213147712158588902102797 4954930392059470838288549)
                  ·
                    refine ⟨929049448511150782179103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4954930392059470838288549 929049448511150782179103)
                    ·
                      rfl

theorem cell23_5427952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 3, 3, 4].length) (baseStart_5427952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427952 prefixEnd_5427952 := by exact prefixLift 5427952
  have htrace : WordTrace (prefixWord ++ tailWord_5427952) baseStart_5427952 baseEnd_5427952 := by
    simpa [prefixWord, tailWord_5427952, baseEnd_5427952] using wordTrace_append hprefix tailTrace_5427952
  have hstable : (prefixWord ++ tailWord_5427952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427952).length < 2 ^ (prefixWord ++ tailWord_5427952).sum := by decide
  have hdescent : baseEnd_5427952 < baseStart_5427952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427955 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4]
def baseStart_5427955 : Nat := 118140960795 + 5427955 * 2 ^ 59
def prefixEnd_5427955 : Nat := 4983230072969 + 3 ^ 40 * 5427955 * 2
def baseEnd_5427955 : Nat := 2787149885975415834799795

theorem tailTrace_5427955 : CollatzResearch.WordTrace tailWord_5427955 prefixEnd_5427955 2787149885975415834799795 := by
  unfold tailWord_5427955
  simp only [CollatzResearch.WordTrace]
  refine ⟨197973783050453530755205319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131982522033635687170136879 197973783050453530755205319)
  ·
    refine ⟨296960674575680296132807979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197973783050453530755205319 296960674575680296132807979)
    ·
      refine ⟨445441011863520444199211969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296960674575680296132807979 445441011863520444199211969)
      ·
        refine ⟨334080758897640333149408977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445441011863520444199211969 334080758897640333149408977)
        ·
          refine ⟨250560569173230249862056733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334080758897640333149408977 250560569173230249862056733)
          ·
            refine ⟨93960213439961343698271275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250560569173230249862056733 93960213439961343698271275)
            ·
              refine ⟨140940320159942015547406913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93960213439961343698271275 140940320159942015547406913)
              ·
                refine ⟨105705240119956511660555185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140940320159942015547406913 105705240119956511660555185)
                ·
                  refine ⟨79278930089967383745416389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105705240119956511660555185 79278930089967383745416389)
                  ·
                    refine ⟨14864799391868884452265573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79278930089967383745416389 14864799391868884452265573)
                    ·
                      refine ⟨2787149885975415834799795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14864799391868884452265573 2787149885975415834799795)
                      ·
                        rfl

theorem cell23_5427955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_5427955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427955 prefixEnd_5427955 := by exact prefixLift 5427955
  have htrace : WordTrace (prefixWord ++ tailWord_5427955) baseStart_5427955 baseEnd_5427955 := by
    simpa [prefixWord, tailWord_5427955, baseEnd_5427955] using wordTrace_append hprefix tailTrace_5427955
  have hstable : (prefixWord ++ tailWord_5427955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427955).length < 2 ^ (prefixWord ++ tailWord_5427955).sum := by decide
  have hdescent : baseEnd_5427955 < baseStart_5427955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427962 : List Nat := [3, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3]
def baseStart_5427962 : Nat := 118140960795 + 5427962 * 2 ^ 59
def prefixEnd_5427962 : Nat := 4983230072969 + 3 ^ 40 * 5427962 * 2
def baseEnd_5427962 : Nat := 2787153480339997307412263

theorem tailTrace_5427962 : CollatzResearch.WordTrace tailWord_5427962 prefixEnd_5427962 2787153480339997307412263 := by
  unfold tailWord_5427962
  simp only [CollatzResearch.WordTrace]
  refine ⟨49493509590357042737677535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131982692240952113967140093 49493509590357042737677535)
  ·
    refine ⟨74240264385535564106516303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49493509590357042737677535 74240264385535564106516303)
    ·
      refine ⟨111360396578303346159774455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74240264385535564106516303 111360396578303346159774455)
      ·
        refine ⟨167040594867455019239661683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111360396578303346159774455 167040594867455019239661683)
        ·
          refine ⟨250560892301182528859492525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167040594867455019239661683 250560892301182528859492525)
          ·
            refine ⟨93960334612943448322309697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250560892301182528859492525 93960334612943448322309697)
            ·
              refine ⟨70470250959707586241732273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93960334612943448322309697 70470250959707586241732273)
              ·
                refine ⟨52852688219780689681299205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70470250959707586241732273 52852688219780689681299205)
                ·
                  refine ⟨9909879041208879315243601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52852688219780689681299205 9909879041208879315243601)
                  ·
                    refine ⟨7432409280906659486432701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9909879041208879315243601 7432409280906659486432701)
                    ·
                      refine ⟨2787153480339997307412263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432409280906659486432701 2787153480339997307412263)
                      ·
                        rfl

theorem cell23_5427962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 2, 4, 2, 3].length) (baseStart_5427962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427962 prefixEnd_5427962 := by exact prefixLift 5427962
  have htrace : WordTrace (prefixWord ++ tailWord_5427962) baseStart_5427962 baseEnd_5427962 := by
    simpa [prefixWord, tailWord_5427962, baseEnd_5427962] using wordTrace_append hprefix tailTrace_5427962
  have hstable : (prefixWord ++ tailWord_5427962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427962).length < 2 ^ (prefixWord ++ tailWord_5427962).sum := by decide
  have hdescent : baseEnd_5427962 < baseStart_5427962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5427999 : List Nat := [1, 1, 2, 4, 2, 4, 1, 2, 6]
def baseStart_5427999 : Nat := 118140960795 + 5427999 * 2 ^ 59
def prefixEnd_5427999 : Nat := 4983230072969 + 3 ^ 40 * 5427999 * 2
def baseEnd_5427999 : Nat := 309685831013801518072177

theorem tailTrace_5427999 : CollatzResearch.WordTrace tailWord_5427999 prefixEnd_5427999 309685831013801518072177 := by
  unfold tailWord_5427999
  simp only [CollatzResearch.WordTrace]
  refine ⟨197975387862294126269807051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131983591908196084179871367 197975387862294126269807051)
  ·
    refine ⟨296963081793441189404710577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197975387862294126269807051 296963081793441189404710577)
    ·
      refine ⟨222722311345080892053532933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296963081793441189404710577 222722311345080892053532933)
      ·
        refine ⟨41760433377202667260037425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222722311345080892053532933 41760433377202667260037425)
        ·
          refine ⟨31320325032902000445028069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41760433377202667260037425 31320325032902000445028069)
          ·
            refine ⟨5872560943669125083442763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31320325032902000445028069 5872560943669125083442763)
            ·
              refine ⟨8808841415503687625164145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872560943669125083442763 8808841415503687625164145)
              ·
                refine ⟨6606631061627765718873109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8808841415503687625164145 6606631061627765718873109)
                ·
                  refine ⟨309685831013801518072177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6606631061627765718873109 309685831013801518072177)
                  ·
                    rfl

theorem cell23_5427999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 6].length) (baseStart_5427999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5427999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5427999 prefixEnd_5427999 := by exact prefixLift 5427999
  have htrace : WordTrace (prefixWord ++ tailWord_5427999) baseStart_5427999 baseEnd_5427999 := by
    simpa [prefixWord, tailWord_5427999, baseEnd_5427999] using wordTrace_append hprefix tailTrace_5427999
  have hstable : (prefixWord ++ tailWord_5427999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5427999).length < 2 ^ (prefixWord ++ tailWord_5427999).sum := by decide
  have hdescent : baseEnd_5427999 < baseStart_5427999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5427999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428002 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6]
def baseStart_5428002 : Nat := 118140960795 + 5428002 * 2 ^ 59
def prefixEnd_5428002 : Nat := 4983230072969 + 3 ^ 40 * 5428002 * 2
def baseEnd_5428002 : Nat := 2787174019566177150912079

theorem tailTrace_5428002 : CollatzResearch.WordTrace tailWord_5428002 prefixEnd_5428002 2787174019566177150912079 := by
  unfold tailWord_5428002
  simp only [CollatzResearch.WordTrace]
  refine ⟨49493874320320814445541565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131983664854188838521444173 49493874320320814445541565)
  ·
    refine ⟨18560202870120305417078087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49493874320320814445541565 18560202870120305417078087)
    ·
      refine ⟨27840304305180458125617131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18560202870120305417078087 27840304305180458125617131)
      ·
        refine ⟨41760456457770687188425697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27840304305180458125617131 41760456457770687188425697)
        ·
          refine ⟨31320342343328015391319273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41760456457770687188425697 31320342343328015391319273)
          ·
            refine ⟨23490256757496011543489455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31320342343328015391319273 23490256757496011543489455)
            ·
              refine ⟨35235385136244017315234183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23490256757496011543489455 35235385136244017315234183)
              ·
                refine ⟨52853077704366025972851275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35235385136244017315234183 52853077704366025972851275)
                ·
                  refine ⟨79279616556549038959276913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52853077704366025972851275 79279616556549038959276913)
                  ·
                    refine ⟨59459712417411779219457685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79279616556549038959276913 59459712417411779219457685)
                    ·
                      refine ⟨2787174019566177150912079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59459712417411779219457685 2787174019566177150912079)
                      ·
                        rfl

theorem cell23_5428002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6].length) (baseStart_5428002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428002 prefixEnd_5428002 := by exact prefixLift 5428002
  have htrace : WordTrace (prefixWord ++ tailWord_5428002) baseStart_5428002 baseEnd_5428002 := by
    simpa [prefixWord, tailWord_5428002, baseEnd_5428002] using wordTrace_append hprefix tailTrace_5428002
  have hstable : (prefixWord ++ tailWord_5428002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428002).length < 2 ^ (prefixWord ++ tailWord_5428002).sum := by decide
  have hdescent : baseEnd_5428002 < baseStart_5428002 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428019 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 1, 5, 2]
def baseStart_5428019 : Nat := 118140960795 + 5428019 * 2 ^ 59
def prefixEnd_5428019 : Nat := 4983230072969 + 3 ^ 40 * 5428019 * 2
def baseEnd_5428019 : Nat := 2787182748737303584399501

theorem tailTrace_5428019 : CollatzResearch.WordTrace tailWord_5428019 prefixEnd_5428019 2787182748737303584399501 := by
  unfold tailWord_5428019
  simp only [CollatzResearch.WordTrace]
  refine ⟨197976117322221669685535111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131984078214814446457023407 197976117322221669685535111)
  ·
    refine ⟨296964175983332504528302667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197976117322221669685535111 296964175983332504528302667)
    ·
      refine ⟨445446263974998756792454001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296964175983332504528302667 445446263974998756792454001)
      ·
        refine ⟨334084697981249067594340501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445446263974998756792454001 334084697981249067594340501)
        ·
          refine ⟨15660220217871050043484711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 334084697981249067594340501 15660220217871050043484711)
          ·
            refine ⟨23490330326806575065227067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15660220217871050043484711 23490330326806575065227067)
            ·
              refine ⟨35235495490209862597840601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23490330326806575065227067 35235495490209862597840601)
              ·
                refine ⟨26426621617657396948380451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35235495490209862597840601 26426621617657396948380451)
                ·
                  refine ⟨39639932426486095422570677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26426621617657396948380451 39639932426486095422570677)
                  ·
                    refine ⟨3716243664983071445866001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39639932426486095422570677 3716243664983071445866001)
                    ·
                      refine ⟨2787182748737303584399501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716243664983071445866001 2787182748737303584399501)
                      ·
                        rfl

theorem cell23_5428019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 1, 5, 2].length) (baseStart_5428019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428019 prefixEnd_5428019 := by exact prefixLift 5428019
  have htrace : WordTrace (prefixWord ++ tailWord_5428019) baseStart_5428019 baseEnd_5428019 := by
    simpa [prefixWord, tailWord_5428019, baseEnd_5428019] using wordTrace_append hprefix tailTrace_5428019
  have hstable : (prefixWord ++ tailWord_5428019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428019).length < 2 ^ (prefixWord ++ tailWord_5428019).sum := by decide
  have hdescent : baseEnd_5428019 < baseStart_5428019 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428032 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4]
def baseStart_5428032 : Nat := 118140960795 + 5428032 * 2 ^ 59
def prefixEnd_5428032 : Nat := 4983230072969 + 3 ^ 40 * 5428032 * 2
def baseEnd_5428032 : Nat := 2787189423985812033536941

theorem tailTrace_5428032 : CollatzResearch.WordTrace tailWord_5428032 prefixEnd_5428032 2787189423985812033536941 := by
  unfold tailWord_5428032
  simp only [CollatzResearch.WordTrace]
  refine ⟨98988295735587286452879175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131984394314116381937172233 98988295735587286452879175)
  ·
    refine ⟨148482443603380929679318763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98988295735587286452879175 148482443603380929679318763)
    ·
      refine ⟨222723665405071394518978145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148482443603380929679318763 222723665405071394518978145)
      ·
        refine ⟨167042749053803545889233609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222723665405071394518978145 167042749053803545889233609)
        ·
          refine ⟨125282061790352659416925207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167042749053803545889233609 125282061790352659416925207)
          ·
            refine ⟨187923092685528989125387811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125282061790352659416925207 187923092685528989125387811)
            ·
              refine ⟨281884639028293483688081717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187923092685528989125387811 281884639028293483688081717)
              ·
                refine ⟨26426684908902514095757661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281884639028293483688081717 26426684908902514095757661)
                ·
                  refine ⟨9910006840838442785909123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26426684908902514095757661 9910006840838442785909123)
                  ·
                    refine ⟨14865010261257664178863685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9910006840838442785909123 14865010261257664178863685)
                    ·
                      refine ⟨2787189423985812033536941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14865010261257664178863685 2787189423985812033536941)
                      ·
                        rfl

theorem cell23_5428032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_5428032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428032 prefixEnd_5428032 := by exact prefixLift 5428032
  have htrace : WordTrace (prefixWord ++ tailWord_5428032) baseStart_5428032 baseEnd_5428032 := by
    simpa [prefixWord, tailWord_5428032, baseEnd_5428032] using wordTrace_append hprefix tailTrace_5428032
  have hstable : (prefixWord ++ tailWord_5428032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428032).length < 2 ^ (prefixWord ++ tailWord_5428032).sum := by decide
  have hdescent : baseEnd_5428032 < baseStart_5428032 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428072 : List Nat := [2, 1, 4, 2, 1, 2, 1, 10]
def baseStart_5428072 : Nat := 118140960795 + 5428072 * 2 ^ 59
def prefixEnd_5428072 : Nat := 4983230072969 + 3 ^ 40 * 5428072 * 2
def baseEnd_5428072 : Nat := 103229998637481180630991

theorem tailTrace_5428072 : CollatzResearch.WordTrace tailWord_5428072 prefixEnd_5428072 103229998637481180630991 := by
  unfold tailWord_5428072
  simp only [CollatzResearch.WordTrace]
  refine ⟨98989025195514829868607235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131985366927353106491476313 98989025195514829868607235)
  ·
    refine ⟨148483537793272244802910853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98989025195514829868607235 148483537793272244802910853)
    ·
      refine ⟨27840663336238545900545785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148483537793272244802910853 27840663336238545900545785)
      ·
        refine ⟨20880497502178909425409339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27840663336238545900545785 20880497502178909425409339)
        ·
          refine ⟨31320746253268364138114009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20880497502178909425409339 31320746253268364138114009)
          ·
            refine ⟨23490559689951273103585507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31320746253268364138114009 23490559689951273103585507)
            ·
              refine ⟨35235839534926909655378261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23490559689951273103585507 35235839534926909655378261)
              ·
                refine ⟨103229998637481180630991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 35235839534926909655378261 103229998637481180630991)
                ·
                  rfl

theorem cell23_5428072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 10].length) (baseStart_5428072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428072 prefixEnd_5428072 := by exact prefixLift 5428072
  have htrace : WordTrace (prefixWord ++ tailWord_5428072) baseStart_5428072 baseEnd_5428072 := by
    simpa [prefixWord, tailWord_5428072, baseEnd_5428072] using wordTrace_append hprefix tailTrace_5428072
  have hstable : (prefixWord ++ tailWord_5428072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428072).length < 2 ^ (prefixWord ++ tailWord_5428072).sum := by decide
  have hdescent : baseEnd_5428072 < baseStart_5428072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428099 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 3]
def baseStart_5428099 : Nat := 118140960795 + 5428099 * 2 ^ 59
def prefixEnd_5428099 : Nat := 4983230072969 + 3 ^ 40 * 5428099 * 2
def baseEnd_5428099 : Nat := 2787223827189663271399133

theorem tailTrace_5428099 : CollatzResearch.WordTrace tailWord_5428099 prefixEnd_5428099 2787223827189663271399133 := by
  unfold tailWord_5428099
  simp only [CollatzResearch.WordTrace]
  refine ⟨197979035161931843348447351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131986023441287895565631567 197979035161931843348447351)
  ·
    refine ⟨296968552742897765022671027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197979035161931843348447351 296968552742897765022671027)
    ·
      refine ⟨445452829114346647534006541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296968552742897765022671027 445452829114346647534006541)
      ·
        refine ⟨167044810917879992825252453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 445452829114346647534006541 167044810917879992825252453)
        ·
          refine ⟨31320902047102498654734835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167044810917879992825252453 31320902047102498654734835)
          ·
            refine ⟨46981353070653747982102253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31320902047102498654734835 46981353070653747982102253)
            ·
              refine ⟨17618007401495155493288345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46981353070653747982102253 17618007401495155493288345)
              ·
                refine ⟨13213505551121366619966259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17618007401495155493288345 13213505551121366619966259)
                ·
                  refine ⟨19820258326682049929949389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13213505551121366619966259 19820258326682049929949389)
                  ·
                    refine ⟨7432596872505768723731021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19820258326682049929949389 7432596872505768723731021)
                    ·
                      refine ⟨2787223827189663271399133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432596872505768723731021 2787223827189663271399133)
                      ·
                        rfl

theorem cell23_5428099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 1, 3, 3].length) (baseStart_5428099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428099 prefixEnd_5428099 := by exact prefixLift 5428099
  have htrace : WordTrace (prefixWord ++ tailWord_5428099) baseStart_5428099 baseEnd_5428099 := by
    simpa [prefixWord, tailWord_5428099, baseEnd_5428099] using wordTrace_append hprefix tailTrace_5428099
  have hstable : (prefixWord ++ tailWord_5428099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428099).length < 2 ^ (prefixWord ++ tailWord_5428099).sum := by decide
  have hdescent : baseEnd_5428099 < baseStart_5428099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428103 : List Nat := [1, 1, 4, 2, 3, 2, 3, 1, 1, 2, 3]
def baseStart_5428103 : Nat := 118140960795 + 5428103 * 2 ^ 59
def prefixEnd_5428103 : Nat := 4983230072969 + 3 ^ 40 * 5428103 * 2
def baseEnd_5428103 : Nat := 2787225881112281255749115

theorem tailTrace_5428103 : CollatzResearch.WordTrace tailWord_5428103 prefixEnd_5428103 2787225881112281255749115 := by
  unfold tailWord_5428103
  simp only [CollatzResearch.WordTrace]
  refine ⟨197979181053917352031592963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131986120702611568021061975 197979181053917352031592963)
  ·
    refine ⟨296968771580876028047389445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197979181053917352031592963 296968771580876028047389445)
    ·
      refine ⟨55681644671414255258885521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296968771580876028047389445 55681644671414255258885521)
      ·
        refine ⟨41761233503560691444164141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55681644671414255258885521 41761233503560691444164141)
        ·
          refine ⟨15660462563835259291561553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41761233503560691444164141 15660462563835259291561553)
          ·
            refine ⟨11745346922876444468671165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15660462563835259291561553 11745346922876444468671165)
            ·
              refine ⟨4404505096078666675751687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11745346922876444468671165 4404505096078666675751687)
              ·
                refine ⟨6606757644118000013627531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404505096078666675751687 6606757644118000013627531)
                ·
                  refine ⟨9910136466177000020441297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6606757644118000013627531 9910136466177000020441297)
                  ·
                    refine ⟨7432602349632750015330973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9910136466177000020441297 7432602349632750015330973)
                    ·
                      refine ⟨2787225881112281255749115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432602349632750015330973 2787225881112281255749115)
                      ·
                        rfl

theorem cell23_5428103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 3, 1, 1, 2, 3].length) (baseStart_5428103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428103 prefixEnd_5428103 := by exact prefixLift 5428103
  have htrace : WordTrace (prefixWord ++ tailWord_5428103) baseStart_5428103 baseEnd_5428103 := by
    simpa [prefixWord, tailWord_5428103, baseEnd_5428103] using wordTrace_append hprefix tailTrace_5428103
  have hstable : (prefixWord ++ tailWord_5428103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428103).length < 2 ^ (prefixWord ++ tailWord_5428103).sum := by decide
  have hdescent : baseEnd_5428103 < baseStart_5428103 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428117 : List Nat := [1, 3, 2, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_5428117 : Nat := 118140960795 + 5428117 * 2 ^ 59
def prefixEnd_5428117 : Nat := 4983230072969 + 3 ^ 40 * 5428117 * 2
def baseEnd_5428117 : Nat := 2787233069841444200974051

theorem tailTrace_5428117 : CollatzResearch.WordTrace tailWord_5428117 prefixEnd_5428117 2787233069841444200974051 := by
  unfold tailWord_5428117
  simp only [CollatzResearch.WordTrace]
  refine ⟨197979691675866632422602605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131986461117244421615068403 197979691675866632422602605)
  ·
    refine ⟨74242384378449987158475977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197979691675866632422602605 74242384378449987158475977)
    ·
      refine ⟨55681788283837490368856983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74242384378449987158475977 55681788283837490368856983)
      ·
        refine ⟨83522682425756235553285475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55681788283837490368856983 83522682425756235553285475)
        ·
          refine ⟨125284023638634353329928213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83522682425756235553285475 125284023638634353329928213)
          ·
            refine ⟨5872688608060985312340385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 125284023638634353329928213 5872688608060985312340385)
            ·
              refine ⟨4404516456045738984255289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872688608060985312340385 4404516456045738984255289)
              ·
                refine ⟨3303387342034304238191467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4404516456045738984255289 3303387342034304238191467)
                ·
                  refine ⟨4955081013051456357287201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303387342034304238191467 4955081013051456357287201)
                  ·
                    refine ⟨3716310759788592267965401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4955081013051456357287201 3716310759788592267965401)
                    ·
                      refine ⟨2787233069841444200974051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716310759788592267965401 2787233069841444200974051)
                      ·
                        rfl

theorem cell23_5428117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_5428117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428117 prefixEnd_5428117 := by exact prefixLift 5428117
  have htrace : WordTrace (prefixWord ++ tailWord_5428117) baseStart_5428117 baseEnd_5428117 := by
    simpa [prefixWord, tailWord_5428117, baseEnd_5428117] using wordTrace_append hprefix tailTrace_5428117
  have hstable : (prefixWord ++ tailWord_5428117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428117).length < 2 ^ (prefixWord ++ tailWord_5428117).sum := by decide
  have hdescent : baseEnd_5428117 < baseStart_5428117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428139 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 5, 4, 2]
def baseStart_5428139 : Nat := 118140960795 + 5428139 * 2 ^ 59
def prefixEnd_5428139 : Nat := 4983230072969 + 3 ^ 40 * 5428139 * 2
def baseEnd_5428139 : Nat := 2787244366415843114898949

theorem tailTrace_5428139 : CollatzResearch.WordTrace tailWord_5428139 prefixEnd_5428139 2787244366415843114898949 := by
  unfold tailWord_5428139
  simp only [CollatzResearch.WordTrace]
  refine ⟨197980494081786930179903471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131986996054524620119935647 197980494081786930179903471)
  ·
    refine ⟨296970741122680395269855207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197980494081786930179903471 296970741122680395269855207)
    ·
      refine ⟨445456111684020592904782811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296970741122680395269855207 445456111684020592904782811)
      ·
        refine ⟨668184167526030889357174217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445456111684020592904782811 668184167526030889357174217)
        ·
          refine ⟨501138125644523167017880663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668184167526030889357174217 501138125644523167017880663)
          ·
            refine ⟨751707188466784750526820995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501138125644523167017880663 751707188466784750526820995)
            ·
              refine ⟨1127560782700177125790231493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751707188466784750526820995 1127560782700177125790231493)
              ·
                refine ⟨211417646756283211085668405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1127560782700177125790231493 211417646756283211085668405)
                ·
                  refine ⟨19820404383401551039281413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211417646756283211085668405 19820404383401551039281413)
                  ·
                    refine ⟨3716325821887790819865265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19820404383401551039281413 3716325821887790819865265)
                    ·
                      refine ⟨2787244366415843114898949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716325821887790819865265 2787244366415843114898949)
                      ·
                        rfl

theorem cell23_5428139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 5, 4, 2].length) (baseStart_5428139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428139 prefixEnd_5428139 := by exact prefixLift 5428139
  have htrace : WordTrace (prefixWord ++ tailWord_5428139) baseStart_5428139 baseEnd_5428139 := by
    simpa [prefixWord, tailWord_5428139, baseEnd_5428139] using wordTrace_append hprefix tailTrace_5428139
  have hstable : (prefixWord ++ tailWord_5428139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428139).length < 2 ^ (prefixWord ++ tailWord_5428139).sum := by decide
  have hdescent : baseEnd_5428139 < baseStart_5428139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428160 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 1, 3, 2]
def baseStart_5428160 : Nat := 118140960795 + 5428160 * 2 ^ 59
def prefixEnd_5428160 : Nat := 4983230072969 + 3 ^ 40 * 5428160 * 2
def baseEnd_5428160 : Nat := 2787255149509587532736353

theorem tailTrace_5428160 : CollatzResearch.WordTrace tailWord_5428160 prefixEnd_5428160 2787255149509587532736353 := by
  unfold tailWord_5428160
  simp only [CollatzResearch.WordTrace]
  refine ⟨98990630007355425383208967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131987506676473900510945289 98990630007355425383208967)
  ·
    refine ⟨148485945011033138074813451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98990630007355425383208967 148485945011033138074813451)
    ·
      refine ⟨222728917516549707112220177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148485945011033138074813451 222728917516549707112220177)
      ·
        refine ⟨167046688137412280334165133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222728917516549707112220177 167046688137412280334165133)
        ·
          refine ⟨62642508051529605125311925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167046688137412280334165133 62642508051529605125311925)
          ·
            refine ⟨5872735129830900480497993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62642508051529605125311925 5872735129830900480497993)
            ·
              refine ⟨4404551347373175360373495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5872735129830900480497993 4404551347373175360373495)
              ·
                refine ⟨6606827021059763040560243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404551347373175360373495 6606827021059763040560243)
                ·
                  refine ⟨9910240531589644560840365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6606827021059763040560243 9910240531589644560840365)
                  ·
                    refine ⟨3716340199346116710315137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9910240531589644560840365 3716340199346116710315137)
                    ·
                      refine ⟨2787255149509587532736353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716340199346116710315137 2787255149509587532736353)
                      ·
                        rfl

theorem cell23_5428160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_5428160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428160 prefixEnd_5428160 := by exact prefixLift 5428160
  have htrace : WordTrace (prefixWord ++ tailWord_5428160) baseStart_5428160 baseEnd_5428160 := by
    simpa [prefixWord, tailWord_5428160, baseEnd_5428160] using wordTrace_append hprefix tailTrace_5428160
  have hstable : (prefixWord ++ tailWord_5428160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428160).length < 2 ^ (prefixWord ++ tailWord_5428160).sum := by decide
  have hdescent : baseEnd_5428160 < baseStart_5428160 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428209 : List Nat := [1, 2, 2, 2, 4, 1, 2, 1, 1, 7]
def baseStart_5428209 : Nat := 118140960795 + 5428209 * 2 ^ 59
def prefixEnd_5428209 : Nat := 4983230072969 + 3 ^ 40 * 5428209 * 2
def baseEnd_5428209 : Nat := 929093436687219280341209

theorem tailTrace_5428209 : CollatzResearch.WordTrace tailWord_5428209 prefixEnd_5428209 929093436687219280341209 := by
  unfold tailWord_5428209
  simp only [CollatzResearch.WordTrace]
  refine ⟨197983047191533332134951681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131988698127688888089967787 197983047191533332134951681)
  ·
    refine ⟨148487285393649999101213761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197983047191533332134951681 148487285393649999101213761)
    ·
      refine ⟨111365464045237499325910321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148487285393649999101213761 111365464045237499325910321)
      ·
        refine ⟨83524098033928124494432741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111365464045237499325910321 83524098033928124494432741)
        ·
          refine ⟨15660768381361523342706139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 83524098033928124494432741 15660768381361523342706139)
          ·
            refine ⟨23491152572042285014059209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15660768381361523342706139 23491152572042285014059209)
            ·
              refine ⟨17618364429031713760544407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23491152572042285014059209 17618364429031713760544407)
              ·
                refine ⟨26427546643547570640816611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17618364429031713760544407 26427546643547570640816611)
                ·
                  refine ⟨39641319965321355961224917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26427546643547570640816611 39641319965321355961224917)
                  ·
                    refine ⟨929093436687219280341209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39641319965321355961224917 929093436687219280341209)
                    ·
                      rfl

theorem cell23_5428209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 7].length) (baseStart_5428209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428209 prefixEnd_5428209 := by exact prefixLift 5428209
  have htrace : WordTrace (prefixWord ++ tailWord_5428209) baseStart_5428209 baseEnd_5428209 := by
    simpa [prefixWord, tailWord_5428209, baseEnd_5428209] using wordTrace_append hprefix tailTrace_5428209
  have hstable : (prefixWord ++ tailWord_5428209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428209).length < 2 ^ (prefixWord ++ tailWord_5428209).sum := by decide
  have hdescent : baseEnd_5428209 < baseStart_5428209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428239 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 9, 4]
def baseStart_5428239 : Nat := 118140960795 + 5428239 * 2 ^ 59
def prefixEnd_5428239 : Nat := 4983230072969 + 3 ^ 40 * 5428239 * 2
def baseEnd_5428239 : Nat := 929098571493764241216163

theorem tailTrace_5428239 : CollatzResearch.WordTrace tailWord_5428239 prefixEnd_5428239 929098571493764241216163 := by
  unfold tailWord_5428239
  simp only [CollatzResearch.WordTrace]
  refine ⟨197984141381424647258543771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131989427587616431505695847 197984141381424647258543771)
  ·
    refine ⟨296976212072136970887815657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197984141381424647258543771 296976212072136970887815657)
    ·
      refine ⟨222732159054102728165861743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296976212072136970887815657 222732159054102728165861743)
      ·
        refine ⟨334098238581154092248792615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222732159054102728165861743 334098238581154092248792615)
        ·
          refine ⟨501147357871731138373188923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334098238581154092248792615 501147357871731138373188923)
          ·
            refine ⟨751721036807596707559783385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501147357871731138373188923 751721036807596707559783385)
            ·
              refine ⟨563790777605697530669837539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751721036807596707559783385 563790777605697530669837539)
              ·
                refine ⟨845686166408546296004756309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563790777605697530669837539 845686166408546296004756309)
                ·
                  refine ⟨4955192381300075953152869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 845686166408546296004756309 4955192381300075953152869)
                  ·
                    refine ⟨929098571493764241216163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955192381300075953152869 929098571493764241216163)
                    ·
                      rfl

theorem cell23_5428239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 4].length) (baseStart_5428239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428239 prefixEnd_5428239 := by exact prefixLift 5428239
  have htrace : WordTrace (prefixWord ++ tailWord_5428239) baseStart_5428239 baseEnd_5428239 := by
    simpa [prefixWord, tailWord_5428239, baseEnd_5428239] using wordTrace_append hprefix tailTrace_5428239
  have hstable : (prefixWord ++ tailWord_5428239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428239).length < 2 ^ (prefixWord ++ tailWord_5428239).sum := by decide
  have hdescent : baseEnd_5428239 < baseStart_5428239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428249 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 3]
def baseStart_5428249 : Nat := 118140960795 + 5428249 * 2 ^ 59
def prefixEnd_5428249 : Nat := 4983230072969 + 3 ^ 40 * 5428249 * 2
def baseEnd_5428249 : Nat := 2787300849287837684523443

theorem tailTrace_5428249 : CollatzResearch.WordTrace tailWord_5428249 prefixEnd_5428249 2787300849287837684523443 := by
  unfold tailWord_5428249
  simp only [CollatzResearch.WordTrace]
  refine ⟨197984506111388418966407801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131989670740925612644271867 197984506111388418966407801)
  ·
    refine ⟨148488379583541314224805851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197984506111388418966407801 148488379583541314224805851)
    ·
      refine ⟨222732569375311971337208777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148488379583541314224805851 222732569375311971337208777)
      ·
        refine ⟨167049427031483978502906583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222732569375311971337208777 167049427031483978502906583)
        ·
          refine ⟨250574140547225967754359875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167049427031483978502906583 250574140547225967754359875)
          ·
            refine ⟨375861210820838951631539813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250574140547225967754359875 375861210820838951631539813)
            ·
              refine ⟨70473977028907303430913715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375861210820838951631539813 70473977028907303430913715)
              ·
                refine ⟨105710965543360955146370573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70473977028907303430913715 105710965543360955146370573)
                ·
                  refine ⟨39641612078760358179888965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105710965543360955146370573 39641612078760358179888965)
                  ·
                    refine ⟨7432802264767567158729181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39641612078760358179888965 7432802264767567158729181)
                    ·
                      refine ⟨2787300849287837684523443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432802264767567158729181 2787300849287837684523443)
                      ·
                        rfl

theorem cell23_5428249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_5428249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428249 prefixEnd_5428249 := by exact prefixLift 5428249
  have htrace : WordTrace (prefixWord ++ tailWord_5428249) baseStart_5428249 baseEnd_5428249 := by
    simpa [prefixWord, tailWord_5428249, baseEnd_5428249] using wordTrace_append hprefix tailTrace_5428249
  have hstable : (prefixWord ++ tailWord_5428249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428249).length < 2 ^ (prefixWord ++ tailWord_5428249).sum := by decide
  have hdescent : baseEnd_5428249 < baseStart_5428249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428263 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5428263 : Nat := 118140960795 + 5428263 * 2 ^ 59
def prefixEnd_5428263 : Nat := 4983230072969 + 3 ^ 40 * 5428263 * 2
def baseEnd_5428263 : Nat := 2787308038017000629748379

theorem tailTrace_5428263 : CollatzResearch.WordTrace tailWord_5428263 prefixEnd_5428263 2787308038017000629748379 := by
  unfold tailWord_5428263
  simp only [CollatzResearch.WordTrace]
  refine ⟨197985016733337699357417443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131990011155558466238278295 197985016733337699357417443)
  ·
    refine ⟨296977525100006549036126165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197985016733337699357417443 296977525100006549036126165)
    ·
      refine ⟨6960410744531403493034207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 296977525100006549036126165 6960410744531403493034207)
      ·
        refine ⟨10440616116797105239551311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6960410744531403493034207 10440616116797105239551311)
        ·
          refine ⟨15660924175195657859326967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10440616116797105239551311 15660924175195657859326967)
          ·
            refine ⟨23491386262793486788990451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15660924175195657859326967 23491386262793486788990451)
            ·
              refine ⟨35237079394190230183485677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23491386262793486788990451 35237079394190230183485677)
              ·
                refine ⟨13213904772821336318807129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35237079394190230183485677 13213904772821336318807129)
                ·
                  refine ⟨9910428579616002239105347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13213904772821336318807129 9910428579616002239105347)
                  ·
                    refine ⟨14865642869424003358658021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9910428579616002239105347 14865642869424003358658021)
                    ·
                      refine ⟨2787308038017000629748379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14865642869424003358658021 2787308038017000629748379)
                      ·
                        rfl

theorem cell23_5428263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5428263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428263 prefixEnd_5428263 := by exact prefixLift 5428263
  have htrace : WordTrace (prefixWord ++ tailWord_5428263) baseStart_5428263 baseEnd_5428263 := by
    simpa [prefixWord, tailWord_5428263, baseEnd_5428263] using wordTrace_append hprefix tailTrace_5428263
  have hstable : (prefixWord ++ tailWord_5428263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428263).length < 2 ^ (prefixWord ++ tailWord_5428263).sum := by decide
  have hdescent : baseEnd_5428263 < baseStart_5428263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428273 : List Nat := [1, 2, 2, 3, 1, 2, 2, 5, 1, 4]
def baseStart_5428273 : Nat := 118140960795 + 5428273 * 2 ^ 59
def prefixEnd_5428273 : Nat := 4983230072969 + 3 ^ 40 * 5428273 * 2
def baseEnd_5428273 : Nat := 929104390941181863541111

theorem tailTrace_5428273 : CollatzResearch.WordTrace tailWord_5428273 prefixEnd_5428273 929104390941181863541111 := by
  unfold tailWord_5428273
  simp only [CollatzResearch.WordTrace]
  refine ⟨197985381463301471065281473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131990254308867647376854315 197985381463301471065281473)
  ·
    refine ⟨148489036097476103298961105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197985381463301471065281473 148489036097476103298961105)
    ·
      refine ⟨111366777073107077474220829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148489036097476103298961105 111366777073107077474220829)
      ·
        refine ⟨41762541402415154052832811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111366777073107077474220829 41762541402415154052832811)
        ·
          refine ⟨62643812103622731079249217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41762541402415154052832811 62643812103622731079249217)
          ·
            refine ⟨46982859077717048309436913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62643812103622731079249217 46982859077717048309436913)
            ·
              refine ⟨35237144308287786232077685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46982859077717048309436913 35237144308287786232077685)
              ·
                refine ⟨3303482278901979959257283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35237144308287786232077685 3303482278901979959257283)
                ·
                  refine ⟨4955223418352969938885925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303482278901979959257283 4955223418352969938885925)
                  ·
                    refine ⟨929104390941181863541111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955223418352969938885925 929104390941181863541111)
                    ·
                      rfl

theorem cell23_5428273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 5, 1, 4].length) (baseStart_5428273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428273 prefixEnd_5428273 := by exact prefixLift 5428273
  have htrace : WordTrace (prefixWord ++ tailWord_5428273) baseStart_5428273 baseEnd_5428273 := by
    simpa [prefixWord, tailWord_5428273, baseEnd_5428273] using wordTrace_append hprefix tailTrace_5428273
  have hstable : (prefixWord ++ tailWord_5428273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428273).length < 2 ^ (prefixWord ++ tailWord_5428273).sum := by decide
  have hdescent : baseEnd_5428273 < baseStart_5428273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428309 : List Nat := [1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_5428309 : Nat := 118140960795 + 5428309 * 2 ^ 59
def prefixEnd_5428309 : Nat := 4983230072969 + 3 ^ 40 * 5428309 * 2
def baseEnd_5428309 : Nat := 2787331658127107449773167

theorem tailTrace_5428309 : CollatzResearch.WordTrace tailWord_5428309 prefixEnd_5428309 2787331658127107449773167 := by
  unfold tailWord_5428309
  simp only [CollatzResearch.WordTrace]
  refine ⟨197986694491171049213591981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131991129660780699475727987 197986694491171049213591981)
  ·
    refine ⟨74245010434189143455096993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197986694491171049213591981 74245010434189143455096993)
    ·
      refine ⟨55683757825641857591322745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74245010434189143455096993 55683757825641857591322745)
      ·
        refine ⟨41762818369231393193492059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55683757825641857591322745 41762818369231393193492059)
        ·
          refine ⟨62644227553847089790238089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41762818369231393193492059 62644227553847089790238089)
          ·
            refine ⟨46983170665385317342678567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62644227553847089790238089 46983170665385317342678567)
            ·
              refine ⟨70474755998077976014017851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46983170665385317342678567 70474755998077976014017851)
              ·
                refine ⟨105712133997116964021026777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70474755998077976014017851 105712133997116964021026777)
                ·
                  refine ⟨79284100497837723015770083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105712133997116964021026777 79284100497837723015770083)
                  ·
                    refine ⟨118926150746756584523655125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79284100497837723015770083 118926150746756584523655125)
                    ·
                      refine ⟨2787331658127107449773167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118926150746756584523655125 2787331658127107449773167)
                      ·
                        rfl

theorem cell23_5428309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_5428309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428309 prefixEnd_5428309 := by exact prefixLift 5428309
  have htrace : WordTrace (prefixWord ++ tailWord_5428309) baseStart_5428309 baseEnd_5428309 := by
    simpa [prefixWord, tailWord_5428309, baseEnd_5428309] using wordTrace_append hprefix tailTrace_5428309
  have hstable : (prefixWord ++ tailWord_5428309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428309).length < 2 ^ (prefixWord ++ tailWord_5428309).sum := by decide
  have hdescent : baseEnd_5428309 < baseStart_5428309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428316 : List Nat := [2, 2, 4, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5428316 : Nat := 118140960795 + 5428316 * 2 ^ 59
def prefixEnd_5428316 : Nat := 4983230072969 + 3 ^ 40 * 5428316 * 2
def baseEnd_5428316 : Nat := 929111750830562974128545

theorem tailTrace_5428316 : CollatzResearch.WordTrace tailWord_5428316 prefixEnd_5428316 929111750830562974128545 := by
  unfold tailWord_5428316
  simp only [CollatzResearch.WordTrace]
  refine ⟨98993474901072844704548401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131991299868097126272731201 98993474901072844704548401)
  ·
    refine ⟨74245106175804633528411301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 98993474901072844704548401 74245106175804633528411301)
    ·
      refine ⟨13920957407963368786577119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74245106175804633528411301 13920957407963368786577119)
      ·
        refine ⟨20881436111945053179865679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13920957407963368786577119 20881436111945053179865679)
        ·
          refine ⟨31322154167917579769798519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20881436111945053179865679 31322154167917579769798519)
          ·
            refine ⟨46983231251876369654697779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31322154167917579769798519 46983231251876369654697779)
            ·
              refine ⟨70474846877814554482046669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46983231251876369654697779 70474846877814554482046669)
              ·
                refine ⟨26428067579180457930767501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70474846877814554482046669 26428067579180457930767501)
                ·
                  refine ⟨9910525342192671724037813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26428067579180457930767501 9910525342192671724037813)
                  ·
                    refine ⟨929111750830562974128545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9910525342192671724037813 929111750830562974128545)
                    ·
                      rfl

theorem cell23_5428316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5428316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428316 prefixEnd_5428316 := by exact prefixLift 5428316
  have htrace : WordTrace (prefixWord ++ tailWord_5428316) baseStart_5428316 baseEnd_5428316 := by
    simpa [prefixWord, tailWord_5428316, baseEnd_5428316] using wordTrace_append hprefix tailTrace_5428316
  have hstable : (prefixWord ++ tailWord_5428316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428316).length < 2 ^ (prefixWord ++ tailWord_5428316).sum := by decide
  have hdescent : baseEnd_5428316 < baseStart_5428316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428317 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 3]
def baseStart_5428317 : Nat := 118140960795 + 5428317 * 2 ^ 59
def prefixEnd_5428317 : Nat := 4983230072969 + 3 ^ 40 * 5428317 * 2
def baseEnd_5428317 : Nat := 2787335765972343418473131

theorem tailTrace_5428317 : CollatzResearch.WordTrace tailWord_5428317 prefixEnd_5428317 2787335765972343418473131 := by
  unfold tailWord_5428317
  simp only [CollatzResearch.WordTrace]
  refine ⟨197986986275142066579883205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131991324183428044386588803 197986986275142066579883205)
  ·
    refine ⟨37122559926589137483728101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 197986986275142066579883205 37122559926589137483728101)
    ·
      refine ⟨6960479986235463278199019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37122559926589137483728101 6960479986235463278199019)
      ·
        refine ⟨10440719979353194917298529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6960479986235463278199019 10440719979353194917298529)
        ·
          refine ⟨7830539984514896187973897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10440719979353194917298529 7830539984514896187973897)
          ·
            refine ⟨5872904988386172140980423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7830539984514896187973897 5872904988386172140980423)
            ·
              refine ⟨8809357482579258211470635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5872904988386172140980423 8809357482579258211470635)
              ·
                refine ⟨13214036223868887317205953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8809357482579258211470635 13214036223868887317205953)
                ·
                  refine ⟨9910527167901665487904465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13214036223868887317205953 9910527167901665487904465)
                  ·
                    refine ⟨7432895375926249115928349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9910527167901665487904465 7432895375926249115928349)
                    ·
                      refine ⟨2787335765972343418473131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7432895375926249115928349 2787335765972343418473131)
                      ·
                        rfl

theorem cell23_5428317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 2, 2, 3].length) (baseStart_5428317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428317 prefixEnd_5428317 := by exact prefixLift 5428317
  have htrace : WordTrace (prefixWord ++ tailWord_5428317) baseStart_5428317 baseEnd_5428317 := by
    simpa [prefixWord, tailWord_5428317, baseEnd_5428317] using wordTrace_append hprefix tailTrace_5428317
  have hstable : (prefixWord ++ tailWord_5428317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428317).length < 2 ^ (prefixWord ++ tailWord_5428317).sum := by decide
  have hdescent : baseEnd_5428317 < baseStart_5428317 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428333 : List Nat := [1, 5, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_5428333 : Nat := 118140960795 + 5428333 * 2 ^ 59
def prefixEnd_5428333 : Nat := 4983230072969 + 3 ^ 40 * 5428333 * 2
def baseEnd_5428333 : Nat := 929114660554271785291019

theorem tailTrace_5428333 : CollatzResearch.WordTrace tailWord_5428333 prefixEnd_5428333 929114660554271785291019 := by
  unfold tailWord_5428333
  simp only [CollatzResearch.WordTrace]
  refine ⟨197987569843084101312465653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131991713228722734208310435 197987569843084101312465653)
  ·
    refine ⟨18561334672789134498043655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 197987569843084101312465653 18561334672789134498043655)
    ·
      refine ⟨27842002009183701747065483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18561334672789134498043655 27842002009183701747065483)
      ·
        refine ⟨41763003013775552620598225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27842002009183701747065483 41763003013775552620598225)
        ·
          refine ⟨31322252260331664465448669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41763003013775552620598225 31322252260331664465448669)
          ·
            refine ⟨11745844597624374174543251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31322252260331664465448669 11745844597624374174543251)
            ·
              refine ⟨17618766896436561261814877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11745844597624374174543251 17618766896436561261814877)
              ·
                refine ⟨6607037586163710473180579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17618766896436561261814877 6607037586163710473180579)
                ·
                  refine ⟨9910556379245565709770869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6607037586163710473180579 9910556379245565709770869)
                  ·
                    refine ⟨929114660554271785291019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9910556379245565709770869 929114660554271785291019)
                    ·
                      rfl

theorem cell23_5428333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_5428333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428333 prefixEnd_5428333 := by exact prefixLift 5428333
  have htrace : WordTrace (prefixWord ++ tailWord_5428333) baseStart_5428333 baseEnd_5428333 := by
    simpa [prefixWord, tailWord_5428333, baseEnd_5428333] using wordTrace_append hprefix tailTrace_5428333
  have hstable : (prefixWord ++ tailWord_5428333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428333).length < 2 ^ (prefixWord ++ tailWord_5428333).sum := by decide
  have hdescent : baseEnd_5428333 < baseStart_5428333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428339 : List Nat := [1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5]
def baseStart_5428339 : Nat := 118140960795 + 5428339 * 2 ^ 59
def prefixEnd_5428339 : Nat := 4983230072969 + 3 ^ 40 * 5428339 * 2
def baseEnd_5428339 : Nat := 2787347062546742332398029

theorem tailTrace_5428339 : CollatzResearch.WordTrace tailWord_5428339 prefixEnd_5428339 2787347062546742332398029 := by
  unfold tailWord_5428339
  simp only [CollatzResearch.WordTrace]
  refine ⟨197987788681062364337184071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131991859120708242891456047 197987788681062364337184071)
  ·
    refine ⟨296981683021593546505776107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197987788681062364337184071 296981683021593546505776107)
    ·
      refine ⟨445472524532390319758664161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296981683021593546505776107 445472524532390319758664161)
      ·
        refine ⟨334104393399292739818998121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445472524532390319758664161 334104393399292739818998121)
        ·
          refine ⟨250578295049469554864248591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334104393399292739818998121 250578295049469554864248591)
          ·
            refine ⟨375867442574204332296372887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250578295049469554864248591 375867442574204332296372887)
            ·
              refine ⟨563801163861306498444559331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375867442574204332296372887 563801163861306498444559331)
              ·
                refine ⟨845701745791959747666838997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563801163861306498444559331 845701745791959747666838997)
                ·
                  refine ⟨19821134666999056585941539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 845701745791959747666838997 19821134666999056585941539)
                  ·
                    refine ⟨29731702000498584878912309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19821134666999056585941539 29731702000498584878912309)
                    ·
                      refine ⟨2787347062546742332398029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29731702000498584878912309 2787347062546742332398029)
                      ·
                        rfl

theorem cell23_5428339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_5428339 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428339 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428339 prefixEnd_5428339 := by exact prefixLift 5428339
  have htrace : WordTrace (prefixWord ++ tailWord_5428339) baseStart_5428339 baseEnd_5428339 := by
    simpa [prefixWord, tailWord_5428339, baseEnd_5428339] using wordTrace_append hprefix tailTrace_5428339
  have hstable : (prefixWord ++ tailWord_5428339).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428339).length < 2 ^ (prefixWord ++ tailWord_5428339).sum := by decide
  have hdescent : baseEnd_5428339 < baseStart_5428339 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428356 : List Nat := [2, 3, 2, 1, 2, 2, 1, 1, 3, 1, 5]
def baseStart_5428356 : Nat := 118140960795 + 5428356 * 2 ^ 59
def prefixEnd_5428356 : Nat := 4983230072969 + 3 ^ 40 * 5428356 * 2
def baseEnd_5428356 : Nat := 2787355791717868765885451

theorem tailTrace_5428356 : CollatzResearch.WordTrace tailWord_5428356 prefixEnd_5428356 2787355791717868765885451 := by
  unfold tailWord_5428356
  simp only [CollatzResearch.WordTrace]
  refine ⟨98994204361000388120276461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131992272481333850827035281 98994204361000388120276461)
  ·
    refine ⟨37122826635375145545103673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 98994204361000388120276461 37122826635375145545103673)
    ·
      refine ⟨27842119976531359158827755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37122826635375145545103673 27842119976531359158827755)
      ·
        refine ⟨41763179964797038738241633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27842119976531359158827755 41763179964797038738241633)
        ·
          refine ⟨31322384973597779053681225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41763179964797038738241633 31322384973597779053681225)
          ·
            refine ⟨23491788730198334290260919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31322384973597779053681225 23491788730198334290260919)
            ·
              refine ⟨35237683095297501435391379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23491788730198334290260919 35237683095297501435391379)
              ·
                refine ⟨52856524642946252153087069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35237683095297501435391379 52856524642946252153087069)
                ·
                  refine ⟨19821196741104844557407651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52856524642946252153087069 19821196741104844557407651)
                  ·
                    refine ⟨29731795111657266836111477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19821196741104844557407651 29731795111657266836111477)
                    ·
                      refine ⟨2787355791717868765885451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29731795111657266836111477 2787355791717868765885451)
                      ·
                        rfl

theorem cell23_5428356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_5428356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428356 prefixEnd_5428356 := by exact prefixLift 5428356
  have htrace : WordTrace (prefixWord ++ tailWord_5428356) baseStart_5428356 baseEnd_5428356 := by
    simpa [prefixWord, tailWord_5428356, baseEnd_5428356] using wordTrace_append hprefix tailTrace_5428356
  have hstable : (prefixWord ++ tailWord_5428356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428356).length < 2 ^ (prefixWord ++ tailWord_5428356).sum := by decide
  have hdescent : baseEnd_5428356 < baseStart_5428356 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428359 : List Nat := [1, 1, 4, 2, 1, 1, 1, 12]
def baseStart_5428359 : Nat := 118140960795 + 5428359 * 2 ^ 59
def prefixEnd_5428359 : Nat := 4983230072969 + 3 ^ 40 * 5428359 * 2
def baseEnd_5428359 : Nat := 103235456746660453857331

theorem tailTrace_5428359 : CollatzResearch.WordTrace tailWord_5428359 prefixEnd_5428359 103235456746660453857331 := by
  unfold tailWord_5428359
  simp only [CollatzResearch.WordTrace]
  refine ⟨197988518140989907752912131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131992345427326605168608087 197988518140989907752912131)
  ·
    refine ⟨296982777211484861629368197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197988518140989907752912131 296982777211484861629368197)
    ·
      refine ⟨55684270727153411555506537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 296982777211484861629368197 55684270727153411555506537)
      ·
        refine ⟨41763203045365058666629903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55684270727153411555506537 41763203045365058666629903)
        ·
          refine ⟨62644804568047587999944855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41763203045365058666629903 62644804568047587999944855)
          ·
            refine ⟨93967206852071381999917283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62644804568047587999944855 93967206852071381999917283)
            ·
              refine ⟨140950810278107072999875925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93967206852071381999917283 140950810278107072999875925)
              ·
                refine ⟨103235456746660453857331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 140950810278107072999875925 103235456746660453857331)
                ·
                  rfl

theorem cell23_5428359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 12].length) (baseStart_5428359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428359 prefixEnd_5428359 := by exact prefixLift 5428359
  have htrace : WordTrace (prefixWord ++ tailWord_5428359) baseStart_5428359 baseEnd_5428359 := by
    simpa [prefixWord, tailWord_5428359, baseEnd_5428359] using wordTrace_append hprefix tailTrace_5428359
  have hstable : (prefixWord ++ tailWord_5428359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428359).length < 2 ^ (prefixWord ++ tailWord_5428359).sum := by decide
  have hdescent : baseEnd_5428359 < baseStart_5428359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428370 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 1, 1, 4]
def baseStart_5428370 : Nat := 118140960795 + 5428370 * 2 ^ 59
def prefixEnd_5428370 : Nat := 4983230072969 + 3 ^ 40 * 5428370 * 2
def baseEnd_5428370 : Nat := 2787362980447031711110387

theorem tailTrace_5428370 : CollatzResearch.WordTrace tailWord_5428370 prefixEnd_5428370 2787362980447031711110387 := by
  unfold tailWord_5428370
  simp only [CollatzResearch.WordTrace]
  refine ⟨49497229835987514157890641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131992612895966704421041709 49497229835987514157890641)
  ·
    refine ⟨37122922376990635618417981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49497229835987514157890641 37122922376990635618417981)
    ·
      refine ⟨13921095891371488356906743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37122922376990635618417981 13921095891371488356906743)
      ·
        refine ⟨20881643837057232535360115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13921095891371488356906743 20881643837057232535360115)
        ·
          refine ⟨31322465755585848803040173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20881643837057232535360115 31322465755585848803040173)
          ·
            refine ⟨11745924658344693301140065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31322465755585848803040173 11745924658344693301140065)
            ·
              refine ⟨8809443493758519975855049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11745924658344693301140065 8809443493758519975855049)
              ·
                refine ⟨6607082620318889981891287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8809443493758519975855049 6607082620318889981891287)
                ·
                  refine ⟨9910623930478334972836931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6607082620318889981891287 9910623930478334972836931)
                  ·
                    refine ⟨14865935895717502459255397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9910623930478334972836931 14865935895717502459255397)
                    ·
                      refine ⟨2787362980447031711110387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14865935895717502459255397 2787362980447031711110387)
                      ·
                        rfl

theorem cell23_5428370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_5428370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428370 prefixEnd_5428370 := by exact prefixLift 5428370
  have htrace : WordTrace (prefixWord ++ tailWord_5428370) baseStart_5428370 baseEnd_5428370 := by
    simpa [prefixWord, tailWord_5428370, baseEnd_5428370] using wordTrace_append hprefix tailTrace_5428370
  have hstable : (prefixWord ++ tailWord_5428370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428370).length < 2 ^ (prefixWord ++ tailWord_5428370).sum := by decide
  have hdescent : baseEnd_5428370 < baseStart_5428370 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428376 : List Nat := [2, 1, 2, 4, 2, 2, 1, 9]
def baseStart_5428376 : Nat := 118140960795 + 5428376 * 2 ^ 59
def prefixEnd_5428376 : Nat := 4983230072969 + 3 ^ 40 * 5428376 * 2
def baseEnd_5428376 : Nat := 103235780049294766208717

theorem tailTrace_5428376 : CollatzResearch.WordTrace tailWord_5428376 prefixEnd_5428376 103235780049294766208717 := by
  unfold tailWord_5428376
  simp only [CollatzResearch.WordTrace]
  refine ⟨98994569090964159828140491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 131992758787952213104187321 98994569090964159828140491)
  ·
    refine ⟨148491853636446239742210737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 98994569090964159828140491 148491853636446239742210737)
    ·
      refine ⟨111368890227334679806658053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148491853636446239742210737 111368890227334679806658053)
      ·
        refine ⟨20881666917625252463748385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111368890227334679806658053 20881666917625252463748385)
        ·
          refine ⟨15661250188218939347811289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20881666917625252463748385 15661250188218939347811289)
          ·
            refine ⟨11745937641164204510858467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15661250188218939347811289 11745937641164204510858467)
            ·
              refine ⟨17618906461746306766287701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11745937641164204510858467 17618906461746306766287701)
              ·
                refine ⟨103235780049294766208717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17618906461746306766287701 103235780049294766208717)
                ·
                  rfl

theorem cell23_5428376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 9].length) (baseStart_5428376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428376 prefixEnd_5428376 := by exact prefixLift 5428376
  have htrace : WordTrace (prefixWord ++ tailWord_5428376) baseStart_5428376 baseEnd_5428376 := by
    simpa [prefixWord, tailWord_5428376, baseEnd_5428376] using wordTrace_append hprefix tailTrace_5428376
  have hstable : (prefixWord ++ tailWord_5428376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428376).length < 2 ^ (prefixWord ++ tailWord_5428376).sum := by decide
  have hdescent : baseEnd_5428376 < baseStart_5428376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428403 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 3]
def baseStart_5428403 : Nat := 118140960795 + 5428403 * 2 ^ 59
def prefixEnd_5428403 : Nat := 4983230072969 + 3 ^ 40 * 5428403 * 2
def baseEnd_5428403 : Nat := 2787379925308630081997735

theorem tailTrace_5428403 : CollatzResearch.WordTrace tailWord_5428403 prefixEnd_5428403 2787379925308630081997735 := by
  unfold tailWord_5428403
  simp only [CollatzResearch.WordTrace]
  refine ⟨197990122952830503267513863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131993415301887002178342575 197990122952830503267513863)
  ·
    refine ⟨296985184429245754901270795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197990122952830503267513863 296985184429245754901270795)
    ·
      refine ⟨445477776643868632351906193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296985184429245754901270795 445477776643868632351906193)
      ·
        refine ⟨334108332482901474263929645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445477776643868632351906193 334108332482901474263929645)
        ·
          refine ⟨125290624681088052848973617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334108332482901474263929645 125290624681088052848973617)
          ·
            refine ⟨93967968510816039636730213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125290624681088052848973617 93967968510816039636730213)
            ·
              refine ⟨17618994095778007431886915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93967968510816039636730213 17618994095778007431886915)
              ·
                refine ⟨26428491143667011147830373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17618994095778007431886915 26428491143667011147830373)
                ·
                  refine ⟨4955342089437564590218195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26428491143667011147830373 4955342089437564590218195)
                  ·
                    refine ⟨7433013134156346885327293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4955342089437564590218195 7433013134156346885327293)
                    ·
                      refine ⟨2787379925308630081997735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433013134156346885327293 2787379925308630081997735)
                      ·
                        rfl

theorem cell23_5428403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 4, 1, 3].length) (baseStart_5428403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428403 prefixEnd_5428403 := by exact prefixLift 5428403
  have htrace : WordTrace (prefixWord ++ tailWord_5428403) baseStart_5428403 baseEnd_5428403 := by
    simpa [prefixWord, tailWord_5428403, baseEnd_5428403] using wordTrace_append hprefix tailTrace_5428403
  have hstable : (prefixWord ++ tailWord_5428403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428403).length < 2 ^ (prefixWord ++ tailWord_5428403).sum := by decide
  have hdescent : baseEnd_5428403 < baseStart_5428403 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428498 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5428498 : Nat := 118140960795 + 5428498 * 2 ^ 59
def prefixEnd_5428498 : Nat := 4983230072969 + 3 ^ 40 * 5428498 * 2
def baseEnd_5428498 : Nat := 2787428705970807210309799

theorem tailTrace_5428498 : CollatzResearch.WordTrace tailWord_5428498 prefixEnd_5428498 2787428705970807210309799 := by
  unfold tailWord_5428498
  simp only [CollatzResearch.WordTrace]
  refine ⟨49498396971871583623055537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131995725258324222994814765 49498396971871583623055537)
  ·
    refine ⟨37123797728903687717291653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49498396971871583623055537 37123797728903687717291653)
    ·
      refine ⟨6960712074169441446992185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 37123797728903687717291653 6960712074169441446992185)
      ·
        refine ⟨5220534055627081085244139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6960712074169441446992185 5220534055627081085244139)
        ·
          refine ⟨7830801083440621627866209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5220534055627081085244139 7830801083440621627866209)
          ·
            refine ⟨5873100812580466220899657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7830801083440621627866209 5873100812580466220899657)
            ·
              refine ⟨4404825609435349665674743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5873100812580466220899657 4404825609435349665674743)
              ·
                refine ⟨6607238414153024498512115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4404825609435349665674743 6607238414153024498512115)
                ·
                  refine ⟨9910857621229536747768173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6607238414153024498512115 9910857621229536747768173)
                  ·
                    refine ⟨3716571607961076280413065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9910857621229536747768173 3716571607961076280413065)
                    ·
                      refine ⟨2787428705970807210309799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716571607961076280413065 2787428705970807210309799)
                      ·
                        rfl

theorem cell23_5428498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5428498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428498 prefixEnd_5428498 := by exact prefixLift 5428498
  have htrace : WordTrace (prefixWord ++ tailWord_5428498) baseStart_5428498 baseEnd_5428498 := by
    simpa [prefixWord, tailWord_5428498, baseEnd_5428498] using wordTrace_append hprefix tailTrace_5428498
  have hstable : (prefixWord ++ tailWord_5428498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428498).length < 2 ^ (prefixWord ++ tailWord_5428498).sum := by decide
  have hdescent : baseEnd_5428498 < baseStart_5428498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428511 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 2, 2, 2]
def baseStart_5428511 : Nat := 118140960795 + 5428511 * 2 ^ 59
def prefixEnd_5428511 : Nat := 4983230072969 + 3 ^ 40 * 5428511 * 2
def baseEnd_5428511 : Nat := 2787435381219315659447239

theorem tailTrace_5428511 : CollatzResearch.WordTrace tailWord_5428511 prefixEnd_5428511 2787435381219315659447239 := by
  unfold tailWord_5428511
  simp only [CollatzResearch.WordTrace]
  refine ⟨197994062036439237712445387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131996041357626158474963591 197994062036439237712445387)
  ·
    refine ⟨296991093054658856568668081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197994062036439237712445387 296991093054658856568668081)
    ·
      refine ⟨222743319790994142426501061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 296991093054658856568668081 222743319790994142426501061)
      ·
        refine ⟨41764372460811401704968949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222743319790994142426501061 41764372460811401704968949)
        ·
          refine ⟨3915409918201068909840839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41764372460811401704968949 3915409918201068909840839)
          ·
            refine ⟨5873114877301603364761259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915409918201068909840839 5873114877301603364761259)
            ·
              refine ⟨8809672315952405047141889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873114877301603364761259 8809672315952405047141889)
              ·
                refine ⟨6607254236964303785356417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8809672315952405047141889 6607254236964303785356417)
                ·
                  refine ⟨4955440677723227839017313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607254236964303785356417 4955440677723227839017313)
                  ·
                    refine ⟨3716580508292420879262985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4955440677723227839017313 3716580508292420879262985)
                    ·
                      refine ⟨2787435381219315659447239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716580508292420879262985 2787435381219315659447239)
                      ·
                        rfl

theorem cell23_5428511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_5428511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428511 prefixEnd_5428511 := by exact prefixLift 5428511
  have htrace : WordTrace (prefixWord ++ tailWord_5428511) baseStart_5428511 baseEnd_5428511 := by
    simpa [prefixWord, tailWord_5428511, baseEnd_5428511] using wordTrace_append hprefix tailTrace_5428511
  have hstable : (prefixWord ++ tailWord_5428511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428511).length < 2 ^ (prefixWord ++ tailWord_5428511).sum := by decide
  have hdescent : baseEnd_5428511 < baseStart_5428511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428533 : List Nat := [1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_5428533 : Nat := 118140960795 + 5428533 * 2 ^ 59
def prefixEnd_5428533 : Nat := 4983230072969 + 3 ^ 40 * 5428533 * 2
def baseEnd_5428533 : Nat := 2787446677793714573372137

theorem tailTrace_5428533 : CollatzResearch.WordTrace tailWord_5428533 prefixEnd_5428533 2787446677793714573372137 := by
  unfold tailWord_5428533
  simp only [CollatzResearch.WordTrace]
  refine ⟨197994864442359535469746253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131996576294906356979830835 197994864442359535469746253)
  ·
    refine ⟨74248074165884825801154845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 197994864442359535469746253 74248074165884825801154845)
    ·
      refine ⟨27843027812206809675433067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74248074165884825801154845 27843027812206809675433067)
      ·
        refine ⟨41764541718310214513149601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27843027812206809675433067 41764541718310214513149601)
        ·
          refine ⟨31323406288732660884862201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41764541718310214513149601 31323406288732660884862201)
          ·
            refine ⟨23492554716549495663646651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31323406288732660884862201 23492554716549495663646651)
            ·
              refine ⟨35238832074824243495469977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23492554716549495663646651 35238832074824243495469977)
              ·
                refine ⟨26429124056118182621602483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35238832074824243495469977 26429124056118182621602483)
                ·
                  refine ⟨39643686084177273932403725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26429124056118182621602483 39643686084177273932403725)
                  ·
                    refine ⟨14866382281566477724651397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39643686084177273932403725 14866382281566477724651397)
                    ·
                      refine ⟨2787446677793714573372137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14866382281566477724651397 2787446677793714573372137)
                      ·
                        rfl

theorem cell23_5428533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_5428533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428533 prefixEnd_5428533 := by exact prefixLift 5428533
  have htrace : WordTrace (prefixWord ++ tailWord_5428533) baseStart_5428533 baseEnd_5428533 := by
    simpa [prefixWord, tailWord_5428533, baseEnd_5428533] using wordTrace_append hprefix tailTrace_5428533
  have hstable : (prefixWord ++ tailWord_5428533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428533).length < 2 ^ (prefixWord ++ tailWord_5428533).sum := by decide
  have hdescent : baseEnd_5428533 < baseStart_5428533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428553 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 3]
def baseStart_5428553 : Nat := 118140960795 + 5428553 * 2 ^ 59
def prefixEnd_5428553 : Nat := 4983230072969 + 3 ^ 40 * 5428553 * 2
def baseEnd_5428553 : Nat := 2787456947406804495122045

theorem tailTrace_5428553 : CollatzResearch.WordTrace tailWord_5428553 prefixEnd_5428553 2787456947406804495122045 := by
  unfold tailWord_5428553
  simp only [CollatzResearch.WordTrace]
  refine ⟨197995593902287078885474313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131997062601524719256982875 197995593902287078885474313)
  ·
    refine ⟨148496695426715309164105735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 197995593902287078885474313 148496695426715309164105735)
    ·
      refine ⟨222745043140072963746158603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148496695426715309164105735 222745043140072963746158603)
      ·
        refine ⟨334117564710109445619237905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222745043140072963746158603 334117564710109445619237905)
        ·
          refine ⟨250588173532582084214428429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334117564710109445619237905 250588173532582084214428429)
          ·
            refine ⟨93970565074718281580410661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250588173532582084214428429 93970565074718281580410661)
            ·
              refine ⟨17619480951509677796326999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93970565074718281580410661 17619480951509677796326999)
              ·
                refine ⟨26429221427264516694490499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17619480951509677796326999 26429221427264516694490499)
                ·
                  refine ⟨39643832140896775041735749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26429221427264516694490499 39643832140896775041735749)
                  ·
                    refine ⟨7433218526418145320325453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39643832140896775041735749 7433218526418145320325453)
                    ·
                      refine ⟨2787456947406804495122045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433218526418145320325453 2787456947406804495122045)
                      ·
                        rfl

theorem cell23_5428553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 1, 4, 3].length) (baseStart_5428553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428553 prefixEnd_5428553 := by exact prefixLift 5428553
  have htrace : WordTrace (prefixWord ++ tailWord_5428553) baseStart_5428553 baseEnd_5428553 := by
    simpa [prefixWord, tailWord_5428553, baseEnd_5428553] using wordTrace_append hprefix tailTrace_5428553
  have hstable : (prefixWord ++ tailWord_5428553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428553).length < 2 ^ (prefixWord ++ tailWord_5428553).sum := by decide
  have hdescent : baseEnd_5428553 < baseStart_5428553 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428603 : List Nat := [1, 1, 1, 1, 1, 6, 3, 1, 3, 5]
def baseStart_5428603 : Nat := 118140960795 + 5428603 * 2 ^ 59
def prefixEnd_5428603 : Nat := 4983230072969 + 3 ^ 40 * 5428603 * 2
def baseEnd_5428603 : Nat := 929160873813176433165605

theorem tailTrace_5428603 : CollatzResearch.WordTrace tailWord_5428603 prefixEnd_5428603 929160873813176433165605 := by
  unfold tailWord_5428603
  simp only [CollatzResearch.WordTrace]
  refine ⟨197997417552105937424794463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131998278368070624949862975 197997417552105937424794463)
  ·
    refine ⟨296996126328158906137191695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197997417552105937424794463 296996126328158906137191695)
    ·
      refine ⟨445494189492238359205787543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296996126328158906137191695 445494189492238359205787543)
      ·
        refine ⟨668241284238357538808681315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445494189492238359205787543 668241284238357538808681315)
        ·
          refine ⟨1002361926357536308213021973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668241284238357538808681315 1002361926357536308213021973)
          ·
            refine ⟨46985715298009514447485405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1002361926357536308213021973 46985715298009514447485405)
            ·
              refine ⟨17619643236753567917807027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46985715298009514447485405 17619643236753567917807027)
              ·
                refine ⟨26429464855130351876710541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17619643236753567917807027 26429464855130351876710541)
                ·
                  refine ⟨9911049320673881953766453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26429464855130351876710541 9911049320673881953766453)
                  ·
                    refine ⟨929160873813176433165605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9911049320673881953766453 929160873813176433165605)
                    ·
                      rfl

theorem cell23_5428603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 1, 3, 5].length) (baseStart_5428603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428603 prefixEnd_5428603 := by exact prefixLift 5428603
  have htrace : WordTrace (prefixWord ++ tailWord_5428603) baseStart_5428603 baseEnd_5428603 := by
    simpa [prefixWord, tailWord_5428603, baseEnd_5428603] using wordTrace_append hprefix tailTrace_5428603
  have hstable : (prefixWord ++ tailWord_5428603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428603).length < 2 ^ (prefixWord ++ tailWord_5428603).sum := by decide
  have hdescent : baseEnd_5428603 < baseStart_5428603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428634 : List Nat := [3, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3]
def baseStart_5428634 : Nat := 118140960795 + 5428634 * 2 ^ 59
def prefixEnd_5428634 : Nat := 4983230072969 + 3 ^ 40 * 5428634 * 2
def baseEnd_5428634 : Nat := 2787498539339818678209173

theorem tailTrace_5428634 : CollatzResearch.WordTrace tailWord_5428634 prefixEnd_5428634 2787498539339818678209173 := by
  unfold tailWord_5428634
  simp only [CollatzResearch.WordTrace]
  refine ⟨49499637053748407429793239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 131999032143329086479448637 49499637053748407429793239)
  ·
    refine ⟨74249455580622611144689859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49499637053748407429793239 74249455580622611144689859)
    ·
      refine ⟨111374183370933916717034789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74249455580622611144689859 111374183370933916717034789)
      ·
        refine ⟨20882659382050109384444023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111374183370933916717034789 20882659382050109384444023)
        ·
          refine ⟨31323989073075164076666035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20882659382050109384444023 31323989073075164076666035)
          ·
            refine ⟨46985983609612746114999053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31323989073075164076666035 46985983609612746114999053)
            ·
              refine ⟨17619743853604779793124645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46985983609612746114999053 17619743853604779793124645)
              ·
                refine ⟨3303701972550896211210871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17619743853604779793124645 3303701972550896211210871)
                ·
                  refine ⟨4955552958826344316816307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303701972550896211210871 4955552958826344316816307)
                  ·
                    refine ⟨7433329438239516475224461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4955552958826344316816307 7433329438239516475224461)
                    ·
                      refine ⟨2787498539339818678209173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433329438239516475224461 2787498539339818678209173)
                      ·
                        rfl

theorem cell23_5428634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_5428634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428634 prefixEnd_5428634 := by exact prefixLift 5428634
  have htrace : WordTrace (prefixWord ++ tailWord_5428634) baseStart_5428634 baseEnd_5428634 := by
    simpa [prefixWord, tailWord_5428634, baseEnd_5428634] using wordTrace_append hprefix tailTrace_5428634
  have hstable : (prefixWord ++ tailWord_5428634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428634).length < 2 ^ (prefixWord ++ tailWord_5428634).sum := by decide
  have hdescent : baseEnd_5428634 < baseStart_5428634 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428643 : List Nat := [1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5]
def baseStart_5428643 : Nat := 118140960795 + 5428643 * 2 ^ 59
def prefixEnd_5428643 : Nat := 4983230072969 + 3 ^ 40 * 5428643 * 2
def baseEnd_5428643 : Nat := 2787503160665709142996631

theorem tailTrace_5428643 : CollatzResearch.WordTrace tailWord_5428643 prefixEnd_5428643 2787503160665709142996631 := by
  unfold tailWord_5428643
  simp only [CollatzResearch.WordTrace]
  refine ⟨197998876471961024256250583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 131999250981307349504167055 197998876471961024256250583)
  ·
    refine ⟨296998314707941536384375875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 197998876471961024256250583 296998314707941536384375875)
    ·
      refine ⟨445497472061912304576563813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 296998314707941536384375875 445497472061912304576563813)
      ·
        refine ⟨83530776011608557108105715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 445497472061912304576563813 83530776011608557108105715)
        ·
          refine ⟨125296164017412835662158573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83530776011608557108105715 125296164017412835662158573)
          ·
            refine ⟨46986061506529813373309465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125296164017412835662158573 46986061506529813373309465)
            ·
              refine ⟨35239546129897360029982099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46986061506529813373309465 35239546129897360029982099)
              ·
                refine ⟨52859319194846040044973149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35239546129897360029982099 52859319194846040044973149)
                ·
                  refine ⟨19822244698067265016864931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52859319194846040044973149 19822244698067265016864931)
                  ·
                    refine ⟨29733367047100897525297397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19822244698067265016864931 29733367047100897525297397)
                    ·
                      refine ⟨2787503160665709142996631, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29733367047100897525297397 2787503160665709142996631)
                      ·
                        rfl

theorem cell23_5428643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_5428643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428643 prefixEnd_5428643 := by exact prefixLift 5428643
  have htrace : WordTrace (prefixWord ++ tailWord_5428643) baseStart_5428643 baseEnd_5428643 := by
    simpa [prefixWord, tailWord_5428643, baseEnd_5428643] using wordTrace_append hprefix tailTrace_5428643
  have hstable : (prefixWord ++ tailWord_5428643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428643).length < 2 ^ (prefixWord ++ tailWord_5428643).sum := by decide
  have hdescent : baseEnd_5428643 < baseStart_5428643 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428684 : List Nat := [2, 2, 1, 4, 2, 3, 1, 2, 2, 4]
def baseStart_5428684 : Nat := 118140960795 + 5428684 * 2 ^ 59
def prefixEnd_5428684 : Nat := 4983230072969 + 3 ^ 40 * 5428684 * 2
def baseEnd_5428684 : Nat := 929174737790847827527981

theorem tailTrace_5428684 : CollatzResearch.WordTrace tailWord_5428684 prefixEnd_5428684 929174737790847827527981 := by
  unfold tailWord_5428684
  simp only [CollatzResearch.WordTrace]
  refine ⟨99000185932406244129246553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132000247909874992172328737 99000185932406244129246553)
  ·
    refine ⟨74250139449304683096934915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99000185932406244129246553 74250139449304683096934915)
    ·
      refine ⟨111375209173957024645402373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74250139449304683096934915 111375209173957024645402373)
      ·
        refine ⟨20882851720116942121012945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111375209173957024645402373 20882851720116942121012945)
        ·
          refine ⟨15662138790087706590759709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20882851720116942121012945 15662138790087706590759709)
          ·
            refine ⟨5873302046282889971534891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15662138790087706590759709 5873302046282889971534891)
            ·
              refine ⟨8809953069424334957302337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873302046282889971534891 8809953069424334957302337)
              ·
                refine ⟨6607464802068251217976753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8809953069424334957302337 6607464802068251217976753)
                ·
                  refine ⟨4955598601551188413482565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607464802068251217976753 4955598601551188413482565)
                  ·
                    refine ⟨929174737790847827527981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955598601551188413482565 929174737790847827527981)
                    ·
                      rfl

theorem cell23_5428684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 2, 2, 4].length) (baseStart_5428684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428684 prefixEnd_5428684 := by exact prefixLift 5428684
  have htrace : WordTrace (prefixWord ++ tailWord_5428684) baseStart_5428684 baseEnd_5428684 := by
    simpa [prefixWord, tailWord_5428684, baseEnd_5428684] using wordTrace_append hprefix tailTrace_5428684
  have hstable : (prefixWord ++ tailWord_5428684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428684).length < 2 ^ (prefixWord ++ tailWord_5428684).sum := by decide
  have hdescent : baseEnd_5428684 < baseStart_5428684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428707 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 3]
def baseStart_5428707 : Nat := 118140960795 + 5428707 * 2 ^ 59
def prefixEnd_5428707 : Nat := 4983230072969 + 3 ^ 40 * 5428707 * 2
def baseEnd_5428707 : Nat := 2787536023427596892596337

theorem tailTrace_5428707 : CollatzResearch.WordTrace tailWord_5428707 prefixEnd_5428707 2787536023427596892596337 := by
  unfold tailWord_5428707
  simp only [CollatzResearch.WordTrace]
  refine ⟨198001210743729163186580375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132000807162486108791053583 198001210743729163186580375)
  ·
    refine ⟨297001816115593744779870563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198001210743729163186580375 297001816115593744779870563)
    ·
      refine ⟨445502724173390617169805845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297001816115593744779870563 445502724173390617169805845)
      ·
        refine ⟨20882940195627685179834649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 445502724173390617169805845 20882940195627685179834649)
        ·
          refine ⟨15662205146720763884875987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20882940195627685179834649 15662205146720763884875987)
          ·
            refine ⟨23493307720081145827313981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15662205146720763884875987 23493307720081145827313981)
            ·
              refine ⟨8809990395030429685242743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23493307720081145827313981 8809990395030429685242743)
              ·
                refine ⟨13214985592545644527864115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8809990395030429685242743 13214985592545644527864115)
                ·
                  refine ⟨19822478388818466791796173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13214985592545644527864115 19822478388818466791796173)
                  ·
                    refine ⟨7433429395806925046923565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19822478388818466791796173 7433429395806925046923565)
                    ·
                      refine ⟨2787536023427596892596337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433429395806925046923565 2787536023427596892596337)
                      ·
                        rfl

theorem cell23_5428707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_5428707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428707 prefixEnd_5428707 := by exact prefixLift 5428707
  have htrace : WordTrace (prefixWord ++ tailWord_5428707) baseStart_5428707 baseEnd_5428707 := by
    simpa [prefixWord, tailWord_5428707, baseEnd_5428707] using wordTrace_append hprefix tailTrace_5428707
  have hstable : (prefixWord ++ tailWord_5428707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428707).length < 2 ^ (prefixWord ++ tailWord_5428707).sum := by decide
  have hdescent : baseEnd_5428707 < baseStart_5428707 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428713 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 4]
def baseStart_5428713 : Nat := 118140960795 + 5428713 * 2 ^ 59
def prefixEnd_5428713 : Nat := 4983230072969 + 3 ^ 40 * 5428713 * 2
def baseEnd_5428713 : Nat := 2787539104311523869121309

theorem tailTrace_5428713 : CollatzResearch.WordTrace tailWord_5428713 prefixEnd_5428713 2787539104311523869121309 := by
  unfold tailWord_5428713
  simp only [CollatzResearch.WordTrace]
  refine ⟨198001429581707426211298793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132000953054471617474199195 198001429581707426211298793)
  ·
    refine ⟨148501072186280569658474095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198001429581707426211298793 148501072186280569658474095)
    ·
      refine ⟨222751608279420854487711143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148501072186280569658474095 222751608279420854487711143)
      ·
        refine ⟨334127412419131281731566715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222751608279420854487711143 334127412419131281731566715)
        ·
          refine ⟨501191118628696922597350073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334127412419131281731566715 501191118628696922597350073)
          ·
            refine ⟨375893338971522691948012555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501191118628696922597350073 375893338971522691948012555)
            ·
              refine ⟨563840008457284037922018833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375893338971522691948012555 563840008457284037922018833)
              ·
                refine ⟨422880006342963028441514125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563840008457284037922018833 422880006342963028441514125)
                ·
                  refine ⟨158580002378611135665567797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 422880006342963028441514125 158580002378611135665567797)
                  ·
                    refine ⟨14866875222994793968646981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 158580002378611135665567797 14866875222994793968646981)
                    ·
                      refine ⟨2787539104311523869121309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14866875222994793968646981 2787539104311523869121309)
                      ·
                        rfl

theorem cell23_5428713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 3, 5, 4].length) (baseStart_5428713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428713 prefixEnd_5428713 := by exact prefixLift 5428713
  have htrace : WordTrace (prefixWord ++ tailWord_5428713) baseStart_5428713 baseEnd_5428713 := by
    simpa [prefixWord, tailWord_5428713, baseEnd_5428713] using wordTrace_append hprefix tailTrace_5428713
  have hstable : (prefixWord ++ tailWord_5428713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428713).length < 2 ^ (prefixWord ++ tailWord_5428713).sum := by decide
  have hdescent : baseEnd_5428713 < baseStart_5428713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428714 : List Nat := [3, 1, 3, 1, 5, 1, 2, 7]
def baseStart_5428714 : Nat := 118140960795 + 5428714 * 2 ^ 59
def prefixEnd_5428714 : Nat := 4983230072969 + 3 ^ 40 * 5428714 * 2
def baseEnd_5428714 : Nat := 103242208066376976489215

theorem tailTrace_5428714 : CollatzResearch.WordTrace tailWord_5428714 prefixEnd_5428714 103242208066376976489215 := by
  unfold tailWord_5428714
  simp only [CollatzResearch.WordTrace]
  refine ⟨49500366513675950845521299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132000977369802535588056797 49500366513675950845521299)
  ·
    refine ⟨74250549770513926268281949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49500366513675950845521299 74250549770513926268281949)
    ·
      refine ⟨27843956163942722350605731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74250549770513926268281949 27843956163942722350605731)
      ·
        refine ⟨41765934245914083525908597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27843956163942722350605731 41765934245914083525908597)
        ·
          refine ⟨3915556335554445330553931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41765934245914083525908597 3915556335554445330553931)
          ·
            refine ⟨5873334503331667995830897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915556335554445330553931 5873334503331667995830897)
            ·
              refine ⟨4405000877498750996873173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5873334503331667995830897 4405000877498750996873173)
              ·
                refine ⟨103242208066376976489215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4405000877498750996873173 103242208066376976489215)
                ·
                  rfl

theorem cell23_5428714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 5, 1, 2, 7].length) (baseStart_5428714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428714 prefixEnd_5428714 := by exact prefixLift 5428714
  have htrace : WordTrace (prefixWord ++ tailWord_5428714) baseStart_5428714 baseEnd_5428714 := by
    simpa [prefixWord, tailWord_5428714, baseEnd_5428714] using wordTrace_append hprefix tailTrace_5428714
  have hstable : (prefixWord ++ tailWord_5428714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428714).length < 2 ^ (prefixWord ++ tailWord_5428714).sum := by decide
  have hdescent : baseEnd_5428714 < baseStart_5428714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428723 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 4, 6]
def baseStart_5428723 : Nat := 118140960795 + 5428723 * 2 ^ 59
def prefixEnd_5428723 : Nat := 4983230072969 + 3 ^ 40 * 5428723 * 2
def baseEnd_5428723 : Nat := 929181413039356276665421

theorem tailTrace_5428723 : CollatzResearch.WordTrace tailWord_5428723 prefixEnd_5428723 929181413039356276665421 := by
  unfold tailWord_5428723
  simp only [CollatzResearch.WordTrace]
  refine ⟨198001794311671197919162823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132001196207780798612775215 198001794311671197919162823)
  ·
    refine ⟨297002691467506796878744235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198001794311671197919162823 297002691467506796878744235)
    ·
      refine ⟨445504037201260195318116353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297002691467506796878744235 445504037201260195318116353)
      ·
        refine ⟨334128027900945146488587265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445504037201260195318116353 334128027900945146488587265)
        ·
          refine ⟨250596020925708859866440449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334128027900945146488587265 250596020925708859866440449)
          ·
            refine ⟨187947015694281644899830337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250596020925708859866440449 187947015694281644899830337)
            ·
              refine ⟨140960261770711233674872753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187947015694281644899830337 140960261770711233674872753)
              ·
                refine ⟨105720196328033425256154565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140960261770711233674872753 105720196328033425256154565)
                ·
                  refine ⟨19822536811506267235528981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105720196328033425256154565 19822536811506267235528981)
                  ·
                    refine ⟨929181413039356276665421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19822536811506267235528981 929181413039356276665421)
                    ·
                      rfl

theorem cell23_5428723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 6].length) (baseStart_5428723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428723 prefixEnd_5428723 := by exact prefixLift 5428723
  have htrace : WordTrace (prefixWord ++ tailWord_5428723) baseStart_5428723 baseEnd_5428723 := by
    simpa [prefixWord, tailWord_5428723, baseEnd_5428723] using wordTrace_append hprefix tailTrace_5428723
  have hstable : (prefixWord ++ tailWord_5428723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428723).length < 2 ^ (prefixWord ++ tailWord_5428723).sum := by decide
  have hdescent : baseEnd_5428723 < baseStart_5428723 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428725 : List Nat := [1, 3, 5, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5428725 : Nat := 118140960795 + 5428725 * 2 ^ 59
def prefixEnd_5428725 : Nat := 4983230072969 + 3 ^ 40 * 5428725 * 2
def baseEnd_5428725 : Nat := 2787545266079377822171255

theorem tailTrace_5428725 : CollatzResearch.WordTrace tailWord_5428725 prefixEnd_5428725 2787545266079377822171255 := by
  unfold tailWord_5428725
  simp only [CollatzResearch.WordTrace]
  refine ⟨198001867257663952260735629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132001244838442634840490419 198001867257663952260735629)
  ·
    refine ⟨74250700221623982097775861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198001867257663952260735629 74250700221623982097775861)
    ·
      refine ⟨6961003145777248321666487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 74250700221623982097775861 6961003145777248321666487)
      ·
        refine ⟨10441504718665872482499731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961003145777248321666487 10441504718665872482499731)
        ·
          refine ⟨15662257077998808723749597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10441504718665872482499731 15662257077998808723749597)
          ·
            refine ⟨5873346404249553271406099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15662257077998808723749597 5873346404249553271406099)
            ·
              refine ⟨8810019606374329907109149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873346404249553271406099 8810019606374329907109149)
              ·
                refine ⟨3303757352390373715165931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8810019606374329907109149 3303757352390373715165931)
                ·
                  refine ⟨4955636028585560572748897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303757352390373715165931 4955636028585560572748897)
                  ·
                    refine ⟨3716727021439170429561673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4955636028585560572748897 3716727021439170429561673)
                    ·
                      refine ⟨2787545266079377822171255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716727021439170429561673 2787545266079377822171255)
                      ·
                        rfl

theorem cell23_5428725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5428725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428725 prefixEnd_5428725 := by exact prefixLift 5428725
  have htrace : WordTrace (prefixWord ++ tailWord_5428725) baseStart_5428725 baseEnd_5428725 := by
    simpa [prefixWord, tailWord_5428725, baseEnd_5428725] using wordTrace_append hprefix tailTrace_5428725
  have hstable : (prefixWord ++ tailWord_5428725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428725).length < 2 ^ (prefixWord ++ tailWord_5428725).sum := by decide
  have hdescent : baseEnd_5428725 < baseStart_5428725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428742 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_5428742 : Nat := 118140960795 + 5428742 * 2 ^ 59
def prefixEnd_5428742 : Nat := 4983230072969 + 3 ^ 40 * 5428742 * 2
def baseEnd_5428742 : Nat := 2787553995250504255658677

theorem tailTrace_5428742 : CollatzResearch.WordTrace tailWord_5428742 prefixEnd_5428742 2787553995250504255658677 := by
  unfold tailWord_5428742
  simp only [CollatzResearch.WordTrace]
  refine ⟨6187577728081323880128265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132001658199068242776069653 6187577728081323880128265)
  ·
    refine ⟨4640683296060992910096199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6187577728081323880128265 4640683296060992910096199)
    ·
      refine ⟨6961024944091489365144299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4640683296060992910096199 6961024944091489365144299)
      ·
        refine ⟨10441537416137234047716449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961024944091489365144299 10441537416137234047716449)
        ·
          refine ⟨7831153062102925535787337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10441537416137234047716449 7831153062102925535787337)
          ·
            refine ⟨5873364796577194151840503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7831153062102925535787337 5873364796577194151840503)
            ·
              refine ⟨8810047194865791227760755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873364796577194151840503 8810047194865791227760755)
              ·
                refine ⟨13215070792298686841641133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810047194865791227760755 13215070792298686841641133)
                ·
                  refine ⟨4955651547112007565615425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13215070792298686841641133 4955651547112007565615425)
                  ·
                    refine ⟨3716738660334005674211569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4955651547112007565615425 3716738660334005674211569)
                    ·
                      refine ⟨2787553995250504255658677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716738660334005674211569 2787553995250504255658677)
                      ·
                        rfl

theorem cell23_5428742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_5428742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428742 prefixEnd_5428742 := by exact prefixLift 5428742
  have htrace : WordTrace (prefixWord ++ tailWord_5428742) baseStart_5428742 baseEnd_5428742 := by
    simpa [prefixWord, tailWord_5428742, baseEnd_5428742] using wordTrace_append hprefix tailTrace_5428742
  have hstable : (prefixWord ++ tailWord_5428742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428742).length < 2 ^ (prefixWord ++ tailWord_5428742).sum := by decide
  have hdescent : baseEnd_5428742 < baseStart_5428742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428770 : List Nat := [3, 3, 1, 1, 1, 1, 2, 4, 7]
def baseStart_5428770 : Nat := 118140960795 + 5428770 * 2 ^ 59
def prefixEnd_5428770 : Nat := 4983230072969 + 3 ^ 40 * 5428770 * 2
def baseEnd_5428770 : Nat := 309729819189870016234283

theorem tailTrace_5428770 : CollatzResearch.WordTrace tailWord_5428770 prefixEnd_5428770 309729819189870016234283 := by
  unfold tailWord_5428770
  simp only [CollatzResearch.WordTrace]
  refine ⟨49500877135625231236530941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132002339028333949964082509 49500877135625231236530941)
  ·
    refine ⟨18562828925859461713699103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49500877135625231236530941 18562828925859461713699103)
    ·
      refine ⟨27844243388789192570548655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18562828925859461713699103 27844243388789192570548655)
      ·
        refine ⟨41766365083183788855822983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27844243388789192570548655 41766365083183788855822983)
        ·
          refine ⟨62649547624775683283734475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41766365083183788855822983 62649547624775683283734475)
          ·
            refine ⟨93974321437163524925601713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62649547624775683283734475 93974321437163524925601713)
            ·
              refine ⟨70480741077872643694201285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93974321437163524925601713 70480741077872643694201285)
              ·
                refine ⟨13215138952101120692662741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70480741077872643694201285 13215138952101120692662741)
                ·
                  refine ⟨309729819189870016234283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13215138952101120692662741 309729819189870016234283)
                  ·
                    rfl

theorem cell23_5428770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_5428770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428770 prefixEnd_5428770 := by exact prefixLift 5428770
  have htrace : WordTrace (prefixWord ++ tailWord_5428770) baseStart_5428770 baseEnd_5428770 := by
    simpa [prefixWord, tailWord_5428770, baseEnd_5428770] using wordTrace_append hprefix tailTrace_5428770
  have hstable : (prefixWord ++ tailWord_5428770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428770).length < 2 ^ (prefixWord ++ tailWord_5428770).sum := by decide
  have hdescent : baseEnd_5428770 < baseStart_5428770 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428780 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 3]
def baseStart_5428780 : Nat := 118140960795 + 5428780 * 2 ^ 59
def prefixEnd_5428780 : Nat := 4983230072969 + 3 ^ 40 * 5428780 * 2
def baseEnd_5428780 : Nat := 2787573507515375106983501

theorem tailTrace_5428780 : CollatzResearch.WordTrace tailWord_5428780 prefixEnd_5428780 2787573507515375106983501 := by
  unfold tailWord_5428780
  simp only [CollatzResearch.WordTrace]
  refine ⟨99001936636232348326993897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132002582181643131102658529 99001936636232348326993897)
  ·
    refine ⟨74251452477174261245245423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99001936636232348326993897 74251452477174261245245423)
    ·
      refine ⟨111377178715761391867868135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74251452477174261245245423 111377178715761391867868135)
      ·
        refine ⟨167065768073642087801802203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111377178715761391867868135 167065768073642087801802203)
        ·
          refine ⟨250598652110463131702703305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167065768073642087801802203 250598652110463131702703305)
          ·
            refine ⟨187948989082847348777027479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250598652110463131702703305 187948989082847348777027479)
            ·
              refine ⟨281923483624271023165541219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187948989082847348777027479 281923483624271023165541219)
              ·
                refine ⟨422885225436406534748311829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281923483624271023165541219 422885225436406534748311829)
                ·
                  refine ⟨19822744942331556316327117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 422885225436406534748311829 19822744942331556316327117)
                  ·
                    refine ⟨7433529353374333618622669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19822744942331556316327117 7433529353374333618622669)
                    ·
                      refine ⟨2787573507515375106983501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433529353374333618622669 2787573507515375106983501)
                      ·
                        rfl

theorem cell23_5428780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 3].length) (baseStart_5428780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428780 prefixEnd_5428780 := by exact prefixLift 5428780
  have htrace : WordTrace (prefixWord ++ tailWord_5428780) baseStart_5428780 baseEnd_5428780 := by
    simpa [prefixWord, tailWord_5428780, baseEnd_5428780] using wordTrace_append hprefix tailTrace_5428780
  have hstable : (prefixWord ++ tailWord_5428780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428780).length < 2 ^ (prefixWord ++ tailWord_5428780).sum := by decide
  have hdescent : baseEnd_5428780 < baseStart_5428780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428810 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_5428810 : Nat := 118140960795 + 5428810 * 2 ^ 59
def prefixEnd_5428810 : Nat := 4983230072969 + 3 ^ 40 * 5428810 * 2
def baseEnd_5428810 : Nat := 2787588911935009989608363

theorem tailTrace_5428810 : CollatzResearch.WordTrace tailWord_5428810 prefixEnd_5428810 2787588911935009989608363 := by
  unfold tailWord_5428810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49501241865589002944394971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132003311641570674518386589 49501241865589002944394971)
  ·
    refine ⟨74251862798383504416592457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49501241865589002944394971 74251862798383504416592457)
    ·
      refine ⟨55688897098787628312444343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74251862798383504416592457 55688897098787628312444343)
      ·
        refine ⟨83533345648181442468666515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55688897098787628312444343 83533345648181442468666515)
        ·
          refine ⟨125300018472272163702999773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83533345648181442468666515 125300018472272163702999773)
          ·
            refine ⟨46987506927102061388624915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125300018472272163702999773 46987506927102061388624915)
            ·
              refine ⟨70481260390653092082937373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46987506927102061388624915 70481260390653092082937373)
              ·
                refine ⟨26430472646494909531101515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70481260390653092082937373 26430472646494909531101515)
                ·
                  refine ⟨39645708969742364296652273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26430472646494909531101515 39645708969742364296652273)
                  ·
                    refine ⟨29734281727306773222489205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39645708969742364296652273 29734281727306773222489205)
                    ·
                      refine ⟨2787588911935009989608363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29734281727306773222489205 2787588911935009989608363)
                      ·
                        rfl

theorem cell23_5428810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_5428810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428810 prefixEnd_5428810 := by exact prefixLift 5428810
  have htrace : WordTrace (prefixWord ++ tailWord_5428810) baseStart_5428810 baseEnd_5428810 := by
    simpa [prefixWord, tailWord_5428810, baseEnd_5428810] using wordTrace_append hprefix tailTrace_5428810
  have hstable : (prefixWord ++ tailWord_5428810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428810).length < 2 ^ (prefixWord ++ tailWord_5428810).sum := by decide
  have hdescent : baseEnd_5428810 < baseStart_5428810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428837 : List Nat := [1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 4]
def baseStart_5428837 : Nat := 118140960795 + 5428837 * 2 ^ 59
def prefixEnd_5428837 : Nat := 4983230072969 + 3 ^ 40 * 5428837 * 2
def baseEnd_5428837 : Nat := 2787602775912681383970739

theorem tailTrace_5428837 : CollatzResearch.WordTrace tailWord_5428837 prefixEnd_5428837 2787602775912681383970739 := by
  unfold tailWord_5428837
  simp only [CollatzResearch.WordTrace]
  refine ⟨198005952233258195388812765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132003968155505463592541843 198005952233258195388812765)
  ·
    refine ⟨74252232087471823270804787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198005952233258195388812765 74252232087471823270804787)
    ·
      refine ⟨111378348131207734906207181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74252232087471823270804787 111378348131207734906207181)
      ·
        refine ⟨41766880549202900589827693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111378348131207734906207181 41766880549202900589827693)
        ·
          refine ⟨15662580205951087721185385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41766880549202900589827693 15662580205951087721185385)
          ·
            refine ⟨11746935154463315790889039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15662580205951087721185385 11746935154463315790889039)
            ·
              refine ⟨17620402731694973686333559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11746935154463315790889039 17620402731694973686333559)
              ·
                refine ⟨26430604097542460529500339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17620402731694973686333559 26430604097542460529500339)
                ·
                  refine ⟨39645906146313690794250509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26430604097542460529500339 39645906146313690794250509)
                  ·
                    refine ⟨14867214804867634047843941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39645906146313690794250509 14867214804867634047843941)
                    ·
                      refine ⟨2787602775912681383970739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14867214804867634047843941 2787602775912681383970739)
                      ·
                        rfl

theorem cell23_5428837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_5428837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428837 prefixEnd_5428837 := by exact prefixLift 5428837
  have htrace : WordTrace (prefixWord ++ tailWord_5428837) baseStart_5428837 baseEnd_5428837 := by
    simpa [prefixWord, tailWord_5428837, baseEnd_5428837] using wordTrace_append hprefix tailTrace_5428837
  have hstable : (prefixWord ++ tailWord_5428837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428837).length < 2 ^ (prefixWord ++ tailWord_5428837).sum := by decide
  have hdescent : baseEnd_5428837 < baseStart_5428837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428857 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 3]
def baseStart_5428857 : Nat := 118140960795 + 5428857 * 2 ^ 59
def prefixEnd_5428857 : Nat := 4983230072969 + 3 ^ 40 * 5428857 * 2
def baseEnd_5428857 : Nat := 2787613045525771305720647

theorem tailTrace_5428857 : CollatzResearch.WordTrace tailWord_5428857 prefixEnd_5428857 2787613045525771305720647 := by
  unfold tailWord_5428857
  simp only [CollatzResearch.WordTrace]
  refine ⟨198006681693185738804540825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132004454462123825869693883 198006681693185738804540825)
  ·
    refine ⟨148505011269889304103405619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198006681693185738804540825 148505011269889304103405619)
    ·
      refine ⟨222757516904833956155108429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148505011269889304103405619 222757516904833956155108429)
      ·
        refine ⟨83534068839312733558165661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222757516904833956155108429 83534068839312733558165661)
        ·
          refine ⟨31325275814742275084312123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83534068839312733558165661 31325275814742275084312123)
          ·
            refine ⟨46987913722113412626468185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31325275814742275084312123 46987913722113412626468185)
            ·
              refine ⟨35240935291585059469851139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46987913722113412626468185 35240935291585059469851139)
              ·
                refine ⟨52861402937377589204776709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35240935291585059469851139 52861402937377589204776709)
                ·
                  refine ⟨9911513050758297975895633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52861402937377589204776709 9911513050758297975895633)
                  ·
                    refine ⟨7433634788068723481921725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9911513050758297975895633 7433634788068723481921725)
                    ·
                      refine ⟨2787613045525771305720647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433634788068723481921725 2787613045525771305720647)
                      ·
                        rfl

theorem cell23_5428857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_5428857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428857 prefixEnd_5428857 := by exact prefixLift 5428857
  have htrace : WordTrace (prefixWord ++ tailWord_5428857) baseStart_5428857 baseEnd_5428857 := by
    simpa [prefixWord, tailWord_5428857, baseEnd_5428857] using wordTrace_append hprefix tailTrace_5428857
  have hstable : (prefixWord ++ tailWord_5428857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428857).length < 2 ^ (prefixWord ++ tailWord_5428857).sum := by decide
  have hdescent : baseEnd_5428857 < baseStart_5428857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428864 : List Nat := [2, 1, 1, 2, 1, 4, 1, 6, 1, 4]
def baseStart_5428864 : Nat := 118140960795 + 5428864 * 2 ^ 59
def prefixEnd_5428864 : Nat := 4983230072969 + 3 ^ 40 * 5428864 * 2
def baseEnd_5428864 : Nat := 929205546630117592777705

theorem tailTrace_5428864 : CollatzResearch.WordTrace tailWord_5428864 prefixEnd_5428864 929205546630117592777705 := by
  unfold tailWord_5428864
  simp only [CollatzResearch.WordTrace]
  refine ⟨99003468502080189500022823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132004624669440252666697097 99003468502080189500022823)
  ·
    refine ⟨148505202753120284250034235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99003468502080189500022823 148505202753120284250034235)
    ·
      refine ⟨222757804129680426375051353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148505202753120284250034235 222757804129680426375051353)
      ·
        refine ⟨167068353097260319781288515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222757804129680426375051353 167068353097260319781288515)
        ·
          refine ⟨250602529645890479671932773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167068353097260319781288515 250602529645890479671932773)
          ·
            refine ⟨46987974308604464938487395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250602529645890479671932773 46987974308604464938487395)
            ·
              refine ⟨70481961462906697407731093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46987974308604464938487395 70481961462906697407731093)
              ·
                refine ⟨3303841943573751440987395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70481961462906697407731093 3303841943573751440987395)
                ·
                  refine ⟨4955762915360627161481093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303841943573751440987395 4955762915360627161481093)
                  ·
                    refine ⟨929205546630117592777705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955762915360627161481093 929205546630117592777705)
                    ·
                      rfl

theorem cell23_5428864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 6, 1, 4].length) (baseStart_5428864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428864 prefixEnd_5428864 := by exact prefixLift 5428864
  have htrace : WordTrace (prefixWord ++ tailWord_5428864) baseStart_5428864 baseEnd_5428864 := by
    simpa [prefixWord, tailWord_5428864, baseEnd_5428864] using wordTrace_append hprefix tailTrace_5428864
  have hstable : (prefixWord ++ tailWord_5428864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428864).length < 2 ^ (prefixWord ++ tailWord_5428864).sum := by decide
  have hdescent : baseEnd_5428864 < baseStart_5428864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428914 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2]
def baseStart_5428914 : Nat := 118140960795 + 5428914 * 2 ^ 59
def prefixEnd_5428914 : Nat := 4983230072969 + 3 ^ 40 * 5428914 * 2
def baseEnd_5428914 : Nat := 2787642313923077582707885

theorem tailTrace_5428914 : CollatzResearch.WordTrace tailWord_5428914 prefixEnd_5428914 2787642313923077582707885 := by
  unfold tailWord_5428914
  simp only [CollatzResearch.WordTrace]
  refine ⟨49502190163494809384841449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132005840435986158359577197 49502190163494809384841449)
  ·
    refine ⟨37126642622621107038631087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49502190163494809384841449 37126642622621107038631087)
    ·
      refine ⟨55689963933931660557946631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37126642622621107038631087 55689963933931660557946631)
      ·
        refine ⟨83534945900897490836919947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55689963933931660557946631 83534945900897490836919947)
        ·
          refine ⟨125302418851346236255379921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83534945900897490836919947 125302418851346236255379921)
          ·
            refine ⟨93976814138509677191534941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125302418851346236255379921 93976814138509677191534941)
            ·
              refine ⟨35241305301941128946825603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93976814138509677191534941 35241305301941128946825603)
              ·
                refine ⟨52861957952911693420238405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35241305301941128946825603 52861957952911693420238405)
                ·
                  refine ⟨9911617116170942516294701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52861957952911693420238405 9911617116170942516294701)
                  ·
                    refine ⟨3716856418564103443610513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9911617116170942516294701 3716856418564103443610513)
                    ·
                      refine ⟨2787642313923077582707885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716856418564103443610513 2787642313923077582707885)
                      ·
                        rfl

theorem cell23_5428914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 3, 2].length) (baseStart_5428914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428914 prefixEnd_5428914 := by exact prefixLift 5428914
  have htrace : WordTrace (prefixWord ++ tailWord_5428914) baseStart_5428914 baseEnd_5428914 := by
    simpa [prefixWord, tailWord_5428914, baseEnd_5428914] using wordTrace_append hprefix tailTrace_5428914
  have hstable : (prefixWord ++ tailWord_5428914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428914).length < 2 ^ (prefixWord ++ tailWord_5428914).sum := by decide
  have hdescent : baseEnd_5428914 < baseStart_5428914 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428921 : List Nat := [1, 2, 1, 4, 1, 1, 2, 6, 1, 1, 3]
def baseStart_5428921 : Nat := 118140960795 + 5428921 * 2 ^ 59
def prefixEnd_5428921 : Nat := 4983230072969 + 3 ^ 40 * 5428921 * 2
def baseEnd_5428921 : Nat := 2787645908287659055320353

theorem tailTrace_5428921 : CollatzResearch.WordTrace tailWord_5428921 prefixEnd_5428921 2787645908287659055320353 := by
  unfold tailWord_5428921
  simp only [CollatzResearch.WordTrace]
  refine ⟨198009015964953877734870617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132006010643302585156580411 198009015964953877734870617)
  ·
    refine ⟨148506761973715408301152963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198009015964953877734870617 148506761973715408301152963)
    ·
      refine ⟨222760142960573112451729445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148506761973715408301152963 222760142960573112451729445)
      ·
        refine ⟨41767526805107458584699271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222760142960573112451729445 41767526805107458584699271)
        ·
          refine ⟨62651290207661187877048907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41767526805107458584699271 62651290207661187877048907)
          ·
            refine ⟨93976935311491781815573361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62651290207661187877048907 93976935311491781815573361)
            ·
              refine ⟨70482701483618836361680021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93976935311491781815573361 70482701483618836361680021)
              ·
                refine ⟨3303876632044632954453751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 70482701483618836361680021 3303876632044632954453751)
                ·
                  refine ⟨4955814948066949431680627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3303876632044632954453751 4955814948066949431680627)
                  ·
                    refine ⟨7433722422100424147520941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4955814948066949431680627 7433722422100424147520941)
                    ·
                      refine ⟨2787645908287659055320353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433722422100424147520941 2787645908287659055320353)
                      ·
                        rfl

theorem cell23_5428921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_5428921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428921 prefixEnd_5428921 := by exact prefixLift 5428921
  have htrace : WordTrace (prefixWord ++ tailWord_5428921) baseStart_5428921 baseEnd_5428921 := by
    simpa [prefixWord, tailWord_5428921, baseEnd_5428921] using wordTrace_append hprefix tailTrace_5428921
  have hstable : (prefixWord ++ tailWord_5428921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428921).length < 2 ^ (prefixWord ++ tailWord_5428921).sum := by decide
  have hdescent : baseEnd_5428921 < baseStart_5428921 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428927 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 4]
def baseStart_5428927 : Nat := 118140960795 + 5428927 * 2 ^ 59
def prefixEnd_5428927 : Nat := 4983230072969 + 3 ^ 40 * 5428927 * 2
def baseEnd_5428927 : Nat := 2787648989171586031845325

theorem tailTrace_5428927 : CollatzResearch.WordTrace tailWord_5428927 prefixEnd_5428927 2787648989171586031845325 := by
  unfold tailWord_5428927
  simp only [CollatzResearch.WordTrace]
  refine ⟨198009234802932140759589035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132006156535288093839726023 198009234802932140759589035)
  ·
    refine ⟨297013852204398211139383553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198009234802932140759589035 297013852204398211139383553)
    ·
      refine ⟨222760389153298658354537665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297013852204398211139383553 222760389153298658354537665)
      ·
        refine ⟨167070291864973993765903249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222760389153298658354537665 167070291864973993765903249)
        ·
          refine ⟨125302718898730495324427437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167070291864973993765903249 125302718898730495324427437)
          ·
            refine ⟨46988519587023935746660289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125302718898730495324427437 46988519587023935746660289)
            ·
              refine ⟨35241389690267951809995217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46988519587023935746660289 35241389690267951809995217)
              ·
                refine ⟨26431042267700963857496413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35241389690267951809995217 26431042267700963857496413)
                ·
                  refine ⟨9911640850387861446561155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26431042267700963857496413 9911640850387861446561155)
                  ·
                    refine ⟨14867461275581792169841733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9911640850387861446561155 14867461275581792169841733)
                    ·
                      refine ⟨2787648989171586031845325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14867461275581792169841733 2787648989171586031845325)
                      ·
                        rfl

theorem cell23_5428927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_5428927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428927 prefixEnd_5428927 := by exact prefixLift 5428927
  have htrace : WordTrace (prefixWord ++ tailWord_5428927) baseStart_5428927 baseEnd_5428927 := by
    simpa [prefixWord, tailWord_5428927, baseEnd_5428927] using wordTrace_append hprefix tailTrace_5428927
  have hstable : (prefixWord ++ tailWord_5428927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428927).length < 2 ^ (prefixWord ++ tailWord_5428927).sum := by decide
  have hdescent : baseEnd_5428927 < baseStart_5428927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428941 : List Nat := [1, 6, 2, 1, 1, 2, 1, 1, 3, 5]
def baseStart_5428941 : Nat := 118140960795 + 5428941 * 2 ^ 59
def prefixEnd_5428941 : Nat := 4983230072969 + 3 ^ 40 * 5428941 * 2
def baseEnd_5428941 : Nat := 929218725966916325690087

theorem tailTrace_5428941 : CollatzResearch.WordTrace tailWord_5428941 prefixEnd_5428941 929218725966916325690087 := by
  unfold tailWord_5428941
  simp only [CollatzResearch.WordTrace]
  refine ⟨198009745424881421150598677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132006496949920947433732451 198009745424881421150598677)
  ·
    refine ⟨9281706816791316616434313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198009745424881421150598677 9281706816791316616434313)
    ·
      refine ⟨6961280112593487462325735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9281706816791316616434313 6961280112593487462325735)
      ·
        refine ⟨10441920168890231193488603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961280112593487462325735 10441920168890231193488603)
        ·
          refine ⟨15662880253335346790232905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10441920168890231193488603 15662880253335346790232905)
          ·
            refine ⟨11747160190001510092674679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15662880253335346790232905 11747160190001510092674679)
            ·
              refine ⟨17620740285002265139012019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11747160190001510092674679 17620740285002265139012019)
              ·
                refine ⟨26431110427503397708518029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17620740285002265139012019 26431110427503397708518029)
                ·
                  refine ⟨9911666410313774140694261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26431110427503397708518029 9911666410313774140694261)
                  ·
                    refine ⟨929218725966916325690087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9911666410313774140694261 929218725966916325690087)
                    ·
                      rfl

theorem cell23_5428941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_5428941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428941 prefixEnd_5428941 := by exact prefixLift 5428941
  have htrace : WordTrace (prefixWord ++ tailWord_5428941) baseStart_5428941 baseEnd_5428941 := by
    simpa [prefixWord, tailWord_5428941, baseEnd_5428941] using wordTrace_append hprefix tailTrace_5428941
  have hstable : (prefixWord ++ tailWord_5428941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428941).length < 2 ^ (prefixWord ++ tailWord_5428941).sum := by decide
  have hdescent : baseEnd_5428941 < baseStart_5428941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428948 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 2, 3, 2]
def baseStart_5428948 : Nat := 118140960795 + 5428948 * 2 ^ 59
def prefixEnd_5428948 : Nat := 4983230072969 + 3 ^ 40 * 5428948 * 2
def baseEnd_5428948 : Nat := 2787659772265330449682729

theorem tailTrace_5428948 : CollatzResearch.WordTrace tailWord_5428948 prefixEnd_5428948 2787659772265330449682729 := by
  unfold tailWord_5428948
  simp only [CollatzResearch.WordTrace]
  refine ⟨99005000367928030673051749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132006667157237374230735665 99005000367928030673051749)
  ·
    refine ⟨18563437568986505751197203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99005000367928030673051749 18563437568986505751197203)
    ·
      refine ⟨27845156353479758626795805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18563437568986505751197203 27845156353479758626795805)
      ·
        refine ⟨10441933632554909485048427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27845156353479758626795805 10441933632554909485048427)
        ·
          refine ⟨15662900448832364227572641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10441933632554909485048427 15662900448832364227572641)
          ·
            refine ⟨11747175336624273170679481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15662900448832364227572641 11747175336624273170679481)
            ·
              refine ⟨8810381502468204878009611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11747175336624273170679481 8810381502468204878009611)
              ·
                refine ⟨13215572253702307317014417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810381502468204878009611 13215572253702307317014417)
                ·
                  refine ⟨9911679190276730487760813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13215572253702307317014417 9911679190276730487760813)
                  ·
                    refine ⟨3716879696353773932910305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9911679190276730487760813 3716879696353773932910305)
                    ·
                      refine ⟨2787659772265330449682729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716879696353773932910305 2787659772265330449682729)
                      ·
                        rfl

theorem cell23_5428948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 3, 2].length) (baseStart_5428948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428948 prefixEnd_5428948 := by exact prefixLift 5428948
  have htrace : WordTrace (prefixWord ++ tailWord_5428948) baseStart_5428948 baseEnd_5428948 := by
    simpa [prefixWord, tailWord_5428948, baseEnd_5428948] using wordTrace_append hprefix tailTrace_5428948
  have hstable : (prefixWord ++ tailWord_5428948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428948).length < 2 ^ (prefixWord ++ tailWord_5428948).sum := by decide
  have hdescent : baseEnd_5428948 < baseStart_5428948 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5428967 : List Nat := [1, 1, 5, 4, 12]
def baseStart_5428967 : Nat := 118140960795 + 5428967 * 2 ^ 59
def prefixEnd_5428967 : Nat := 4983230072969 + 3 ^ 40 * 5428967 * 2
def baseEnd_5428967 : Nat := 3823963687788430556029

theorem tailTrace_5428967 : CollatzResearch.WordTrace tailWord_5428967 prefixEnd_5428967 3823963687788430556029 := by
  unfold tailWord_5428967
  simp only [CollatzResearch.WordTrace]
  refine ⟨198010693722787227591045155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132007129148524818394030103 198010693722787227591045155)
  ·
    refine ⟨297016040584180841386567733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198010693722787227591045155 297016040584180841386567733)
    ·
      refine ⟨27845253804766953879990725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297016040584180841386567733 27845253804766953879990725)
      ·
        refine ⟨5220985088393803852498261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27845253804766953879990725 5220985088393803852498261)
        ·
          refine ⟨3823963687788430556029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5220985088393803852498261 3823963687788430556029)
          ·
            rfl

theorem cell23_5428967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 12].length) (baseStart_5428967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5428967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5428967 prefixEnd_5428967 := by exact prefixLift 5428967
  have htrace : WordTrace (prefixWord ++ tailWord_5428967) baseStart_5428967 baseEnd_5428967 := by
    simpa [prefixWord, tailWord_5428967, baseEnd_5428967] using wordTrace_append hprefix tailTrace_5428967
  have hstable : (prefixWord ++ tailWord_5428967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5428967).length < 2 ^ (prefixWord ++ tailWord_5428967).sum := by decide
  have hdescent : baseEnd_5428967 < baseStart_5428967 := by decide
  rcases family_descends (prefixWord ++ tailWord_5428967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429022 : List Nat := [4, 3, 2, 2, 1, 2, 1, 2, 2, 4]
def baseStart_5429022 : Nat := 118140960795 + 5429022 * 2 ^ 59
def prefixEnd_5429022 : Nat := 4983230072969 + 3 ^ 40 * 5429022 * 2
def baseEnd_5429022 : Nat := 929232589944587720052463

theorem tailTrace_5429022 : CollatzResearch.WordTrace tailWord_5429022 prefixEnd_5429022 929232589944587720052463 := by
  unfold tailWord_5429022
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751587467198496498037165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132008466491725314656198213 24751587467198496498037165)
  ·
    refine ⟨9281845300199436186763937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24751587467198496498037165 9281845300199436186763937)
    ·
      refine ⟨6961383975149577140072953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9281845300199436186763937 6961383975149577140072953)
      ·
        refine ⟨5221037981362182855054715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6961383975149577140072953 5221037981362182855054715)
        ·
          refine ⟨7831556972043274282582073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221037981362182855054715 7831556972043274282582073)
          ·
            refine ⟨5873667729032455711936555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7831556972043274282582073 5873667729032455711936555)
            ·
              refine ⟨8810501593548683567904833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873667729032455711936555 8810501593548683567904833)
              ·
                refine ⟨6607876195161512675928625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8810501593548683567904833 6607876195161512675928625)
                ·
                  refine ⟨4955907146371134506946469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607876195161512675928625 4955907146371134506946469)
                  ·
                    refine ⟨929232589944587720052463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4955907146371134506946469 929232589944587720052463)
                    ·
                      rfl

theorem cell23_5429022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_5429022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429022 prefixEnd_5429022 := by exact prefixLift 5429022
  have htrace : WordTrace (prefixWord ++ tailWord_5429022) baseStart_5429022 baseEnd_5429022 := by
    simpa [prefixWord, tailWord_5429022, baseEnd_5429022] using wordTrace_append hprefix tailTrace_5429022
  have hstable : (prefixWord ++ tailWord_5429022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429022).length < 2 ^ (prefixWord ++ tailWord_5429022).sum := by decide
  have hdescent : baseEnd_5429022 < baseStart_5429022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429027 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 2, 6]
def baseStart_5429027 : Nat := 118140960795 + 5429027 * 2 ^ 59
def prefixEnd_5429027 : Nat := 4983230072969 + 3 ^ 40 * 5429027 * 2
def baseEnd_5429027 : Nat := 929233445745678546864955

theorem tailTrace_5429027 : CollatzResearch.WordTrace tailWord_5429027 prefixEnd_5429027 929233445745678546864955 := by
  unfold tailWord_5429027
  simp only [CollatzResearch.WordTrace]
  refine ⟨198012882102569857838229335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132008588068379905225486223 198012882102569857838229335)
  ·
    refine ⟨297019323153854786757344003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198012882102569857838229335 297019323153854786757344003)
    ·
      refine ⟨445528984730782180136016005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297019323153854786757344003 445528984730782180136016005)
      ·
        refine ⟨83536684637021658775503001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 445528984730782180136016005 83536684637021658775503001)
        ·
          refine ⟨62652513477766244081627251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83536684637021658775503001 62652513477766244081627251)
          ·
            refine ⟨93978770216649366122440877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62652513477766244081627251 93978770216649366122440877)
            ·
              refine ⟨35242038831243512295915329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93978770216649366122440877 35242038831243512295915329)
              ·
                refine ⟨26431529123432634221936497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35242038831243512295915329 26431529123432634221936497)
                ·
                  refine ⟨19823646842574475666452373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26431529123432634221936497 19823646842574475666452373)
                  ·
                    refine ⟨929233445745678546864955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19823646842574475666452373 929233445745678546864955)
                    ·
                      rfl

theorem cell23_5429027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 6].length) (baseStart_5429027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429027 prefixEnd_5429027 := by exact prefixLift 5429027
  have htrace : WordTrace (prefixWord ++ tailWord_5429027) baseStart_5429027 baseEnd_5429027 := by
    simpa [prefixWord, tailWord_5429027, baseEnd_5429027] using wordTrace_append hprefix tailTrace_5429027
  have hstable : (prefixWord ++ tailWord_5429027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429027).length < 2 ^ (prefixWord ++ tailWord_5429027).sum := by decide
  have hdescent : baseEnd_5429027 < baseStart_5429027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429028 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 2, 1, 3]
def baseStart_5429028 : Nat := 118140960795 + 5429028 * 2 ^ 59
def prefixEnd_5429028 : Nat := 4983230072969 + 3 ^ 40 * 5429028 * 2
def baseEnd_5429028 : Nat := 2787700850717690136682361

theorem tailTrace_5429028 : CollatzResearch.WordTrace tailWord_5429028 prefixEnd_5429028 2787700850717690136682361 := by
  unfold tailWord_5429028
  simp only [CollatzResearch.WordTrace]
  refine ⟨99006459287783117504507869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132008612383710823339343825 99006459287783117504507869)
  ·
    refine ⟨37127422232918669064190451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99006459287783117504507869 37127422232918669064190451)
    ·
      refine ⟨55691133349378003596285677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37127422232918669064190451 55691133349378003596285677)
      ·
        refine ⟨20884175006016751348607129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55691133349378003596285677 20884175006016751348607129)
        ·
          refine ⟨15663131254512563511455347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20884175006016751348607129 15663131254512563511455347)
          ·
            refine ⟨23494696881768845267183021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15663131254512563511455347 23494696881768845267183021)
            ·
              refine ⟨8810511330663316975193633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23494696881768845267183021 8810511330663316975193633)
              ·
                refine ⟨6607883497997487731395225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8810511330663316975193633 6607883497997487731395225)
                ·
                  refine ⟨4955912623498115798546419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607883497997487731395225 4955912623498115798546419)
                  ·
                    refine ⟨7433868935247173697819629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4955912623498115798546419 7433868935247173697819629)
                    ·
                      refine ⟨2787700850717690136682361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433868935247173697819629 2787700850717690136682361)
                      ·
                        rfl

theorem cell23_5429028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_5429028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429028 prefixEnd_5429028 := by exact prefixLift 5429028
  have htrace : WordTrace (prefixWord ++ tailWord_5429028) baseStart_5429028 baseEnd_5429028 := by
    simpa [prefixWord, tailWord_5429028, baseEnd_5429028] using wordTrace_append hprefix tailTrace_5429028
  have hstable : (prefixWord ++ tailWord_5429028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429028).length < 2 ^ (prefixWord ++ tailWord_5429028).sum := by decide
  have hdescent : baseEnd_5429028 < baseStart_5429028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429045 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_5429045 : Nat := 118140960795 + 5429045 * 2 ^ 59
def prefixEnd_5429045 : Nat := 4983230072969 + 3 ^ 40 * 5429045 * 2
def baseEnd_5429045 : Nat := 2787709579888816570169783

theorem tailTrace_5429045 : CollatzResearch.WordTrace tailWord_5429045 prefixEnd_5429045 2787709579888816570169783 := by
  unfold tailWord_5429045
  simp only [CollatzResearch.WordTrace]
  refine ⟨198013538616504646912384589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132009025744336431274923059 198013538616504646912384589)
  ·
    refine ⟨74255076981189242592144221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198013538616504646912384589 74255076981189242592144221)
    ·
      refine ⟨27845653867945965972054083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74255076981189242592144221 27845653867945965972054083)
      ·
        refine ⟨41768480801918948958081125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27845653867945965972054083 41768480801918948958081125)
        ·
          refine ⟨7831590150359802929640211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41768480801918948958081125 7831590150359802929640211)
          ·
            refine ⟨11747385225539704394460317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831590150359802929640211 11747385225539704394460317)
            ·
              refine ⟨4405269459577389147922619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11747385225539704394460317 4405269459577389147922619)
              ·
                refine ⟨6607904189366083721883929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405269459577389147922619 6607904189366083721883929)
                ·
                  refine ⟨4955928142024562791412947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607904189366083721883929 4955928142024562791412947)
                  ·
                    refine ⟨7433892213036844187119421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4955928142024562791412947 7433892213036844187119421)
                    ·
                      refine ⟨2787709579888816570169783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7433892213036844187119421 2787709579888816570169783)
                      ·
                        rfl

theorem cell23_5429045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_5429045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429045 prefixEnd_5429045 := by exact prefixLift 5429045
  have htrace : WordTrace (prefixWord ++ tailWord_5429045) baseStart_5429045 baseEnd_5429045 := by
    simpa [prefixWord, tailWord_5429045, baseEnd_5429045] using wordTrace_append hprefix tailTrace_5429045
  have hstable : (prefixWord ++ tailWord_5429045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429045).length < 2 ^ (prefixWord ++ tailWord_5429045).sum := by decide
  have hdescent : baseEnd_5429045 < baseStart_5429045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429047 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 4]
def baseStart_5429047 : Nat := 118140960795 + 5429047 * 2 ^ 59
def prefixEnd_5429047 : Nat := 4983230072969 + 3 ^ 40 * 5429047 * 2
def baseEnd_5429047 : Nat := 2787710606850125562344773

theorem tailTrace_5429047 : CollatzResearch.WordTrace tailWord_5429047 prefixEnd_5429047 2787710606850125562344773 := by
  unfold tailWord_5429047
  simp only [CollatzResearch.WordTrace]
  refine ⟨198013611562497401253957395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132009074374998267502638263 198013611562497401253957395)
  ·
    refine ⟨297020417343746101880936093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198013611562497401253957395 297020417343746101880936093)
    ·
      refine ⟨111382656503904788205351035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297020417343746101880936093 111382656503904788205351035)
      ·
        refine ⟨167073984755857182308026553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111382656503904788205351035 167073984755857182308026553)
        ·
          refine ⟨125305488566892886731019915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167073984755857182308026553 125305488566892886731019915)
          ·
            refine ⟨187958232850339330096529873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125305488566892886731019915 187958232850339330096529873)
            ·
              refine ⟨140968674637754497572397405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187958232850339330096529873 140968674637754497572397405)
              ·
                refine ⟨52863252989157936589649027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 140968674637754497572397405 52863252989157936589649027)
                ·
                  refine ⟨79294879483736904884473541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52863252989157936589649027 79294879483736904884473541)
                  ·
                    refine ⟨14867789903200669665838789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79294879483736904884473541 14867789903200669665838789)
                    ·
                      refine ⟨2787710606850125562344773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14867789903200669665838789 2787710606850125562344773)
                      ·
                        rfl

theorem cell23_5429047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 1, 4, 4].length) (baseStart_5429047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429047 prefixEnd_5429047 := by exact prefixLift 5429047
  have htrace : WordTrace (prefixWord ++ tailWord_5429047) baseStart_5429047 baseEnd_5429047 := by
    simpa [prefixWord, tailWord_5429047, baseEnd_5429047] using wordTrace_append hprefix tailTrace_5429047
  have hstable : (prefixWord ++ tailWord_5429047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429047).length < 2 ^ (prefixWord ++ tailWord_5429047).sum := by decide
  have hdescent : baseEnd_5429047 < baseStart_5429047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429091 : List Nat := [1, 1, 1, 5, 4, 2, 1, 1, 7]
def baseStart_5429091 : Nat := 118140960795 + 5429091 * 2 ^ 59
def prefixEnd_5429091 : Nat := 4983230072969 + 3 ^ 40 * 5429091 * 2
def baseEnd_5429091 : Nat := 309748133333213710021619

theorem tailTrace_5429091 : CollatzResearch.WordTrace tailWord_5429091 prefixEnd_5429091 309748133333213710021619 := by
  unfold tailWord_5429091
  simp only [CollatzResearch.WordTrace]
  refine ⟨198015216374337996768559127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132010144249558664512372751 198015216374337996768559127)
  ·
    refine ⟨297022824561506995152838691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198015216374337996768559127 297022824561506995152838691)
    ·
      refine ⟨445534236842260492729258037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297022824561506995152838691 445534236842260492729258037)
      ·
        refine ⟨41768834703961921193367941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 445534236842260492729258037 41768834703961921193367941)
        ·
          refine ⟨7831656506992860223756489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41768834703961921193367941 7831656506992860223756489)
          ·
            refine ⟨5873742380244645167817367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7831656506992860223756489 5873742380244645167817367)
            ·
              refine ⟨8810613570366967751726051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873742380244645167817367 8810613570366967751726051)
              ·
                refine ⟨13215920355550451627589077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810613570366967751726051 13215920355550451627589077)
                ·
                  refine ⟨309748133333213710021619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13215920355550451627589077 309748133333213710021619)
                  ·
                    rfl

theorem cell23_5429091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 2, 1, 1, 7].length) (baseStart_5429091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429091 prefixEnd_5429091 := by exact prefixLift 5429091
  have htrace : WordTrace (prefixWord ++ tailWord_5429091) baseStart_5429091 baseEnd_5429091 := by
    simpa [prefixWord, tailWord_5429091, baseEnd_5429091] using wordTrace_append hprefix tailTrace_5429091
  have hstable : (prefixWord ++ tailWord_5429091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429091).length < 2 ^ (prefixWord ++ tailWord_5429091).sum := by decide
  have hdescent : baseEnd_5429091 < baseStart_5429091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429102 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2]
def baseStart_5429102 : Nat := 118140960795 + 5429102 * 2 ^ 59
def prefixEnd_5429102 : Nat := 4983230072969 + 3 ^ 40 * 5429102 * 2
def baseEnd_5429102 : Nat := 2787738848286122847157021

theorem tailTrace_5429102 : CollatzResearch.WordTrace tailWord_5429102 prefixEnd_5429102 2787738848286122847157021 := by
  unfold tailWord_5429102
  simp only [CollatzResearch.WordTrace]
  refine ⟨24751952197162268205901195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132010411718198763764806373 24751952197162268205901195)
  ·
    refine ⟨37127928295743402308851793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24751952197162268205901195 37127928295743402308851793)
    ·
      refine ⟨27845946221807551731638845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37127928295743402308851793 27845946221807551731638845)
      ·
        refine ⟨10442229833177831899364567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27845946221807551731638845 10442229833177831899364567)
        ·
          refine ⟨15663344749766747849046851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10442229833177831899364567 15663344749766747849046851)
          ·
            refine ⟨23495017124650121773570277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15663344749766747849046851 23495017124650121773570277)
            ·
              refine ⟨4405315710871897832544427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23495017124650121773570277 4405315710871897832544427)
              ·
                refine ⟨6607973566307846748816641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405315710871897832544427 6607973566307846748816641)
                ·
                  refine ⟨4955980174730885061612481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6607973566307846748816641 4955980174730885061612481)
                  ·
                    refine ⟨3716985131048163796209361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4955980174730885061612481 3716985131048163796209361)
                    ·
                      refine ⟨2787738848286122847157021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3716985131048163796209361 2787738848286122847157021)
                      ·
                        rfl

theorem cell23_5429102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_5429102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429102 prefixEnd_5429102 := by exact prefixLift 5429102
  have htrace : WordTrace (prefixWord ++ tailWord_5429102) baseStart_5429102 baseEnd_5429102 := by
    simpa [prefixWord, tailWord_5429102, baseEnd_5429102] using wordTrace_append hprefix tailTrace_5429102
  have hstable : (prefixWord ++ tailWord_5429102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429102).length < 2 ^ (prefixWord ++ tailWord_5429102).sum := by decide
  have hdescent : baseEnd_5429102 < baseStart_5429102 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429124 : List Nat := [2, 3, 2, 1, 1, 1, 2, 3, 1, 3, 4]
def baseStart_5429124 : Nat := 118140960795 + 5429124 * 2 ^ 59
def prefixEnd_5429124 : Nat := 4983230072969 + 3 ^ 40 * 5429124 * 2
def baseEnd_5429124 : Nat := 2787750144860521761081919

theorem tailTrace_5429124 : CollatzResearch.WordTrace tailWord_5429124 prefixEnd_5429124 2787750144860521761081919 := by
  unfold tailWord_5429124
  simp only [CollatzResearch.WordTrace]
  refine ⟨99008209991609221702255213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132010946655478962269673617 99008209991609221702255213)
  ·
    refine ⟨37128078746853458138345705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99008209991609221702255213 37128078746853458138345705)
    ·
      refine ⟨27846059060140093603759279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37128078746853458138345705 27846059060140093603759279)
      ·
        refine ⟨41769088590210140405638919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27846059060140093603759279 41769088590210140405638919)
        ·
          refine ⟨62653632885315210608458379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41769088590210140405638919 62653632885315210608458379)
          ·
            refine ⟨93980449327972815912687569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62653632885315210608458379 93980449327972815912687569)
            ·
              refine ⟨70485336995979611934515677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93980449327972815912687569 70485336995979611934515677)
              ·
                refine ⟨26432001373492354475443379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70485336995979611934515677 26432001373492354475443379)
                ·
                  refine ⟨39648002060238531713165069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26432001373492354475443379 39648002060238531713165069)
                  ·
                    refine ⟨14868000772589449392436901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39648002060238531713165069 14868000772589449392436901)
                    ·
                      refine ⟨2787750144860521761081919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14868000772589449392436901 2787750144860521761081919)
                      ·
                        rfl

theorem cell23_5429124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_5429124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429124 prefixEnd_5429124 := by exact prefixLift 5429124
  have htrace : WordTrace (prefixWord ++ tailWord_5429124) baseStart_5429124 baseEnd_5429124 := by
    simpa [prefixWord, tailWord_5429124, baseEnd_5429124] using wordTrace_append hprefix tailTrace_5429124
  have hstable : (prefixWord ++ tailWord_5429124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429124).length < 2 ^ (prefixWord ++ tailWord_5429124).sum := by decide
  have hdescent : baseEnd_5429124 < baseStart_5429124 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429141 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_5429141 : Nat := 118140960795 + 5429141 * 2 ^ 59
def prefixEnd_5429141 : Nat := 4983230072969 + 3 ^ 40 * 5429141 * 2
def baseEnd_5429141 : Nat := 2787758874031648194569341

theorem tailTrace_5429141 : CollatzResearch.WordTrace tailWord_5429141 prefixEnd_5429141 2787758874031648194569341 := by
  unfold tailWord_5429141
  simp only [CollatzResearch.WordTrace]
  refine ⟨198017040024156855307879277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132011360016104570205252851 198017040024156855307879277)
  ·
    refine ⟨74256390009058820740454729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198017040024156855307879277 74256390009058820740454729)
    ·
      refine ⟨55692292506794115555341047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74256390009058820740454729 55692292506794115555341047)
      ·
        refine ⟨83538438760191173333011571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55692292506794115555341047 83538438760191173333011571)
        ·
          refine ⟨125307658140286759999517357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83538438760191173333011571 125307658140286759999517357)
          ·
            refine ⟨46990371802607534999819009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125307658140286759999517357 46990371802607534999819009)
            ·
              refine ⟨35242778851955651249864257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46990371802607534999819009 35242778851955651249864257)
              ·
                refine ⟨26432084138966738437398193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35242778851955651249864257 26432084138966738437398193)
                ·
                  refine ⟨19824063104225053828048645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26432084138966738437398193 19824063104225053828048645)
                  ·
                    refine ⟨3717011832042197592759121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19824063104225053828048645 3717011832042197592759121)
                    ·
                      refine ⟨2787758874031648194569341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717011832042197592759121 2787758874031648194569341)
                      ·
                        rfl

theorem cell23_5429141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_5429141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429141 prefixEnd_5429141 := by exact prefixLift 5429141
  have htrace : WordTrace (prefixWord ++ tailWord_5429141) baseStart_5429141 baseEnd_5429141 := by
    simpa [prefixWord, tailWord_5429141, baseEnd_5429141] using wordTrace_append hprefix tailTrace_5429141
  have hstable : (prefixWord ++ tailWord_5429141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429141).length < 2 ^ (prefixWord ++ tailWord_5429141).sum := by decide
  have hdescent : baseEnd_5429141 < baseStart_5429141 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429142 : List Nat := [5, 3, 1, 1, 2, 1, 1, 4, 5]
def baseStart_5429142 : Nat := 118140960795 + 5429142 * 2 ^ 59
def prefixEnd_5429142 : Nat := 4983230072969 + 3 ^ 40 * 5429142 * 2
def baseEnd_5429142 : Nat := 309751043056922521184093

theorem tailTrace_5429142 : CollatzResearch.WordTrace tailWord_5429142 prefixEnd_5429142 309751043056922521184093 := by
  unfold tailWord_5429142
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376067281072077029916605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132011384331435488319110453 12376067281072077029916605)
  ·
    refine ⟨4641025230402028886218727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12376067281072077029916605 4641025230402028886218727)
    ·
      refine ⟨6961537845603043329328091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4641025230402028886218727 6961537845603043329328091)
      ·
        refine ⟨10442306768404564993992137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961537845603043329328091 10442306768404564993992137)
        ·
          refine ⟨7831730076303423745494103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10442306768404564993992137 7831730076303423745494103)
          ·
            refine ⟨11747595114455135618241155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831730076303423745494103 11747595114455135618241155)
            ·
              refine ⟨17621392671682703427361733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11747595114455135618241155 17621392671682703427361733)
              ·
                refine ⟨3304011125940506892630325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17621392671682703427361733 3304011125940506892630325)
                ·
                  refine ⟨309751043056922521184093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304011125940506892630325 309751043056922521184093)
                  ·
                    rfl

theorem cell23_5429142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_5429142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429142 prefixEnd_5429142 := by exact prefixLift 5429142
  have htrace : WordTrace (prefixWord ++ tailWord_5429142) baseStart_5429142 baseEnd_5429142 := by
    simpa [prefixWord, tailWord_5429142, baseEnd_5429142] using wordTrace_append hprefix tailTrace_5429142
  have hstable : (prefixWord ++ tailWord_5429142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429142).length < 2 ^ (prefixWord ++ tailWord_5429142).sum := by decide
  have hdescent : baseEnd_5429142 < baseStart_5429142 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429172 : List Nat := [2, 5, 2, 1, 3, 1, 1, 1, 2, 5]
def baseStart_5429172 : Nat := 118140960795 + 5429172 * 2 ^ 59
def prefixEnd_5429172 : Nat := 4983230072969 + 3 ^ 40 * 5429172 * 2
def baseEnd_5429172 : Nat := 929258263977312524427233

theorem tailTrace_5429172 : CollatzResearch.WordTrace tailWord_5429172 prefixEnd_5429172 929258263977312524427233 := by
  unfold tailWord_5429172
  simp only [CollatzResearch.WordTrace]
  refine ⟨99009085343522273801128885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132012113791363031734838513 99009085343522273801128885)
  ·
    refine ⟨9282101750955213168855833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99009085343522273801128885 9282101750955213168855833)
    ·
      refine ⟨6961576313216409876641875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9282101750955213168855833 6961576313216409876641875)
      ·
        refine ⟨10442364469824614814962813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6961576313216409876641875 10442364469824614814962813)
        ·
          refine ⟨3915886676184230555611055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10442364469824614814962813 3915886676184230555611055)
          ·
            refine ⟨5873830014276345833416583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3915886676184230555611055 5873830014276345833416583)
            ·
              refine ⟨8810745021414518750124875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873830014276345833416583 8810745021414518750124875)
              ·
                refine ⟨13216117532121778125187313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810745021414518750124875 13216117532121778125187313)
                ·
                  refine ⟨9912088149091333593890485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13216117532121778125187313 9912088149091333593890485)
                  ·
                    refine ⟨929258263977312524427233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9912088149091333593890485 929258263977312524427233)
                    ·
                      rfl

theorem cell23_5429172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 1, 1, 2, 5].length) (baseStart_5429172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429172 prefixEnd_5429172 := by exact prefixLift 5429172
  have htrace : WordTrace (prefixWord ++ tailWord_5429172) baseStart_5429172 baseEnd_5429172 := by
    simpa [prefixWord, tailWord_5429172, baseEnd_5429172] using wordTrace_append hprefix tailTrace_5429172
  have hstable : (prefixWord ++ tailWord_5429172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429172).length < 2 ^ (prefixWord ++ tailWord_5429172).sum := by decide
  have hdescent : baseEnd_5429172 < baseStart_5429172 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429191 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 3]
def baseStart_5429191 : Nat := 118140960795 + 5429191 * 2 ^ 59
def prefixEnd_5429191 : Nat := 4983230072969 + 3 ^ 40 * 5429191 * 2
def baseEnd_5429191 : Nat := 2787784548064372998944111

theorem tailTrace_5429191 : CollatzResearch.WordTrace tailWord_5429191 prefixEnd_5429191 2787784548064372998944111 := by
  unfold tailWord_5429191
  simp only [CollatzResearch.WordTrace]
  refine ⟨198018863673975713847199427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132012575782650475898132951 198018863673975713847199427)
  ·
    refine ⟨297028295510963570770799141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198018863673975713847199427 297028295510963570770799141)
    ·
      refine ⟨55692805408305669519524839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297028295510963570770799141 55692805408305669519524839)
      ·
        refine ⟨83539208112458504279287259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55692805408305669519524839 83539208112458504279287259)
        ·
          refine ⟨125308812168687756418930889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83539208112458504279287259 125308812168687756418930889)
          ·
            refine ⟨93981609126515817314198167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125308812168687756418930889 93981609126515817314198167)
            ·
              refine ⟨140972413689773725971297251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93981609126515817314198167 140972413689773725971297251)
              ·
                refine ⟨211458620534660588956945877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140972413689773725971297251 211458620534660588956945877)
                ·
                  refine ⟨4956061418781107553678419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 211458620534660588956945877 4956061418781107553678419)
                  ·
                    refine ⟨7434092128171661330517629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4956061418781107553678419 7434092128171661330517629)
                    ·
                      refine ⟨2787784548064372998944111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434092128171661330517629 2787784548064372998944111)
                      ·
                        rfl

theorem cell23_5429191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 7, 1, 3].length) (baseStart_5429191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429191 prefixEnd_5429191 := by exact prefixLift 5429191
  have htrace : WordTrace (prefixWord ++ tailWord_5429191) baseStart_5429191 baseEnd_5429191 := by
    simpa [prefixWord, tailWord_5429191, baseEnd_5429191] using wordTrace_append hprefix tailTrace_5429191
  have hstable : (prefixWord ++ tailWord_5429191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429191).length < 2 ^ (prefixWord ++ tailWord_5429191).sum := by decide
  have hdescent : baseEnd_5429191 < baseStart_5429191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429208 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 3, 1, 3]
def baseStart_5429208 : Nat := 118140960795 + 5429208 * 2 ^ 59
def prefixEnd_5429208 : Nat := 4983230072969 + 3 ^ 40 * 5429208 * 2
def baseEnd_5429208 : Nat := 2787793277235499432431533

theorem tailTrace_5429208 : CollatzResearch.WordTrace tailWord_5429208 prefixEnd_5429208 2787793277235499432431533 := by
  unfold tailWord_5429208
  simp only [CollatzResearch.WordTrace]
  refine ⟨99009741857457062875284139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132012989143276083833712185 99009741857457062875284139)
  ·
    refine ⟨148514612786185594312926209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99009741857457062875284139 148514612786185594312926209)
    ·
      refine ⟨111385959589639195734694657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148514612786185594312926209 111385959589639195734694657)
      ·
        refine ⟨83539469692229396801020993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111385959589639195734694657 83539469692229396801020993)
        ·
          refine ⟨62654602269172047600765745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83539469692229396801020993 62654602269172047600765745)
          ·
            refine ⟨46990951701879035700574309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62654602269172047600765745 46990951701879035700574309)
            ·
              refine ⟨8810803444102319193857683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 46990951701879035700574309 8810803444102319193857683)
              ·
                refine ⟨13216205166153478790786525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8810803444102319193857683 13216205166153478790786525)
                ·
                  refine ⟨4956076937307554546544947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13216205166153478790786525 4956076937307554546544947)
                  ·
                    refine ⟨7434115405961331819817421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4956076937307554546544947 7434115405961331819817421)
                    ·
                      refine ⟨2787793277235499432431533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434115405961331819817421 2787793277235499432431533)
                      ·
                        rfl

theorem cell23_5429208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 3, 1, 3].length) (baseStart_5429208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429208 prefixEnd_5429208 := by exact prefixLift 5429208
  have htrace : WordTrace (prefixWord ++ tailWord_5429208) baseStart_5429208 baseEnd_5429208 := by
    simpa [prefixWord, tailWord_5429208, baseEnd_5429208] using wordTrace_append hprefix tailTrace_5429208
  have hstable : (prefixWord ++ tailWord_5429208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429208).length < 2 ^ (prefixWord ++ tailWord_5429208).sum := by decide
  have hdescent : baseEnd_5429208 < baseStart_5429208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429231 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 2, 6, 2]
def baseStart_5429231 : Nat := 118140960795 + 5429231 * 2 ^ 59
def prefixEnd_5429231 : Nat := 4983230072969 + 3 ^ 40 * 5429231 * 2
def baseEnd_5429231 : Nat := 2787805087290552842443927

theorem tailTrace_5429231 : CollatzResearch.WordTrace tailWord_5429231 prefixEnd_5429231 2787805087290552842443927 := by
  unfold tailWord_5429231
  simp only [CollatzResearch.WordTrace]
  refine ⟨198020322593830800678655547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132013548395887200452437031 198020322593830800678655547)
  ·
    refine ⟨297030483890746201017983321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198020322593830800678655547 297030483890746201017983321)
    ·
      refine ⟨222772862918059650763487491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297030483890746201017983321 222772862918059650763487491)
      ·
        refine ⟨334159294377089476145231237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222772862918059650763487491 334159294377089476145231237)
        ·
          refine ⟨62654867695704276777230857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334159294377089476145231237 62654867695704276777230857)
          ·
            refine ⟨46991150771778207582923143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62654867695704276777230857 46991150771778207582923143)
            ·
              refine ⟨70486726157667311374384715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46991150771778207582923143 70486726157667311374384715)
              ·
                refine ⟨105730089236500967061577073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70486726157667311374384715 105730089236500967061577073)
                ·
                  refine ⟨79297566927375725296182805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105730089236500967061577073 79297566927375725296182805)
                  ·
                    refine ⟨3717073449720737123258569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79297566927375725296182805 3717073449720737123258569)
                    ·
                      refine ⟨2787805087290552842443927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717073449720737123258569 2787805087290552842443927)
                      ·
                        rfl

theorem cell23_5429231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 6, 2].length) (baseStart_5429231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429231 prefixEnd_5429231 := by exact prefixLift 5429231
  have htrace : WordTrace (prefixWord ++ tailWord_5429231) baseStart_5429231 baseEnd_5429231 := by
    simpa [prefixWord, tailWord_5429231, baseEnd_5429231] using wordTrace_append hprefix tailTrace_5429231
  have hstable : (prefixWord ++ tailWord_5429231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429231).length < 2 ^ (prefixWord ++ tailWord_5429231).sum := by decide
  have hdescent : baseEnd_5429231 < baseStart_5429231 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429241 : List Nat := [1, 2, 1, 3, 1, 4, 1, 2, 4, 4]
def baseStart_5429241 : Nat := 118140960795 + 5429241 * 2 ^ 59
def prefixEnd_5429241 : Nat := 4983230072969 + 3 ^ 40 * 5429241 * 2
def baseEnd_5429241 : Nat := 929270074032365934439627

theorem tailTrace_5429241 : CollatzResearch.WordTrace tailWord_5429241 prefixEnd_5429241 929270074032365934439627 := by
  unfold tailWord_5429241
  simp only [CollatzResearch.WordTrace]
  refine ⟨198020687323794572386519577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132013791549196381591013051 198020687323794572386519577)
  ·
    refine ⟨148515515492845929289889683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198020687323794572386519577 148515515492845929289889683)
    ·
      refine ⟨222773273239268893934834525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148515515492845929289889683 222773273239268893934834525)
      ·
        refine ⟨83539977464725835225562947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222773273239268893934834525 83539977464725835225562947)
        ·
          refine ⟨125309966197088752838344421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83539977464725835225562947 125309966197088752838344421)
          ·
            refine ⟨23495618661954141157189579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125309966197088752838344421 23495618661954141157189579)
            ·
              refine ⟨35243427992931211735784369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23495618661954141157189579 35243427992931211735784369)
              ·
                refine ⟨26432570994698408801838277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35243427992931211735784369 26432570994698408801838277)
                ·
                  refine ⟨4956107061505951650344677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26432570994698408801838277 4956107061505951650344677)
                  ·
                    refine ⟨929270074032365934439627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956107061505951650344677 929270074032365934439627)
                    ·
                      rfl

theorem cell23_5429241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 2, 4, 4].length) (baseStart_5429241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429241 prefixEnd_5429241 := by exact prefixLift 5429241
  have htrace : WordTrace (prefixWord ++ tailWord_5429241) baseStart_5429241 baseEnd_5429241 := by
    simpa [prefixWord, tailWord_5429241, baseEnd_5429241] using wordTrace_append hprefix tailTrace_5429241
  have hstable : (prefixWord ++ tailWord_5429241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429241).length < 2 ^ (prefixWord ++ tailWord_5429241).sum := by decide
  have hdescent : baseEnd_5429241 < baseStart_5429241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429252 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_5429252 : Nat := 118140960795 + 5429252 * 2 ^ 59
def prefixEnd_5429252 : Nat := 4983230072969 + 3 ^ 40 * 5429252 * 2
def baseEnd_5429252 : Nat := 2787815870384297260281331

theorem tailTrace_5429252 : CollatzResearch.WordTrace tailWord_5429252 prefixEnd_5429252 2787815870384297260281331 := by
  unfold tailWord_5429252
  simp only [CollatzResearch.WordTrace]
  refine ⟨99010544263377360632585005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132014059017836480843446673 99010544263377360632585005)
  ·
    refine ⟨37128954098766510237219377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99010544263377360632585005 37128954098766510237219377)
    ·
      refine ⟨27846715574074882677914533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37128954098766510237219377 27846715574074882677914533)
      ·
        refine ⟨5221259170139040502108975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27846715574074882677914533 5221259170139040502108975)
        ·
          refine ⟨7831888755208560753163463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221259170139040502108975 7831888755208560753163463)
          ·
            refine ⟨11747833132812841129745195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7831888755208560753163463 11747833132812841129745195)
            ·
              refine ⟨17621749699219261694617793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11747833132812841129745195 17621749699219261694617793)
              ·
                refine ⟨13216312274414446270963345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17621749699219261694617793 13216312274414446270963345)
                ·
                  refine ⟨9912234205810834703222509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13216312274414446270963345 9912234205810834703222509)
                  ·
                    refine ⟨3717087827179063013708441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9912234205810834703222509 3717087827179063013708441)
                    ·
                      refine ⟨2787815870384297260281331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717087827179063013708441 2787815870384297260281331)
                      ·
                        rfl

theorem cell23_5429252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_5429252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429252 prefixEnd_5429252 := by exact prefixLift 5429252
  have htrace : WordTrace (prefixWord ++ tailWord_5429252) baseStart_5429252 baseEnd_5429252 := by
    simpa [prefixWord, tailWord_5429252, baseEnd_5429252] using wordTrace_append hprefix tailTrace_5429252
  have hstable : (prefixWord ++ tailWord_5429252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429252).length < 2 ^ (prefixWord ++ tailWord_5429252).sum := by decide
  have hdescent : baseEnd_5429252 < baseStart_5429252 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429285 : List Nat := [1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 3]
def baseStart_5429285 : Nat := 118140960795 + 5429285 * 2 ^ 59
def prefixEnd_5429285 : Nat := 4983230072969 + 3 ^ 40 * 5429285 * 2
def baseEnd_5429285 : Nat := 2787832815245895631168679

theorem tailTrace_5429285 : CollatzResearch.WordTrace tailWord_5429285 prefixEnd_5429285 2787832815245895631168679 := by
  unfold tailWord_5429285
  simp only [CollatzResearch.WordTrace]
  refine ⟨198022292135635167901121309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132014861423756778600747539 198022292135635167901121309)
  ·
    refine ⟨74258359550863187962920491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198022292135635167901121309 74258359550863187962920491)
    ·
      refine ⟨111387539326294781944380737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74258359550863187962920491 111387539326294781944380737)
      ·
        refine ⟨83540654494721086458285553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111387539326294781944380737 83540654494721086458285553)
        ·
          refine ⟨62655490871040814843714165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83540654494721086458285553 62655490871040814843714165)
          ·
            refine ⟨5873952269160076391598203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62655490871040814843714165 5873952269160076391598203)
            ·
              refine ⟨8810928403740114587397305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5873952269160076391598203 8810928403740114587397305)
              ·
                refine ⟨6608196302805085940547979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8810928403740114587397305 6608196302805085940547979)
                ·
                  refine ⟨9912294454207628910821969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608196302805085940547979 9912294454207628910821969)
                  ·
                    refine ⟨7434220840655721683116477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9912294454207628910821969 7434220840655721683116477)
                    ·
                      refine ⟨2787832815245895631168679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434220840655721683116477 2787832815245895631168679)
                      ·
                        rfl

theorem cell23_5429285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 1, 2, 1, 2, 3].length) (baseStart_5429285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429285 prefixEnd_5429285 := by exact prefixLift 5429285
  have htrace : WordTrace (prefixWord ++ tailWord_5429285) baseStart_5429285 baseEnd_5429285 := by
    simpa [prefixWord, tailWord_5429285, baseEnd_5429285] using wordTrace_append hprefix tailTrace_5429285
  have hstable : (prefixWord ++ tailWord_5429285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429285).length < 2 ^ (prefixWord ++ tailWord_5429285).sum := by decide
  have hdescent : baseEnd_5429285 < baseStart_5429285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429298 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3]
def baseStart_5429298 : Nat := 118140960795 + 5429298 * 2 ^ 59
def prefixEnd_5429298 : Nat := 4983230072969 + 3 ^ 40 * 5429298 * 2
def baseEnd_5429298 : Nat := 2787839490494404080306119

theorem tailTrace_5429298 : CollatzResearch.WordTrace tailWord_5429298 prefixEnd_5429298 2787839490494404080306119 := by
  unfold tailWord_5429298
  simp only [CollatzResearch.WordTrace]
  refine ⟨49505691571147017780336137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132015177523058714080896365 49505691571147017780336137)
  ·
    refine ⟨37129268678360263335252103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49505691571147017780336137 37129268678360263335252103)
    ·
      refine ⟨55693903017540395002878155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37129268678360263335252103 55693903017540395002878155)
      ·
        refine ⟨83540854526310592504317233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55693903017540395002878155 83540854526310592504317233)
        ·
          refine ⟨62655640894732944378237925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83540854526310592504317233 62655640894732944378237925)
          ·
            refine ⟨11747932667762427070919611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62655640894732944378237925 11747932667762427070919611)
            ·
              refine ⟨17621899001643640606379417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11747932667762427070919611 17621899001643640606379417)
              ·
                refine ⟨13216424251232730454784563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17621899001643640606379417 13216424251232730454784563)
                ·
                  refine ⟨19824636376849095682176845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13216424251232730454784563 19824636376849095682176845)
                  ·
                    refine ⟨7434238641318410880816317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19824636376849095682176845 7434238641318410880816317)
                    ·
                      refine ⟨2787839490494404080306119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434238641318410880816317 2787839490494404080306119)
                      ·
                        rfl

theorem cell23_5429298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 1, 3, 3].length) (baseStart_5429298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429298 prefixEnd_5429298 := by exact prefixLift 5429298
  have htrace : WordTrace (prefixWord ++ tailWord_5429298) baseStart_5429298 baseEnd_5429298 := by
    simpa [prefixWord, tailWord_5429298, baseEnd_5429298] using wordTrace_append hprefix tailTrace_5429298
  have hstable : (prefixWord ++ tailWord_5429298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429298).length < 2 ^ (prefixWord ++ tailWord_5429298).sum := by decide
  have hdescent : baseEnd_5429298 < baseStart_5429298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429302 : List Nat := [5, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_5429302 : Nat := 118140960795 + 5429302 * 2 ^ 59
def prefixEnd_5429302 : Nat := 4983230072969 + 3 ^ 40 * 5429302 * 2
def baseEnd_5429302 : Nat := 2787841544417022064656101

theorem tailTrace_5429302 : CollatzResearch.WordTrace tailWord_5429302 prefixEnd_5429302 2787841544417022064656101 := by
  unfold tailWord_5429302
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376432011035848737780635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132015274784382386536326773 12376432011035848737780635)
  ·
    refine ⟨18564648016553773106670953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12376432011035848737780635 18564648016553773106670953)
    ·
      refine ⟨13923486012415329830003215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18564648016553773106670953 13923486012415329830003215)
      ·
        refine ⟨20885229018622994745004823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13923486012415329830003215 20885229018622994745004823)
        ·
          refine ⟨31327843527934492117507235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20885229018622994745004823 31327843527934492117507235)
          ·
            refine ⟨46991765291901738176260853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31327843527934492117507235 46991765291901738176260853)
            ·
              refine ⟨4405477996115787954024455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 46991765291901738176260853 4405477996115787954024455)
              ·
                refine ⟨6608216994173681931036683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405477996115787954024455 6608216994173681931036683)
                ·
                  refine ⟨9912325491260522896555025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608216994173681931036683 9912325491260522896555025)
                  ·
                    refine ⟨7434244118445392172416269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9912325491260522896555025 7434244118445392172416269)
                    ·
                      refine ⟨2787841544417022064656101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434244118445392172416269 2787841544417022064656101)
                      ·
                        rfl

theorem cell23_5429302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_5429302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429302 prefixEnd_5429302 := by exact prefixLift 5429302
  have htrace : WordTrace (prefixWord ++ tailWord_5429302) baseStart_5429302 baseEnd_5429302 := by
    simpa [prefixWord, tailWord_5429302, baseEnd_5429302] using wordTrace_append hprefix tailTrace_5429302
  have hstable : (prefixWord ++ tailWord_5429302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429302).length < 2 ^ (prefixWord ++ tailWord_5429302).sum := by decide
  have hdescent : baseEnd_5429302 < baseStart_5429302 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429318 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 1, 9]
def baseStart_5429318 : Nat := 118140960795 + 5429318 * 2 ^ 59
def prefixEnd_5429318 : Nat := 4983230072969 + 3 ^ 40 * 5429318 * 2
def baseEnd_5429318 : Nat := 929283253369164667352009

theorem tailTrace_5429318 : CollatzResearch.WordTrace tailWord_5429318 prefixEnd_5429318 929283253369164667352009 := by
  unfold tailWord_5429318
  simp only [CollatzResearch.WordTrace]
  refine ⟨6188234242016112954283519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 132015663829677076358048405 6188234242016112954283519)
  ·
    refine ⟨9282351363024169431425279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6188234242016112954283519 9282351363024169431425279)
    ·
      refine ⟨13923527044536254147137919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9282351363024169431425279 13923527044536254147137919)
      ·
        refine ⟨20885290566804381220706879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13923527044536254147137919 20885290566804381220706879)
        ·
          refine ⟨31327935850206571831060319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20885290566804381220706879 31327935850206571831060319)
          ·
            refine ⟨46991903775309857746590479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31327935850206571831060319 46991903775309857746590479)
            ·
              refine ⟨70487855662964786619885719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46991903775309857746590479 70487855662964786619885719)
              ·
                refine ⟨105731783494447179929828579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70487855662964786619885719 105731783494447179929828579)
                ·
                  refine ⟨158597675241670769894742869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105731783494447179929828579 158597675241670769894742869)
                  ·
                    refine ⟨929283253369164667352009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 158597675241670769894742869 929283253369164667352009)
                    ·
                      rfl

theorem cell23_5429318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_5429318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429318 prefixEnd_5429318 := by exact prefixLift 5429318
  have htrace : WordTrace (prefixWord ++ tailWord_5429318) baseStart_5429318 baseEnd_5429318 := by
    simpa [prefixWord, tailWord_5429318, baseEnd_5429318] using wordTrace_append hprefix tailTrace_5429318
  have hstable : (prefixWord ++ tailWord_5429318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429318).length < 2 ^ (prefixWord ++ tailWord_5429318).sum := by decide
  have hdescent : baseEnd_5429318 < baseStart_5429318 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429325 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 5, 3, 2]
def baseStart_5429325 : Nat := 118140960795 + 5429325 * 2 ^ 59
def prefixEnd_5429325 : Nat := 4983230072969 + 3 ^ 40 * 5429325 * 2
def baseEnd_5429325 : Nat := 2787853354472075474668495

theorem tailTrace_5429325 : CollatzResearch.WordTrace tailWord_5429325 prefixEnd_5429325 2787853354472075474668495 := by
  unfold tailWord_5429325
  simp only [CollatzResearch.WordTrace]
  refine ⟨198023751055490254732577429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132015834036993503155051619 198023751055490254732577429)
  ·
    refine ⟨9282363330726105690589567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198023751055490254732577429 9282363330726105690589567)
    ·
      refine ⟨13923544996089158535884351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9282363330726105690589567 13923544996089158535884351)
      ·
        refine ⟨20885317494133737803826527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13923544996089158535884351 20885317494133737803826527)
        ·
          refine ⟨31327976241200606705739791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20885317494133737803826527 31327976241200606705739791)
          ·
            refine ⟨46991964361800910058609687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31327976241200606705739791 46991964361800910058609687)
            ·
              refine ⟨70487946542701365087914531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46991964361800910058609687 70487946542701365087914531)
              ·
                refine ⟨105731919814052047631871797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70487946542701365087914531 105731919814052047631871797)
                ·
                  refine ⟨9912367482567379465487981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105731919814052047631871797 9912367482567379465487981)
                  ·
                    refine ⟨3717137805962767299557993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9912367482567379465487981 3717137805962767299557993)
                    ·
                      refine ⟨2787853354472075474668495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717137805962767299557993 2787853354472075474668495)
                      ·
                        rfl

theorem cell23_5429325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 3, 2].length) (baseStart_5429325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429325 prefixEnd_5429325 := by exact prefixLift 5429325
  have htrace : WordTrace (prefixWord ++ tailWord_5429325) baseStart_5429325 baseEnd_5429325 := by
    simpa [prefixWord, tailWord_5429325, baseEnd_5429325] using wordTrace_append hprefix tailTrace_5429325
  have hstable : (prefixWord ++ tailWord_5429325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429325).length < 2 ^ (prefixWord ++ tailWord_5429325).sum := by decide
  have hdescent : baseEnd_5429325 < baseStart_5429325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429351 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 4]
def baseStart_5429351 : Nat := 118140960795 + 5429351 * 2 ^ 59
def prefixEnd_5429351 : Nat := 4983230072969 + 3 ^ 40 * 5429351 * 2
def baseEnd_5429351 : Nat := 2787866704969092372943375

theorem tailTrace_5429351 : CollatzResearch.WordTrace tailWord_5429351 prefixEnd_5429351 2787866704969092372943375 := by
  unfold tailWord_5429351
  simp only [CollatzResearch.WordTrace]
  refine ⟨198024699353396061173023907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132016466235597374115349271 198024699353396061173023907)
  ·
    refine ⟨297037049030094091759535861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198024699353396061173023907 297037049030094091759535861)
    ·
      refine ⟨27847223346571321102456487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297037049030094091759535861 27847223346571321102456487)
      ·
        refine ⟨41770835019856981653684731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27847223346571321102456487 41770835019856981653684731)
        ·
          refine ⟨62656252529785472480527097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41770835019856981653684731 62656252529785472480527097)
          ·
            refine ⟨46992189397339104360395323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62656252529785472480527097 46992189397339104360395323)
            ·
              refine ⟨70488284096008656540592985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46992189397339104360395323 70488284096008656540592985)
              ·
                refine ⟨52866213072006492405444739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70488284096008656540592985 52866213072006492405444739)
                ·
                  refine ⟨79299319608009738608167109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52866213072006492405444739 79299319608009738608167109)
                  ·
                    refine ⟨14868622426501825989031333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79299319608009738608167109 14868622426501825989031333)
                    ·
                      refine ⟨2787866704969092372943375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14868622426501825989031333 2787866704969092372943375)
                      ·
                        rfl

theorem cell23_5429351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 1, 4, 4].length) (baseStart_5429351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429351 prefixEnd_5429351 := by exact prefixLift 5429351
  have htrace : WordTrace (prefixWord ++ tailWord_5429351) baseStart_5429351 baseEnd_5429351 := by
    simpa [prefixWord, tailWord_5429351, baseEnd_5429351] using wordTrace_append hprefix tailTrace_5429351
  have hstable : (prefixWord ++ tailWord_5429351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429351).length < 2 ^ (prefixWord ++ tailWord_5429351).sum := by decide
  have hdescent : baseEnd_5429351 < baseStart_5429351 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429372 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_5429372 : Nat := 118140960795 + 5429372 * 2 ^ 59
def prefixEnd_5429372 : Nat := 4983230072969 + 3 ^ 40 * 5429372 * 2
def baseEnd_5429372 : Nat := 2787877488062836790780779

theorem tailTrace_5429372 : CollatzResearch.WordTrace tailWord_5429372 prefixEnd_5429372 2787877488062836790780779 := by
  unfold tailWord_5429372
  simp only [CollatzResearch.WordTrace]
  refine ⟨99012732643159990879769185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132016976857546654506358913 99012732643159990879769185)
  ·
    refine ⟨74259549482369993159826889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99012732643159990879769185 74259549482369993159826889)
    ·
      refine ⟨55694662111777494869870167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74259549482369993159826889 55694662111777494869870167)
      ·
        refine ⟨83541993167666242304805251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55694662111777494869870167 83541993167666242304805251)
        ·
          refine ⟨125312989751499363457207877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83541993167666242304805251 125312989751499363457207877)
          ·
            refine ⟨23496185578406130648226477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125312989751499363457207877 23496185578406130648226477)
            ·
              refine ⟨8811069591902298993084929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23496185578406130648226477 8811069591902298993084929)
              ·
                refine ⟨6608302193926724244813697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8811069591902298993084929 6608302193926724244813697)
                ·
                  refine ⟨4956226645445043183610273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6608302193926724244813697 4956226645445043183610273)
                  ·
                    refine ⟨3717169984083782387707705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4956226645445043183610273 3717169984083782387707705)
                    ·
                      refine ⟨2787877488062836790780779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717169984083782387707705 2787877488062836790780779)
                      ·
                        rfl

theorem cell23_5429372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_5429372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429372 prefixEnd_5429372 := by exact prefixLift 5429372
  have htrace : WordTrace (prefixWord ++ tailWord_5429372) baseStart_5429372 baseEnd_5429372 := by
    simpa [prefixWord, tailWord_5429372, baseEnd_5429372] using wordTrace_append hprefix tailTrace_5429372
  have hstable : (prefixWord ++ tailWord_5429372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429372).length < 2 ^ (prefixWord ++ tailWord_5429372).sum := by decide
  have hdescent : baseEnd_5429372 < baseStart_5429372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429412 : List Nat := [2, 3, 1, 2, 4, 2, 1, 3, 5]
def baseStart_5429412 : Nat := 118140960795 + 5429412 * 2 ^ 59
def prefixEnd_5429412 : Nat := 4983230072969 + 3 ^ 40 * 5429412 * 2
def baseEnd_5429412 : Nat := 309766447476557403808955

theorem tailTrace_5429412 : CollatzResearch.WordTrace tailWord_5429412 prefixEnd_5429412 309766447476557403808955 := by
  unfold tailWord_5429412
  simp only [CollatzResearch.WordTrace]
  refine ⟨99013462103087534295497245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132017949470783379060662993 99013462103087534295497245)
  ·
    refine ⟨37130048288657825360811467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99013462103087534295497245 37130048288657825360811467)
    ·
      refine ⟨55695072432986738041217201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37130048288657825360811467 55695072432986738041217201)
      ·
        refine ⟨41771304324740053530912901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55695072432986738041217201 41771304324740053530912901)
        ·
          refine ⟨7832119560888760037046169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41771304324740053530912901 7832119560888760037046169)
          ·
            refine ⟨5874089670666570027784627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7832119560888760037046169 5874089670666570027784627)
            ·
              refine ⟨8811134505999855041676941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874089670666570027784627 8811134505999855041676941)
              ·
                refine ⟨3304175439749945640628853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8811134505999855041676941 3304175439749945640628853)
                ·
                  refine ⟨309766447476557403808955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304175439749945640628853 309766447476557403808955)
                  ·
                    rfl

theorem cell23_5429412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 2, 1, 3, 5].length) (baseStart_5429412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429412 prefixEnd_5429412 := by exact prefixLift 5429412
  have htrace : WordTrace (prefixWord ++ tailWord_5429412) baseStart_5429412 baseEnd_5429412 := by
    simpa [prefixWord, tailWord_5429412, baseEnd_5429412] using wordTrace_append hprefix tailTrace_5429412
  have hstable : (prefixWord ++ tailWord_5429412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429412).length < 2 ^ (prefixWord ++ tailWord_5429412).sum := by decide
  have hdescent : baseEnd_5429412 < baseStart_5429412 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429425 : List Nat := [1, 2, 2, 5, 2, 1, 1, 2, 2, 5]
def baseStart_5429425 : Nat := 118140960795 + 5429425 * 2 ^ 59
def prefixEnd_5429425 : Nat := 4983230072969 + 3 ^ 40 * 5429425 * 2
def baseEnd_5429425 : Nat := 929301567512508361139345

theorem tailTrace_5429425 : CollatzResearch.WordTrace tailWord_5429425 prefixEnd_5429425 929301567512508361139345 := by
  unfold tailWord_5429425
  simp only [CollatzResearch.WordTrace]
  refine ⟨198027398355127971811217729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132018265570085314540811819 198027398355127971811217729)
  ·
    refine ⟨148520548766345978858413297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198027398355127971811217729 148520548766345978858413297)
    ·
      refine ⟨111390411574759484143809973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148520548766345978858413297 111390411574759484143809973)
      ·
        refine ⟨10442851085133701638482185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111390411574759484143809973 10442851085133701638482185)
        ·
          refine ⟨7832138313850276228861639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10442851085133701638482185 7832138313850276228861639)
          ·
            refine ⟨11748207470775414343292459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7832138313850276228861639 11748207470775414343292459)
            ·
              refine ⟨17622311206163121514938689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11748207470775414343292459 17622311206163121514938689)
              ·
                refine ⟨13216733404622341136204017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17622311206163121514938689 13216733404622341136204017)
                ·
                  refine ⟨9912550053466755852153013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13216733404622341136204017 9912550053466755852153013)
                  ·
                    refine ⟨929301567512508361139345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9912550053466755852153013 929301567512508361139345)
                    ·
                      rfl

theorem cell23_5429425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 2, 2, 5].length) (baseStart_5429425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429425 prefixEnd_5429425 := by exact prefixLift 5429425
  have htrace : WordTrace (prefixWord ++ tailWord_5429425) baseStart_5429425 baseEnd_5429425 := by
    simpa [prefixWord, tailWord_5429425, baseEnd_5429425] using wordTrace_append hprefix tailTrace_5429425
  have hstable : (prefixWord ++ tailWord_5429425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429425).length < 2 ^ (prefixWord ++ tailWord_5429425).sum := by decide
  have hdescent : baseEnd_5429425 < baseStart_5429425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429429 : List Nat := [1, 3, 3, 4, 1, 1, 3, 2, 5]
def baseStart_5429429 : Nat := 118140960795 + 5429429 * 2 ^ 59
def prefixEnd_5429429 : Nat := 4983230072969 + 3 ^ 40 * 5429429 * 2
def baseEnd_5429429 : Nat := 309767417384460340863113

theorem tailTrace_5429429 : CollatzResearch.WordTrace tailWord_5429429 prefixEnd_5429429 309767417384460340863113 := by
  unfold tailWord_5429429
  simp only [CollatzResearch.WordTrace]
  refine ⟨198027544247113480494363341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132018362831408986996242227 198027544247113480494363341)
  ·
    refine ⟨74260329092667555185386253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198027544247113480494363341 74260329092667555185386253)
    ·
      refine ⟨27847623409750333194519845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74260329092667555185386253 27847623409750333194519845)
      ·
        refine ⟨5221429389328187473972471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27847623409750333194519845 5221429389328187473972471)
        ·
          refine ⟨7832144083992281210958707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221429389328187473972471 7832144083992281210958707)
          ·
            refine ⟨11748216125988421816438061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7832144083992281210958707 11748216125988421816438061)
            ·
              refine ⟨4405581047245658181164273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11748216125988421816438061 4405581047245658181164273)
              ·
                refine ⟨3304185785434243635873205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4405581047245658181164273 3304185785434243635873205)
                ·
                  refine ⟨309767417384460340863113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304185785434243635873205 309767417384460340863113)
                  ·
                    rfl

theorem cell23_5429429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 3, 2, 5].length) (baseStart_5429429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429429 prefixEnd_5429429 := by exact prefixLift 5429429
  have htrace : WordTrace (prefixWord ++ tailWord_5429429) baseStart_5429429 baseEnd_5429429 := by
    simpa [prefixWord, tailWord_5429429, baseEnd_5429429] using wordTrace_append hprefix tailTrace_5429429
  have hstable : (prefixWord ++ tailWord_5429429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429429).length < 2 ^ (prefixWord ++ tailWord_5429429).sum := by decide
  have hdescent : baseEnd_5429429 < baseStart_5429429 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429448 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 6, 2, 3]
def baseStart_5429448 : Nat := 118140960795 + 5429448 * 2 ^ 59
def prefixEnd_5429448 : Nat := 4983230072969 + 3 ^ 40 * 5429448 * 2
def baseEnd_5429448 : Nat := 2787916512592578493430429

theorem tailTrace_5429448 : CollatzResearch.WordTrace tailWord_5429448 prefixEnd_5429448 2787916512592578493430429 := by
  unfold tailWord_5429448
  simp only [CollatzResearch.WordTrace]
  refine ⟨99014118617022323369652499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132018824822696431159536665 99014118617022323369652499)
  ·
    refine ⟨148521177925533485054478749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99014118617022323369652499 148521177925533485054478749)
    ·
      refine ⟨55695441722075056895429531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148521177925533485054478749 55695441722075056895429531)
      ·
        refine ⟨83543162583112585343144297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55695441722075056895429531 83543162583112585343144297)
        ·
          refine ⟨62657371937334439007358223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83543162583112585343144297 62657371937334439007358223)
          ·
            refine ⟨93986057906001658511037335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62657371937334439007358223 93986057906001658511037335)
            ·
              refine ⟨140979086859002487766556003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93986057906001658511037335 140979086859002487766556003)
              ·
                refine ⟨211468630288503731649834005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 140979086859002487766556003 211468630288503731649834005)
                ·
                  refine ⟨9912592044773612421085969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 211468630288503731649834005 9912592044773612421085969)
                  ·
                    refine ⟨7434444033580209315814477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9912592044773612421085969 7434444033580209315814477)
                    ·
                      refine ⟨2787916512592578493430429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434444033580209315814477 2787916512592578493430429)
                      ·
                        rfl

theorem cell23_5429448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 6, 2, 3].length) (baseStart_5429448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429448 prefixEnd_5429448 := by exact prefixLift 5429448
  have htrace : WordTrace (prefixWord ++ tailWord_5429448) baseStart_5429448 baseEnd_5429448 := by
    simpa [prefixWord, tailWord_5429448, baseEnd_5429448] using wordTrace_append hprefix tailTrace_5429448
  have hstable : (prefixWord ++ tailWord_5429448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429448).length < 2 ^ (prefixWord ++ tailWord_5429448).sum := by decide
  have hdescent : baseEnd_5429448 < baseStart_5429448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429462 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 2, 1, 4]
def baseStart_5429462 : Nat := 118140960795 + 5429462 * 2 ^ 59
def prefixEnd_5429462 : Nat := 4983230072969 + 3 ^ 40 * 5429462 * 2
def baseEnd_5429462 : Nat := 2787923701321741438655365

theorem tailTrace_5429462 : CollatzResearch.WordTrace tailWord_5429462 prefixEnd_5429462 2787923701321741438655365 := by
  unfold tailWord_5429462
  simp only [CollatzResearch.WordTrace]
  refine ⟨12376796740999620445644665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132019165237329284753543093 12376796740999620445644665)
  ·
    refine ⟨9282597555749715334233499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12376796740999620445644665 9282597555749715334233499)
    ·
      refine ⟨13923896333624573001350249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9282597555749715334233499 13923896333624573001350249)
      ·
        refine ⟨10442922250218429751012687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13923896333624573001350249 10442922250218429751012687)
        ·
          refine ⟨15664383375327644626519031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10442922250218429751012687 15664383375327644626519031)
          ·
            refine ⟨23496575062991466939778547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15664383375327644626519031 23496575062991466939778547)
            ·
              refine ⟨35244862594487200409667821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23496575062991466939778547 35244862594487200409667821)
              ·
                refine ⟨13216823472932700153625433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35244862594487200409667821 13216823472932700153625433)
                ·
                  refine ⟨9912617604699525115219075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13216823472932700153625433 9912617604699525115219075)
                  ·
                    refine ⟨14868926407049287672828613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9912617604699525115219075 14868926407049287672828613)
                    ·
                      refine ⟨2787923701321741438655365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14868926407049287672828613 2787923701321741438655365)
                      ·
                        rfl

theorem cell23_5429462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_5429462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429462 prefixEnd_5429462 := by exact prefixLift 5429462
  have htrace : WordTrace (prefixWord ++ tailWord_5429462) baseStart_5429462 baseEnd_5429462 := by
    simpa [prefixWord, tailWord_5429462, baseEnd_5429462] using wordTrace_append hprefix tailTrace_5429462
  have hstable : (prefixWord ++ tailWord_5429462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429462).length < 2 ^ (prefixWord ++ tailWord_5429462).sum := by decide
  have hdescent : baseEnd_5429462 < baseStart_5429462 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429471 : List Nat := [1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 8]
def baseStart_5429471 : Nat := 118140960795 + 5429471 * 2 ^ 59
def prefixEnd_5429471 : Nat := 4983230072969 + 3 ^ 40 * 5429471 * 2
def baseEnd_5429471 : Nat := 2787928322647631903442823

theorem tailTrace_5429471 : CollatzResearch.WordTrace tailWord_5429471 prefixEnd_5429471 2787928322647631903442823 := by
  unfold tailWord_5429471
  simp only [CollatzResearch.WordTrace]
  refine ⟨198029076112961321667392267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132019384075307547778261511 198029076112961321667392267)
  ·
    refine ⟨297043614169441982501088401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198029076112961321667392267 297043614169441982501088401)
    ·
      refine ⟨222782710627081486875816301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297043614169441982501088401 222782710627081486875816301)
      ·
        refine ⟨83543516485155557578431113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222782710627081486875816301 83543516485155557578431113)
        ·
          refine ⟨62657637363866668183823335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83543516485155557578431113 62657637363866668183823335)
          ·
            refine ⟨93986456045800002275735003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62657637363866668183823335 93986456045800002275735003)
            ·
              refine ⟨140979684068700003413602505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 93986456045800002275735003 140979684068700003413602505)
              ·
                refine ⟨105734763051525002560201879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 140979684068700003413602505 105734763051525002560201879)
                ·
                  refine ⟨158602144577287503840302819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105734763051525002560201879 158602144577287503840302819)
                  ·
                    refine ⟨237903216865931255760454229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 158602144577287503840302819 237903216865931255760454229)
                    ·
                      refine ⟨2787928322647631903442823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 237903216865931255760454229 2787928322647631903442823)
                      ·
                        rfl

theorem cell23_5429471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_5429471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429471 prefixEnd_5429471 := by exact prefixLift 5429471
  have htrace : WordTrace (prefixWord ++ tailWord_5429471) baseStart_5429471 baseEnd_5429471 := by
    simpa [prefixWord, tailWord_5429471, baseEnd_5429471] using wordTrace_append hprefix tailTrace_5429471
  have hstable : (prefixWord ++ tailWord_5429471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429471).length < 2 ^ (prefixWord ++ tailWord_5429471).sum := by decide
  have hdescent : baseEnd_5429471 < baseStart_5429471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429498 : List Nat := [3, 1, 1, 1, 1, 5, 1, 2, 3, 5]
def baseStart_5429498 : Nat := 118140960795 + 5429498 * 2 ^ 59
def prefixEnd_5429498 : Nat := 4983230072969 + 3 ^ 40 * 5429498 * 2
def baseEnd_5429498 : Nat := 929314062208434432601733

theorem tailTrace_5429498 : CollatzResearch.WordTrace tailWord_5429498 prefixEnd_5429498 929314062208434432601733 := by
  unfold tailWord_5429498
  simp only [CollatzResearch.WordTrace]
  refine ⟨49507515220965876319656287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132020040589242336852416765 49507515220965876319656287)
  ·
    refine ⟨74261272831448814479484431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49507515220965876319656287 74261272831448814479484431)
    ·
      refine ⟨111391909247173221719226647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74261272831448814479484431 111391909247173221719226647)
      ·
        refine ⟨167087863870759832578839971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111391909247173221719226647 167087863870759832578839971)
        ·
          refine ⟨250631795806139748868259957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167087863870759832578839971 250631795806139748868259957)
          ·
            refine ⟨23496730856825601456399371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 250631795806139748868259957 23496730856825601456399371)
            ·
              refine ⟨35245096285238402184599057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23496730856825601456399371 35245096285238402184599057)
              ·
                refine ⟨26433822213928801638449293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35245096285238402184599057 26433822213928801638449293)
                ·
                  refine ⟨9912683330223300614418485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26433822213928801638449293 9912683330223300614418485)
                  ·
                    refine ⟨929314062208434432601733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9912683330223300614418485 929314062208434432601733)
                    ·
                      rfl

theorem cell23_5429498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 2, 3, 5].length) (baseStart_5429498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429498 prefixEnd_5429498 := by exact prefixLift 5429498
  have htrace : WordTrace (prefixWord ++ tailWord_5429498) baseStart_5429498 baseEnd_5429498 := by
    simpa [prefixWord, tailWord_5429498, baseEnd_5429498] using wordTrace_append hprefix tailTrace_5429498
  have hstable : (prefixWord ++ tailWord_5429498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429498).length < 2 ^ (prefixWord ++ tailWord_5429498).sum := by decide
  have hdescent : baseEnd_5429498 < baseStart_5429498 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429505 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 1, 5, 2]
def baseStart_5429505 : Nat := 118140960795 + 5429505 * 2 ^ 59
def prefixEnd_5429505 : Nat := 4983230072969 + 3 ^ 40 * 5429505 * 2
def baseEnd_5429505 : Nat := 2787945780989884770417667

theorem tailTrace_5429505 : CollatzResearch.WordTrace tailWord_5429505 prefixEnd_5429505 2787945780989884770417667 := by
  unfold tailWord_5429505
  simp only [CollatzResearch.WordTrace]
  refine ⟨198030316194838145474129969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132020210796558763649419979 198030316194838145474129969)
  ·
    refine ⟨148522737146128609105597477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198030316194838145474129969 148522737146128609105597477)
    ·
      refine ⟨27848013214899114207299527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148522737146128609105597477 27848013214899114207299527)
      ·
        refine ⟨41772019822348671310949291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27848013214899114207299527 41772019822348671310949291)
        ·
          refine ⟨62658029733523006966423937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41772019822348671310949291 62658029733523006966423937)
          ·
            refine ⟨46993522300142255224817953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62658029733523006966423937 46993522300142255224817953)
            ·
              refine ⟨35245141725106691418613465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46993522300142255224817953 35245141725106691418613465)
              ·
                refine ⟨26433856293830018563960099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35245141725106691418613465 26433856293830018563960099)
                ·
                  refine ⟨39650784440745027845940149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26433856293830018563960099 39650784440745027845940149)
                  ·
                    refine ⟨3717261041319846360556889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39650784440745027845940149 3717261041319846360556889)
                    ·
                      refine ⟨2787945780989884770417667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717261041319846360556889 2787945780989884770417667)
                      ·
                        rfl

theorem cell23_5429505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 5, 2].length) (baseStart_5429505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429505 prefixEnd_5429505 := by exact prefixLift 5429505
  have htrace : WordTrace (prefixWord ++ tailWord_5429505) baseStart_5429505 baseEnd_5429505 := by
    simpa [prefixWord, tailWord_5429505, baseEnd_5429505] using wordTrace_append hprefix tailTrace_5429505
  have hstable : (prefixWord ++ tailWord_5429505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429505).length < 2 ^ (prefixWord ++ tailWord_5429505).sum := by decide
  have hdescent : baseEnd_5429505 < baseStart_5429505 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429512 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 3, 1, 3]
def baseStart_5429512 : Nat := 118140960795 + 5429512 * 2 ^ 59
def prefixEnd_5429512 : Nat := 4983230072969 + 3 ^ 40 * 5429512 * 2
def baseEnd_5429512 : Nat := 2787949375354466243030135

theorem tailTrace_5429512 : CollatzResearch.WordTrace tailWord_5429512 prefixEnd_5429512 2787949375354466243030135 := by
  unfold tailWord_5429512
  simp only [CollatzResearch.WordTrace]
  refine ⟨99015285752906392834817395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132020381003875190446423193 99015285752906392834817395)
  ·
    refine ⟨148522928629359589252226093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99015285752906392834817395 148522928629359589252226093)
    ·
      refine ⟨55696098236009845969584785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148522928629359589252226093 55696098236009845969584785)
      ·
        refine ⟨41772073677007384477188589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55696098236009845969584785 41772073677007384477188589)
        ·
          refine ⟨15664527628877769178945721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41772073677007384477188589 15664527628877769178945721)
          ·
            refine ⟨11748395721658326884209291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15664527628877769178945721 11748395721658326884209291)
            ·
              refine ⟨17622593582487490326313937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11748395721658326884209291 17622593582487490326313937)
              ·
                refine ⟨13216945186865617744735453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17622593582487490326313937 13216945186865617744735453)
                ·
                  refine ⟨4956354445074606654275795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13216945186865617744735453 4956354445074606654275795)
                  ·
                    refine ⟨7434531667611909981413693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4956354445074606654275795 7434531667611909981413693)
                    ·
                      refine ⟨2787949375354466243030135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434531667611909981413693 2787949375354466243030135)
                      ·
                        rfl

theorem cell23_5429512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 3, 1, 3].length) (baseStart_5429512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429512 prefixEnd_5429512 := by exact prefixLift 5429512
  have htrace : WordTrace (prefixWord ++ tailWord_5429512) baseStart_5429512 baseEnd_5429512 := by
    simpa [prefixWord, tailWord_5429512, baseEnd_5429512] using wordTrace_append hprefix tailTrace_5429512
  have hstable : (prefixWord ++ tailWord_5429512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429512).length < 2 ^ (prefixWord ++ tailWord_5429512).sum := by decide
  have hdescent : baseEnd_5429512 < baseStart_5429512 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429528 : List Nat := [2, 1, 2, 3, 1, 2, 1, 4, 1, 6]
def baseStart_5429528 : Nat := 118140960795 + 5429528 * 2 ^ 59
def prefixEnd_5429528 : Nat := 4983230072969 + 3 ^ 40 * 5429528 * 2
def baseEnd_5429528 : Nat := 929319197014979393476687

theorem tailTrace_5429528 : CollatzResearch.WordTrace tailWord_5429528 prefixEnd_5429528 929319197014979393476687 := by
  unfold tailWord_5429528
  simp only [CollatzResearch.WordTrace]
  refine ⟨99015577536877410201108619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132020770049169880268144825 99015577536877410201108619)
  ·
    refine ⟨148523366305316115301662929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99015577536877410201108619 148523366305316115301662929)
    ·
      refine ⟨111392524728987086476247197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148523366305316115301662929 111392524728987086476247197)
      ·
        refine ⟨41772196773370157428592699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111392524728987086476247197 41772196773370157428592699)
        ·
          refine ⟨62658295160055236142889049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41772196773370157428592699 62658295160055236142889049)
          ·
            refine ⟨46993721370041427107166787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62658295160055236142889049 46993721370041427107166787)
            ·
              refine ⟨70490582055062140660750181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46993721370041427107166787 70490582055062140660750181)
              ·
                refine ⟨13216984135324151373890659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70490582055062140660750181 13216984135324151373890659)
                ·
                  refine ⟨19825476202986227060835989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13216984135324151373890659 19825476202986227060835989)
                  ·
                    refine ⟨929319197014979393476687, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19825476202986227060835989 929319197014979393476687)
                    ·
                      rfl

theorem cell23_5429528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 1, 4, 1, 6].length) (baseStart_5429528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429528 prefixEnd_5429528 := by exact prefixLift 5429528
  have htrace : WordTrace (prefixWord ++ tailWord_5429528) baseStart_5429528 baseEnd_5429528 := by
    simpa [prefixWord, tailWord_5429528, baseEnd_5429528] using wordTrace_append hprefix tailTrace_5429528
  have hstable : (prefixWord ++ tailWord_5429528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429528).length < 2 ^ (prefixWord ++ tailWord_5429528).sum := by decide
  have hdescent : baseEnd_5429528 < baseStart_5429528 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429548 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 4]
def baseStart_5429548 : Nat := 118140960795 + 5429548 * 2 ^ 59
def prefixEnd_5429548 : Nat := 4983230072969 + 3 ^ 40 * 5429548 * 2
def baseEnd_5429548 : Nat := 2787967860658028102179969

theorem tailTrace_5429548 : CollatzResearch.WordTrace tailWord_5429548 prefixEnd_5429548 2787967860658028102179969 := by
  unfold tailWord_5429548
  simp only [CollatzResearch.WordTrace]
  refine ⟨99015942266841181908972649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132021256355788242545296865 99015942266841181908972649)
  ·
    refine ⟨74261956700130886431729487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99015942266841181908972649 74261956700130886431729487)
    ·
      refine ⟨111392935050196329647594231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74261956700130886431729487 111392935050196329647594231)
      ·
        refine ⟨167089402575294494471391347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111392935050196329647594231 167089402575294494471391347)
        ·
          refine ⟨250634103862941741707087021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167089402575294494471391347 250634103862941741707087021)
          ·
            refine ⟨93987788948603153140157633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250634103862941741707087021 93987788948603153140157633)
            ·
              refine ⟨70490841711452364855118225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 93987788948603153140157633 70490841711452364855118225)
              ·
                refine ⟨52868131283589273641338669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70490841711452364855118225 52868131283589273641338669)
                ·
                  refine ⟨19825549231345977615502001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52868131283589273641338669 19825549231345977615502001)
                  ·
                    refine ⟨14869161923509483211626501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19825549231345977615502001 14869161923509483211626501)
                    ·
                      refine ⟨2787967860658028102179969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14869161923509483211626501 2787967860658028102179969)
                      ·
                        rfl

theorem cell23_5429548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 4].length) (baseStart_5429548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429548 prefixEnd_5429548 := by exact prefixLift 5429548
  have htrace : WordTrace (prefixWord ++ tailWord_5429548) baseStart_5429548 baseEnd_5429548 := by
    simpa [prefixWord, tailWord_5429548, baseEnd_5429548] using wordTrace_append hprefix tailTrace_5429548
  have hstable : (prefixWord ++ tailWord_5429548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429548).length < 2 ^ (prefixWord ++ tailWord_5429548).sum := by decide
  have hdescent : baseEnd_5429548 < baseStart_5429548 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429569 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 4]
def baseStart_5429569 : Nat := 118140960795 + 5429569 * 2 ^ 59
def prefixEnd_5429569 : Nat := 4983230072969 + 3 ^ 40 * 5429569 * 2
def baseEnd_5429569 : Nat := 2787978643751772520017373

theorem tailTrace_5429569 : CollatzResearch.WordTrace tailWord_5429569 prefixEnd_5429569 2787978643751772520017373 := by
  unfold tailWord_5429569
  simp only [CollatzResearch.WordTrace]
  refine ⟨198032650466606284404459761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132021766977737522936306507 198032650466606284404459761)
  ·
    refine ⟨148524487849954713303344821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198032650466606284404459761 148524487849954713303344821)
    ·
      refine ⟨13924170735933254372188577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148524487849954713303344821 13924170735933254372188577)
      ·
        refine ⟨10443128051949940779141433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13924170735933254372188577 10443128051949940779141433)
        ·
          refine ⟨7832346038962455584356075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10443128051949940779141433 7832346038962455584356075)
          ·
            refine ⟨11748519058443683376534113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7832346038962455584356075 11748519058443683376534113)
            ·
              refine ⟨8811389293832762532400585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11748519058443683376534113 8811389293832762532400585)
              ·
                refine ⟨6608541970374571899300439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8811389293832762532400585 6608541970374571899300439)
                ·
                  refine ⟨9912812955561857848950659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608541970374571899300439 9912812955561857848950659)
                  ·
                    refine ⟨14869219433342786773425989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9912812955561857848950659 14869219433342786773425989)
                    ·
                      refine ⟨2787978643751772520017373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14869219433342786773425989 2787978643751772520017373)
                      ·
                        rfl

theorem cell23_5429569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_5429569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429569 prefixEnd_5429569 := by exact prefixLift 5429569
  have htrace : WordTrace (prefixWord ++ tailWord_5429569) baseStart_5429569 baseEnd_5429569 := by
    simpa [prefixWord, tailWord_5429569, baseEnd_5429569] using wordTrace_append hprefix tailTrace_5429569
  have hstable : (prefixWord ++ tailWord_5429569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429569).length < 2 ^ (prefixWord ++ tailWord_5429569).sum := by decide
  have hdescent : baseEnd_5429569 < baseStart_5429569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429586 : List Nat := [3, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_5429586 : Nat := 118140960795 + 5429586 * 2 ^ 59
def prefixEnd_5429586 : Nat := 4983230072969 + 3 ^ 40 * 5429586 * 2
def baseEnd_5429586 : Nat := 2787987372922898953504795

theorem tailTrace_5429586 : CollatzResearch.WordTrace tailWord_5429586 prefixEnd_5429586 2787987372922898953504795 := by
  unfold tailWord_5429586
  simp only [CollatzResearch.WordTrace]
  refine ⟨49508317626886174076957153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132022180338363130871885741 49508317626886174076957153)
  ·
    refine ⟨37131238220164630557717865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49508317626886174076957153 37131238220164630557717865)
    ·
      refine ⟨27848428665123472918288399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37131238220164630557717865 27848428665123472918288399)
      ·
        refine ⟨41772642997685209377432599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27848428665123472918288399 41772642997685209377432599)
        ·
          refine ⟨62658964496527814066148899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41772642997685209377432599 62658964496527814066148899)
          ·
            refine ⟨93988446744791721099223349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62658964496527814066148899 93988446744791721099223349)
            ·
              refine ⟨8811416882324223853052189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 93988446744791721099223349 8811416882324223853052189)
              ·
                refine ⟨3304281330871583944894571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8811416882324223853052189 3304281330871583944894571)
                ·
                  refine ⟨4956421996307375917341857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304281330871583944894571 4956421996307375917341857)
                  ·
                    refine ⟨3717316497230531938006393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4956421996307375917341857 3717316497230531938006393)
                    ·
                      refine ⟨2787987372922898953504795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717316497230531938006393 2787987372922898953504795)
                      ·
                        rfl

theorem cell23_5429586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_5429586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429586 prefixEnd_5429586 := by exact prefixLift 5429586
  have htrace : WordTrace (prefixWord ++ tailWord_5429586) baseStart_5429586 baseEnd_5429586 := by
    simpa [prefixWord, tailWord_5429586, baseEnd_5429586] using wordTrace_append hprefix tailTrace_5429586
  have hstable : (prefixWord ++ tailWord_5429586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429586).length < 2 ^ (prefixWord ++ tailWord_5429586).sum := by decide
  have hdescent : baseEnd_5429586 < baseStart_5429586 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429629 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 1, 3, 2]
def baseStart_5429629 : Nat := 118140960795 + 5429629 * 2 ^ 59
def prefixEnd_5429629 : Nat := 4983230072969 + 3 ^ 40 * 5429629 * 2
def baseEnd_5429629 : Nat := 2788009452591042285267097

theorem tailTrace_5429629 : CollatzResearch.WordTrace tailWord_5429629 prefixEnd_5429629 2788009452591042285267097 := by
  unfold tailWord_5429629
  simp only [CollatzResearch.WordTrace]
  refine ⟨198034838846388914651643941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132023225897592609767762627 198034838846388914651643941)
  ·
    refine ⟨37131532283697921497183239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198034838846388914651643941 37131532283697921497183239)
    ·
      refine ⟨55697298425546882245774859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37131532283697921497183239 55697298425546882245774859)
      ·
        refine ⟨83545947638320323368662289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55697298425546882245774859 83545947638320323368662289)
        ·
          refine ⟨62659460728740242526496717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83545947638320323368662289 62659460728740242526496717)
          ·
            refine ⟨23497297773277590947436269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62659460728740242526496717 23497297773277590947436269)
            ·
              refine ⟨8811486664979096605288601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23497297773277590947436269 8811486664979096605288601)
              ·
                refine ⟨6608614998734322453966451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8811486664979096605288601 6608614998734322453966451)
                ·
                  refine ⟨9912922498101483680949677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608614998734322453966451 9912922498101483680949677)
                  ·
                    refine ⟨3717345936788056380356129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9912922498101483680949677 3717345936788056380356129)
                    ·
                      refine ⟨2788009452591042285267097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717345936788056380356129 2788009452591042285267097)
                      ·
                        rfl

theorem cell23_5429629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_5429629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429629 prefixEnd_5429629 := by exact prefixLift 5429629
  have htrace : WordTrace (prefixWord ++ tailWord_5429629) baseStart_5429629 baseEnd_5429629 := by
    simpa [prefixWord, tailWord_5429629, baseEnd_5429629] using wordTrace_append hprefix tailTrace_5429629
  have hstable : (prefixWord ++ tailWord_5429629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429629).length < 2 ^ (prefixWord ++ tailWord_5429629).sum := by decide
  have hdescent : baseEnd_5429629 < baseStart_5429629 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429672 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 1, 4, 4]
def baseStart_5429672 : Nat := 118140960795 + 5429672 * 2 ^ 59
def prefixEnd_5429672 : Nat := 4983230072969 + 3 ^ 40 * 5429672 * 2
def baseEnd_5429672 : Nat := 2788031532259185617029399

theorem tailTrace_5429672 : CollatzResearch.WordTrace tailWord_5429672 prefixEnd_5429672 2788031532259185617029399 := by
  unfold tailWord_5429672
  simp only [CollatzResearch.WordTrace]
  refine ⟨99018203592616566497729635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132024271456822088663639513 99018203592616566497729635)
  ·
    refine ⟨148527305388924849746594453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99018203592616566497729635 148527305388924849746594453)
    ·
      refine ⟨6962217440105852331871615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148527305388924849746594453 6962217440105852331871615)
      ·
        refine ⟨10443326160158778497807423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6962217440105852331871615 10443326160158778497807423)
        ·
          refine ⟨15664989240238167746711135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10443326160158778497807423 15664989240238167746711135)
          ·
            refine ⟨23497483860357251620066703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15664989240238167746711135 23497483860357251620066703)
            ·
              refine ⟨35246225790535877430100055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23497483860357251620066703 35246225790535877430100055)
              ·
                refine ⟨52869338685803816145150083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35246225790535877430100055 52869338685803816145150083)
                ·
                  refine ⟨79304008028705724217725125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52869338685803816145150083 79304008028705724217725125)
                  ·
                    refine ⟨14869501505382323290823461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79304008028705724217725125 14869501505382323290823461)
                    ·
                      refine ⟨2788031532259185617029399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14869501505382323290823461 2788031532259185617029399)
                      ·
                        rfl

theorem cell23_5429672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_5429672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429672 prefixEnd_5429672 := by exact prefixLift 5429672
  have htrace : WordTrace (prefixWord ++ tailWord_5429672) baseStart_5429672 baseEnd_5429672 := by
    simpa [prefixWord, tailWord_5429672, baseEnd_5429672] using wordTrace_append hprefix tailTrace_5429672
  have hstable : (prefixWord ++ tailWord_5429672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429672).length < 2 ^ (prefixWord ++ tailWord_5429672).sum := by decide
  have hdescent : baseEnd_5429672 < baseStart_5429672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429697 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 1, 3, 2]
def baseStart_5429697 : Nat := 118140960795 + 5429697 * 2 ^ 59
def prefixEnd_5429697 : Nat := 4983230072969 + 3 ^ 40 * 5429697 * 2
def baseEnd_5429697 : Nat := 2788044369275548019216785

theorem tailTrace_5429697 : CollatzResearch.WordTrace tailWord_5429697 prefixEnd_5429697 2788044369275548019216785 := by
  unfold tailWord_5429697
  simp only [CollatzResearch.WordTrace]
  refine ⟨198037319010142562265119345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132024879340095041510079563 198037319010142562265119345)
  ·
    refine ⟨148527989257606921698839509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198037319010142562265119345 148527989257606921698839509)
    ·
      refine ⟨3481124748225162227316551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 148527989257606921698839509 3481124748225162227316551)
      ·
        refine ⟨5221687122337743340974827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481124748225162227316551 5221687122337743340974827)
        ·
          refine ⟨7832530683506615011462241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5221687122337743340974827 7832530683506615011462241)
          ·
            refine ⟨5874398012629961258596681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7832530683506615011462241 5874398012629961258596681)
            ·
              refine ⟨4405798509472470943947511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5874398012629961258596681 4405798509472470943947511)
              ·
                refine ⟨6608697764208706415921267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405798509472470943947511 6608697764208706415921267)
                ·
                  refine ⟨9913046646313059623881901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608697764208706415921267 9913046646313059623881901)
                  ·
                    refine ⟨3717392492367397358955713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9913046646313059623881901 3717392492367397358955713)
                    ·
                      refine ⟨2788044369275548019216785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717392492367397358955713 2788044369275548019216785)
                      ·
                        rfl

theorem cell23_5429697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 3, 2].length) (baseStart_5429697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429697 prefixEnd_5429697 := by exact prefixLift 5429697
  have htrace : WordTrace (prefixWord ++ tailWord_5429697) baseStart_5429697 baseEnd_5429697 := by
    simpa [prefixWord, tailWord_5429697, baseEnd_5429697] using wordTrace_append hprefix tailTrace_5429697
  have hstable : (prefixWord ++ tailWord_5429697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429697).length < 2 ^ (prefixWord ++ tailWord_5429697).sum := by decide
  have hdescent : baseEnd_5429697 < baseStart_5429697 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429745 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 4]
def baseStart_5429745 : Nat := 118140960795 + 5429745 * 2 ^ 59
def prefixEnd_5429745 : Nat := 4983230072969 + 3 ^ 40 * 5429745 * 2
def baseEnd_5429745 : Nat := 2788069016346963831416563

theorem tailTrace_5429745 : CollatzResearch.WordTrace tailWord_5429745 prefixEnd_5429745 2788069016346963831416563 := by
  unfold tailWord_5429745
  simp only [CollatzResearch.WordTrace]
  refine ⟨198039069713968666462866689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132026046475979110975244459 198039069713968666462866689)
  ·
    refine ⟨148529302285476499847150017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198039069713968666462866689 148529302285476499847150017)
    ·
      refine ⟨111396976714107374885362513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148529302285476499847150017 111396976714107374885362513)
      ·
        refine ⟨83547732535580531164021885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111396976714107374885362513 83547732535580531164021885)
        ·
          refine ⟨31330399700842699186508207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83547732535580531164021885 31330399700842699186508207)
          ·
            refine ⟨46995599551264048779762311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31330399700842699186508207 46995599551264048779762311)
            ·
              refine ⟨70493399326896073169643467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46995599551264048779762311 70493399326896073169643467)
              ·
                refine ⟨105740098990344109754465201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70493399326896073169643467 105740098990344109754465201)
                ·
                  refine ⟨79305074242758082315848901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105740098990344109754465201 79305074242758082315848901)
                  ·
                    refine ⟨14869701420517140434221669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79305074242758082315848901 14869701420517140434221669)
                    ·
                      refine ⟨2788069016346963831416563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14869701420517140434221669 2788069016346963831416563)
                      ·
                        rfl

theorem cell23_5429745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 2, 4, 4].length) (baseStart_5429745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429745 prefixEnd_5429745 := by exact prefixLift 5429745
  have htrace : WordTrace (prefixWord ++ tailWord_5429745) baseStart_5429745 baseEnd_5429745 := by
    simpa [prefixWord, tailWord_5429745, baseEnd_5429745] using wordTrace_append hprefix tailTrace_5429745
  have hstable : (prefixWord ++ tailWord_5429745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429745).length < 2 ^ (prefixWord ++ tailWord_5429745).sum := by decide
  have hdescent : baseEnd_5429745 < baseStart_5429745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429752 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 2, 2, 3]
def baseStart_5429752 : Nat := 118140960795 + 5429752 * 2 ^ 59
def prefixEnd_5429752 : Nat := 4983230072969 + 3 ^ 40 * 5429752 * 2
def baseEnd_5429752 : Nat := 2788072610711545304029031

theorem tailTrace_5429752 : CollatzResearch.WordTrace tailWord_5429752 prefixEnd_5429752 2788072610711545304029031 := by
  unfold tailWord_5429752
  simp only [CollatzResearch.WordTrace]
  refine ⟨99019662512471653329185755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132026216683295537772247673 99019662512471653329185755)
  ·
    refine ⟨148529493768707479993778633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99019662512471653329185755 148529493768707479993778633)
    ·
      refine ⟨111397120326530609995333975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148529493768707479993778633 111397120326530609995333975)
      ·
        refine ⟨167095680489795914993000963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111397120326530609995333975 167095680489795914993000963)
        ·
          refine ⟨250643520734693872489501445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167095680489795914993000963 250643520734693872489501445)
          ·
            refine ⟨46995660137755101091781521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 250643520734693872489501445 46995660137755101091781521)
            ·
              refine ⟨35246745103316325818836141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46995660137755101091781521 35246745103316325818836141)
              ·
                refine ⟨13217529413743622182063553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35246745103316325818836141 13217529413743622182063553)
                ·
                  refine ⟨9913147060307716636547665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13217529413743622182063553 9913147060307716636547665)
                  ·
                    refine ⟨7434860295230787477410749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9913147060307716636547665 7434860295230787477410749)
                    ·
                      refine ⟨2788072610711545304029031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434860295230787477410749 2788072610711545304029031)
                      ·
                        rfl

theorem cell23_5429752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 2, 2, 3].length) (baseStart_5429752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429752 prefixEnd_5429752 := by exact prefixLift 5429752
  have htrace : WordTrace (prefixWord ++ tailWord_5429752) baseStart_5429752 baseEnd_5429752 := by
    simpa [prefixWord, tailWord_5429752, baseEnd_5429752] using wordTrace_append hprefix tailTrace_5429752
  have hstable : (prefixWord ++ tailWord_5429752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429752).length < 2 ^ (prefixWord ++ tailWord_5429752).sum := by decide
  have hdescent : baseEnd_5429752 < baseStart_5429752 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429785 : List Nat := [1, 2, 1, 2, 1, 1, 2, 3, 5, 5]
def baseStart_5429785 : Nat := 118140960795 + 5429785 * 2 ^ 59
def prefixEnd_5429785 : Nat := 4983230072969 + 3 ^ 40 * 5429785 * 2
def baseEnd_5429785 : Nat := 929363185191047891638793

theorem tailTrace_5429785 : CollatzResearch.WordTrace tailWord_5429785 prefixEnd_5429785 929363185191047891638793 := by
  unfold tailWord_5429785
  simp only [CollatzResearch.WordTrace]
  refine ⟨198040528633823753294322809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132027019089215835529548539 198040528633823753294322809)
  ·
    refine ⟨148530396475367814970742107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198040528633823753294322809 148530396475367814970742107)
    ·
      refine ⟨222795594713051722456113161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148530396475367814970742107 222795594713051722456113161)
      ·
        refine ⟨167096696034788791842084871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222795594713051722456113161 167096696034788791842084871)
        ·
          refine ⟨250645044052183187763127307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167096696034788791842084871 250645044052183187763127307)
          ·
            refine ⟨375967566078274781644690961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250645044052183187763127307 375967566078274781644690961)
            ·
              refine ⟨281975674558706086233518221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 375967566078274781644690961 281975674558706086233518221)
              ·
                refine ⟨105740877959514782337569333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 281975674558706086233518221 105740877959514782337569333)
                ·
                  refine ⟨9913207308704510844147125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105740877959514782337569333 9913207308704510844147125)
                  ·
                    refine ⟨929363185191047891638793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9913207308704510844147125 929363185191047891638793)
                    ·
                      rfl

theorem cell23_5429785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 3, 5, 5].length) (baseStart_5429785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429785 prefixEnd_5429785 := by exact prefixLift 5429785
  have htrace : WordTrace (prefixWord ++ tailWord_5429785) baseStart_5429785 baseEnd_5429785 := by
    simpa [prefixWord, tailWord_5429785, baseEnd_5429785] using wordTrace_append hprefix tailTrace_5429785
  have hstable : (prefixWord ++ tailWord_5429785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429785).length < 2 ^ (prefixWord ++ tailWord_5429785).sum := by decide
  have hdescent : baseEnd_5429785 < baseStart_5429785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429789 : List Nat := [1, 4, 2, 2, 1, 2, 4, 1, 6]
def baseStart_5429789 : Nat := 118140960795 + 5429789 * 2 ^ 59
def prefixEnd_5429789 : Nat := 4983230072969 + 3 ^ 40 * 5429789 * 2
def baseEnd_5429789 : Nat := 309787956610640184362929

theorem tailTrace_5429789 : CollatzResearch.WordTrace tailWord_5429789 prefixEnd_5429789 309787956610640184362929 := by
  unfold tailWord_5429789
  simp only [CollatzResearch.WordTrace]
  refine ⟨198040674525809261977468421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132027116350539507984978947 198040674525809261977468421)
  ·
    refine ⟨37132626473589236620775329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198040674525809261977468421 37132626473589236620775329)
    ·
      refine ⟨27849469855191927465581497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37132626473589236620775329 27849469855191927465581497)
      ·
        refine ⟨20887102391393945599186123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27849469855191927465581497 20887102391393945599186123)
        ·
          refine ⟨31330653587090918398779185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20887102391393945599186123 31330653587090918398779185)
          ·
            refine ⟨23497990190318188799084389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31330653587090918398779185 23497990190318188799084389)
            ·
              refine ⟨4405873160684660399828323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23497990190318188799084389 4405873160684660399828323)
              ·
                refine ⟨6608809741026990599742485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4405873160684660399828323 6608809741026990599742485)
                ·
                  refine ⟨309787956610640184362929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6608809741026990599742485 309787956610640184362929)
                  ·
                    rfl

theorem cell23_5429789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 4, 1, 6].length) (baseStart_5429789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429789 prefixEnd_5429789 := by exact prefixLift 5429789
  have htrace : WordTrace (prefixWord ++ tailWord_5429789) baseStart_5429789 baseEnd_5429789 := by
    simpa [prefixWord, tailWord_5429789, baseEnd_5429789] using wordTrace_append hprefix tailTrace_5429789
  have hstable : (prefixWord ++ tailWord_5429789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429789).length < 2 ^ (prefixWord ++ tailWord_5429789).sum := by decide
  have hdescent : baseEnd_5429789 < baseStart_5429789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429809 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 2, 3, 2]
def baseStart_5429809 : Nat := 118140960795 + 5429809 * 2 ^ 59
def prefixEnd_5429809 : Nat := 4983230072969 + 3 ^ 40 * 5429809 * 2
def baseEnd_5429809 : Nat := 2788101879108851581016269

theorem tailTrace_5429809 : CollatzResearch.WordTrace tailWord_5429809 prefixEnd_5429809 2788101879108851581016269 := by
  unfold tailWord_5429809
  simp only [CollatzResearch.WordTrace]
  refine ⟨198041403985736805393196481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132027602657157870262130987 198041403985736805393196481)
  ·
    refine ⟨148531052989302604044897361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198041403985736805393196481 148531052989302604044897361)
    ·
      refine ⟨111398289741976953033673021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148531052989302604044897361 111398289741976953033673021)
      ·
        refine ⟨41774358653241357387627383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111398289741976953033673021 41774358653241357387627383)
        ·
          refine ⟨62661537979862036081441075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41774358653241357387627383 62661537979862036081441075)
          ·
            refine ⟨93992306969793054122161613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62661537979862036081441075 93992306969793054122161613)
            ·
              refine ⟨35247115113672395295810605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93992306969793054122161613 35247115113672395295810605)
              ·
                refine ⟨13217668167627148235928977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35247115113672395295810605 13217668167627148235928977)
                ·
                  refine ⟨9913251125720361176946733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13217668167627148235928977 9913251125720361176946733)
                  ·
                    refine ⟨3717469172145135441355025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9913251125720361176946733 3717469172145135441355025)
                    ·
                      refine ⟨2788101879108851581016269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717469172145135441355025 2788101879108851581016269)
                      ·
                        rfl

theorem cell23_5429809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_5429809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429809 prefixEnd_5429809 := by exact prefixLift 5429809
  have htrace : WordTrace (prefixWord ++ tailWord_5429809) baseStart_5429809 baseEnd_5429809 := by
    simpa [prefixWord, tailWord_5429809, baseEnd_5429809] using wordTrace_append hprefix tailTrace_5429809
  have hstable : (prefixWord ++ tailWord_5429809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429809).length < 2 ^ (prefixWord ++ tailWord_5429809).sum := by decide
  have hdescent : baseEnd_5429809 < baseStart_5429809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429816 : List Nat := [2, 1, 2, 1, 4, 1, 2, 5, 1, 1, 3]
def baseStart_5429816 : Nat := 118140960795 + 5429816 * 2 ^ 59
def prefixEnd_5429816 : Nat := 4983230072969 + 3 ^ 40 * 5429816 * 2
def baseEnd_5429816 : Nat := 2788105473473433053628737

theorem tailTrace_5429816 : CollatzResearch.WordTrace tailWord_5429816 prefixEnd_5429816 2788105473473433053628737 := by
  unfold tailWord_5429816
  simp only [CollatzResearch.WordTrace]
  refine ⟨99020829648355722794350651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132027772864474297059134201 99020829648355722794350651)
  ·
    refine ⟨148531244472533584191525977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99020829648355722794350651 148531244472533584191525977)
    ·
      refine ⟨111398433354400188143644483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148531244472533584191525977 111398433354400188143644483)
      ·
        refine ⟨167097650031600282215466725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111398433354400188143644483 167097650031600282215466725)
        ·
          refine ⟨31330809380925052915400011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167097650031600282215466725 31330809380925052915400011)
          ·
            refine ⟨46996214071387579373100017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31330809380925052915400011 46996214071387579373100017)
            ·
              refine ⟨35247160553540684529825013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46996214071387579373100017 35247160553540684529825013)
              ·
                refine ⟨3304421301894439174671095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 35247160553540684529825013 3304421301894439174671095)
                ·
                  refine ⟨4956631952841658762006643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304421301894439174671095 4956631952841658762006643)
                  ·
                    refine ⟨7434947929262488143009965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4956631952841658762006643 7434947929262488143009965)
                    ·
                      refine ⟨2788105473473433053628737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7434947929262488143009965 2788105473473433053628737)
                      ·
                        rfl

theorem cell23_5429816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 5, 1, 1, 3].length) (baseStart_5429816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429816 prefixEnd_5429816 := by exact prefixLift 5429816
  have htrace : WordTrace (prefixWord ++ tailWord_5429816) baseStart_5429816 baseEnd_5429816 := by
    simpa [prefixWord, tailWord_5429816, baseEnd_5429816] using wordTrace_append hprefix tailTrace_5429816
  have hstable : (prefixWord ++ tailWord_5429816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429816).length < 2 ^ (prefixWord ++ tailWord_5429816).sum := by decide
  have hdescent : baseEnd_5429816 < baseStart_5429816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429832 : List Nat := [2, 1, 3, 1, 1, 1, 1, 5, 4, 4]
def baseStart_5429832 : Nat := 118140960795 + 5429832 * 2 ^ 59
def prefixEnd_5429832 : Nat := 4983230072969 + 3 ^ 40 * 5429832 * 2
def baseEnd_5429832 : Nat := 929371229721301663676221

theorem tailTrace_5429832 : CollatzResearch.WordTrace tailWord_5429832 prefixEnd_5429832 929371229721301663676221 := by
  unfold tailWord_5429832
  simp only [CollatzResearch.WordTrace]
  refine ⟨99021121432326740160641875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132028161909768986880855833 99021121432326740160641875)
  ·
    refine ⟨148531682148490110240962813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99021121432326740160641875 148531682148490110240962813)
    ·
      refine ⟨55699380805683791340361055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148531682148490110240962813 55699380805683791340361055)
      ·
        refine ⟨83549071208525687010541583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55699380805683791340361055 83549071208525687010541583)
        ·
          refine ⟨125323606812788530515812375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83549071208525687010541583 125323606812788530515812375)
          ·
            refine ⟨187985410219182795773718563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125323606812788530515812375 187985410219182795773718563)
            ·
              refine ⟨281978115328774193660577845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187985410219182795773718563 281978115328774193660577845)
              ·
                refine ⟨26435448312072580655679173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 281978115328774193660577845 26435448312072580655679173)
                ·
                  refine ⟨4956646558513608872939845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26435448312072580655679173 4956646558513608872939845)
                  ·
                    refine ⟨929371229721301663676221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956646558513608872939845 929371229721301663676221)
                    ·
                      rfl

theorem cell23_5429832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 5, 4, 4].length) (baseStart_5429832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429832 prefixEnd_5429832 := by exact prefixLift 5429832
  have htrace : WordTrace (prefixWord ++ tailWord_5429832) baseStart_5429832 baseEnd_5429832 := by
    simpa [prefixWord, tailWord_5429832, baseEnd_5429832] using wordTrace_append hprefix tailTrace_5429832
  have hstable : (prefixWord ++ tailWord_5429832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429832).length < 2 ^ (prefixWord ++ tailWord_5429832).sum := by decide
  have hdescent : baseEnd_5429832 < baseStart_5429832 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429835 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6]
def baseStart_5429835 : Nat := 118140960795 + 5429835 * 2 ^ 59
def prefixEnd_5429835 : Nat := 4983230072969 + 3 ^ 40 * 5429835 * 2
def baseEnd_5429835 : Nat := 2788115229605868479291149

theorem tailTrace_5429835 : CollatzResearch.WordTrace tailWord_5429835 prefixEnd_5429835 2788115229605868479291149 := by
  unfold tailWord_5429835
  simp only [CollatzResearch.WordTrace]
  refine ⟨198042352283642611833642959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132028234855761741222428639 198042352283642611833642959)
  ·
    refine ⟨297063528425463917750464439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198042352283642611833642959 297063528425463917750464439)
    ·
      refine ⟨445595292638195876625696659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297063528425463917750464439 445595292638195876625696659)
      ·
        refine ⟨668392938957293814938544989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445595292638195876625696659 668392938957293814938544989)
        ·
          refine ⟨250647352108985180601954371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 668392938957293814938544989 250647352108985180601954371)
          ·
            refine ⟨375971028163477770902931557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250647352108985180601954371 375971028163477770902931557)
            ·
              refine ⟨70494567780652082044299667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375971028163477770902931557 70494567780652082044299667)
              ·
                refine ⟨105741851670978123066449501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70494567780652082044299667 105741851670978123066449501)
                ·
                  refine ⟨39653194376616796149918563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105741851670978123066449501 39653194376616796149918563)
                  ·
                    refine ⟨59479791564925194224877845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39653194376616796149918563 59479791564925194224877845)
                    ·
                      refine ⟨2788115229605868479291149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59479791564925194224877845 2788115229605868479291149)
                      ·
                        rfl

theorem cell23_5429835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 3, 1, 6].length) (baseStart_5429835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429835 prefixEnd_5429835 := by exact prefixLift 5429835
  have htrace : WordTrace (prefixWord ++ tailWord_5429835) baseStart_5429835 baseEnd_5429835 := by
    simpa [prefixWord, tailWord_5429835, baseEnd_5429835] using wordTrace_append hprefix tailTrace_5429835
  have hstable : (prefixWord ++ tailWord_5429835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429835).length < 2 ^ (prefixWord ++ tailWord_5429835).sum := by decide
  have hdescent : baseEnd_5429835 < baseStart_5429835 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429842 : List Nat := [3, 2, 2, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_5429842 : Nat := 118140960795 + 5429842 * 2 ^ 59
def prefixEnd_5429842 : Nat := 4983230072969 + 3 ^ 40 * 5429842 * 2
def baseEnd_5429842 : Nat := 2788118823970449951903617

theorem tailTrace_5429842 : CollatzResearch.WordTrace tailWord_5429842 prefixEnd_5429842 2788118823970449951903617 := by
  unfold tailWord_5429842
  simp only [CollatzResearch.WordTrace]
  refine ⟨49510651898654313007286945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132028405063078168019431853 49510651898654313007286945)
  ·
    refine ⟨37132988923990734755465209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49510651898654313007286945 37132988923990734755465209)
    ·
      refine ⟨27849741692993051066598907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37132988923990734755465209 27849741692993051066598907)
      ·
        refine ⟨41774612539489576599898361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27849741692993051066598907 41774612539489576599898361)
        ·
          refine ⟨31330959404617182449923771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41774612539489576599898361 31330959404617182449923771)
          ·
            refine ⟨46996439106925773674885657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31330959404617182449923771 46996439106925773674885657)
            ·
              refine ⟨35247329330194330256164243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46996439106925773674885657 35247329330194330256164243)
              ·
                refine ⟨52870993995291495384246365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35247329330194330256164243 52870993995291495384246365)
                ·
                  refine ⟨19826622748234310769092387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52870993995291495384246365 19826622748234310769092387)
                  ·
                    refine ⟨29739934122351466153638581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19826622748234310769092387 29739934122351466153638581)
                    ·
                      refine ⟨2788118823970449951903617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29739934122351466153638581 2788118823970449951903617)
                      ·
                        rfl

theorem cell23_5429842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_5429842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429842 prefixEnd_5429842 := by exact prefixLift 5429842
  have htrace : WordTrace (prefixWord ++ tailWord_5429842) baseStart_5429842 baseEnd_5429842 := by
    simpa [prefixWord, tailWord_5429842, baseEnd_5429842] using wordTrace_append hprefix tailTrace_5429842
  have hstable : (prefixWord ++ tailWord_5429842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429842).length < 2 ^ (prefixWord ++ tailWord_5429842).sum := by decide
  have hdescent : baseEnd_5429842 < baseStart_5429842 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429855 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 7]
def baseStart_5429855 : Nat := 118140960795 + 5429855 * 2 ^ 59
def prefixEnd_5429855 : Nat := 4983230072969 + 3 ^ 40 * 5429855 * 2
def baseEnd_5429855 : Nat := 2788125499218958401041057

theorem tailTrace_5429855 : CollatzResearch.WordTrace tailWord_5429855 prefixEnd_5429855 2788125499218958401041057 := by
  unfold tailWord_5429855
  simp only [CollatzResearch.WordTrace]
  refine ⟨198043081743570155249371019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132028721162380103499580679 198043081743570155249371019)
  ·
    refine ⟨297064622615355232874056529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198043081743570155249371019 297064622615355232874056529)
    ·
      refine ⟨222798466961516424655542397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297064622615355232874056529 222798466961516424655542397)
      ·
        refine ⟨83549425110568659245828399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222798466961516424655542397 83549425110568659245828399)
        ·
          refine ⟨125324137665852988868742599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83549425110568659245828399 125324137665852988868742599)
          ·
            refine ⟨187986206498779483303113899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125324137665852988868742599 187986206498779483303113899)
            ·
              refine ⟨281979309748169224954670849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 187986206498779483303113899 281979309748169224954670849)
              ·
                refine ⟨211484482311126918716003137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 281979309748169224954670849 211484482311126918716003137)
                ·
                  refine ⟨158613361733345189037002353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211484482311126918716003137 158613361733345189037002353)
                  ·
                    refine ⟨118960021300008891777751765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158613361733345189037002353 118960021300008891777751765)
                    ·
                      refine ⟨2788125499218958401041057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118960021300008891777751765 2788125499218958401041057)
                      ·
                        rfl

theorem cell23_5429855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_5429855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429855 prefixEnd_5429855 := by exact prefixLift 5429855
  have htrace : WordTrace (prefixWord ++ tailWord_5429855) baseStart_5429855 baseEnd_5429855 := by
    simpa [prefixWord, tailWord_5429855, baseEnd_5429855] using wordTrace_append hprefix tailTrace_5429855
  have hstable : (prefixWord ++ tailWord_5429855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429855).length < 2 ^ (prefixWord ++ tailWord_5429855).sum := by decide
  have hdescent : baseEnd_5429855 < baseStart_5429855 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429859 : List Nat := [1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 3]
def baseStart_5429859 : Nat := 118140960795 + 5429859 * 2 ^ 59
def prefixEnd_5429859 : Nat := 4983230072969 + 3 ^ 40 * 5429859 * 2
def baseEnd_5429859 : Nat := 2788127553141576385391039

theorem tailTrace_5429859 : CollatzResearch.WordTrace tailWord_5429859 prefixEnd_5429859 2788127553141576385391039 := by
  unfold tailWord_5429859
  simp only [CollatzResearch.WordTrace]
  refine ⟨198043227635555663932516631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132028818423703775955011087 198043227635555663932516631)
  ·
    refine ⟨297064841453333495898774947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198043227635555663932516631 297064841453333495898774947)
    ·
      refine ⟨445597262180000243848162421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297064841453333495898774947 445597262180000243848162421)
      ·
        refine ⟨41774743329375022860765227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 445597262180000243848162421 41774743329375022860765227)
        ·
          refine ⟨62662114994062534291147841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41774743329375022860765227 62662114994062534291147841)
          ·
            refine ⟨46996586245546900718360881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62662114994062534291147841 46996586245546900718360881)
            ·
              refine ⟨35247439684160175538770661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46996586245546900718360881 35247439684160175538770661)
              ·
                refine ⟨6608894940780032913519499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35247439684160175538770661 6608894940780032913519499)
                ·
                  refine ⟨9913342411170049370279249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608894940780032913519499 9913342411170049370279249)
                  ·
                    refine ⟨7435006808377537027709437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9913342411170049370279249 7435006808377537027709437)
                    ·
                      refine ⟨2788127553141576385391039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7435006808377537027709437 2788127553141576385391039)
                      ·
                        rfl

theorem cell23_5429859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_5429859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429859 prefixEnd_5429859 := by exact prefixLift 5429859
  have htrace : WordTrace (prefixWord ++ tailWord_5429859) baseStart_5429859 baseEnd_5429859 := by
    simpa [prefixWord, tailWord_5429859, baseEnd_5429859] using wordTrace_append hprefix tailTrace_5429859
  have hstable : (prefixWord ++ tailWord_5429859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429859).length < 2 ^ (prefixWord ++ tailWord_5429859).sum := by decide
  have hdescent : baseEnd_5429859 < baseStart_5429859 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429869 : List Nat := [1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_5429869 : Nat := 118140960795 + 5429869 * 2 ^ 59
def prefixEnd_5429869 : Nat := 4983230072969 + 3 ^ 40 * 5429869 * 2
def baseEnd_5429869 : Nat := 2788132687948121346265993

theorem tailTrace_5429869 : CollatzResearch.WordTrace tailWord_5429869 prefixEnd_5429869 2788132687948121346265993 := by
  unfold tailWord_5429869
  simp only [CollatzResearch.WordTrace]
  refine ⟨198043592365519435640380661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132029061577012957093587107 198043592365519435640380661)
  ·
    refine ⟨18566586784267447091285687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198043592365519435640380661 18566586784267447091285687)
    ·
      refine ⟨27849880176401170636928531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18566586784267447091285687 27849880176401170636928531)
      ·
        refine ⟨41774820264601755955392797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27849880176401170636928531 41774820264601755955392797)
        ·
          refine ⟨15665557599225658483272299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41774820264601755955392797 15665557599225658483272299)
          ·
            refine ⟨23498336398838487724908449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15665557599225658483272299 23498336398838487724908449)
            ·
              refine ⟨17623752299128865793681337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23498336398838487724908449 17623752299128865793681337)
              ·
                refine ⟨13217814224346649345261003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17623752299128865793681337 13217814224346649345261003)
                ·
                  refine ⟨19826721336519974017891505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13217814224346649345261003 19826721336519974017891505)
                  ·
                    refine ⟨14870041002389980513418629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19826721336519974017891505 14870041002389980513418629)
                    ·
                      refine ⟨2788132687948121346265993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14870041002389980513418629 2788132687948121346265993)
                      ·
                        rfl

theorem cell23_5429869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_5429869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429869 prefixEnd_5429869 := by exact prefixLift 5429869
  have htrace : WordTrace (prefixWord ++ tailWord_5429869) baseStart_5429869 baseEnd_5429869 := by
    simpa [prefixWord, tailWord_5429869, baseEnd_5429869] using wordTrace_append hprefix tailTrace_5429869
  have hstable : (prefixWord ++ tailWord_5429869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429869).length < 2 ^ (prefixWord ++ tailWord_5429869).sum := by decide
  have hdescent : baseEnd_5429869 < baseStart_5429869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429875 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 1, 9]
def baseStart_5429875 : Nat := 118140960795 + 5429875 * 2 ^ 59
def prefixEnd_5429875 : Nat := 4983230072969 + 3 ^ 40 * 5429875 * 2
def baseEnd_5429875 : Nat := 929378589610682774263655

theorem tailTrace_5429875 : CollatzResearch.WordTrace tailWord_5429875 prefixEnd_5429875 929378589610682774263655 := by
  unfold tailWord_5429875
  simp only [CollatzResearch.WordTrace]
  refine ⟨198043811203497698665099079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132029207468998465776732719 198043811203497698665099079)
  ·
    refine ⟨297065716805246547997648619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198043811203497698665099079 297065716805246547997648619)
    ·
      refine ⟨445598575207869821996472929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297065716805246547997648619 445598575207869821996472929)
      ·
        refine ⟨334198931405902366497354697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445598575207869821996472929 334198931405902366497354697)
        ·
          refine ⟨250649198554426774873016023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334198931405902366497354697 250649198554426774873016023)
          ·
            refine ⟨375973797831640162309524035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250649198554426774873016023 375973797831640162309524035)
            ·
              refine ⟨563960696747460243464286053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375973797831640162309524035 563960696747460243464286053)
              ·
                refine ⟨105742630640148795649553635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 563960696747460243464286053 105742630640148795649553635)
                ·
                  refine ⟨158613945960223193474330453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105742630640148795649553635 158613945960223193474330453)
                  ·
                    refine ⟨929378589610682774263655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 158613945960223193474330453 929378589610682774263655)
                    ·
                      rfl

theorem cell23_5429875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 9].length) (baseStart_5429875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429875 prefixEnd_5429875 := by exact prefixLift 5429875
  have htrace : WordTrace (prefixWord ++ tailWord_5429875) baseStart_5429875 baseEnd_5429875 := by
    simpa [prefixWord, tailWord_5429875, baseEnd_5429875] using wordTrace_append hprefix tailTrace_5429875
  have hstable : (prefixWord ++ tailWord_5429875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429875).length < 2 ^ (prefixWord ++ tailWord_5429875).sum := by decide
  have hdescent : baseEnd_5429875 < baseStart_5429875 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429899 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 3, 3, 2]
def baseStart_5429899 : Nat := 118140960795 + 5429899 * 2 ^ 59
def prefixEnd_5429899 : Nat := 4983230072969 + 3 ^ 40 * 5429899 * 2
def baseEnd_5429899 : Nat := 2788148092367756228890855

theorem tailTrace_5429899 : CollatzResearch.WordTrace tailWord_5429899 prefixEnd_5429899 2788148092367756228890855 := by
  unfold tailWord_5429899
  simp only [CollatzResearch.WordTrace]
  refine ⟨198044686555410750763972751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132029791036940500509315167 198044686555410750763972751)
  ·
    refine ⟨297067029833116126145959127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198044686555410750763972751 297067029833116126145959127)
    ·
      refine ⟨445600544749674189218938691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297067029833116126145959127 445600544749674189218938691)
      ·
        refine ⟨668400817124511283828408037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445600544749674189218938691 668400817124511283828408037)
        ·
          refine ⟨125325153210845865717826507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 668400817124511283828408037 125325153210845865717826507)
          ·
            refine ⟨187987729816268798576739761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125325153210845865717826507 187987729816268798576739761)
            ·
              refine ⟨140990797362201598932554821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 187987729816268798576739761 140990797362201598932554821)
              ·
                refine ⟨26435774505412799799854029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 140990797362201598932554821 26435774505412799799854029)
                ·
                  refine ⟨9913415439529799924945261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26435774505412799799854029 9913415439529799924945261)
                  ·
                    refine ⟨3717530789823674971854473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9913415439529799924945261 3717530789823674971854473)
                    ·
                      refine ⟨2788148092367756228890855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717530789823674971854473 2788148092367756228890855)
                      ·
                        rfl

theorem cell23_5429899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 3, 2].length) (baseStart_5429899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429899 prefixEnd_5429899 := by exact prefixLift 5429899
  have htrace : WordTrace (prefixWord ++ tailWord_5429899) baseStart_5429899 baseEnd_5429899 := by
    simpa [prefixWord, tailWord_5429899, baseEnd_5429899] using wordTrace_append hprefix tailTrace_5429899
  have hstable : (prefixWord ++ tailWord_5429899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429899).length < 2 ^ (prefixWord ++ tailWord_5429899).sum := by decide
  have hdescent : baseEnd_5429899 < baseStart_5429899 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429906 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_5429906 : Nat := 118140960795 + 5429906 * 2 ^ 59
def prefixEnd_5429906 : Nat := 4983230072969 + 3 ^ 40 * 5429906 * 2
def baseEnd_5429906 : Nat := 2788151686732337701503323

theorem tailTrace_5429906 : CollatzResearch.WordTrace tailWord_5429906 prefixEnd_5429906 2788151686732337701503323 := by
  unfold tailWord_5429906
  simp only [CollatzResearch.WordTrace]
  refine ⟨49511235466596347739869393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132029961244256927306318381 49511235466596347739869393)
  ·
    refine ⟨37133426599947260804902045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49511235466596347739869393 37133426599947260804902045)
    ·
      refine ⟨13925034974980222801838267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37133426599947260804902045 13925034974980222801838267)
      ·
        refine ⟨20887552462470334202757401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13925034974980222801838267 20887552462470334202757401)
        ·
          refine ⟨15665664346852750652068051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20887552462470334202757401 15665664346852750652068051)
          ·
            refine ⟨23498496520279125978102077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15665664346852750652068051 23498496520279125978102077)
            ·
              refine ⟨8811936195104672241788279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23498496520279125978102077 8811936195104672241788279)
              ·
                refine ⟨13217904292657008362682419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8811936195104672241788279 13217904292657008362682419)
                ·
                  refine ⟨19826856438985512544023629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13217904292657008362682419 19826856438985512544023629)
                  ·
                    refine ⟨7435071164619567204008861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19826856438985512544023629 7435071164619567204008861)
                    ·
                      refine ⟨2788151686732337701503323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7435071164619567204008861 2788151686732337701503323)
                      ·
                        rfl

theorem cell23_5429906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_5429906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429906 prefixEnd_5429906 := by exact prefixLift 5429906
  have htrace : WordTrace (prefixWord ++ tailWord_5429906) baseStart_5429906 baseEnd_5429906 := by
    simpa [prefixWord, tailWord_5429906, baseEnd_5429906] using wordTrace_append hprefix tailTrace_5429906
  have hstable : (prefixWord ++ tailWord_5429906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429906).length < 2 ^ (prefixWord ++ tailWord_5429906).sum := by decide
  have hdescent : baseEnd_5429906 < baseStart_5429906 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429933 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 1, 3, 2]
def baseStart_5429933 : Nat := 118140960795 + 5429933 * 2 ^ 59
def prefixEnd_5429933 : Nat := 4983230072969 + 3 ^ 40 * 5429933 * 2
def baseEnd_5429933 : Nat := 2788165550710009095865699

theorem tailTrace_5429933 : CollatzResearch.WordTrace tailWord_5429933 prefixEnd_5429933 2788165550710009095865699 := by
  unfold tailWord_5429933
  simp only [CollatzResearch.WordTrace]
  refine ⟨198045926637287574570710453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132030617758191716380473635 198045926637287574570710453)
  ·
    refine ⟨18566805622245710116004105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198045926637287574570710453 18566805622245710116004105)
    ·
      refine ⟨13925104216684282587003079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18566805622245710116004105 13925104216684282587003079)
      ·
        refine ⟨20887656325026423880504619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13925104216684282587003079 20887656325026423880504619)
        ·
          refine ⟨31331484487539635820756929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20887656325026423880504619 31331484487539635820756929)
          ·
            refine ⟨23498613365654726865567697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31331484487539635820756929 23498613365654726865567697)
            ·
              refine ⟨17623960024241045149175773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23498613365654726865567697 17623960024241045149175773)
              ·
                refine ⟨6608985009090391930940915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17623960024241045149175773 6608985009090391930940915)
                ·
                  refine ⟨9913477513635587896411373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6608985009090391930940915 9913477513635587896411373)
                  ·
                    refine ⟨3717554067613345461154265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9913477513635587896411373 3717554067613345461154265)
                    ·
                      refine ⟨2788165550710009095865699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717554067613345461154265 2788165550710009095865699)
                      ·
                        rfl

theorem cell23_5429933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 3, 2].length) (baseStart_5429933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429933 prefixEnd_5429933 := by exact prefixLift 5429933
  have htrace : WordTrace (prefixWord ++ tailWord_5429933) baseStart_5429933 baseEnd_5429933 := by
    simpa [prefixWord, tailWord_5429933, baseEnd_5429933] using wordTrace_append hprefix tailTrace_5429933
  have hstable : (prefixWord ++ tailWord_5429933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429933).length < 2 ^ (prefixWord ++ tailWord_5429933).sum := by decide
  have hdescent : baseEnd_5429933 < baseStart_5429933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429946 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2]
def baseStart_5429946 : Nat := 118140960795 + 5429946 * 2 ^ 59
def prefixEnd_5429946 : Nat := 4983230072969 + 3 ^ 40 * 5429946 * 2
def baseEnd_5429946 : Nat := 2788172225958517545003139

theorem tailTrace_5429946 : CollatzResearch.WordTrace tailWord_5429946 prefixEnd_5429946 2788172225958517545003139 := by
  unfold tailWord_5429946
  simp only [CollatzResearch.WordTrace]
  refine ⟨49511600196560119447733423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132030933857493651860622461 49511600196560119447733423)
  ·
    refine ⟨74267400294840179171600135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49511600196560119447733423 74267400294840179171600135)
    ·
      refine ⟨111401100442260268757400203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74267400294840179171600135 111401100442260268757400203)
      ·
        refine ⟨167101650663390403136100305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111401100442260268757400203 167101650663390403136100305)
        ·
          refine ⟨125326237997542802352075229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167101650663390403136100305 125326237997542802352075229)
          ·
            refine ⟨46997339249078550882028211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125326237997542802352075229 46997339249078550882028211)
            ·
              refine ⟨70496008873617826323042317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46997339249078550882028211 70496008873617826323042317)
              ·
                refine ⟨26436003327606684871140869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70496008873617826323042317 26436003327606684871140869)
                ·
                  refine ⟨4956750623926253413338913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26436003327606684871140869 4956750623926253413338913)
                  ·
                    refine ⟨3717562967944690060004185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4956750623926253413338913 3717562967944690060004185)
                    ·
                      refine ⟨2788172225958517545003139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717562967944690060004185 2788172225958517545003139)
                      ·
                        rfl

theorem cell23_5429946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 2, 2].length) (baseStart_5429946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429946 prefixEnd_5429946 := by exact prefixLift 5429946
  have htrace : WordTrace (prefixWord ++ tailWord_5429946) baseStart_5429946 baseEnd_5429946 := by
    simpa [prefixWord, tailWord_5429946, baseEnd_5429946] using wordTrace_append hprefix tailTrace_5429946
  have hstable : (prefixWord ++ tailWord_5429946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429946).length < 2 ^ (prefixWord ++ tailWord_5429946).sum := by decide
  have hdescent : baseEnd_5429946 < baseStart_5429946 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5429999 : List Nat := [1, 1, 2, 1, 5, 2, 2, 2, 2, 5]
def baseStart_5429999 : Nat := 118140960795 + 5429999 * 2 ^ 59
def prefixEnd_5429999 : Nat := 4983230072969 + 3 ^ 40 * 5429999 * 2
def baseEnd_5429999 : Nat := 929399813477735279213465

theorem tailTrace_5429999 : CollatzResearch.WordTrace tailWord_5429999 prefixEnd_5429999 929399813477735279213465 := by
  unfold tailWord_5429999
  simp only [CollatzResearch.WordTrace]
  refine ⟨198048333855048467842613051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132032222570032311895075367 198048333855048467842613051)
  ·
    refine ⟨297072500782572701763919577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198048333855048467842613051 297072500782572701763919577)
    ·
      refine ⟨222804375586929526322939683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297072500782572701763919577 222804375586929526322939683)
      ·
        refine ⟨334206563380394289484409525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222804375586929526322939683 334206563380394289484409525)
        ·
          refine ⟨31331865316911964639163393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334206563380394289484409525 31331865316911964639163393)
          ·
            refine ⟨23498898987683973479372545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31331865316911964639163393 23498898987683973479372545)
            ·
              refine ⟨17624174240762980109529409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23498898987683973479372545 17624174240762980109529409)
              ·
                refine ⟨13218130680572235082147057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17624174240762980109529409 13218130680572235082147057)
                ·
                  refine ⟨9913598010429176311610293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13218130680572235082147057 9913598010429176311610293)
                  ·
                    refine ⟨929399813477735279213465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9913598010429176311610293 929399813477735279213465)
                    ·
                      rfl

theorem cell23_5429999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 2, 2, 5].length) (baseStart_5429999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5429999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5429999 prefixEnd_5429999 := by exact prefixLift 5429999
  have htrace : WordTrace (prefixWord ++ tailWord_5429999) baseStart_5429999 baseEnd_5429999 := by
    simpa [prefixWord, tailWord_5429999, baseEnd_5429999] using wordTrace_append hprefix tailTrace_5429999
  have hstable : (prefixWord ++ tailWord_5429999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5429999).length < 2 ^ (prefixWord ++ tailWord_5429999).sum := by decide
  have hdescent : baseEnd_5429999 < baseStart_5429999 := by decide
  rcases family_descends (prefixWord ++ tailWord_5429999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430006 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2]
def baseStart_5430006 : Nat := 118140960795 + 5430006 * 2 ^ 59
def prefixEnd_5430006 : Nat := 4983230072969 + 3 ^ 40 * 5430006 * 2
def baseEnd_5430006 : Nat := 2788203034797787310252863

theorem tailTrace_5430006 : CollatzResearch.WordTrace tailWord_5430006 prefixEnd_5430006 2788203034797787310252863 := by
  unfold tailWord_5430006
  simp only [CollatzResearch.WordTrace]
  refine ⟨12378036822876444252382367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132032392777348738692078581 12378036822876444252382367)
  ·
    refine ⟨18567055234314666378573551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12378036822876444252382367 18567055234314666378573551)
    ·
      refine ⟨27850582851471999567860327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18567055234314666378573551 27850582851471999567860327)
      ·
        refine ⟨41775874277207999351790491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27850582851471999567860327 41775874277207999351790491)
        ·
          refine ⟨62663811415811999027685737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41775874277207999351790491 62663811415811999027685737)
          ·
            refine ⟨46997858561858999270764303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62663811415811999027685737 46997858561858999270764303)
            ·
              refine ⟨70496787842788498906146455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 46997858561858999270764303 70496787842788498906146455)
              ·
                refine ⟨105745181764182748359219683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70496787842788498906146455 105745181764182748359219683)
                ·
                  refine ⟨158617772646274122538829525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105745181764182748359219683 158617772646274122538829525)
                  ·
                    refine ⟨3717604046397049747003817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 158617772646274122538829525 3717604046397049747003817)
                    ·
                      refine ⟨2788203034797787310252863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717604046397049747003817 2788203034797787310252863)
                      ·
                        rfl

theorem cell23_5430006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2].length) (baseStart_5430006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430006 prefixEnd_5430006 := by exact prefixLift 5430006
  have htrace : WordTrace (prefixWord ++ tailWord_5430006) baseStart_5430006 baseEnd_5430006 := by
    simpa [prefixWord, tailWord_5430006, baseEnd_5430006] using wordTrace_append hprefix tailTrace_5430006
  have hstable : (prefixWord ++ tailWord_5430006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430006).length < 2 ^ (prefixWord ++ tailWord_5430006).sum := by decide
  have hdescent : baseEnd_5430006 < baseStart_5430006 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430056 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 4, 2, 3]
def baseStart_5430056 : Nat := 118140960795 + 5430056 * 2 ^ 59
def prefixEnd_5430056 : Nat := 4983230072969 + 3 ^ 40 * 5430056 * 2
def baseEnd_5430056 : Nat := 2788228708830512114627633

theorem tailTrace_5430056 : CollatzResearch.WordTrace tailWord_5430056 prefixEnd_5430056 2788228708830512114627633 := by
  unfold tailWord_5430056
  simp only [CollatzResearch.WordTrace]
  refine ⟨99025206407920983288719011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132033608543894644384958681 99025206407920983288719011)
  ·
    refine ⟨148537809611881474933078517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99025206407920983288719011 148537809611881474933078517)
    ·
      refine ⟨13925419651113888274976111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148537809611881474933078517 13925419651113888274976111)
      ·
        refine ⟨20888129476670832412464167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13925419651113888274976111 20888129476670832412464167)
        ·
          refine ⟨31332194215006248618696251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20888129476670832412464167 31332194215006248618696251)
          ·
            refine ⟨46998291322509372928044377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31332194215006248618696251 46998291322509372928044377)
            ·
              refine ⟨35248718491882029696033283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46998291322509372928044377 35248718491882029696033283)
              ·
                refine ⟨52873077737823044544049925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35248718491882029696033283 52873077737823044544049925)
                ·
                  refine ⟨9913702075841820852009361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52873077737823044544049925 9913702075841820852009361)
                  ·
                    refine ⟨7435276556881365639007021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9913702075841820852009361 7435276556881365639007021)
                    ·
                      refine ⟨2788228708830512114627633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7435276556881365639007021 2788228708830512114627633)
                      ·
                        rfl

theorem cell23_5430056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_5430056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430056 prefixEnd_5430056 := by exact prefixLift 5430056
  have htrace : WordTrace (prefixWord ++ tailWord_5430056) baseStart_5430056 baseEnd_5430056 := by
    simpa [prefixWord, tailWord_5430056, baseEnd_5430056] using wordTrace_append hprefix tailTrace_5430056
  have hstable : (prefixWord ++ tailWord_5430056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430056).length < 2 ^ (prefixWord ++ tailWord_5430056).sum := by decide
  have hdescent : baseEnd_5430056 < baseStart_5430056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430096 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 1, 5, 2]
def baseStart_5430096 : Nat := 118140960795 + 5430096 * 2 ^ 59
def prefixEnd_5430096 : Nat := 4983230072969 + 3 ^ 40 * 5430096 * 2
def baseEnd_5430096 : Nat := 2788249248056691958127449

theorem tailTrace_5430096 : CollatzResearch.WordTrace tailWord_5430096 prefixEnd_5430096 2788249248056691958127449 := by
  unfold tailWord_5430096
  simp only [CollatzResearch.WordTrace]
  refine ⟨99025935867848526704447071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132034581157131368939262761 99025935867848526704447071)
  ·
    refine ⟨148538903801772790056670607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99025935867848526704447071 148538903801772790056670607)
    ·
      refine ⟨222808355702659185085005911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148538903801772790056670607 222808355702659185085005911)
      ·
        refine ⟨334212533553988777627508867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222808355702659185085005911 334212533553988777627508867)
        ·
          refine ⟨501318800330983166441263301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334212533553988777627508867 501318800330983166441263301)
          ·
            refine ⟨93997275062059343707736869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 501318800330983166441263301 93997275062059343707736869)
            ·
              refine ⟨17624489074136126945200663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93997275062059343707736869 17624489074136126945200663)
              ·
                refine ⟨26436733611204190417800995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17624489074136126945200663 26436733611204190417800995)
                ·
                  refine ⟨39655100416806285626701493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26436733611204190417800995 39655100416806285626701493)
                  ·
                    refine ⟨3717665664075589277503265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39655100416806285626701493 3717665664075589277503265)
                    ·
                      refine ⟨2788249248056691958127449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717665664075589277503265 2788249248056691958127449)
                      ·
                        rfl

theorem cell23_5430096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 5, 2].length) (baseStart_5430096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430096 prefixEnd_5430096 := by exact prefixLift 5430096
  have htrace : WordTrace (prefixWord ++ tailWord_5430096) baseStart_5430096 baseEnd_5430096 := by
    simpa [prefixWord, tailWord_5430096, baseEnd_5430096] using wordTrace_append hprefix tailTrace_5430096
  have hstable : (prefixWord ++ tailWord_5430096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430096).length < 2 ^ (prefixWord ++ tailWord_5430096).sum := by decide
  have hdescent : baseEnd_5430096 < baseStart_5430096 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430097 : List Nat := [1, 2, 2, 1, 7, 1, 1, 3, 1, 4]
def baseStart_5430097 : Nat := 118140960795 + 5430097 * 2 ^ 59
def prefixEnd_5430097 : Nat := 4983230072969 + 3 ^ 40 * 5430097 * 2
def baseEnd_5430097 : Nat := 929416587179115484738315

theorem tailTrace_5430097 : CollatzResearch.WordTrace tailWord_5430097 prefixEnd_5430097 929416587179115484738315 := by
  unfold tailWord_5430097
  simp only [CollatzResearch.WordTrace]
  refine ⟨198051908208693430579680545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132034605472462287053120363 198051908208693430579680545)
  ·
    refine ⟨148538931156520072934760409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198051908208693430579680545 148538931156520072934760409)
    ·
      refine ⟨111404198367390054701070307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148538931156520072934760409 111404198367390054701070307)
      ·
        refine ⟨167106297551085082051605461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111404198367390054701070307 167106297551085082051605461)
        ·
          refine ⟨3916553848853556610584503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 167106297551085082051605461 3916553848853556610584503)
          ·
            refine ⟨5874830773280334915876755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916553848853556610584503 5874830773280334915876755)
            ·
              refine ⟨8812246159920502373815133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874830773280334915876755 8812246159920502373815133)
              ·
                refine ⟨3304592309970188390180675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8812246159920502373815133 3304592309970188390180675)
                ·
                  refine ⟨4956888464955282585271013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3304592309970188390180675 4956888464955282585271013)
                  ·
                    refine ⟨929416587179115484738315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956888464955282585271013 929416587179115484738315)
                    ·
                      rfl

theorem cell23_5430097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 3, 1, 4].length) (baseStart_5430097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430097 prefixEnd_5430097 := by exact prefixLift 5430097
  have htrace : WordTrace (prefixWord ++ tailWord_5430097) baseStart_5430097 baseEnd_5430097 := by
    simpa [prefixWord, tailWord_5430097, baseEnd_5430097] using wordTrace_append hprefix tailTrace_5430097
  have hstable : (prefixWord ++ tailWord_5430097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430097).length < 2 ^ (prefixWord ++ tailWord_5430097).sum := by decide
  have hdescent : baseEnd_5430097 < baseStart_5430097 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430106 : List Nat := [3, 1, 1, 2, 1, 4, 2, 3, 1, 5]
def baseStart_5430106 : Nat := 118140960795 + 5430106 * 2 ^ 59
def prefixEnd_5430106 : Nat := 4983230072969 + 3 ^ 40 * 5430106 * 2
def baseEnd_5430106 : Nat := 929418127621078973000801

theorem tailTrace_5430106 : CollatzResearch.WordTrace tailWord_5430106 prefixEnd_5430106 929418127621078973000801 := by
  unfold tailWord_5430106
  simp only [CollatzResearch.WordTrace]
  refine ⟨49513059116415206279189543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132034824310440550077838781 49513059116415206279189543)
  ·
    refine ⟨74269588674622809418784315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49513059116415206279189543 74269588674622809418784315)
    ·
      refine ⟨111404383011934214128176473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74269588674622809418784315 111404383011934214128176473)
      ·
        refine ⟨83553287258950660596132355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111404383011934214128176473 83553287258950660596132355)
        ·
          refine ⟨125329930888425990894198533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83553287258950660596132355 125329930888425990894198533)
          ·
            refine ⟨23499362041579873292662225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125329930888425990894198533 23499362041579873292662225)
            ·
              refine ⟨17624521531184904969496669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23499362041579873292662225 17624521531184904969496669)
              ·
                refine ⟨6609195574194339363561251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17624521531184904969496669 6609195574194339363561251)
                ·
                  refine ⟨9913793361291509045341877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609195574194339363561251 9913793361291509045341877)
                  ·
                    refine ⟨929418127621078973000801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9913793361291509045341877 929418127621078973000801)
                    ·
                      rfl

theorem cell23_5430106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 3, 1, 5].length) (baseStart_5430106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430106 prefixEnd_5430106 := by exact prefixLift 5430106
  have htrace : WordTrace (prefixWord ++ tailWord_5430106) baseStart_5430106 baseEnd_5430106 := by
    simpa [prefixWord, tailWord_5430106, baseEnd_5430106] using wordTrace_append hprefix tailTrace_5430106
  have hstable : (prefixWord ++ tailWord_5430106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430106).length < 2 ^ (prefixWord ++ tailWord_5430106).sum := by decide
  have hdescent : baseEnd_5430106 < baseStart_5430106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430120 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 3, 1, 3]
def baseStart_5430120 : Nat := 118140960795 + 5430120 * 2 ^ 59
def prefixEnd_5430120 : Nat := 4983230072969 + 3 ^ 40 * 5430120 * 2
def baseEnd_5430120 : Nat := 2788261571592399864227339

theorem tailTrace_5430120 : CollatzResearch.WordTrace tailWord_5430120 prefixEnd_5430120 2788261571592399864227339 := by
  unfold tailWord_5430120
  simp only [CollatzResearch.WordTrace]
  refine ⟨99026373543805052753883907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132035164725073403671845209 99026373543805052753883907)
  ·
    refine ⟨148539560315707579130825861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99026373543805052753883907 148539560315707579130825861)
    ·
      refine ⟨27851167559195171087029849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148539560315707579130825861 27851167559195171087029849)
      ·
        refine ⟨20888375669396378315272387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27851167559195171087029849 20888375669396378315272387)
        ·
          refine ⟨31332563504094567472908581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20888375669396378315272387 31332563504094567472908581)
          ·
            refine ⟨5874855657017731401170359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31332563504094567472908581 5874855657017731401170359)
            ·
              refine ⟨8812283485526597101755539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874855657017731401170359 8812283485526597101755539)
              ·
                refine ⟨13218425228289895652633309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8812283485526597101755539 13218425228289895652633309)
                ·
                  refine ⟨4956909460608710869737491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13218425228289895652633309 4956909460608710869737491)
                  ·
                    refine ⟨7435364190913066304606237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4956909460608710869737491 7435364190913066304606237)
                    ·
                      refine ⟨2788261571592399864227339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7435364190913066304606237 2788261571592399864227339)
                      ·
                        rfl

theorem cell23_5430120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_5430120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430120 prefixEnd_5430120 := by exact prefixLift 5430120
  have htrace : WordTrace (prefixWord ++ tailWord_5430120) baseStart_5430120 baseEnd_5430120 := by
    simpa [prefixWord, tailWord_5430120, baseEnd_5430120] using wordTrace_append hprefix tailTrace_5430120
  have hstable : (prefixWord ++ tailWord_5430120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430120).length < 2 ^ (prefixWord ++ tailWord_5430120).sum := by decide
  have hdescent : baseEnd_5430120 < baseStart_5430120 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430139 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6]
def baseStart_5430139 : Nat := 118140960795 + 5430139 * 2 ^ 59
def prefixEnd_5430139 : Nat := 4983230072969 + 3 ^ 40 * 5430139 * 2
def baseEnd_5430139 : Nat := 2788271327724835289889751

theorem tailTrace_5430139 : CollatzResearch.WordTrace tailWord_5430139 prefixEnd_5430139 2788271327724835289889751 := by
  unfold tailWord_5430139
  simp only [CollatzResearch.WordTrace]
  refine ⟨198053440074541271752709471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132035626716360847835139647 198053440074541271752709471)
  ·
    refine ⟨297080160111811907629064207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198053440074541271752709471 297080160111811907629064207)
    ·
      refine ⟨445620240167717861443596311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297080160111811907629064207 445620240167717861443596311)
      ·
        refine ⟨668430360251576792165394467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445620240167717861443596311 668430360251576792165394467)
        ·
          refine ⟨1002645540377365188248091701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668430360251576792165394467 1002645540377365188248091701)
          ·
            refine ⟨93998019410377986398258597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1002645540377365188248091701 93998019410377986398258597)
            ·
              refine ⟨17624628639445872449673487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 93998019410377986398258597 17624628639445872449673487)
              ·
                refine ⟨26436942959168808674510231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17624628639445872449673487 26436942959168808674510231)
                ·
                  refine ⟨39655414438753213011765347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26436942959168808674510231 39655414438753213011765347)
                  ·
                    refine ⟨59483121658129819517648021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39655414438753213011765347 59483121658129819517648021)
                    ·
                      refine ⟨2788271327724835289889751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59483121658129819517648021 2788271327724835289889751)
                      ·
                        rfl

theorem cell23_5430139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 1, 1, 6].length) (baseStart_5430139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430139 prefixEnd_5430139 := by exact prefixLift 5430139
  have htrace : WordTrace (prefixWord ++ tailWord_5430139) baseStart_5430139 baseEnd_5430139 := by
    simpa [prefixWord, tailWord_5430139, baseEnd_5430139] using wordTrace_append hprefix tailTrace_5430139
  have hstable : (prefixWord ++ tailWord_5430139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430139).length < 2 ^ (prefixWord ++ tailWord_5430139).sum := by decide
  have hdescent : baseEnd_5430139 < baseStart_5430139 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430143 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 3, 2, 2]
def baseStart_5430143 : Nat := 118140960795 + 5430143 * 2 ^ 59
def prefixEnd_5430143 : Nat := 4983230072969 + 3 ^ 40 * 5430143 * 2
def baseEnd_5430143 : Nat := 2788273381647453274239733

theorem tailTrace_5430143 : CollatzResearch.WordTrace tailWord_5430143 prefixEnd_5430143 2788273381647453274239733 := by
  unfold tailWord_5430143
  simp only [CollatzResearch.WordTrace]
  refine ⟨198053585966526780435855083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132035723977684520290570055 198053585966526780435855083)
  ·
    refine ⟨297080378949790170653782625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198053585966526780435855083 297080378949790170653782625)
    ·
      refine ⟨222810284212342627990336969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297080378949790170653782625 222810284212342627990336969)
      ·
        refine ⟨167107713159256970992752727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222810284212342627990336969 167107713159256970992752727)
        ·
          refine ⟨250661569738885456489129091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167107713159256970992752727 250661569738885456489129091)
          ·
            refine ⟨375992354608328184733693637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250661569738885456489129091 375992354608328184733693637)
            ·
              refine ⟨70498566489061534637567557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 375992354608328184733693637 70498566489061534637567557)
              ·
                refine ⟨13218481216699037744543917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70498566489061534637567557 13218481216699037744543917)
                ·
                  refine ⟨4956930456262139154203969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13218481216699037744543917 4956930456262139154203969)
                  ·
                    refine ⟨3717697842196604365652977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4956930456262139154203969 3717697842196604365652977)
                    ·
                      refine ⟨2788273381647453274239733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717697842196604365652977 2788273381647453274239733)
                      ·
                        rfl

theorem cell23_5430143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_5430143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430143 prefixEnd_5430143 := by exact prefixLift 5430143
  have htrace : WordTrace (prefixWord ++ tailWord_5430143) baseStart_5430143 baseEnd_5430143 := by
    simpa [prefixWord, tailWord_5430143, baseEnd_5430143] using wordTrace_append hprefix tailTrace_5430143
  have hstable : (prefixWord ++ tailWord_5430143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430143).length < 2 ^ (prefixWord ++ tailWord_5430143).sum := by decide
  have hdescent : baseEnd_5430143 < baseStart_5430143 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430149 : List Nat := [1, 3, 1, 1, 3, 3, 2, 9]
def baseStart_5430149 : Nat := 118140960795 + 5430149 * 2 ^ 59
def prefixEnd_5430149 : Nat := 4983230072969 + 3 ^ 40 * 5430149 * 2
def baseEnd_5430149 : Nat := 103269498612273342620915

theorem tailTrace_5430149 : CollatzResearch.WordTrace tailWord_5430149 prefixEnd_5430149 103269498612273342620915 := by
  unfold tailWord_5430149
  simp only [CollatzResearch.WordTrace]
  refine ⟨198053804804505043460573501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132035869869670028973715667 198053804804505043460573501)
  ·
    refine ⟨74270176801689391297715063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198053804804505043460573501 74270176801689391297715063)
    ·
      refine ⟨111405265202534086946572595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74270176801689391297715063 111405265202534086946572595)
      ·
        refine ⟨167107897803801130419858893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111405265202534086946572595 167107897803801130419858893)
        ·
          refine ⟨62665461676425423907447085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167107897803801130419858893 62665461676425423907447085)
          ·
            refine ⟨23499548128659533965292657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62665461676425423907447085 23499548128659533965292657)
            ·
              refine ⟨17624661096494650473969493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23499548128659533965292657 17624661096494650473969493)
              ·
                refine ⟨103269498612273342620915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 17624661096494650473969493 103269498612273342620915)
                ·
                  rfl

theorem cell23_5430149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 9].length) (baseStart_5430149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430149 prefixEnd_5430149 := by exact prefixLift 5430149
  have htrace : WordTrace (prefixWord ++ tailWord_5430149) baseStart_5430149 baseEnd_5430149 := by
    simpa [prefixWord, tailWord_5430149, baseEnd_5430149] using wordTrace_append hprefix tailTrace_5430149
  have hstable : (prefixWord ++ tailWord_5430149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430149).length < 2 ^ (prefixWord ++ tailWord_5430149).sum := by decide
  have hdescent : baseEnd_5430149 < baseStart_5430149 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430170 : List Nat := [3, 1, 1, 4, 3, 1, 2, 2, 2, 4]
def baseStart_5430170 : Nat := 118140960795 + 5430170 * 2 ^ 59
def prefixEnd_5430170 : Nat := 4983230072969 + 3 ^ 40 * 5430170 * 2
def baseEnd_5430170 : Nat := 929429081875041556200703

theorem tailTrace_5430170 : CollatzResearch.WordTrace tailWord_5430170 prefixEnd_5430170 929429081875041556200703 := by
  unfold tailWord_5430170
  simp only [CollatzResearch.WordTrace]
  refine ⟨49513642684357241011771991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132036380491619309364725309 49513642684357241011771991)
  ·
    refine ⟨74270464026535861517657987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49513642684357241011771991 74270464026535861517657987)
    ·
      refine ⟨111405696039803792276486981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74270464026535861517657987 111405696039803792276486981)
      ·
        refine ⟨20888568007463211051841309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111405696039803792276486981 20888568007463211051841309)
        ·
          refine ⟨7833213002798704144440491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20888568007463211051841309 7833213002798704144440491)
          ·
            refine ⟨11749819504198056216660737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833213002798704144440491 11749819504198056216660737)
            ·
              refine ⟨8812364628148542162495553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11749819504198056216660737 8812364628148542162495553)
              ·
                refine ⟨6609273471111406621871665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8812364628148542162495553 6609273471111406621871665)
                ·
                  refine ⟨4956955103333554966403749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6609273471111406621871665 4956955103333554966403749)
                  ·
                    refine ⟨929429081875041556200703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4956955103333554966403749 929429081875041556200703)
                    ·
                      rfl

theorem cell23_5430170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 2, 2, 4].length) (baseStart_5430170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430170 prefixEnd_5430170 := by exact prefixLift 5430170
  have htrace : WordTrace (prefixWord ++ tailWord_5430170) baseStart_5430170 baseEnd_5430170 := by
    simpa [prefixWord, tailWord_5430170, baseEnd_5430170] using wordTrace_append hprefix tailTrace_5430170
  have hstable : (prefixWord ++ tailWord_5430170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430170).length < 2 ^ (prefixWord ++ tailWord_5430170).sum := by decide
  have hdescent : baseEnd_5430170 < baseStart_5430170 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430179 : List Nat := [1, 1, 1, 4, 1, 2, 3, 1, 2, 7]
def baseStart_5430179 : Nat := 118140960795 + 5430179 * 2 ^ 59
def prefixEnd_5430179 : Nat := 4983230072969 + 3 ^ 40 * 5430179 * 2
def baseEnd_5430179 : Nat := 929430622317005044463189

theorem tailTrace_5430179 : CollatzResearch.WordTrace tailWord_5430179 prefixEnd_5430179 929430622317005044463189 := by
  unfold tailWord_5430179
  simp only [CollatzResearch.WordTrace]
  refine ⟨198054898994396358584165591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132036599329597572389443727 198054898994396358584165591)
  ·
    refine ⟨297082348491594537876248387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198054898994396358584165591 297082348491594537876248387)
    ·
      refine ⟨445623522737391806814372581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297082348491594537876248387 445623522737391806814372581)
      ·
        refine ⟨83554410513260963777694859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 445623522737391806814372581 83554410513260963777694859)
        ·
          refine ⟨125331615769891445666542289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83554410513260963777694859 125331615769891445666542289)
          ·
            refine ⟨93998711827418584249906717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125331615769891445666542289 93998711827418584249906717)
            ·
              refine ⟨35249516935281969093715019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 93998711827418584249906717 35249516935281969093715019)
              ·
                refine ⟨52874275402922953640572529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35249516935281969093715019 52874275402922953640572529)
                ·
                  refine ⟨39655706552192215230429397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52874275402922953640572529 39655706552192215230429397)
                  ·
                    refine ⟨929430622317005044463189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39655706552192215230429397 929430622317005044463189)
                    ·
                      rfl

theorem cell23_5430179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 7].length) (baseStart_5430179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430179 prefixEnd_5430179 := by exact prefixLift 5430179
  have htrace : WordTrace (prefixWord ++ tailWord_5430179) baseStart_5430179 baseEnd_5430179 := by
    simpa [prefixWord, tailWord_5430179, baseEnd_5430179] using wordTrace_append hprefix tailTrace_5430179
  have hstable : (prefixWord ++ tailWord_5430179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430179).length < 2 ^ (prefixWord ++ tailWord_5430179).sum := by decide
  have hdescent : baseEnd_5430179 < baseStart_5430179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430183 : List Nat := [1, 1, 6, 1, 3, 2, 1, 8]
def baseStart_5430183 : Nat := 118140960795 + 5430183 * 2 ^ 59
def prefixEnd_5430183 : Nat := 4983230072969 + 3 ^ 40 * 5430183 * 2
def baseEnd_5430183 : Nat := 103270145217541967323687

theorem tailTrace_5430183 : CollatzResearch.WordTrace tailWord_5430183 prefixEnd_5430183 103270145217541967323687 := by
  unfold tailWord_5430183
  simp only [CollatzResearch.WordTrace]
  refine ⟨198055044886381867267311203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132036696590921244844874135 198055044886381867267311203)
  ·
    refine ⟨297082567329572800900966805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198055044886381867267311203 297082567329572800900966805)
    ·
      refine ⟨13925745343573725042232819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 297082567329572800900966805 13925745343573725042232819)
      ·
        refine ⟨20888618015360587563349229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13925745343573725042232819 20888618015360587563349229)
        ·
          refine ⟨7833231755760220336255961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20888618015360587563349229 7833231755760220336255961)
          ·
            refine ⟨5874923816820165252191971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7833231755760220336255961 5874923816820165252191971)
            ·
              refine ⟨8812385725230247878287957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874923816820165252191971 8812385725230247878287957)
              ·
                refine ⟨103270145217541967323687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8812385725230247878287957 103270145217541967323687)
                ·
                  rfl

theorem cell23_5430183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 1, 8].length) (baseStart_5430183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430183 prefixEnd_5430183 := by exact prefixLift 5430183
  have htrace : WordTrace (prefixWord ++ tailWord_5430183) baseStart_5430183 baseEnd_5430183 := by
    simpa [prefixWord, tailWord_5430183, baseEnd_5430183] using wordTrace_append hprefix tailTrace_5430183
  have hstable : (prefixWord ++ tailWord_5430183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430183).length < 2 ^ (prefixWord ++ tailWord_5430183).sum := by decide
  have hdescent : baseEnd_5430183 < baseStart_5430183 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430198 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5430198 : Nat := 118140960795 + 5430198 * 2 ^ 59
def prefixEnd_5430198 : Nat := 4983230072969 + 3 ^ 40 * 5430198 * 2
def baseEnd_5430198 : Nat := 2788301623083450559051981

theorem tailTrace_5430198 : CollatzResearch.WordTrace tailWord_5430198 prefixEnd_5430198 2788301623083450559051981 := by
  unfold tailWord_5430198
  simp only [CollatzResearch.WordTrace]
  refine ⟨12378474498832970301819203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132037061320885016552738165 12378474498832970301819203)
  ·
    refine ⟨18567711748249455452728805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12378474498832970301819203 18567711748249455452728805)
    ·
      refine ⟨3481445952796772897386651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18567711748249455452728805 3481445952796772897386651)
      ·
        refine ⟨5222168929195159346079977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481445952796772897386651 5222168929195159346079977)
        ·
          refine ⟨3916626696896369509559983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5222168929195159346079977 3916626696896369509559983)
          ·
            refine ⟨5874940045344554264339975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3916626696896369509559983 5874940045344554264339975)
            ·
              refine ⟨8812410068016831396509963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874940045344554264339975 8812410068016831396509963)
              ·
                refine ⟨13218615102025247094764945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8812410068016831396509963 13218615102025247094764945)
                ·
                  refine ⟨9913961326518935321073709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13218615102025247094764945 9913961326518935321073709)
                  ·
                    refine ⟨3717735497444600745402641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9913961326518935321073709 3717735497444600745402641)
                    ·
                      refine ⟨2788301623083450559051981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717735497444600745402641 2788301623083450559051981)
                      ·
                        rfl

theorem cell23_5430198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5430198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430198 prefixEnd_5430198 := by exact prefixLift 5430198
  have htrace : WordTrace (prefixWord ++ tailWord_5430198) baseStart_5430198 baseEnd_5430198 := by
    simpa [prefixWord, tailWord_5430198, baseEnd_5430198] using wordTrace_append hprefix tailTrace_5430198
  have hstable : (prefixWord ++ tailWord_5430198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430198).length < 2 ^ (prefixWord ++ tailWord_5430198).sum := by decide
  have hdescent : baseEnd_5430198 < baseStart_5430198 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430206 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5]
def baseStart_5430206 : Nat := 118140960795 + 5430206 * 2 ^ 59
def prefixEnd_5430206 : Nat := 4983230072969 + 3 ^ 40 * 5430206 * 2
def baseEnd_5430206 : Nat := 2788305730928686527751943

theorem tailTrace_5430206 : CollatzResearch.WordTrace tailWord_5430206 prefixEnd_5430206 2788305730928686527751943 := by
  unfold tailWord_5430206
  simp only [CollatzResearch.WordTrace]
  refine ⟨24756985470662317774424809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132037255843532361463598981 24756985470662317774424809)
  ·
    refine ⟨18567739102996738330818607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24756985470662317774424809 18567739102996738330818607)
    ·
      refine ⟨27851608654495107496227911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18567739102996738330818607 27851608654495107496227911)
      ·
        refine ⟨41777412981742661244341867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27851608654495107496227911 41777412981742661244341867)
        ·
          refine ⟨62666119472613991866512801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41777412981742661244341867 62666119472613991866512801)
          ·
            refine ⟨46999589604460493899884601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62666119472613991866512801 46999589604460493899884601)
            ·
              refine ⟨35249692203345370424913451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 46999589604460493899884601 35249692203345370424913451)
              ·
                refine ⟨52874538305018055637370177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35249692203345370424913451 52874538305018055637370177)
                ·
                  refine ⟨39655903728763541728027633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52874538305018055637370177 39655903728763541728027633)
                  ·
                    refine ⟨29741927796572656296020725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39655903728763541728027633 29741927796572656296020725)
                    ·
                      refine ⟨2788305730928686527751943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29741927796572656296020725 2788305730928686527751943)
                      ·
                        rfl

theorem cell23_5430206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_5430206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430206 prefixEnd_5430206 := by exact prefixLift 5430206
  have htrace : WordTrace (prefixWord ++ tailWord_5430206) baseStart_5430206 baseEnd_5430206 := by
    simpa [prefixWord, tailWord_5430206, baseEnd_5430206] using wordTrace_append hprefix tailTrace_5430206
  have hstable : (prefixWord ++ tailWord_5430206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430206).length < 2 ^ (prefixWord ++ tailWord_5430206).sum := by decide
  have hdescent : baseEnd_5430206 < baseStart_5430206 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430220 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 1, 3, 2]
def baseStart_5430220 : Nat := 118140960795 + 5430220 * 2 ^ 59
def prefixEnd_5430220 : Nat := 4983230072969 + 3 ^ 40 * 5430220 * 2
def baseEnd_5430220 : Nat := 2788312919657849472976879

theorem tailTrace_5430220 : CollatzResearch.WordTrace tailWord_5430220 prefixEnd_5430220 2788312919657849472976879 := by
  unfold tailWord_5430220
  simp only [CollatzResearch.WordTrace]
  refine ⟨99028197193623911293204057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132037596258165215057605409 99028197193623911293204057)
  ·
    refine ⟨74271147895217933469903043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99028197193623911293204057 74271147895217933469903043)
    ·
      refine ⟨111406721842826900204854565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74271147895217933469903043 111406721842826900204854565)
      ·
        refine ⟨20888760345530043788410231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 111406721842826900204854565 20888760345530043788410231)
        ·
          refine ⟨31333140518295065682615347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20888760345530043788410231 31333140518295065682615347)
          ·
            refine ⟨46999710777442598523923021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31333140518295065682615347 46999710777442598523923021)
            ·
              refine ⟨17624891541540974446471133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 46999710777442598523923021 17624891541540974446471133)
              ·
                refine ⟨6609334328077865417426675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17624891541540974446471133 6609334328077865417426675)
                ·
                  refine ⟨9914001492116798126140013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609334328077865417426675 9914001492116798126140013)
                  ·
                    refine ⟨3717750559543799297302505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9914001492116798126140013 3717750559543799297302505)
                    ·
                      refine ⟨2788312919657849472976879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717750559543799297302505 2788312919657849472976879)
                      ·
                        rfl

theorem cell23_5430220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_5430220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430220 prefixEnd_5430220 := by exact prefixLift 5430220
  have htrace : WordTrace (prefixWord ++ tailWord_5430220) baseStart_5430220 baseEnd_5430220 := by
    simpa [prefixWord, tailWord_5430220, baseEnd_5430220] using wordTrace_append hprefix tailTrace_5430220
  have hstable : (prefixWord ++ tailWord_5430220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430220).length < 2 ^ (prefixWord ++ tailWord_5430220).sum := by decide
  have hdescent : baseEnd_5430220 < baseStart_5430220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430221 : List Nat := [1, 6, 3, 1, 1, 2, 1, 2, 2, 4]
def baseStart_5430221 : Nat := 118140960795 + 5430221 * 2 ^ 59
def prefixEnd_5430221 : Nat := 4983230072969 + 3 ^ 40 * 5430221 * 2
def baseEnd_5430221 : Nat := 929437811046167989688125

theorem tailTrace_5430221 : CollatzResearch.WordTrace tailWord_5430221 prefixEnd_5430221 929437811046167989688125 := by
  unfold tailWord_5430221
  simp only [CollatzResearch.WordTrace]
  refine ⟨198056430860244199757194517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132037620573496133171463011 198056430860244199757194517)
  ·
    refine ⟨9283895196573946863618493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198056430860244199757194517 9283895196573946863618493)
    ·
      refine ⟨3481460698715230073856935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9283895196573946863618493 3481460698715230073856935)
      ·
        refine ⟨5222191048072845110785403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481460698715230073856935 5222191048072845110785403)
        ·
          refine ⟨7833286572109267666178105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222191048072845110785403 7833286572109267666178105)
          ·
            refine ⟨5874964929081950749633579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7833286572109267666178105 5874964929081950749633579)
            ·
              refine ⟨8812447393622926124450369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5874964929081950749633579 8812447393622926124450369)
              ·
                refine ⟨6609335545217194593337777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8812447393622926124450369 6609335545217194593337777)
                ·
                  refine ⟨4957001658912895945003333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6609335545217194593337777 4957001658912895945003333)
                  ·
                    refine ⟨929437811046167989688125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4957001658912895945003333 929437811046167989688125)
                    ·
                      rfl

theorem cell23_5430221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_5430221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430221 prefixEnd_5430221 := by exact prefixLift 5430221
  have htrace : WordTrace (prefixWord ++ tailWord_5430221) baseStart_5430221 baseEnd_5430221 := by
    simpa [prefixWord, tailWord_5430221, baseEnd_5430221] using wordTrace_append hprefix tailTrace_5430221
  have hstable : (prefixWord ++ tailWord_5430221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430221).length < 2 ^ (prefixWord ++ tailWord_5430221).sum := by decide
  have hdescent : baseEnd_5430221 < baseStart_5430221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430249 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 9]
def baseStart_5430249 : Nat := 118140960795 + 5430249 * 2 ^ 59
def prefixEnd_5430249 : Nat := 4983230072969 + 3 ^ 40 * 5430249 * 2
def baseEnd_5430249 : Nat := 2788327810596829859514245

theorem tailTrace_5430249 : CollatzResearch.WordTrace tailWord_5430249 prefixEnd_5430249 2788327810596829859514245 := by
  unfold tailWord_5430249
  simp only [CollatzResearch.WordTrace]
  refine ⟨198057452104142760539213801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132038301402761840359475867 198057452104142760539213801)
  ·
    refine ⟨148543089078107070404410351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198057452104142760539213801 148543089078107070404410351)
    ·
      refine ⟨222814633617160605606615527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148543089078107070404410351 222814633617160605606615527)
      ·
        refine ⟨334221950425740908409923291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222814633617160605606615527 334221950425740908409923291)
        ·
          refine ⟨501332925638611362614884937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334221950425740908409923291 501332925638611362614884937)
          ·
            refine ⟨375999694228958521961163703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501332925638611362614884937 375999694228958521961163703)
            ·
              refine ⟨563999541343437782941745555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 375999694228958521961163703 563999541343437782941745555)
              ·
                refine ⟨845999312015156674412618333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 563999541343437782941745555 845999312015156674412618333)
                ·
                  refine ⟨317249742005683752904731875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 845999312015156674412618333 317249742005683752904731875)
                  ·
                    refine ⟨475874613008525629357097813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 317249742005683752904731875 475874613008525629357097813)
                    ·
                      refine ⟨2788327810596829859514245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 475874613008525629357097813 2788327810596829859514245)
                      ·
                        rfl

theorem cell23_5430249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 3, 1, 9].length) (baseStart_5430249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430249 prefixEnd_5430249 := by exact prefixLift 5430249
  have htrace : WordTrace (prefixWord ++ tailWord_5430249) baseStart_5430249 baseEnd_5430249 := by
    simpa [prefixWord, tailWord_5430249, baseEnd_5430249] using wordTrace_append hprefix tailTrace_5430249
  have hstable : (prefixWord ++ tailWord_5430249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430249).length < 2 ^ (prefixWord ++ tailWord_5430249).sum := by decide
  have hdescent : baseEnd_5430249 < baseStart_5430249 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430250 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_5430250 : Nat := 118140960795 + 5430250 * 2 ^ 59
def prefixEnd_5430250 : Nat := 4983230072969 + 3 ^ 40 * 5430250 * 2
def baseEnd_5430250 : Nat := 2788328324077484355601741

theorem tailTrace_5430250 : CollatzResearch.WordTrace tailWord_5430250 prefixEnd_5430250 2788328324077484355601741 := by
  unfold tailWord_5430250
  simp only [CollatzResearch.WordTrace]
  refine ⟨49514372144284784427500051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132038325718092758473333469 49514372144284784427500051)
  ·
    refine ⟨74271558216427176641250077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49514372144284784427500051 74271558216427176641250077)
    ·
      refine ⟨27851834331160191240468779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74271558216427176641250077 27851834331160191240468779)
      ·
        refine ⟨41777751496740286860703169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27851834331160191240468779 41777751496740286860703169)
        ·
          refine ⟨31333313622555215145527377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41777751496740286860703169 31333313622555215145527377)
          ·
            refine ⟨23499985216916411359145533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31333313622555215145527377 23499985216916411359145533)
            ·
              refine ⟨8812494456343654259679575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23499985216916411359145533 8812494456343654259679575)
              ·
                refine ⟨13218741684515481389519363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8812494456343654259679575 13218741684515481389519363)
                ·
                  refine ⟨19828112526773222084279045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13218741684515481389519363 19828112526773222084279045)
                  ·
                    refine ⟨3717771098769979140802321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19828112526773222084279045 3717771098769979140802321)
                    ·
                      refine ⟨2788328324077484355601741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717771098769979140802321 2788328324077484355601741)
                      ·
                        rfl

theorem cell23_5430250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_5430250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430250 prefixEnd_5430250 := by exact prefixLift 5430250
  have htrace : WordTrace (prefixWord ++ tailWord_5430250) baseStart_5430250 baseEnd_5430250 := by
    simpa [prefixWord, tailWord_5430250, baseEnd_5430250] using wordTrace_append hprefix tailTrace_5430250
  have hstable : (prefixWord ++ tailWord_5430250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430250).length < 2 ^ (prefixWord ++ tailWord_5430250).sum := by decide
  have hdescent : baseEnd_5430250 < baseStart_5430250 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430266 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3]
def baseStart_5430266 : Nat := 118140960795 + 5430266 * 2 ^ 59
def prefixEnd_5430266 : Nat := 4983230072969 + 3 ^ 40 * 5430266 * 2
def baseEnd_5430266 : Nat := 2788336539767956293001667

theorem tailTrace_5430266 : CollatzResearch.WordTrace tailWord_5430266 prefixEnd_5430266 2788336539767956293001667 := by
  unfold tailWord_5430266
  simp only [CollatzResearch.WordTrace]
  refine ⟨49514518036270293110645663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132038714763387448295055101 49514518036270293110645663)
  ·
    refine ⟨74271777054405439665968495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49514518036270293110645663 74271777054405439665968495)
    ·
      refine ⟨111407665581608159498952743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74271777054405439665968495 111407665581608159498952743)
      ·
        refine ⟨167111498372412239248429115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111407665581608159498952743 167111498372412239248429115)
        ·
          refine ⟨250667247558618358872643673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167111498372412239248429115 250667247558618358872643673)
          ·
            refine ⟨188000435668963769154482755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250667247558618358872643673 188000435668963769154482755)
            ·
              refine ⟨282000653503445653731724133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188000435668963769154482755 282000653503445653731724133)
              ·
                refine ⟨52875122531896060074698275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282000653503445653731724133 52875122531896060074698275)
                ·
                  refine ⟨79312683797844090112047413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52875122531896060074698275 79312683797844090112047413)
                  ·
                    refine ⟨7435564106047883448004445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79312683797844090112047413 7435564106047883448004445)
                    ·
                      refine ⟨2788336539767956293001667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7435564106047883448004445 2788336539767956293001667)
                      ·
                        rfl

theorem cell23_5430266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 1, 5, 3].length) (baseStart_5430266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430266 prefixEnd_5430266 := by exact prefixLift 5430266
  have htrace : WordTrace (prefixWord ++ tailWord_5430266) baseStart_5430266 baseEnd_5430266 := by
    simpa [prefixWord, tailWord_5430266, baseEnd_5430266] using wordTrace_append hprefix tailTrace_5430266
  have hstable : (prefixWord ++ tailWord_5430266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430266).length < 2 ^ (prefixWord ++ tailWord_5430266).sum := by decide
  have hdescent : baseEnd_5430266 < baseStart_5430266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430270 : List Nat := [4, 2, 2, 2, 2, 1, 1, 1, 2, 1, 5]
def baseStart_5430270 : Nat := 118140960795 + 5430270 * 2 ^ 59
def prefixEnd_5430270 : Nat := 4983230072969 + 3 ^ 40 * 5430270 * 2
def baseEnd_5430270 : Nat := 2788338593690574277351649

theorem tailTrace_5430270 : CollatzResearch.WordTrace tailWord_5430270 prefixEnd_5430270 2788338593690574277351649 := by
  unfold tailWord_5430270
  simp only [CollatzResearch.WordTrace]
  refine ⟨24757277254633335140716033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132038812024711120750485509 24757277254633335140716033)
  ·
    refine ⟨18567957940975001355537025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24757277254633335140716033 18567957940975001355537025)
    ·
      refine ⟨13925968455731251016652769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18567957940975001355537025 13925968455731251016652769)
      ·
        refine ⟨10444476341798438262489577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13925968455731251016652769 10444476341798438262489577)
        ·
          refine ⟨7833357256348828696867183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10444476341798438262489577 7833357256348828696867183)
          ·
            refine ⟨11750035884523243045300775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833357256348828696867183 11750035884523243045300775)
            ·
              refine ⟨17625053826784864567951163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11750035884523243045300775 17625053826784864567951163)
              ·
                refine ⟨26437580740177296851926745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17625053826784864567951163 26437580740177296851926745)
                ·
                  refine ⟨19828185555132972638945059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26437580740177296851926745 19828185555132972638945059)
                  ·
                    refine ⟨29742278332699458958417589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19828185555132972638945059 29742278332699458958417589)
                    ·
                      refine ⟨2788338593690574277351649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29742278332699458958417589 2788338593690574277351649)
                      ·
                        rfl

theorem cell23_5430270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_5430270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430270 prefixEnd_5430270 := by exact prefixLift 5430270
  have htrace : WordTrace (prefixWord ++ tailWord_5430270) baseStart_5430270 baseEnd_5430270 := by
    simpa [prefixWord, tailWord_5430270, baseEnd_5430270] using wordTrace_append hprefix tailTrace_5430270
  have hstable : (prefixWord ++ tailWord_5430270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430270).length < 2 ^ (prefixWord ++ tailWord_5430270).sum := by decide
  have hdescent : baseEnd_5430270 < baseStart_5430270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430296 : List Nat := [2, 1, 2, 3, 2, 2, 1, 1, 1, 1, 7]
def baseStart_5430296 : Nat := 118140960795 + 5430296 * 2 ^ 59
def prefixEnd_5430296 : Nat := 4983230072969 + 3 ^ 40 * 5430296 * 2
def baseEnd_5430296 : Nat := 2788351944187591175626529

theorem tailTrace_5430296 : CollatzResearch.WordTrace tailWord_5430296 prefixEnd_5430296 2788351944187591175626529 := by
  unfold tailWord_5430296
  simp only [CollatzResearch.WordTrace]
  refine ⟨99029583167486243783087371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132039444223314991710783161 99029583167486243783087371)
  ·
    refine ⟨148544374751229365674631057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99029583167486243783087371 148544374751229365674631057)
    ·
      refine ⟨111408281063422024255973293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148544374751229365674631057 111408281063422024255973293)
      ·
        refine ⟨41778105398783259095989985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111408281063422024255973293 41778105398783259095989985)
        ·
          refine ⟨31333579049087444321992489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41778105398783259095989985 31333579049087444321992489)
          ·
            refine ⟨23500184286815583241494367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31333579049087444321992489 23500184286815583241494367)
            ·
              refine ⟨35250276430223374862241551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23500184286815583241494367 35250276430223374862241551)
              ·
                refine ⟨52875414645335062293362327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35250276430223374862241551 52875414645335062293362327)
                ·
                  refine ⟨79313121968002593440043491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52875414645335062293362327 79313121968002593440043491)
                  ·
                    refine ⟨118969682952003890160065237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79313121968002593440043491 118969682952003890160065237)
                    ·
                      refine ⟨2788351944187591175626529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118969682952003890160065237 2788351944187591175626529)
                      ·
                        rfl

theorem cell23_5430296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_5430296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430296 prefixEnd_5430296 := by exact prefixLift 5430296
  have htrace : WordTrace (prefixWord ++ tailWord_5430296) baseStart_5430296 baseEnd_5430296 := by
    simpa [prefixWord, tailWord_5430296, baseEnd_5430296] using wordTrace_append hprefix tailTrace_5430296
  have hstable : (prefixWord ++ tailWord_5430296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430296).length < 2 ^ (prefixWord ++ tailWord_5430296).sum := by decide
  have hdescent : baseEnd_5430296 < baseStart_5430296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430301 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_5430301 : Nat := 118140960795 + 5430301 * 2 ^ 59
def prefixEnd_5430301 : Nat := 4983230072969 + 3 ^ 40 * 5430301 * 2
def baseEnd_5430301 : Nat := 2788354511590863656064007

theorem tailTrace_5430301 : CollatzResearch.WordTrace tailWord_5430301 prefixEnd_5430301 2788354511590863656064007 := by
  unfold tailWord_5430301
  simp only [CollatzResearch.WordTrace]
  refine ⟨198059348699954373420106757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132039565799969582280071171 198059348699954373420106757)
  ·
    refine ⟨37136127881241445016270017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198059348699954373420106757 37136127881241445016270017)
    ·
      refine ⟨27852095910931083762202513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37136127881241445016270017 27852095910931083762202513)
      ·
        refine ⟨20889071933198312821651885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27852095910931083762202513 20889071933198312821651885)
        ·
          refine ⟨7833401974949367308119457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20889071933198312821651885 7833401974949367308119457)
          ·
            refine ⟨5875051481212025481089593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7833401974949367308119457 5875051481212025481089593)
            ·
              refine ⟨4406288610909019110817195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5875051481212025481089593 4406288610909019110817195)
              ·
                refine ⟨6609432916363528666225793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406288610909019110817195 6609432916363528666225793)
                ·
                  refine ⟨4957074687272646499669345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6609432916363528666225793 4957074687272646499669345)
                  ·
                    refine ⟨3717806015454484874752009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4957074687272646499669345 3717806015454484874752009)
                    ·
                      refine ⟨2788354511590863656064007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717806015454484874752009 2788354511590863656064007)
                      ·
                        rfl

theorem cell23_5430301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_5430301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430301 prefixEnd_5430301 := by exact prefixLift 5430301
  have htrace : WordTrace (prefixWord ++ tailWord_5430301) baseStart_5430301 baseEnd_5430301 := by
    simpa [prefixWord, tailWord_5430301, baseEnd_5430301] using wordTrace_append hprefix tailTrace_5430301
  have hstable : (prefixWord ++ tailWord_5430301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430301).length < 2 ^ (prefixWord ++ tailWord_5430301).sum := by decide
  have hdescent : baseEnd_5430301 < baseStart_5430301 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430323 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 4, 4, 2]
def baseStart_5430323 : Nat := 118140960795 + 5430323 * 2 ^ 59
def prefixEnd_5430323 : Nat := 4983230072969 + 3 ^ 40 * 5430323 * 2
def baseEnd_5430323 : Nat := 2788365808165262569988905

theorem tailTrace_5430323 : CollatzResearch.WordTrace tailWord_5430323 prefixEnd_5430323 2788365808165262569988905 := by
  unfold tailWord_5430323
  simp only [CollatzResearch.WordTrace]
  refine ⟨198060151105874671177407623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132040100737249780784938415 198060151105874671177407623)
  ·
    refine ⟨297090226658812006766111435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198060151105874671177407623 297090226658812006766111435)
    ·
      refine ⟨445635339988218010149167153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297090226658812006766111435 445635339988218010149167153)
      ·
        refine ⟨334226504991163507611875365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445635339988218010149167153 334226504991163507611875365)
        ·
          refine ⟨62667469685843157677226631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334226504991163507611875365 62667469685843157677226631)
          ·
            refine ⟨94001204528764736515839947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62667469685843157677226631 94001204528764736515839947)
            ·
              refine ⟨141001806793147104773759921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94001204528764736515839947 141001806793147104773759921)
              ·
                refine ⟨105751355094860328580319941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141001806793147104773759921 105751355094860328580319941)
                ·
                  refine ⟨19828379080286311608809989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105751355094860328580319941 19828379080286311608809989)
                  ·
                    refine ⟨3717821077553683426651873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19828379080286311608809989 3717821077553683426651873)
                    ·
                      refine ⟨2788365808165262569988905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717821077553683426651873 2788365808165262569988905)
                      ·
                        rfl

theorem cell23_5430323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 4, 2].length) (baseStart_5430323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430323 prefixEnd_5430323 := by exact prefixLift 5430323
  have htrace : WordTrace (prefixWord ++ tailWord_5430323) baseStart_5430323 baseEnd_5430323 := by
    simpa [prefixWord, tailWord_5430323, baseEnd_5430323] using wordTrace_append hprefix tailTrace_5430323
  have hstable : (prefixWord ++ tailWord_5430323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430323).length < 2 ^ (prefixWord ++ tailWord_5430323).sum := by decide
  have hdescent : baseEnd_5430323 < baseStart_5430323 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430336 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6]
def baseStart_5430336 : Nat := 118140960795 + 5430336 * 2 ^ 59
def prefixEnd_5430336 : Nat := 4983230072969 + 3 ^ 40 * 5430336 * 2
def baseEnd_5430336 : Nat := 2788372483413771019126345

theorem tailTrace_5430336 : CollatzResearch.WordTrace tailWord_5430336 prefixEnd_5430336 2788372483413771019126345 := by
  unfold tailWord_5430336
  simp only [CollatzResearch.WordTrace]
  refine ⟨99030312627413787198815431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132040416836551716265087241 99030312627413787198815431)
  ·
    refine ⟨148545468941120680798223147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99030312627413787198815431 148545468941120680798223147)
    ·
      refine ⟨222818203411681021197334721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148545468941120680798223147 222818203411681021197334721)
      ·
        refine ⟨167113652558760765898001041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222818203411681021197334721 167113652558760765898001041)
        ·
          refine ⟨125335239419070574423500781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167113652558760765898001041 125335239419070574423500781)
          ·
            refine ⟨47000714782151465408812793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125335239419070574423500781 47000714782151465408812793)
            ·
              refine ⟨35250536086613599056609595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47000714782151465408812793 35250536086613599056609595)
              ·
                refine ⟨52875804129920398584914393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35250536086613599056609595 52875804129920398584914393)
                ·
                  refine ⟨39656853097440298938685795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52875804129920398584914393 39656853097440298938685795)
                  ·
                    refine ⟨59485279646160448408028693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39656853097440298938685795 59485279646160448408028693)
                    ·
                      refine ⟨2788372483413771019126345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59485279646160448408028693 2788372483413771019126345)
                      ·
                        rfl

theorem cell23_5430336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_5430336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430336 prefixEnd_5430336 := by exact prefixLift 5430336
  have htrace : WordTrace (prefixWord ++ tailWord_5430336) baseStart_5430336 baseEnd_5430336 := by
    simpa [prefixWord, tailWord_5430336, baseEnd_5430336] using wordTrace_append hprefix tailTrace_5430336
  have hstable : (prefixWord ++ tailWord_5430336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430336).length < 2 ^ (prefixWord ++ tailWord_5430336).sum := by decide
  have hdescent : baseEnd_5430336 < baseStart_5430336 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430346 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 8]
def baseStart_5430346 : Nat := 118140960795 + 5430346 * 2 ^ 59
def prefixEnd_5430346 : Nat := 4983230072969 + 3 ^ 40 * 5430346 * 2
def baseEnd_5430346 : Nat := 309819735357812886666811

theorem tailTrace_5430346 : CollatzResearch.WordTrace tailWord_5430346 prefixEnd_5430346 309819735357812886666811 := by
  unfold tailWord_5430346
  simp only [CollatzResearch.WordTrace]
  refine ⟨49515247496197836526373723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132040659989860897403663261 49515247496197836526373723)
  ·
    refine ⟨74272871244296754789560585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49515247496197836526373723 74272871244296754789560585)
    ·
      refine ⟨55704653433222566092170439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74272871244296754789560585 55704653433222566092170439)
      ·
        refine ⟨83556980149833849138255659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55704653433222566092170439 83556980149833849138255659)
        ·
          refine ⟨125335470224750773707383489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83556980149833849138255659 125335470224750773707383489)
          ·
            refine ⟨94001602668563080280537617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125335470224750773707383489 94001602668563080280537617)
            ·
              refine ⟨70501202001422310210403213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94001602668563080280537617 70501202001422310210403213)
              ·
                refine ⟨26437950750533366328901205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70501202001422310210403213 26437950750533366328901205)
                ·
                  refine ⟨309819735357812886666811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26437950750533366328901205 309819735357812886666811)
                  ·
                    rfl

theorem cell23_5430346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 8].length) (baseStart_5430346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430346 prefixEnd_5430346 := by exact prefixLift 5430346
  have htrace : WordTrace (prefixWord ++ tailWord_5430346) baseStart_5430346 baseEnd_5430346 := by
    simpa [prefixWord, tailWord_5430346, baseEnd_5430346] using wordTrace_append hprefix tailTrace_5430346
  have hstable : (prefixWord ++ tailWord_5430346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430346).length < 2 ^ (prefixWord ++ tailWord_5430346).sum := by decide
  have hdescent : baseEnd_5430346 < baseStart_5430346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430400 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 2, 3, 2]
def baseStart_5430400 : Nat := 118140960795 + 5430400 * 2 ^ 59
def prefixEnd_5430400 : Nat := 4983230072969 + 3 ^ 40 * 5430400 * 2
def baseEnd_5430400 : Nat := 2788405346175658768726051

theorem tailTrace_5430400 : CollatzResearch.WordTrace tailWord_5430400 prefixEnd_5430400 2788405346175658768726051 := by
  unfold tailWord_5430400
  simp only [CollatzResearch.WordTrace]
  refine ⟨99031479763297856663980327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132041973017730475551973769 99031479763297856663980327)
  ·
    refine ⟨148547219644946784995970491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99031479763297856663980327 148547219644946784995970491)
    ·
      refine ⟨222820829467420177493955737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148547219644946784995970491 222820829467420177493955737)
      ·
        refine ⟨167115622100565133120466803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222820829467420177493955737 167115622100565133120466803)
        ·
          refine ⟨250673433150847699680700205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167115622100565133120466803 250673433150847699680700205)
          ·
            refine ⟨94002537431567887380262577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250673433150847699680700205 94002537431567887380262577)
            ·
              refine ⟨70501903073675915535196933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94002537431567887380262577 70501903073675915535196933)
              ·
                refine ⟨13219106826314234162849425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70501903073675915535196933 13219106826314234162849425)
                ·
                  refine ⟨9914330119735675622137069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13219106826314234162849425 9914330119735675622137069)
                  ·
                    refine ⟨3717873794900878358301401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9914330119735675622137069 3717873794900878358301401)
                    ·
                      refine ⟨2788405346175658768726051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717873794900878358301401 2788405346175658768726051)
                      ·
                        rfl

theorem cell23_5430400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_5430400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430400 prefixEnd_5430400 := by exact prefixLift 5430400
  have htrace : WordTrace (prefixWord ++ tailWord_5430400) baseStart_5430400 baseEnd_5430400 := by
    simpa [prefixWord, tailWord_5430400, baseEnd_5430400] using wordTrace_append hprefix tailTrace_5430400
  have hstable : (prefixWord ++ tailWord_5430400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430400).length < 2 ^ (prefixWord ++ tailWord_5430400).sum := by decide
  have hdescent : baseEnd_5430400 < baseStart_5430400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430433 : List Nat := [1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 5]
def baseStart_5430433 : Nat := 118140960795 + 5430433 * 2 ^ 59
def prefixEnd_5430433 : Nat := 4983230072969 + 3 ^ 40 * 5430433 * 2
def baseEnd_5430433 : Nat := 2788422291037257139613399

theorem tailTrace_5430433 : CollatzResearch.WordTrace tailWord_5430433 prefixEnd_5430433 2788422291037257139613399 := by
  unfold tailWord_5430433
  simp only [CollatzResearch.WordTrace]
  refine ⟨198064163135476159963911953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132042775423650773309274635 198064163135476159963911953)
  ·
    refine ⟨148548122351607119972933965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198064163135476159963911953 148548122351607119972933965)
    ·
      refine ⟨55705545881852669989850237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148548122351607119972933965 55705545881852669989850237)
      ·
        refine ⟨20889579705694751246193839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55705545881852669989850237 20889579705694751246193839)
        ·
          refine ⟨31334369558542126869290759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20889579705694751246193839 31334369558542126869290759)
          ·
            refine ⟨47001554337813190303936139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31334369558542126869290759 47001554337813190303936139)
            ·
              refine ⟨70502331506719785455904209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47001554337813190303936139 70502331506719785455904209)
              ·
                refine ⟨52876748630039839091928157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70502331506719785455904209 52876748630039839091928157)
                ·
                  refine ⟨19828780736264939659473059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 52876748630039839091928157 19828780736264939659473059)
                  ·
                    refine ⟨29743171104397409489209589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19828780736264939659473059 29743171104397409489209589)
                    ·
                      refine ⟨2788422291037257139613399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29743171104397409489209589 2788422291037257139613399)
                      ·
                        rfl

theorem cell23_5430433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_5430433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430433 prefixEnd_5430433 := by exact prefixLift 5430433
  have htrace : WordTrace (prefixWord ++ tailWord_5430433) baseStart_5430433 baseEnd_5430433 := by
    simpa [prefixWord, tailWord_5430433, baseEnd_5430433] using wordTrace_append hprefix tailTrace_5430433
  have hstable : (prefixWord ++ tailWord_5430433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430433).length < 2 ^ (prefixWord ++ tailWord_5430433).sum := by decide
  have hdescent : baseEnd_5430433 < baseStart_5430433 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430450 : List Nat := [3, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5]
def baseStart_5430450 : Nat := 118140960795 + 5430450 * 2 ^ 59
def prefixEnd_5430450 : Nat := 4983230072969 + 3 ^ 40 * 5430450 * 2
def baseEnd_5430450 : Nat := 2788431020208383573100821

theorem tailTrace_5430450 : CollatzResearch.WordTrace tailWord_5430450 prefixEnd_5430450 2788431020208383573100821 := by
  unfold tailWord_5430450
  simp only [CollatzResearch.WordTrace]
  refine ⟨49516195794103642966820201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132043188784276381244853869 49516195794103642966820201)
  ·
    refine ⟨37137146845577732225115151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49516195794103642966820201 37137146845577732225115151)
    ·
      refine ⟨55705720268366598337672727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37137146845577732225115151 55705720268366598337672727)
      ·
        refine ⟨83558580402549897506509091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55705720268366598337672727 83558580402549897506509091)
        ·
          refine ⟨125337870603824846259763637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83558580402549897506509091 125337870603824846259763637)
          ·
            refine ⟨11750425369108579336852841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125337870603824846259763637 11750425369108579336852841)
            ·
              refine ⟨8812819026831434502639631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11750425369108579336852841 8812819026831434502639631)
              ·
                refine ⟨13219228540247151753959447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8812819026831434502639631 13219228540247151753959447)
                ·
                  refine ⟨19828842810370727630939171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13219228540247151753959447 19828842810370727630939171)
                  ·
                    refine ⟨29743264215556091446408757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19828842810370727630939171 29743264215556091446408757)
                    ·
                      refine ⟨2788431020208383573100821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29743264215556091446408757 2788431020208383573100821)
                      ·
                        rfl

theorem cell23_5430450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5].length) (baseStart_5430450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430450 prefixEnd_5430450 := by exact prefixLift 5430450
  have htrace : WordTrace (prefixWord ++ tailWord_5430450) baseStart_5430450 baseEnd_5430450 := by
    simpa [prefixWord, tailWord_5430450, baseEnd_5430450] using wordTrace_append hprefix tailTrace_5430450
  have hstable : (prefixWord ++ tailWord_5430450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430450).length < 2 ^ (prefixWord ++ tailWord_5430450).sum := by decide
  have hdescent : baseEnd_5430450 < baseStart_5430450 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430474 : List Nat := [3, 1, 2, 1, 3, 4, 2, 1, 2, 4]
def baseStart_5430474 : Nat := 118140960795 + 5430474 * 2 ^ 59
def prefixEnd_5430474 : Nat := 4983230072969 + 3 ^ 40 * 5430474 * 2
def baseEnd_5430474 : Nat := 929481114581363826400237

theorem tailTrace_5430474 : CollatzResearch.WordTrace tailWord_5430474 prefixEnd_5430474 929481114581363826400237 := by
  unfold tailWord_5430474
  simp only [CollatzResearch.WordTrace]
  refine ⟨49516414632081905991538619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132043772352218415977436317 49516414632081905991538619)
  ·
    refine ⟨74274621948122858987307929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49516414632081905991538619 74274621948122858987307929)
    ·
      refine ⟨55705966461092144240480947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74274621948122858987307929 55705966461092144240480947)
      ·
        refine ⟨83558949691638216360721421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55705966461092144240480947 83558949691638216360721421)
        ·
          refine ⟨31334606134364331135270533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83558949691638216360721421 31334606134364331135270533)
          ·
            refine ⟨5875238650193312087863225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31334606134364331135270533 5875238650193312087863225)
            ·
              refine ⟨4406428987644984065897419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5875238650193312087863225 4406428987644984065897419)
              ·
                refine ⟨6609643481467476098846129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406428987644984065897419 6609643481467476098846129)
                ·
                  refine ⟨4957232611100607074134597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6609643481467476098846129 4957232611100607074134597)
                  ·
                    refine ⟨929481114581363826400237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4957232611100607074134597 929481114581363826400237)
                    ·
                      rfl

theorem cell23_5430474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_5430474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430474 prefixEnd_5430474 := by exact prefixLift 5430474
  have htrace : WordTrace (prefixWord ++ tailWord_5430474) baseStart_5430474 baseEnd_5430474 := by
    simpa [prefixWord, tailWord_5430474, baseEnd_5430474] using wordTrace_append hprefix tailTrace_5430474
  have hstable : (prefixWord ++ tailWord_5430474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430474).length < 2 ^ (prefixWord ++ tailWord_5430474).sum := by decide
  have hdescent : baseEnd_5430474 < baseStart_5430474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430484 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_5430484 : Nat := 118140960795 + 5430484 * 2 ^ 59
def prefixEnd_5430484 : Nat := 4983230072969 + 3 ^ 40 * 5430484 * 2
def baseEnd_5430484 : Nat := 2788448478550636440075665

theorem tailTrace_5430484 : CollatzResearch.WordTrace tailWord_5430484 prefixEnd_5430484 2788448478550636440075665 := by
  unfold tailWord_5430484
  simp only [CollatzResearch.WordTrace]
  refine ⟨99033011629145697837009253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132044015505527597116012337 99033011629145697837009253)
  ·
    refine ⟨18568689680464818344439235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 99033011629145697837009253 18568689680464818344439235)
    ·
      refine ⟨27853034520697227516658853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18568689680464818344439235 27853034520697227516658853)
      ·
        refine ⟨5222443972630730159373535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 27853034520697227516658853 5222443972630730159373535)
        ·
          refine ⟨7833665958946095239060303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222443972630730159373535 7833665958946095239060303)
          ·
            refine ⟨11750498938419142858590455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833665958946095239060303 11750498938419142858590455)
            ·
              refine ⟨17625748407628714287885683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11750498938419142858590455 17625748407628714287885683)
              ·
                refine ⟨26438622611443071431828525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17625748407628714287885683 26438622611443071431828525)
                ·
                  refine ⟨9914483479291151786935697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26438622611443071431828525 9914483479291151786935697)
                  ·
                    refine ⟨7435862609468363840201773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9914483479291151786935697 7435862609468363840201773)
                    ·
                      refine ⟨2788448478550636440075665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7435862609468363840201773 2788448478550636440075665)
                      ·
                        rfl

theorem cell23_5430484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_5430484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430484 prefixEnd_5430484 := by exact prefixLift 5430484
  have htrace : WordTrace (prefixWord ++ tailWord_5430484) baseStart_5430484 baseEnd_5430484 := by
    simpa [prefixWord, tailWord_5430484, baseEnd_5430484] using wordTrace_append hprefix tailTrace_5430484
  have hstable : (prefixWord ++ tailWord_5430484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430484).length < 2 ^ (prefixWord ++ tailWord_5430484).sum := by decide
  have hdescent : baseEnd_5430484 < baseStart_5430484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430513 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 2, 6]
def baseStart_5430513 : Nat := 118140960795 + 5430513 * 2 ^ 59
def prefixEnd_5430513 : Nat := 4983230072969 + 3 ^ 40 * 5430513 * 2
def baseEnd_5430513 : Nat := 929487789829872275537677

theorem tailTrace_5430513 : CollatzResearch.WordTrace tailWord_5430513 prefixEnd_5430513 929487789829872275537677 := by
  unfold tailWord_5430513
  simp only [CollatzResearch.WordTrace]
  refine ⟨198067080975186333626824193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132044720650124222417882795 198067080975186333626824193)
  ·
    refine ⟨148550310731389750220118145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198067080975186333626824193 148550310731389750220118145)
    ·
      refine ⟨111412733048542312665088609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148550310731389750220118145 111412733048542312665088609)
      ·
        refine ⟨83559549786406734498816457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111412733048542312665088609 83559549786406734498816457)
        ·
          refine ⟨62669662339805050874112343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83559549786406734498816457 62669662339805050874112343)
          ·
            refine ⟨94004493509707576311168515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62669662339805050874112343 94004493509707576311168515)
            ·
              refine ⟨141006740264561364466752773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94004493509707576311168515 141006740264561364466752773)
              ·
                refine ⟨26438763799605255837516145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141006740264561364466752773 26438763799605255837516145)
                ·
                  refine ⟨19829072849703941878137109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26438763799605255837516145 19829072849703941878137109)
                  ·
                    refine ⟨929487789829872275537677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19829072849703941878137109 929487789829872275537677)
                    ·
                      rfl

theorem cell23_5430513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 6].length) (baseStart_5430513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430513 prefixEnd_5430513 := by exact prefixLift 5430513
  have htrace : WordTrace (prefixWord ++ tailWord_5430513) baseStart_5430513 baseEnd_5430513 := by
    simpa [prefixWord, tailWord_5430513, baseEnd_5430513] using wordTrace_append hprefix tailTrace_5430513
  have hstable : (prefixWord ++ tailWord_5430513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430513).length < 2 ^ (prefixWord ++ tailWord_5430513).sum := by decide
  have hdescent : baseEnd_5430513 < baseStart_5430513 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430537 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 1, 4, 2]
def baseStart_5430537 : Nat := 118140960795 + 5430537 * 2 ^ 59
def prefixEnd_5430537 : Nat := 4983230072969 + 3 ^ 40 * 5430537 * 2
def baseEnd_5430537 : Nat := 2788475693025324732712921

theorem tailTrace_5430537 : CollatzResearch.WordTrace tailWord_5430537 prefixEnd_5430537 2788475693025324732712921 := by
  unfold tailWord_5430537
  simp only [CollatzResearch.WordTrace]
  refine ⟨198067956327099385725697865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132045304218066257150465243 198067956327099385725697865)
  ·
    refine ⟨148550967245324539294273399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198067956327099385725697865 148550967245324539294273399)
    ·
      refine ⟨222826450867986808941410099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148550967245324539294273399 222826450867986808941410099)
      ·
        refine ⟨334239676301980213412115149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222826450867986808941410099 334239676301980213412115149)
        ·
          refine ⟨125339878613242580029543181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334239676301980213412115149 125339878613242580029543181)
          ·
            refine ⟨47002454479965967511078693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125339878613242580029543181 47002454479965967511078693)
            ·
              refine ⟨8812960214993618908327255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47002454479965967511078693 8812960214993618908327255)
              ·
                refine ⟨13219440322490428362490883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8812960214993618908327255 13219440322490428362490883)
                ·
                  refine ⟨19829160483735642543736325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13219440322490428362490883 19829160483735642543736325)
                  ·
                    refine ⟨3717967590700432976950561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19829160483735642543736325 3717967590700432976950561)
                    ·
                      refine ⟨2788475693025324732712921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717967590700432976950561 2788475693025324732712921)
                      ·
                        rfl

theorem cell23_5430537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 4, 2].length) (baseStart_5430537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430537 prefixEnd_5430537 := by exact prefixLift 5430537
  have htrace : WordTrace (prefixWord ++ tailWord_5430537) baseStart_5430537 baseEnd_5430537 := by
    simpa [prefixWord, tailWord_5430537, baseEnd_5430537] using wordTrace_append hprefix tailTrace_5430537
  have hstable : (prefixWord ++ tailWord_5430537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430537).length < 2 ^ (prefixWord ++ tailWord_5430537).sum := by decide
  have hdescent : baseEnd_5430537 < baseStart_5430537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430558 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5430558 : Nat := 118140960795 + 5430558 * 2 ^ 59
def prefixEnd_5430558 : Nat := 4983230072969 + 3 ^ 40 * 5430558 * 2
def baseEnd_5430558 : Nat := 2788486476119069150550325

theorem tailTrace_5430558 : CollatzResearch.WordTrace tailWord_5430558 prefixEnd_5430558 2788486476119069150550325 := by
  unfold tailWord_5430558
  simp only [CollatzResearch.WordTrace]
  refine ⟨24758590282502913289026541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132045814840015537541474885 24758590282502913289026541)
  ·
    refine ⟨9284471355938592483384953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 24758590282502913289026541 9284471355938592483384953)
    ·
      refine ⟨6963353516953944362538715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9284471355938592483384953 6963353516953944362538715)
      ·
        refine ⟨10445030275430916543808073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6963353516953944362538715 10445030275430916543808073)
        ·
          refine ⟨7833772706573187407856055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10445030275430916543808073 7833772706573187407856055)
          ·
            refine ⟨11750659059859781111784083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7833772706573187407856055 11750659059859781111784083)
            ·
              refine ⟨17625988589789671667676125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11750659059859781111784083 17625988589789671667676125)
              ·
                refine ⟨6609745721171126875378547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17625988589789671667676125 6609745721171126875378547)
                ·
                  refine ⟨9914618581756690313067821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6609745721171126875378547 9914618581756690313067821)
                  ·
                    refine ⟨3717981968158758867400433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9914618581756690313067821 3717981968158758867400433)
                    ·
                      refine ⟨2788486476119069150550325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3717981968158758867400433 2788486476119069150550325)
                      ·
                        rfl

theorem cell23_5430558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5430558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430558 prefixEnd_5430558 := by exact prefixLift 5430558
  have htrace : WordTrace (prefixWord ++ tailWord_5430558) baseStart_5430558 baseEnd_5430558 := by
    simpa [prefixWord, tailWord_5430558, baseEnd_5430558] using wordTrace_append hprefix tailTrace_5430558
  have hstable : (prefixWord ++ tailWord_5430558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430558).length < 2 ^ (prefixWord ++ tailWord_5430558).sum := by decide
  have hdescent : baseEnd_5430558 < baseStart_5430558 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430577 : List Nat := [1, 2, 2, 3, 3, 1, 2, 4, 5]
def baseStart_5430577 : Nat := 118140960795 + 5430577 * 2 ^ 59
def prefixEnd_5430577 : Nat := 4983230072969 + 3 ^ 40 * 5430577 * 2
def baseEnd_5430577 : Nat := 309832914694611619579193

theorem tailTrace_5430577 : CollatzResearch.WordTrace tailWord_5430577 prefixEnd_5430577 309832914694611619579193 := by
  unfold tailWord_5430577
  simp only [CollatzResearch.WordTrace]
  refine ⟨198069415246954472557153985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132046276831302981704769323 198069415246954472557153985)
  ·
    refine ⟨148552061435215854417865489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198069415246954472557153985 148552061435215854417865489)
    ·
      refine ⟨111414046076411890813399117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148552061435215854417865489 111414046076411890813399117)
      ·
        refine ⟨41780267278654459055024669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111414046076411890813399117 41780267278654459055024669)
        ·
          refine ⟨15667600229495422145634251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41780267278654459055024669 15667600229495422145634251)
          ·
            refine ⟨23501400344243133218451377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15667600229495422145634251 23501400344243133218451377)
            ·
              refine ⟨17626050258182349913838533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23501400344243133218451377 17626050258182349913838533)
              ·
                refine ⟨3304884423409190608844725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17626050258182349913838533 3304884423409190608844725)
                ·
                  refine ⟨309832914694611619579193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3304884423409190608844725 309832914694611619579193)
                  ·
                    rfl

theorem cell23_5430577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 2, 4, 5].length) (baseStart_5430577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430577 prefixEnd_5430577 := by exact prefixLift 5430577
  have htrace : WordTrace (prefixWord ++ tailWord_5430577) baseStart_5430577 baseEnd_5430577 := by
    simpa [prefixWord, tailWord_5430577, baseEnd_5430577] using wordTrace_append hprefix tailTrace_5430577
  have hstable : (prefixWord ++ tailWord_5430577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430577).length < 2 ^ (prefixWord ++ tailWord_5430577).sum := by decide
  have hdescent : baseEnd_5430577 < baseStart_5430577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430590 : List Nat := [4, 2, 1, 2, 1, 1, 1, 1, 3, 7]
def baseStart_5430590 : Nat := 118140960795 + 5430590 * 2 ^ 59
def prefixEnd_5430590 : Nat := 4983230072969 + 3 ^ 40 * 5430590 * 2
def baseEnd_5430590 : Nat := 929500969166671008450059

theorem tailTrace_5430590 : CollatzResearch.WordTrace tailWord_5430590 prefixEnd_5430590 929500969166671008450059 := by
  unfold tailWord_5430590
  simp only [CollatzResearch.WordTrace]
  refine ⟨24758736174488421972172153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132046592930604917184918149 24758736174488421972172153)
  ·
    refine ⟨18569052130866316479129115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24758736174488421972172153 18569052130866316479129115)
    ·
      refine ⟨27853578196299474718693673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18569052130866316479129115 27853578196299474718693673)
      ·
        refine ⟨20890183647224606039020255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 27853578196299474718693673 20890183647224606039020255)
        ·
          refine ⟨31335275470836909058530383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20890183647224606039020255 31335275470836909058530383)
          ·
            refine ⟨47002913206255363587795575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31335275470836909058530383 47002913206255363587795575)
            ·
              refine ⟨70504369809383045381693363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47002913206255363587795575 70504369809383045381693363)
              ·
                refine ⟨105756554714074568072540045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70504369809383045381693363 105756554714074568072540045)
                ·
                  refine ⟨39658708017777963027202517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105756554714074568072540045 39658708017777963027202517)
                  ·
                    refine ⟨929500969166671008450059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39658708017777963027202517 929500969166671008450059)
                    ·
                      rfl

theorem cell23_5430590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 1, 3, 7].length) (baseStart_5430590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430590 prefixEnd_5430590 := by exact prefixLift 5430590
  have htrace : WordTrace (prefixWord ++ tailWord_5430590) baseStart_5430590 baseEnd_5430590 := by
    simpa [prefixWord, tailWord_5430590, baseEnd_5430590] using wordTrace_append hprefix tailTrace_5430590
  have hstable : (prefixWord ++ tailWord_5430590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430590).length < 2 ^ (prefixWord ++ tailWord_5430590).sum := by decide
  have hdescent : baseEnd_5430590 < baseStart_5430590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430627 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 4]
def baseStart_5430627 : Nat := 118140960795 + 5430627 * 2 ^ 59
def prefixEnd_5430627 : Nat := 4983230072969 + 3 ^ 40 * 5430627 * 2
def baseEnd_5430627 : Nat := 2788521906284229380587507

theorem tailTrace_5430627 : CollatzResearch.WordTrace tailWord_5430627 prefixEnd_5430627 2788521906284229380587507 := by
  unfold tailWord_5430627
  simp only [CollatzResearch.WordTrace]
  refine ⟨198071238896773331096474135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132047492597848887397649423 198071238896773331096474135)
  ·
    refine ⟨297106858345159996644711203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198071238896773331096474135 297106858345159996644711203)
    ·
      refine ⟨445660287517739994967066805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297106858345159996644711203 445660287517739994967066805)
      ·
        refine ⟨41780651954788124528162513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 445660287517739994967066805 41780651954788124528162513)
        ·
          refine ⟨31335488966091093396121885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41780651954788124528162513 31335488966091093396121885)
          ·
            refine ⟨11750808362284160023545707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31335488966091093396121885 11750808362284160023545707)
            ·
              refine ⟨17626212543426240035318561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11750808362284160023545707 17626212543426240035318561)
              ·
                refine ⟨13219659407569680026488921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17626212543426240035318561 13219659407569680026488921)
                ·
                  refine ⟨9914744555677260019866691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13219659407569680026488921 9914744555677260019866691)
                  ·
                    refine ⟨14872116833515890029800037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9914744555677260019866691 14872116833515890029800037)
                    ·
                      refine ⟨2788521906284229380587507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14872116833515890029800037 2788521906284229380587507)
                      ·
                        rfl

theorem cell23_5430627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_5430627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430627 prefixEnd_5430627 := by exact prefixLift 5430627
  have htrace : WordTrace (prefixWord ++ tailWord_5430627) baseStart_5430627 baseEnd_5430627 := by
    simpa [prefixWord, tailWord_5430627, baseEnd_5430627] using wordTrace_append hprefix tailTrace_5430627
  have hstable : (prefixWord ++ tailWord_5430627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430627).length < 2 ^ (prefixWord ++ tailWord_5430627).sum := by decide
  have hdescent : baseEnd_5430627 < baseStart_5430627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430650 : List Nat := [3, 1, 1, 1, 1, 1, 2, 7, 6]
def baseStart_5430650 : Nat := 118140960795 + 5430650 * 2 ^ 59
def prefixEnd_5430650 : Nat := 4983230072969 + 3 ^ 40 * 5430650 * 2
def baseEnd_5430650 : Nat := 309837079593253643399989

theorem tailTrace_5430650 : CollatzResearch.WordTrace tailWord_5430650 prefixEnd_5430650 309837079593253643399989 := by
  unfold tailWord_5430650
  simp only [CollatzResearch.WordTrace]
  refine ⟨49518019443922501506140351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132048051850460004016374269 49518019443922501506140351)
  ·
    refine ⟨74277029165883752259210527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49518019443922501506140351 74277029165883752259210527)
    ·
      refine ⟨111415543748825628388815791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74277029165883752259210527 111415543748825628388815791)
      ·
        refine ⟨167123315623238442583223687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111415543748825628388815791 167123315623238442583223687)
        ·
          refine ⟨250684973434857663874835531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167123315623238442583223687 250684973434857663874835531)
          ·
            refine ⟨376027460152286495812253297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250684973434857663874835531 376027460152286495812253297)
            ·
              refine ⟨282020595114214871859189973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376027460152286495812253297 282020595114214871859189973)
              ·
                refine ⟨6609857697989411059199765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 282020595114214871859189973 6609857697989411059199765)
                ·
                  refine ⟨309837079593253643399989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6609857697989411059199765 309837079593253643399989)
                  ·
                    rfl

theorem cell23_5430650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 7, 6].length) (baseStart_5430650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430650 prefixEnd_5430650 := by exact prefixLift 5430650
  have htrace : WordTrace (prefixWord ++ tailWord_5430650) baseStart_5430650 baseEnd_5430650 := by
    simpa [prefixWord, tailWord_5430650, baseEnd_5430650] using wordTrace_append hprefix tailTrace_5430650
  have hstable : (prefixWord ++ tailWord_5430650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430650).length < 2 ^ (prefixWord ++ tailWord_5430650).sum := by decide
  have hdescent : baseEnd_5430650 < baseStart_5430650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430664 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 2, 2, 3]
def baseStart_5430664 : Nat := 118140960795 + 5430664 * 2 ^ 59
def prefixEnd_5430664 : Nat := 4983230072969 + 3 ^ 40 * 5430664 * 2
def baseEnd_5430664 : Nat := 2788540905068445735824837

theorem tailTrace_5430664 : CollatzResearch.WordTrace tailWord_5430664 prefixEnd_5430664 2788540905068445735824837 := by
  unfold tailWord_5430664
  simp only [CollatzResearch.WordTrace]
  refine ⟨99036294198819643207785523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132048392265092857610380697 99036294198819643207785523)
  ·
    refine ⟨148554441298229464811678285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99036294198819643207785523 148554441298229464811678285)
    ·
      refine ⟨55707915486836049304379357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148554441298229464811678285 55707915486836049304379357)
      ·
        refine ⟨20890468307563518489142259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55707915486836049304379357 20890468307563518489142259)
        ·
          refine ⟨31335702461345277733713389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20890468307563518489142259 31335702461345277733713389)
          ·
            refine ⟨11750888423004479150142521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31335702461345277733713389 11750888423004479150142521)
            ·
              refine ⟨8813166317253359362606891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11750888423004479150142521 8813166317253359362606891)
              ·
                refine ⟨13219749475880039043910337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8813166317253359362606891 13219749475880039043910337)
                ·
                  refine ⟨9914812106910029282932753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13219749475880039043910337 9914812106910029282932753)
                  ·
                    refine ⟨7436109080182521962199565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9914812106910029282932753 7436109080182521962199565)
                    ·
                      refine ⟨2788540905068445735824837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7436109080182521962199565 2788540905068445735824837)
                      ·
                        rfl

theorem cell23_5430664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_5430664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430664 prefixEnd_5430664 := by exact prefixLift 5430664
  have htrace : WordTrace (prefixWord ++ tailWord_5430664) baseStart_5430664 baseEnd_5430664 := by
    simpa [prefixWord, tailWord_5430664, baseEnd_5430664] using wordTrace_append hprefix tailTrace_5430664
  have hstable : (prefixWord ++ tailWord_5430664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430664).length < 2 ^ (prefixWord ++ tailWord_5430664).sum := by decide
  have hdescent : baseEnd_5430664 < baseStart_5430664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430717 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 4]
def baseStart_5430717 : Nat := 118140960795 + 5430717 * 2 ^ 59
def prefixEnd_5430717 : Nat := 4983230072969 + 3 ^ 40 * 5430717 * 2
def baseEnd_5430717 : Nat := 2788568119543134028462093

theorem tailTrace_5430717 : CollatzResearch.WordTrace tailWord_5430717 prefixEnd_5430717 2788568119543134028462093 := by
  unfold tailWord_5430717
  simp only [CollatzResearch.WordTrace]
  refine ⟨198074521466447276467250405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132049680977631517644833603 198074521466447276467250405)
  ·
    refine ⟨37138972774958864337609451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198074521466447276467250405 37138972774958864337609451)
    ·
      refine ⟨55708459162438296506414177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37138972774958864337609451 55708459162438296506414177)
      ·
        refine ⟨41781344371828722379810633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55708459162438296506414177 41781344371828722379810633)
        ·
          refine ⟨31336008278871541784857975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41781344371828722379810633 31336008278871541784857975)
          ·
            refine ⟨47004012418307312677286963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31336008278871541784857975 47004012418307312677286963)
            ·
              refine ⟨70506018627460969015930445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47004012418307312677286963 70506018627460969015930445)
              ·
                refine ⟨26439756985297863380973917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 70506018627460969015930445 26439756985297863380973917)
                ·
                  refine ⟨9914908869486698767865219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26439756985297863380973917 9914908869486698767865219)
                  ·
                    refine ⟨14872363304230048151797829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9914908869486698767865219 14872363304230048151797829)
                    ·
                      refine ⟨2788568119543134028462093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14872363304230048151797829 2788568119543134028462093)
                      ·
                        rfl

theorem cell23_5430717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_5430717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430717 prefixEnd_5430717 := by exact prefixLift 5430717
  have htrace : WordTrace (prefixWord ++ tailWord_5430717) baseStart_5430717 baseEnd_5430717 := by
    simpa [prefixWord, tailWord_5430717, baseEnd_5430717] using wordTrace_append hprefix tailTrace_5430717
  have hstable : (prefixWord ++ tailWord_5430717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430717).length < 2 ^ (prefixWord ++ tailWord_5430717).sum := by decide
  have hdescent : baseEnd_5430717 < baseStart_5430717 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430727 : List Nat := [1, 1, 4, 1, 1, 3, 2, 2, 4, 4]
def baseStart_5430727 : Nat := 118140960795 + 5430727 * 2 ^ 59
def prefixEnd_5430727 : Nat := 4983230072969 + 3 ^ 40 * 5430727 * 2
def baseEnd_5430727 : Nat := 929524418116559663112349

theorem tailTrace_5430727 : CollatzResearch.WordTrace tailWord_5430727 prefixEnd_5430727 929524418116559663112349 := by
  unfold tailWord_5430727
  simp only [CollatzResearch.WordTrace]
  refine ⟨198074886196411048175114435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132049924130940698783409623 198074886196411048175114435)
  ·
    refine ⟨297112329294616572262671653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198074886196411048175114435 297112329294616572262671653)
    ·
      refine ⟨55708561742740607299250935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297112329294616572262671653 55708561742740607299250935)
      ·
        refine ⟨83562842614110910948876403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55708561742740607299250935 83562842614110910948876403)
        ·
          refine ⟨125344263921166366423314605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83562842614110910948876403 125344263921166366423314605)
          ·
            refine ⟨47004098970437387408742977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125344263921166366423314605 47004098970437387408742977)
            ·
              refine ⟨35253074227828040556557233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47004098970437387408742977 35253074227828040556557233)
              ·
                refine ⟨26439805670871030417417925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35253074227828040556557233 26439805670871030417417925)
                ·
                  refine ⟨4957463563288318203265861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26439805670871030417417925 4957463563288318203265861)
                  ·
                    refine ⟨929524418116559663112349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4957463563288318203265861 929524418116559663112349)
                    ·
                      rfl

theorem cell23_5430727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 2, 4, 4].length) (baseStart_5430727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430727 prefixEnd_5430727 := by exact prefixLift 5430727
  have htrace : WordTrace (prefixWord ++ tailWord_5430727) baseStart_5430727 baseEnd_5430727 := by
    simpa [prefixWord, tailWord_5430727, baseEnd_5430727] using wordTrace_append hprefix tailTrace_5430727
  have hstable : (prefixWord ++ tailWord_5430727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430727).length < 2 ^ (prefixWord ++ tailWord_5430727).sum := by decide
  have hdescent : baseEnd_5430727 < baseStart_5430727 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430744 : List Nat := [2, 1, 2, 2, 2, 1, 5, 2, 2, 4]
def baseStart_5430744 : Nat := 118140960795 + 5430744 * 2 ^ 59
def prefixEnd_5430744 : Nat := 4983230072969 + 3 ^ 40 * 5430744 * 2
def baseEnd_5430744 : Nat := 929527327840268474274823

theorem tailTrace_5430744 : CollatzResearch.WordTrace tailWord_5430744 prefixEnd_5430744 929527327840268474274823 := by
  unfold tailWord_5430744
  simp only [CollatzResearch.WordTrace]
  refine ⟨99037753118674730039241643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132050337491566306718988857 99037753118674730039241643)
  ·
    refine ⟨148556629678012095058862465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99037753118674730039241643 148556629678012095058862465)
    ·
      refine ⟨111417472258509071294146849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148556629678012095058862465 111417472258509071294146849)
      ·
        refine ⟨83563104193881803470610137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111417472258509071294146849 83563104193881803470610137)
        ·
          refine ⟨62672328145411352602957603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83563104193881803470610137 62672328145411352602957603)
          ·
            refine ⟨94008492218117028904436405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62672328145411352602957603 94008492218117028904436405)
            ·
              refine ⟨8813296145448471459790913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 94008492218117028904436405 8813296145448471459790913)
              ·
                refine ⟨6609972109086353594843185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8813296145448471459790913 6609972109086353594843185)
                ·
                  refine ⟨4957479081814765196132389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6609972109086353594843185 4957479081814765196132389)
                  ·
                    refine ⟨929527327840268474274823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4957479081814765196132389 929527327840268474274823)
                    ·
                      rfl

theorem cell23_5430744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 2, 2, 4].length) (baseStart_5430744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430744 prefixEnd_5430744 := by exact prefixLift 5430744
  have htrace : WordTrace (prefixWord ++ tailWord_5430744) baseStart_5430744 baseEnd_5430744 := by
    simpa [prefixWord, tailWord_5430744, baseEnd_5430744] using wordTrace_append hprefix tailTrace_5430744
  have hstable : (prefixWord ++ tailWord_5430744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430744).length < 2 ^ (prefixWord ++ tailWord_5430744).sum := by decide
  have hdescent : baseEnd_5430744 < baseStart_5430744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430751 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 3, 2, 2]
def baseStart_5430751 : Nat := 118140960795 + 5430751 * 2 ^ 59
def prefixEnd_5430751 : Nat := 4983230072969 + 3 ^ 40 * 5430751 * 2
def baseEnd_5430751 : Nat := 2788585577885386895436937

theorem tailTrace_5430751 : CollatzResearch.WordTrace tailWord_5430751 prefixEnd_5430751 2788585577885386895436937 := by
  unfold tailWord_5430751
  simp only [CollatzResearch.WordTrace]
  refine ⟨198075761548324100273988107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132050507698882733515992071 198075761548324100273988107)
  ·
    refine ⟨297113642322486150410982161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198075761548324100273988107 297113642322486150410982161)
    ·
      refine ⟨222835231741864612808236621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297113642322486150410982161 222835231741864612808236621)
      ·
        refine ⟨83563211903199229803088733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222835231741864612808236621 83563211903199229803088733)
        ·
          refine ⟨31336204463699711176158275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 83563211903199229803088733 31336204463699711176158275)
          ·
            refine ⟨47004306695549566764237413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31336204463699711176158275 47004306695549566764237413)
            ·
              refine ⟨8813307505415543768294515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47004306695549566764237413 8813307505415543768294515)
              ·
                refine ⟨13219961258123315652441773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8813307505415543768294515 13219961258123315652441773)
                ·
                  refine ⟨4957485471796243369665665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13219961258123315652441773 4957485471796243369665665)
                  ·
                    refine ⟨3718114103847182527249249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4957485471796243369665665 3718114103847182527249249)
                    ·
                      refine ⟨2788585577885386895436937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718114103847182527249249 2788585577885386895436937)
                      ·
                        rfl

theorem cell23_5430751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_5430751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430751 prefixEnd_5430751 := by exact prefixLift 5430751
  have htrace : WordTrace (prefixWord ++ tailWord_5430751) baseStart_5430751 baseEnd_5430751 := by
    simpa [prefixWord, tailWord_5430751, baseEnd_5430751] using wordTrace_append hprefix tailTrace_5430751
  have hstable : (prefixWord ++ tailWord_5430751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430751).length < 2 ^ (prefixWord ++ tailWord_5430751).sum := by decide
  have hdescent : baseEnd_5430751 < baseStart_5430751 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430774 : List Nat := [5, 1, 1, 1, 2, 2, 4, 7]
def baseStart_5430774 : Nat := 118140960795 + 5430774 * 2 ^ 59
def prefixEnd_5430774 : Nat := 4983230072969 + 3 ^ 40 * 5430774 * 2
def baseEnd_5430774 : Nat := 103281384738534826127753

theorem tailTrace_5430774 : CollatzResearch.WordTrace tailWord_5430774 prefixEnd_5430774 103281384738534826127753 := by
  unfold tailWord_5430774
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379787526702548450129711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132051066951493850134716917 12379787526702548450129711)
  ·
    refine ⟨18569681290053822675194567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12379787526702548450129711 18569681290053822675194567)
    ·
      refine ⟨27854521935080734012791851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18569681290053822675194567 27854521935080734012791851)
      ·
        refine ⟨41781782902621101019187777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27854521935080734012791851 41781782902621101019187777)
        ·
          refine ⟨31336337176965825764390833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41781782902621101019187777 31336337176965825764390833)
          ·
            refine ⟨23502252882724369323293125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31336337176965825764390833 23502252882724369323293125)
            ·
              refine ⟨4406672415510819248117461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23502252882724369323293125 4406672415510819248117461)
              ·
                refine ⟨103281384738534826127753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4406672415510819248117461 103281384738534826127753)
                ·
                  rfl

theorem cell23_5430774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 4, 7].length) (baseStart_5430774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430774 prefixEnd_5430774 := by exact prefixLift 5430774
  have htrace : WordTrace (prefixWord ++ tailWord_5430774) baseStart_5430774 baseEnd_5430774 := by
    simpa [prefixWord, tailWord_5430774, baseEnd_5430774] using wordTrace_append hprefix tailTrace_5430774
  have hstable : (prefixWord ++ tailWord_5430774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430774).length < 2 ^ (prefixWord ++ tailWord_5430774).sum := by decide
  have hdescent : baseEnd_5430774 < baseStart_5430774 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430818 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 2, 1, 3]
def baseStart_5430818 : Nat := 118140960795 + 5430818 * 2 ^ 59
def prefixEnd_5430818 : Nat := 4983230072969 + 3 ^ 40 * 5430818 * 2
def baseEnd_5430818 : Nat := 2788619981089238133299129

theorem tailTrace_5430818 : CollatzResearch.WordTrace tailWord_5430818 prefixEnd_5430818 2788619981089238133299129 := by
  unfold tailWord_5430818
  simp only [CollatzResearch.WordTrace]
  refine ⟨49519551309770342679169277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132052136826054247144451405 49519551309770342679169277)
  ·
    refine ⟨18569831741163878504688479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 49519551309770342679169277 18569831741163878504688479)
    ·
      refine ⟨27854747611745817757032719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18569831741163878504688479 27854747611745817757032719)
      ·
        refine ⟨41782121417618726635549079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27854747611745817757032719 41782121417618726635549079)
        ·
          refine ⟨62673182126428089953323619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41782121417618726635549079 62673182126428089953323619)
          ·
            refine ⟨94009773189642134929985429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62673182126428089953323619 94009773189642134929985429)
            ·
              refine ⟨4406708118264475074843067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 94009773189642134929985429 4406708118264475074843067)
              ·
                refine ⟨6610062177396712612264601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406708118264475074843067 6610062177396712612264601)
                ·
                  refine ⟨4957546633047534459198451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6610062177396712612264601 4957546633047534459198451)
                  ·
                    refine ⟨7436319949571301688797677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4957546633047534459198451 7436319949571301688797677)
                    ·
                      refine ⟨2788619981089238133299129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7436319949571301688797677 2788619981089238133299129)
                      ·
                        rfl

theorem cell23_5430818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 2, 1, 3].length) (baseStart_5430818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430818 prefixEnd_5430818 := by exact prefixLift 5430818
  have htrace : WordTrace (prefixWord ++ tailWord_5430818) baseStart_5430818 baseEnd_5430818 := by
    simpa [prefixWord, tailWord_5430818, baseEnd_5430818] using wordTrace_append hprefix tailTrace_5430818
  have hstable : (prefixWord ++ tailWord_5430818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430818).length < 2 ^ (prefixWord ++ tailWord_5430818).sum := by decide
  have hdescent : baseEnd_5430818 < baseStart_5430818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430841 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5430841 : Nat := 118140960795 + 5430841 * 2 ^ 59
def prefixEnd_5430841 : Nat := 4983230072969 + 3 ^ 40 * 5430841 * 2
def baseEnd_5430841 : Nat := 2788631791144291543311523

theorem tailTrace_5430841 : CollatzResearch.WordTrace tailWord_5430841 prefixEnd_5430841 2788631791144291543311523 := by
  unfold tailWord_5430841
  simp only [CollatzResearch.WordTrace]
  refine ⟨198079044117998045644764377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132052696078665363763176251 198079044117998045644764377)
  ·
    refine ⟨148559283088498534233573283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198079044117998045644764377 148559283088498534233573283)
    ·
      refine ⟨222838924632747801350359925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148559283088498534233573283 222838924632747801350359925)
      ·
        refine ⟨20891149184320106376596243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222838924632747801350359925 20891149184320106376596243)
        ·
          refine ⟨31336723776480159564894365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20891149184320106376596243 31336723776480159564894365)
          ·
            refine ⟨11751271416180059836835387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31336723776480159564894365 11751271416180059836835387)
            ·
              refine ⟨17626907124270089755253081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11751271416180059836835387 17626907124270089755253081)
              ·
                refine ⟨13220180343202567316439811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17626907124270089755253081 13220180343202567316439811)
                ·
                  refine ⟨19830270514803850974659717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13220180343202567316439811 19830270514803850974659717)
                  ·
                    refine ⟨3718175721525722057748697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19830270514803850974659717 3718175721525722057748697)
                    ·
                      refine ⟨2788631791144291543311523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718175721525722057748697 2788631791144291543311523)
                      ·
                        rfl

theorem cell23_5430841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5430841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430841 prefixEnd_5430841 := by exact prefixLift 5430841
  have htrace : WordTrace (prefixWord ++ tailWord_5430841) baseStart_5430841 baseEnd_5430841 := by
    simpa [prefixWord, tailWord_5430841, baseEnd_5430841] using wordTrace_append hprefix tailTrace_5430841
  have hstable : (prefixWord ++ tailWord_5430841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430841).length < 2 ^ (prefixWord ++ tailWord_5430841).sum := by decide
  have hdescent : baseEnd_5430841 < baseStart_5430841 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430845 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 1, 3, 2]
def baseStart_5430845 : Nat := 118140960795 + 5430845 * 2 ^ 59
def prefixEnd_5430845 : Nat := 4983230072969 + 3 ^ 40 * 5430845 * 2
def baseEnd_5430845 : Nat := 2788633845066909527661505

theorem tailTrace_5430845 : CollatzResearch.WordTrace tailWord_5430845 prefixEnd_5430845 2788633845066909527661505 := by
  unfold tailWord_5430845
  simp only [CollatzResearch.WordTrace]
  refine ⟨198079190009983554327909989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132052793339989036218606659 198079190009983554327909989)
  ·
    refine ⟨37139848126871916436483123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198079190009983554327909989 37139848126871916436483123)
    ·
      refine ⟨55709772190307874654724685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37139848126871916436483123 55709772190307874654724685)
      ·
        refine ⟨20891164571365452995521757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55709772190307874654724685 20891164571365452995521757)
        ·
          refine ⟨7834186714262044873320659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 20891164571365452995521757 7834186714262044873320659)
          ·
            refine ⟨11751280071393067309980989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7834186714262044873320659 11751280071393067309980989)
            ·
              refine ⟨4406730026772400241242871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11751280071393067309980989 4406730026772400241242871)
              ·
                refine ⟨6610095040158600361864307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406730026772400241242871 6610095040158600361864307)
                ·
                  refine ⟨9915142560237900542796461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6610095040158600361864307 9915142560237900542796461)
                  ·
                    refine ⟨3718178460089212703548673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9915142560237900542796461 3718178460089212703548673)
                    ·
                      refine ⟨2788633845066909527661505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718178460089212703548673 2788633845066909527661505)
                      ·
                        rfl

theorem cell23_5430845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_5430845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430845 prefixEnd_5430845 := by exact prefixLift 5430845
  have htrace : WordTrace (prefixWord ++ tailWord_5430845) baseStart_5430845 baseEnd_5430845 := by
    simpa [prefixWord, tailWord_5430845, baseEnd_5430845] using wordTrace_append hprefix tailTrace_5430845
  have hstable : (prefixWord ++ tailWord_5430845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430845).length < 2 ^ (prefixWord ++ tailWord_5430845).sum := by decide
  have hdescent : baseEnd_5430845 < baseStart_5430845 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430857 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 3]
def baseStart_5430857 : Nat := 118140960795 + 5430857 * 2 ^ 59
def prefixEnd_5430857 : Nat := 4983230072969 + 3 ^ 40 * 5430857 * 2
def baseEnd_5430857 : Nat := 2788640006834763480711449

theorem tailTrace_5430857 : CollatzResearch.WordTrace tailWord_5430857 prefixEnd_5430857 2788640006834763480711449 := by
  unfold tailWord_5430857
  simp only [CollatzResearch.WordTrace]
  refine ⟨198079627685940080377346825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132053085123960053584897883 198079627685940080377346825)
  ·
    refine ⟨148559720764455060283010119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198079627685940080377346825 148559720764455060283010119)
    ·
      refine ⟨222839581146682590424515179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148559720764455060283010119 222839581146682590424515179)
      ·
        refine ⟨334259371720023885636772769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222839581146682590424515179 334259371720023885636772769)
        ·
          refine ⟨250694528790017914227579577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 334259371720023885636772769 250694528790017914227579577)
          ·
            refine ⟨188020896592513435670684683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250694528790017914227579577 188020896592513435670684683)
            ·
              refine ⟨282031344888770153506027025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188020896592513435670684683 282031344888770153506027025)
              ·
                refine ⟨211523508666577615129520269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282031344888770153506027025 211523508666577615129520269)
                ·
                  refine ⟨79321315749966605673570101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211523508666577615129520269 79321315749966605673570101)
                  ·
                    refine ⟨7436373351559369281897197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79321315749966605673570101 7436373351559369281897197)
                    ·
                      refine ⟨2788640006834763480711449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7436373351559369281897197 2788640006834763480711449)
                      ·
                        rfl

theorem cell23_5430857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 3, 5, 3].length) (baseStart_5430857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430857 prefixEnd_5430857 := by exact prefixLift 5430857
  have htrace : WordTrace (prefixWord ++ tailWord_5430857) baseStart_5430857 baseEnd_5430857 := by
    simpa [prefixWord, tailWord_5430857, baseEnd_5430857] using wordTrace_append hprefix tailTrace_5430857
  have hstable : (prefixWord ++ tailWord_5430857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430857).length < 2 ^ (prefixWord ++ tailWord_5430857).sum := by decide
  have hdescent : baseEnd_5430857 < baseStart_5430857 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430858 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_5430858 : Nat := 118140960795 + 5430858 * 2 ^ 59
def prefixEnd_5430858 : Nat := 4983230072969 + 3 ^ 40 * 5430858 * 2
def baseEnd_5430858 : Nat := 2788640520315417976798945

theorem tailTrace_5430858 : CollatzResearch.WordTrace tailWord_5430858 prefixEnd_5430858 2788640520315417976798945 := by
  unfold tailWord_5430858
  simp only [CollatzResearch.WordTrace]
  refine ⟨49519916039734114387033307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132053109439290971698755485 49519916039734114387033307)
  ·
    refine ⟨74279874059601171580549961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49519916039734114387033307 74279874059601171580549961)
    ·
      refine ⟨55709905544700878685412471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74279874059601171580549961 55709905544700878685412471)
      ·
        refine ⟨83564858317051318028118707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55709905544700878685412471 83564858317051318028118707)
        ·
          refine ⟨125347287475576977042178061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83564858317051318028118707 125347287475576977042178061)
          ·
            refine ⟨47005232803341366390816773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125347287475576977042178061 47005232803341366390816773)
            ·
              refine ⟨8813481150626506198278145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47005232803341366390816773 8813481150626506198278145)
              ·
                refine ⟨6610110862969879648708609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8813481150626506198278145 6610110862969879648708609)
                ·
                  refine ⟨4957583147227409736531457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6610110862969879648708609 4957583147227409736531457)
                  ·
                    refine ⟨3718187360420557302398593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4957583147227409736531457 3718187360420557302398593)
                    ·
                      refine ⟨2788640520315417976798945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718187360420557302398593 2788640520315417976798945)
                      ·
                        rfl

theorem cell23_5430858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_5430858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430858 prefixEnd_5430858 := by exact prefixLift 5430858
  have htrace : WordTrace (prefixWord ++ tailWord_5430858) baseStart_5430858 baseEnd_5430858 := by
    simpa [prefixWord, tailWord_5430858, baseEnd_5430858] using wordTrace_append hprefix tailTrace_5430858
  have hstable : (prefixWord ++ tailWord_5430858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430858).length < 2 ^ (prefixWord ++ tailWord_5430858).sum := by decide
  have hdescent : baseEnd_5430858 < baseStart_5430858 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430864 : List Nat := [2, 1, 1, 1, 1, 3, 5, 4, 5]
def baseStart_5430864 : Nat := 118140960795 + 5430864 * 2 ^ 59
def prefixEnd_5430864 : Nat := 4983230072969 + 3 ^ 40 * 5430864 * 2
def baseEnd_5430864 : Nat := 309849289022149439258213

theorem tailTrace_5430864 : CollatzResearch.WordTrace tailWord_5430864 prefixEnd_5430864 309849289022149439258213 := by
  unfold tailWord_5430864
  simp only [CollatzResearch.WordTrace]
  refine ⟨99039941498457360286425823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132053255331276480381901097 99039941498457360286425823)
  ·
    refine ⟨148559912247686040429638735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99039941498457360286425823 148559912247686040429638735)
    ·
      refine ⟨222839868371529060644458103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148559912247686040429638735 222839868371529060644458103)
      ·
        refine ⟨334259802557293590966687155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222839868371529060644458103 334259802557293590966687155)
        ·
          refine ⟨501389703835940386450030733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334259802557293590966687155 501389703835940386450030733)
          ·
            refine ⟨188021138938477644918761525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501389703835940386450030733 188021138938477644918761525)
            ·
              refine ⟨17626981775482279211133893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 188021138938477644918761525 17626981775482279211133893)
              ·
                refine ⟨3305059082902927352087605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17626981775482279211133893 3305059082902927352087605)
                ·
                  refine ⟨309849289022149439258213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3305059082902927352087605 309849289022149439258213)
                  ·
                    rfl

theorem cell23_5430864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 5, 4, 5].length) (baseStart_5430864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430864 prefixEnd_5430864 := by exact prefixLift 5430864
  have htrace : WordTrace (prefixWord ++ tailWord_5430864) baseStart_5430864 baseEnd_5430864 := by
    simpa [prefixWord, tailWord_5430864, baseEnd_5430864] using wordTrace_append hprefix tailTrace_5430864
  have hstable : (prefixWord ++ tailWord_5430864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430864).length < 2 ^ (prefixWord ++ tailWord_5430864).sum := by decide
  have hdescent : baseEnd_5430864 < baseStart_5430864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430887 : List Nat := [1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 7]
def baseStart_5430887 : Nat := 118140960795 + 5430887 * 2 ^ 59
def prefixEnd_5430887 : Nat := 4983230072969 + 3 ^ 40 * 5430887 * 2
def baseEnd_5430887 : Nat := 2788655411254398363336311

theorem tailTrace_5430887 : CollatzResearch.WordTrace tailWord_5430887 prefixEnd_5430887 2788655411254398363336311 := by
  unfold tailWord_5430887
  simp only [CollatzResearch.WordTrace]
  refine ⟨198080721875831395500938915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132053814583887597000625943 198080721875831395500938915)
  ·
    refine ⟨297121082813747093251408373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198080721875831395500938915 297121082813747093251408373)
    ·
      refine ⟨27855101513788789992319535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 297121082813747093251408373 27855101513788789992319535)
      ·
        refine ⟨41782652270683184988479303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27855101513788789992319535 41782652270683184988479303)
        ·
          refine ⟨62673978406024777482718955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41782652270683184988479303 62673978406024777482718955)
          ·
            refine ⟨94010967609037166224078433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62673978406024777482718955 94010967609037166224078433)
            ·
              refine ⟨70508225706777874668058825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94010967609037166224078433 70508225706777874668058825)
              ·
                refine ⟨52881169280083406001044119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70508225706777874668058825 52881169280083406001044119)
                ·
                  refine ⟨79321753920125109001566179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52881169280083406001044119 79321753920125109001566179)
                  ·
                    refine ⟨118982630880187663502349269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79321753920125109001566179 118982630880187663502349269)
                    ·
                      refine ⟨2788655411254398363336311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 118982630880187663502349269 2788655411254398363336311)
                      ·
                        rfl

theorem cell23_5430887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 2, 1, 1, 7].length) (baseStart_5430887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430887 prefixEnd_5430887 := by exact prefixLift 5430887
  have htrace : WordTrace (prefixWord ++ tailWord_5430887) baseStart_5430887 baseEnd_5430887 := by
    simpa [prefixWord, tailWord_5430887, baseEnd_5430887] using wordTrace_append hprefix tailTrace_5430887
  have hstable : (prefixWord ++ tailWord_5430887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430887).length < 2 ^ (prefixWord ++ tailWord_5430887).sum := by decide
  have hdescent : baseEnd_5430887 < baseStart_5430887 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430927 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 4]
def baseStart_5430927 : Nat := 118140960795 + 5430927 * 2 ^ 59
def prefixEnd_5430927 : Nat := 4983230072969 + 3 ^ 40 * 5430927 * 2
def baseEnd_5430927 : Nat := 2788675950480578206836127

theorem tailTrace_5430927 : CollatzResearch.WordTrace tailWord_5430927 prefixEnd_5430927 2788675950480578206836127 := by
  unfold tailWord_5430927
  simp only [CollatzResearch.WordTrace]
  refine ⟨198082180795686482332395035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132054787197124321554930023 198082180795686482332395035)
  ·
    refine ⟨297123271193529723498592553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198082180795686482332395035 297123271193529723498592553)
    ·
      refine ⟨222842453395147292623944415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297123271193529723498592553 222842453395147292623944415)
      ·
        refine ⟨334263680092720938935916623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222842453395147292623944415 334263680092720938935916623)
        ·
          refine ⟨501395520139081408403874935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334263680092720938935916623 501395520139081408403874935)
          ·
            refine ⟨752093280208622112605812403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501395520139081408403874935 752093280208622112605812403)
            ·
              refine ⟨1128139920312933168908718605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752093280208622112605812403 1128139920312933168908718605)
              ·
                refine ⟨423052470117349938340769477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1128139920312933168908718605 423052470117349938340769477)
                ·
                  refine ⟨79322338147003113438894277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423052470117349938340769477 79322338147003113438894277)
                  ·
                    refine ⟨14872938402563083769792677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 79322338147003113438894277 14872938402563083769792677)
                    ·
                      refine ⟨2788675950480578206836127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14872938402563083769792677 2788675950480578206836127)
                      ·
                        rfl

theorem cell23_5430927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 4, 4, 4].length) (baseStart_5430927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430927 prefixEnd_5430927 := by exact prefixLift 5430927
  have htrace : WordTrace (prefixWord ++ tailWord_5430927) baseStart_5430927 baseEnd_5430927 := by
    simpa [prefixWord, tailWord_5430927, baseEnd_5430927] using wordTrace_append hprefix tailTrace_5430927
  have hstable : (prefixWord ++ tailWord_5430927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430927).length < 2 ^ (prefixWord ++ tailWord_5430927).sum := by decide
  have hdescent : baseEnd_5430927 < baseStart_5430927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5430984 : List Nat := [2, 1, 3, 1, 2, 2, 2, 2, 3, 5]
def baseStart_5430984 : Nat := 118140960795 + 5430984 * 2 ^ 59
def prefixEnd_5430984 : Nat := 4983230072969 + 3 ^ 40 * 5430984 * 2
def baseEnd_5430984 : Nat := 929568406292628161274455

theorem tailTrace_5430984 : CollatzResearch.WordTrace tailWord_5430984 prefixEnd_5430984 929568406292628161274455 := by
  unfold tailWord_5430984
  simp only [CollatzResearch.WordTrace]
  refine ⟨99042129878239990533610003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132056173170986654044813337 99042129878239990533610003)
  ·
    refine ⟨148563194817359985800415005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99042129878239990533610003 148563194817359985800415005)
    ·
      refine ⟨55711198056509994675155627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148563194817359985800415005 55711198056509994675155627)
      ·
        refine ⟨83566797084764992012733441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55711198056509994675155627 83566797084764992012733441)
        ·
          refine ⟨62675097813573744009550081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83566797084764992012733441 62675097813573744009550081)
          ·
            refine ⟨47006323360180308007162561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62675097813573744009550081 47006323360180308007162561)
            ·
              refine ⟨35254742520135231005371921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47006323360180308007162561 35254742520135231005371921)
              ·
                refine ⟨26441056890101423254028941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35254742520135231005371921 26441056890101423254028941)
                ·
                  refine ⟨9915396333788033720260853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26441056890101423254028941 9915396333788033720260853)
                  ·
                    refine ⟨929568406292628161274455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9915396333788033720260853 929568406292628161274455)
                    ·
                      rfl

theorem cell23_5430984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 2, 3, 5].length) (baseStart_5430984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5430984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5430984 prefixEnd_5430984 := by exact prefixLift 5430984
  have htrace : WordTrace (prefixWord ++ tailWord_5430984) baseStart_5430984 baseEnd_5430984 := by
    simpa [prefixWord, tailWord_5430984, baseEnd_5430984] using wordTrace_append hprefix tailTrace_5430984
  have hstable : (prefixWord ++ tailWord_5430984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5430984).length < 2 ^ (prefixWord ++ tailWord_5430984).sum := by decide
  have hdescent : baseEnd_5430984 < baseStart_5430984 := by decide
  rcases family_descends (prefixWord ++ tailWord_5430984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431001 : List Nat := [1, 2, 1, 2, 3, 3, 3, 2, 1, 5]
def baseStart_5431001 : Nat := 118140960795 + 5431001 * 2 ^ 59
def prefixEnd_5431001 : Nat := 4983230072969 + 3 ^ 40 * 5431001 * 2
def baseEnd_5431001 : Nat := 929571316016336972436929

theorem tailTrace_5431001 : CollatzResearch.WordTrace tailWord_5431001 prefixEnd_5431001 929571316016336972436929 := by
  unfold tailWord_5431001
  simp only [CollatzResearch.WordTrace]
  refine ⟨198084879797418392970588857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132056586531612261980392571 198084879797418392970588857)
  ·
    refine ⟨148563659848063794727941643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198084879797418392970588857 148563659848063794727941643)
    ·
      refine ⟨222845489772095692091912465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148563659848063794727941643 222845489772095692091912465)
      ·
        refine ⟨167134117329071769068934349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222845489772095692091912465 167134117329071769068934349)
        ·
          refine ⟨62675293998401913400850381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167134117329071769068934349 62675293998401913400850381)
          ·
            refine ⟨23503235249400717525318893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62675293998401913400850381 23503235249400717525318893)
            ·
              refine ⟨8813713218525269071994585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23503235249400717525318893 8813713218525269071994585)
              ·
                refine ⟨6610284913893951803995939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8813713218525269071994585 6610284913893951803995939)
                ·
                  refine ⟨9915427370840927705993909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6610284913893951803995939 9915427370840927705993909)
                  ·
                    refine ⟨929571316016336972436929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9915427370840927705993909 929571316016336972436929)
                    ·
                      rfl

theorem cell23_5431001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 3, 2, 1, 5].length) (baseStart_5431001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431001 prefixEnd_5431001 := by exact prefixLift 5431001
  have htrace : WordTrace (prefixWord ++ tailWord_5431001) baseStart_5431001 baseEnd_5431001 := by
    simpa [prefixWord, tailWord_5431001, baseEnd_5431001] using wordTrace_append hprefix tailTrace_5431001
  have hstable : (prefixWord ++ tailWord_5431001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431001).length < 2 ^ (prefixWord ++ tailWord_5431001).sum := by decide
  have hdescent : baseEnd_5431001 < baseStart_5431001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431024 : List Nat := [2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5]
def baseStart_5431024 : Nat := 118140960795 + 5431024 * 2 ^ 59
def prefixEnd_5431024 : Nat := 4983230072969 + 3 ^ 40 * 5431024 * 2
def baseEnd_5431024 : Nat := 2788725758104064327323181

theorem tailTrace_5431024 : CollatzResearch.WordTrace tailWord_5431024 prefixEnd_5431024 2788725758104064327323181 := by
  unfold tailWord_5431024
  simp only [CollatzResearch.WordTrace]
  refine ⟨99042859338167533949338063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132057145784223378599117417 99042859338167533949338063)
  ·
    refine ⟨148564289007251300924007095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99042859338167533949338063 148564289007251300924007095)
    ·
      refine ⟨222846433510876951386010643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148564289007251300924007095 222846433510876951386010643)
      ·
        refine ⟨334269650266315427079015965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222846433510876951386010643 334269650266315427079015965)
        ·
          refine ⟨125351118849868285154630987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334269650266315427079015965 125351118849868285154630987)
          ·
            refine ⟨188026678274802427731946481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125351118849868285154630987 188026678274802427731946481)
            ·
              refine ⟨141020008706101820798959861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 188026678274802427731946481 141020008706101820798959861)
              ·
                refine ⟨13220625816197045699902487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 141020008706101820798959861 13220625816197045699902487)
                ·
                  refine ⟨19830938724295568549853731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13220625816197045699902487 19830938724295568549853731)
                  ·
                    refine ⟨29746408086443352824780597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19830938724295568549853731 29746408086443352824780597)
                    ·
                      refine ⟨2788725758104064327323181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29746408086443352824780597 2788725758104064327323181)
                      ·
                        rfl

theorem cell23_5431024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 5].length) (baseStart_5431024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431024 prefixEnd_5431024 := by exact prefixLift 5431024
  have htrace : WordTrace (prefixWord ++ tailWord_5431024) baseStart_5431024 baseEnd_5431024 := by
    simpa [prefixWord, tailWord_5431024, baseEnd_5431024] using wordTrace_append hprefix tailTrace_5431024
  have hstable : (prefixWord ++ tailWord_5431024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431024).length < 2 ^ (prefixWord ++ tailWord_5431024).sum := by decide
  have hdescent : baseEnd_5431024 < baseStart_5431024 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431031 : List Nat := [1, 1, 3, 1, 1, 1, 5, 4, 2, 4]
def baseStart_5431031 : Nat := 118140960795 + 5431031 * 2 ^ 59
def prefixEnd_5431031 : Nat := 4983230072969 + 3 ^ 40 * 5431031 * 2
def baseEnd_5431031 : Nat := 929576450822881933311883

theorem tailTrace_5431031 : CollatzResearch.WordTrace tailWord_5431031 prefixEnd_5431031 929576450822881933311883 := by
  unfold tailWord_5431031
  simp only [CollatzResearch.WordTrace]
  refine ⟨198085973987309708094180947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132057315991539805396120631 198085973987309708094180947)
  ·
    refine ⟨297128960980964562141271421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198085973987309708094180947 297128960980964562141271421)
    ·
      refine ⟨111423360367861710802976783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297128960980964562141271421 111423360367861710802976783)
      ·
        refine ⟨167135040551792566204465175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111423360367861710802976783 167135040551792566204465175)
        ·
          refine ⟨250702560827688849306697763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167135040551792566204465175 250702560827688849306697763)
          ·
            refine ⟨376053841241533273960046645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250702560827688849306697763 376053841241533273960046645)
            ·
              refine ⟨35255047616393744433754373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 376053841241533273960046645 35255047616393744433754373)
              ·
                refine ⟨6610321428073827081328945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35255047616393744433754373 6610321428073827081328945)
                ·
                  refine ⟨4957741071055370310996709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6610321428073827081328945 4957741071055370310996709)
                  ·
                    refine ⟨929576450822881933311883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4957741071055370310996709 929576450822881933311883)
                    ·
                      rfl

theorem cell23_5431031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 4, 2, 4].length) (baseStart_5431031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431031 prefixEnd_5431031 := by exact prefixLift 5431031
  have htrace : WordTrace (prefixWord ++ tailWord_5431031) baseStart_5431031 baseEnd_5431031 := by
    simpa [prefixWord, tailWord_5431031, baseEnd_5431031] using wordTrace_append hprefix tailTrace_5431031
  have hstable : (prefixWord ++ tailWord_5431031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431031).length < 2 ^ (prefixWord ++ tailWord_5431031).sum := by decide
  have hdescent : baseEnd_5431031 < baseStart_5431031 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431034 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4]
def baseStart_5431034 : Nat := 118140960795 + 5431034 * 2 ^ 59
def prefixEnd_5431034 : Nat := 4983230072969 + 3 ^ 40 * 5431034 * 2
def baseEnd_5431034 : Nat := 2788730892910609288198135

theorem tailTrace_5431034 : CollatzResearch.WordTrace tailWord_5431034 prefixEnd_5431034 2788730892910609288198135 := by
  unfold tailWord_5431034
  simp only [CollatzResearch.WordTrace]
  refine ⟨49521520851574709901635039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132057388937532559737693437 49521520851574709901635039)
  ·
    refine ⟨74282281277362064852452559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49521520851574709901635039 74282281277362064852452559)
    ·
      refine ⟨111423421916043097278678839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74282281277362064852452559 111423421916043097278678839)
      ·
        refine ⟨167135132874064645918018259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111423421916043097278678839 167135132874064645918018259)
        ·
          refine ⟨250702699311096968877027389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167135132874064645918018259 250702699311096968877027389)
          ·
            refine ⟨94013512241661363328885271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250702699311096968877027389 94013512241661363328885271)
            ·
              refine ⟨141020268362492044993327907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94013512241661363328885271 141020268362492044993327907)
              ·
                refine ⟨211530402543738067489991861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141020268362492044993327907 211530402543738067489991861)
                ·
                  refine ⟨19830975238475443827186737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 211530402543738067489991861 19830975238475443827186737)
                  ·
                    refine ⟨14873231428856582870390053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19830975238475443827186737 14873231428856582870390053)
                    ·
                      refine ⟨2788730892910609288198135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14873231428856582870390053 2788730892910609288198135)
                      ·
                        rfl

theorem cell23_5431034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 5, 2, 4].length) (baseStart_5431034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431034 prefixEnd_5431034 := by exact prefixLift 5431034
  have htrace : WordTrace (prefixWord ++ tailWord_5431034) baseStart_5431034 baseEnd_5431034 := by
    simpa [prefixWord, tailWord_5431034, baseEnd_5431034] using wordTrace_append hprefix tailTrace_5431034
  have hstable : (prefixWord ++ tailWord_5431034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431034).length < 2 ^ (prefixWord ++ tailWord_5431034).sum := by decide
  have hdescent : baseEnd_5431034 < baseStart_5431034 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431041 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 3]
def baseStart_5431041 : Nat := 118140960795 + 5431041 * 2 ^ 59
def prefixEnd_5431041 : Nat := 4983230072969 + 3 ^ 40 * 5431041 * 2
def baseEnd_5431041 : Nat := 2788734487275190760810603

theorem tailTrace_5431041 : CollatzResearch.WordTrace tailWord_5431041 prefixEnd_5431041 2788734487275190760810603 := by
  unfold tailWord_5431041
  simp only [CollatzResearch.WordTrace]
  refine ⟨198086338717273479802044977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132057559144848986534696651 198086338717273479802044977)
  ·
    refine ⟨148564754037955109851533733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198086338717273479802044977 148564754037955109851533733)
    ·
      refine ⟨27855891382116583097162575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148564754037955109851533733 27855891382116583097162575)
      ·
        refine ⟨41783837073174874645743863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27855891382116583097162575 41783837073174874645743863)
        ·
          refine ⟨62675755609762311968615795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41783837073174874645743863 62675755609762311968615795)
          ·
            refine ⟨94013633414643467952923693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62675755609762311968615795 94013633414643467952923693)
            ·
              refine ⟨35255112530491300482346385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94013633414643467952923693 35255112530491300482346385)
              ·
                refine ⟨26441334397868475361759789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35255112530491300482346385 26441334397868475361759789)
                ·
                  refine ⟨9915500399200678260659921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26441334397868475361759789 9915500399200678260659921)
                  ·
                    refine ⟨7436625299400508695494941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9915500399200678260659921 7436625299400508695494941)
                    ·
                      refine ⟨2788734487275190760810603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7436625299400508695494941 2788734487275190760810603)
                      ·
                        rfl

theorem cell23_5431041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 3, 2, 3].length) (baseStart_5431041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431041 prefixEnd_5431041 := by exact prefixLift 5431041
  have htrace : WordTrace (prefixWord ++ tailWord_5431041) baseStart_5431041 baseEnd_5431041 := by
    simpa [prefixWord, tailWord_5431041, baseEnd_5431041] using wordTrace_append hprefix tailTrace_5431041
  have hstable : (prefixWord ++ tailWord_5431041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431041).length < 2 ^ (prefixWord ++ tailWord_5431041).sum := by decide
  have hdescent : baseEnd_5431041 < baseStart_5431041 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431061 : List Nat := [1, 3, 2, 1, 2, 4, 3, 7]
def baseStart_5431061 : Nat := 118140960795 + 5431061 * 2 ^ 59
def prefixEnd_5431061 : Nat := 4983230072969 + 3 ^ 40 * 5431061 * 2
def baseEnd_5431061 : Nat := 103286842847714099354093

theorem tailTrace_5431061 : CollatzResearch.WordTrace tailWord_5431061 prefixEnd_5431061 103286842847714099354093 := by
  unfold tailWord_5431061
  simp only [CollatzResearch.WordTrace]
  refine ⟨198087068177201023217773037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132058045451467348811848691 198087068177201023217773037)
  ·
    refine ⟨74282650566450383706664889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198087068177201023217773037 74282650566450383706664889)
    ·
      refine ⟨55711987924837787779998667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74282650566450383706664889 55711987924837787779998667)
      ·
        refine ⟨83567981887256681669998001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55711987924837787779998667 83567981887256681669998001)
        ·
          refine ⟨62675986415442511252498501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83567981887256681669998001 62675986415442511252498501)
          ·
            refine ⟨11751747452895470859843469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62675986415442511252498501 11751747452895470859843469)
            ·
              refine ⟨4406905294835801572441301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11751747452895470859843469 4406905294835801572441301)
              ·
                refine ⟨103286842847714099354093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4406905294835801572441301 103286842847714099354093)
                ·
                  rfl

theorem cell23_5431061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 3, 7].length) (baseStart_5431061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431061 prefixEnd_5431061 := by exact prefixLift 5431061
  have htrace : WordTrace (prefixWord ++ tailWord_5431061) baseStart_5431061 baseEnd_5431061 := by
    simpa [prefixWord, tailWord_5431061, baseEnd_5431061] using wordTrace_append hprefix tailTrace_5431061
  have hstable : (prefixWord ++ tailWord_5431061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431061).length < 2 ^ (prefixWord ++ tailWord_5431061).sum := by decide
  have hdescent : baseEnd_5431061 < baseStart_5431061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431071 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 3]
def baseStart_5431071 : Nat := 118140960795 + 5431071 * 2 ^ 59
def prefixEnd_5431071 : Nat := 4983230072969 + 3 ^ 40 * 5431071 * 2
def baseEnd_5431071 : Nat := 2788749891694825643435465

theorem tailTrace_5431071 : CollatzResearch.WordTrace tailWord_5431071 prefixEnd_5431071 2788749891694825643435465 := by
  unfold tailWord_5431071
  simp only [CollatzResearch.WordTrace]
  refine ⟨198087432907164794925637067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132058288604776529950424711 198087432907164794925637067)
  ·
    refine ⟨297131149360747192388455601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198087432907164794925637067 297131149360747192388455601)
    ·
      refine ⟨222848362020560394291341701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297131149360747192388455601 222848362020560394291341701)
      ·
        refine ⟨41784067878855073929626569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 222848362020560394291341701 41784067878855073929626569)
        ·
          refine ⟨31338050909141305447219927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41784067878855073929626569 31338050909141305447219927)
          ·
            refine ⟨47007076363711958170829891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31338050909141305447219927 47007076363711958170829891)
            ·
              refine ⟨70510614545567937256244837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47007076363711958170829891 70510614545567937256244837)
              ·
                refine ⟨13220740227293988235545907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 70510614545567937256244837 13220740227293988235545907)
                ·
                  refine ⟨19831110340940982353318861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13220740227293988235545907 19831110340940982353318861)
                  ·
                    refine ⟨7436666377852868382494573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19831110340940982353318861 7436666377852868382494573)
                    ·
                      refine ⟨2788749891694825643435465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7436666377852868382494573 2788749891694825643435465)
                      ·
                        rfl

theorem cell23_5431071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_5431071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431071 prefixEnd_5431071 := by exact prefixLift 5431071
  have htrace : WordTrace (prefixWord ++ tailWord_5431071) baseStart_5431071 baseEnd_5431071 := by
    simpa [prefixWord, tailWord_5431071, baseEnd_5431071] using wordTrace_append hprefix tailTrace_5431071
  have hstable : (prefixWord ++ tailWord_5431071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431071).length < 2 ^ (prefixWord ++ tailWord_5431071).sum := by decide
  have hdescent : baseEnd_5431071 < baseStart_5431071 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431072 : List Nat := [2, 1, 1, 5, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5431072 : Nat := 118140960795 + 5431072 * 2 ^ 59
def prefixEnd_5431072 : Nat := 4983230072969 + 3 ^ 40 * 5431072 * 2
def baseEnd_5431072 : Nat := 2788750405175480139522961

theorem tailTrace_5431072 : CollatzResearch.WordTrace tailWord_5431072 prefixEnd_5431072 2788750405175480139522961 := by
  unfold tailWord_5431072
  simp only [CollatzResearch.WordTrace]
  refine ⟨99043734690080586048211735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132058312920107448064282313 99043734690080586048211735)
  ·
    refine ⟨148565602035120879072317603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99043734690080586048211735 148565602035120879072317603)
    ·
      refine ⟨222848403052681318608476405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148565602035120879072317603 222848403052681318608476405)
      ·
        refine ⟨20892037786188873619544663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 222848403052681318608476405 20892037786188873619544663)
        ·
          refine ⟨31338056679283310429316995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20892037786188873619544663 31338056679283310429316995)
          ·
            refine ⟨47007085018924965643975493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31338056679283310429316995 47007085018924965643975493)
            ·
              refine ⟨8813828441048431058245405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47007085018924965643975493 8813828441048431058245405)
              ·
                refine ⟨3305185665393161646842027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8813828441048431058245405 3305185665393161646842027)
                ·
                  refine ⟨4957778498089742470263041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305185665393161646842027 4957778498089742470263041)
                  ·
                    refine ⟨3718333873567306852697281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4957778498089742470263041 3718333873567306852697281)
                    ·
                      refine ⟨2788750405175480139522961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718333873567306852697281 2788750405175480139522961)
                      ·
                        rfl

theorem cell23_5431072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5431072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431072 prefixEnd_5431072 := by exact prefixLift 5431072
  have htrace : WordTrace (prefixWord ++ tailWord_5431072) baseStart_5431072 baseEnd_5431072 := by
    simpa [prefixWord, tailWord_5431072, baseEnd_5431072] using wordTrace_append hprefix tailTrace_5431072
  have hstable : (prefixWord ++ tailWord_5431072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431072).length < 2 ^ (prefixWord ++ tailWord_5431072).sum := by decide
  have hdescent : baseEnd_5431072 < baseStart_5431072 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431161 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 3]
def baseStart_5431161 : Nat := 118140960795 + 5431161 * 2 ^ 59
def prefixEnd_5431161 : Nat := 4983230072969 + 3 ^ 40 * 5431161 * 2
def baseEnd_5431161 : Nat := 2788796104953730291310051

theorem tailTrace_5431161 : CollatzResearch.WordTrace tailWord_5431161 prefixEnd_5431161 2788796104953730291310051 := by
  unfold tailWord_5431161
  simp only [CollatzResearch.WordTrace]
  refine ⟨198090715476838740296413337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132060476984559160197608891 198090715476838740296413337)
  ·
    refine ⟨148568036607629055222310003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198090715476838740296413337 148568036607629055222310003)
    ·
      refine ⟨222852054911443582833465005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148568036607629055222310003 222852054911443582833465005)
      ·
        refine ⟨83569520591791343562549377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222852054911443582833465005 83569520591791343562549377)
        ·
          refine ⟨62677140443843507671912033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83569520591791343562549377 62677140443843507671912033)
          ·
            refine ⟨47007855332882630753934025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62677140443843507671912033 47007855332882630753934025)
            ·
              refine ⟨35255891499661973065450519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47007855332882630753934025 35255891499661973065450519)
              ·
                refine ⟨52883837249492959598175779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35255891499661973065450519 52883837249492959598175779)
                ·
                  refine ⟨79325755874239439397263669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52883837249492959598175779 79325755874239439397263669)
                  ·
                    refine ⟨7436789613209947443493469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 79325755874239439397263669 7436789613209947443493469)
                    ·
                      refine ⟨2788796104953730291310051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7436789613209947443493469 2788796104953730291310051)
                      ·
                        rfl

theorem cell23_5431161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_5431161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431161 prefixEnd_5431161 := by exact prefixLift 5431161
  have htrace : WordTrace (prefixWord ++ tailWord_5431161) baseStart_5431161 baseEnd_5431161 := by
    simpa [prefixWord, tailWord_5431161, baseEnd_5431161] using wordTrace_append hprefix tailTrace_5431161
  have hstable : (prefixWord ++ tailWord_5431161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431161).length < 2 ^ (prefixWord ++ tailWord_5431161).sum := by decide
  have hdescent : baseEnd_5431161 < baseStart_5431161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431162 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2]
def baseStart_5431162 : Nat := 118140960795 + 5431162 * 2 ^ 59
def prefixEnd_5431162 : Nat := 4983230072969 + 3 ^ 40 * 5431162 * 2
def baseEnd_5431162 : Nat := 2788796618434384787397547

theorem tailTrace_5431162 : CollatzResearch.WordTrace tailWord_5431162 prefixEnd_5431162 2788796618434384787397547 := by
  unfold tailWord_5431162
  simp only [CollatzResearch.WordTrace]
  refine ⟨49522687987458779366799935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132060501299890078311466493 49522687987458779366799935)
  ·
    refine ⟨74284031981188169050199903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49522687987458779366799935 74284031981188169050199903)
    ·
      refine ⟨111426047971782253575299855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74284031981188169050199903 111426047971782253575299855)
      ·
        refine ⟨167139071957673380362949783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111426047971782253575299855 167139071957673380362949783)
        ·
          refine ⟨250708607936510070544424675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167139071957673380362949783 250708607936510070544424675)
          ·
            refine ⟨376062911904765105816637013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250708607936510070544424675 376062911904765105816637013)
            ·
              refine ⟨4406987248883966083788715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 376062911904765105816637013 4406987248883966083788715)
              ·
                refine ⟨6610480873325949125683073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4406987248883966083788715 6610480873325949125683073)
                ·
                  refine ⟨4957860654994461844262305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6610480873325949125683073 4957860654994461844262305)
                  ·
                    refine ⟨3718395491245846383196729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4957860654994461844262305 3718395491245846383196729)
                    ·
                      refine ⟨2788796618434384787397547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718395491245846383196729 2788796618434384787397547)
                      ·
                        rfl

theorem cell23_5431162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 2, 2].length) (baseStart_5431162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431162 prefixEnd_5431162 := by exact prefixLift 5431162
  have htrace : WordTrace (prefixWord ++ tailWord_5431162) baseStart_5431162 baseEnd_5431162 := by
    simpa [prefixWord, tailWord_5431162, baseEnd_5431162] using wordTrace_append hprefix tailTrace_5431162
  have hstable : (prefixWord ++ tailWord_5431162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431162).length < 2 ^ (prefixWord ++ tailWord_5431162).sum := by decide
  have hdescent : baseEnd_5431162 < baseStart_5431162 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431191 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 5]
def baseStart_5431191 : Nat := 118140960795 + 5431191 * 2 ^ 59
def prefixEnd_5431191 : Nat := 4983230072969 + 3 ^ 40 * 5431191 * 2
def baseEnd_5431191 : Nat := 2788811509373365173934913

theorem tailTrace_5431191 : CollatzResearch.WordTrace tailWord_5431191 prefixEnd_5431191 2788811509373365173934913 := by
  unfold tailWord_5431191
  simp only [CollatzResearch.WordTrace]
  refine ⟨198091809666730055420005427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132061206444486703613336951 198091809666730055420005427)
  ·
    refine ⟨297137714500095083130008141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198091809666730055420005427 297137714500095083130008141)
    ·
      refine ⟨111426642937535656173753053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297137714500095083130008141 111426642937535656173753053)
      ·
        refine ⟨41784991101575871065157395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111426642937535656173753053 41784991101575871065157395)
        ·
          refine ⟨62677486652363806597736093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41784991101575871065157395 62677486652363806597736093)
          ·
            refine ⟨23504057494636427474151035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62677486652363806597736093 23504057494636427474151035)
            ·
              refine ⟨35256086241954641211226553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23504057494636427474151035 35256086241954641211226553)
              ·
                refine ⟨26442064681465980908419915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35256086241954641211226553 26442064681465980908419915)
                ·
                  refine ⟨39663097022198971362629873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26442064681465980908419915 39663097022198971362629873)
                  ·
                    refine ⟨29747322766649228521972405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39663097022198971362629873 29747322766649228521972405)
                    ·
                      refine ⟨2788811509373365173934913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29747322766649228521972405 2788811509373365173934913)
                      ·
                        rfl

theorem cell23_5431191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_5431191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431191 prefixEnd_5431191 := by exact prefixLift 5431191
  have htrace : WordTrace (prefixWord ++ tailWord_5431191) baseStart_5431191 baseEnd_5431191 := by
    simpa [prefixWord, tailWord_5431191, baseEnd_5431191] using wordTrace_append hprefix tailTrace_5431191
  have hstable : (prefixWord ++ tailWord_5431191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431191).length < 2 ^ (prefixWord ++ tailWord_5431191).sum := by decide
  have hdescent : baseEnd_5431191 < baseStart_5431191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431258 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 8]
def baseStart_5431258 : Nat := 118140960795 + 5431258 * 2 ^ 59
def prefixEnd_5431258 : Nat := 4983230072969 + 3 ^ 40 * 5431258 * 2
def baseEnd_5431258 : Nat := 309871768064135156866345

theorem tailTrace_5431258 : CollatzResearch.WordTrace tailWord_5431258 prefixEnd_5431258 309871768064135156866345 := by
  unfold tailWord_5431258
  simp only [CollatzResearch.WordTrace]
  refine ⟨49523563339371831465673607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132062835571658217241796285 49523563339371831465673607)
  ·
    refine ⟨74285345009057747198510411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49523563339371831465673607 74285345009057747198510411)
    ·
      refine ⟨111428017513586620797765617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74285345009057747198510411 111428017513586620797765617)
      ·
        refine ⟨83571013135189965598324213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111428017513586620797765617 83571013135189965598324213)
        ·
          refine ⟨7834782481424059274842895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83571013135189965598324213 7834782481424059274842895)
          ·
            refine ⟨11752173722136088912264343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7834782481424059274842895 11752173722136088912264343)
            ·
              refine ⟨17628260583204133368396515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11752173722136088912264343 17628260583204133368396515)
              ·
                refine ⟨26442390874806200052594773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17628260583204133368396515 26442390874806200052594773)
                ·
                  refine ⟨309871768064135156866345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 26442390874806200052594773 309871768064135156866345)
                  ·
                    rfl

theorem cell23_5431258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 8].length) (baseStart_5431258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431258 prefixEnd_5431258 := by exact prefixLift 5431258
  have htrace : WordTrace (prefixWord ++ tailWord_5431258) baseStart_5431258 baseEnd_5431258 := by
    simpa [prefixWord, tailWord_5431258, baseEnd_5431258] using wordTrace_append hprefix tailTrace_5431258
  have hstable : (prefixWord ++ tailWord_5431258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431258).length < 2 ^ (prefixWord ++ tailWord_5431258).sum := by decide
  have hdescent : baseEnd_5431258 < baseStart_5431258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431288 : List Nat := [2, 1, 2, 1, 1, 3, 3, 4, 1, 5]
def baseStart_5431288 : Nat := 118140960795 + 5431288 * 2 ^ 59
def prefixEnd_5431288 : Nat := 4983230072969 + 3 ^ 40 * 5431288 * 2
def baseEnd_5431288 : Nat := 929620438998950431473989

theorem tailTrace_5431288 : CollatzResearch.WordTrace tailWord_5431288 prefixEnd_5431288 929620438998950431473989 := by
  unfold tailWord_5431288
  simp only [CollatzResearch.WordTrace]
  refine ⟨99047673773689320493143259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132063565031585760657524345 99047673773689320493143259)
  ·
    refine ⟨148571510660533980739714889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99047673773689320493143259 148571510660533980739714889)
    ·
      refine ⟨111428632995400485554786167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148571510660533980739714889 111428632995400485554786167)
      ·
        refine ⟨167142949493100728332179251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111428632995400485554786167 167142949493100728332179251)
        ·
          refine ⟨250714424239651092498268877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167142949493100728332179251 250714424239651092498268877)
          ·
            refine ⟨94017909089869159686850829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250714424239651092498268877 94017909089869159686850829)
            ·
              refine ⟨35256715908700934882569061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94017909089869159686850829 35256715908700934882569061)
              ·
                refine ⟨6610634232881425290481699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 35256715908700934882569061 6610634232881425290481699)
                ·
                  refine ⟨9915951349322137935722549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6610634232881425290481699 9915951349322137935722549)
                  ·
                    refine ⟨929620438998950431473989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9915951349322137935722549 929620438998950431473989)
                    ·
                      rfl

theorem cell23_5431288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 4, 1, 5].length) (baseStart_5431288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431288 prefixEnd_5431288 := by exact prefixLift 5431288
  have htrace : WordTrace (prefixWord ++ tailWord_5431288) baseStart_5431288 baseEnd_5431288 := by
    simpa [prefixWord, tailWord_5431288, baseEnd_5431288] using wordTrace_append hprefix tailTrace_5431288
  have hstable : (prefixWord ++ tailWord_5431288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431288).length < 2 ^ (prefixWord ++ tailWord_5431288).sum := by decide
  have hdescent : baseEnd_5431288 < baseStart_5431288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431319 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 3]
def baseStart_5431319 : Nat := 118140960795 + 5431319 * 2 ^ 59
def prefixEnd_5431319 : Nat := 4983230072969 + 3 ^ 40 * 5431319 * 2
def baseEnd_5431319 : Nat := 2788877234897140673134325

theorem tailTrace_5431319 : CollatzResearch.WordTrace tailWord_5431319 prefixEnd_5431319 2788877234897140673134325 := by
  unfold tailWord_5431319
  simp only [CollatzResearch.WordTrace]
  refine ⟨198096478210266333280665011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132064318806844222187110007 198096478210266333280665011)
  ·
    refine ⟨297144717315399499920997517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198096478210266333280665011 297144717315399499920997517)
    ·
      refine ⟨111429268993274812470374069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 297144717315399499920997517 111429268993274812470374069)
      ·
        refine ⟨10446493968119513669097569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111429268993274812470374069 10446493968119513669097569)
        ·
          refine ⟨7834870476089635251823177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10446493968119513669097569 7834870476089635251823177)
          ·
            refine ⟨5876152857067226438867383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7834870476089635251823177 5876152857067226438867383)
            ·
              refine ⟨8814229285600839658301075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876152857067226438867383 8814229285600839658301075)
              ·
                refine ⟨13221343928401259487451613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8814229285600839658301075 13221343928401259487451613)
                ·
                  refine ⟨4958003973150472307794355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13221343928401259487451613 4958003973150472307794355)
                  ·
                    refine ⟨7437005959725708461691533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4958003973150472307794355 7437005959725708461691533)
                    ·
                      refine ⟨2788877234897140673134325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7437005959725708461691533 2788877234897140673134325)
                      ·
                        rfl

theorem cell23_5431319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_5431319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431319 prefixEnd_5431319 := by exact prefixLift 5431319
  have htrace : WordTrace (prefixWord ++ tailWord_5431319) baseStart_5431319 baseEnd_5431319 := by
    simpa [prefixWord, tailWord_5431319, baseEnd_5431319] using wordTrace_append hprefix tailTrace_5431319
  have hstable : (prefixWord ++ tailWord_5431319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431319).length < 2 ^ (prefixWord ++ tailWord_5431319).sum := by decide
  have hdescent : baseEnd_5431319 < baseStart_5431319 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431342 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_5431342 : Nat := 118140960795 + 5431342 * 2 ^ 59
def prefixEnd_5431342 : Nat := 4983230072969 + 3 ^ 40 * 5431342 * 2
def baseEnd_5431342 : Nat := 2788889044952194083146719

theorem tailTrace_5431342 : CollatzResearch.WordTrace tailWord_5431342 prefixEnd_5431342 2788889044952194083146719 := by
  unfold tailWord_5431342
  simp only [CollatzResearch.WordTrace]
  refine ⟨24762164636147876026094035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132064878059455338805834853 24762164636147876026094035)
  ·
    refine ⟨37143246954221814039141053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24762164636147876026094035 37143246954221814039141053)
    ·
      refine ⟨13928717607833180264677895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37143246954221814039141053 13928717607833180264677895)
      ·
        refine ⟨20893076411749770397016843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13928717607833180264677895 20893076411749770397016843)
        ·
          refine ⟨31339614617624655595525265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20893076411749770397016843 31339614617624655595525265)
          ·
            refine ⟨23504710963218491696643949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31339614617624655595525265 23504710963218491696643949)
            ·
              refine ⟨8814266611206934386241481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23504710963218491696643949 8814266611206934386241481)
              ·
                refine ⟨6610699958405200789681111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8814266611206934386241481 6610699958405200789681111)
                ·
                  refine ⟨9916049937607801184521667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6610699958405200789681111 9916049937607801184521667)
                  ·
                    refine ⟨14874074906411701776782501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9916049937607801184521667 14874074906411701776782501)
                    ·
                      refine ⟨2788889044952194083146719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14874074906411701776782501 2788889044952194083146719)
                      ·
                        rfl

theorem cell23_5431342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_5431342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431342 prefixEnd_5431342 := by exact prefixLift 5431342
  have htrace : WordTrace (prefixWord ++ tailWord_5431342) baseStart_5431342 baseEnd_5431342 := by
    simpa [prefixWord, tailWord_5431342, baseEnd_5431342] using wordTrace_append hprefix tailTrace_5431342
  have hstable : (prefixWord ++ tailWord_5431342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431342).length < 2 ^ (prefixWord ++ tailWord_5431342).sum := by decide
  have hdescent : baseEnd_5431342 < baseStart_5431342 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431345 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 3]
def baseStart_5431345 : Nat := 118140960795 + 5431345 * 2 ^ 59
def prefixEnd_5431345 : Nat := 4983230072969 + 3 ^ 40 * 5431345 * 2
def baseEnd_5431345 : Nat := 2788890585394157571409205

theorem tailTrace_5431345 : CollatzResearch.WordTrace tailWord_5431345 prefixEnd_5431345 2788890585394157571409205 := by
  unfold tailWord_5431345
  simp only [CollatzResearch.WordTrace]
  refine ⟨198097426508172139721111489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132064951005448093147407659 198097426508172139721111489)
  ·
    refine ⟨148573069881129104790833617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198097426508172139721111489 148573069881129104790833617)
    ·
      refine ⟨111429802410846828593125213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148573069881129104790833617 111429802410846828593125213)
      ·
        refine ⟨41786175904067560722421955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111429802410846828593125213 41786175904067560722421955)
        ·
          refine ⟨62679263856101341083632933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41786175904067560722421955 62679263856101341083632933)
          ·
            refine ⟨11752361973019001453181175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62679263856101341083632933 11752361973019001453181175)
            ·
              refine ⟨17628542959528502179771763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11752361973019001453181175 17628542959528502179771763)
              ·
                refine ⟨26442814439292753269657645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17628542959528502179771763 26442814439292753269657645)
                ·
                  refine ⟨9916055414734782476121617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26442814439292753269657645 9916055414734782476121617)
                  ·
                    refine ⟨7437041561051086857091213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9916055414734782476121617 7437041561051086857091213)
                    ·
                      refine ⟨2788890585394157571409205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7437041561051086857091213 2788890585394157571409205)
                      ·
                        rfl

theorem cell23_5431345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_5431345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431345 prefixEnd_5431345 := by exact prefixLift 5431345
  have htrace : WordTrace (prefixWord ++ tailWord_5431345) baseStart_5431345 baseEnd_5431345 := by
    simpa [prefixWord, tailWord_5431345, baseEnd_5431345] using wordTrace_append hprefix tailTrace_5431345
  have hstable : (prefixWord ++ tailWord_5431345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431345).length < 2 ^ (prefixWord ++ tailWord_5431345).sum := by decide
  have hdescent : baseEnd_5431345 < baseStart_5431345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431382 : List Nat := [5, 2, 2, 1, 1, 1, 3, 8]
def baseStart_5431382 : Nat := 118140960795 + 5431382 * 2 ^ 59
def prefixEnd_5431382 : Nat := 4983230072969 + 3 ^ 40 * 5431382 * 2
def baseEnd_5431382 : Nat := 103292947562161997283205

theorem tailTrace_5431382 : CollatzResearch.WordTrace tailWord_5431382 prefixEnd_5431382 103292947562161997283205 := by
  unfold tailWord_5431382
  simp only [CollatzResearch.WordTrace]
  refine ⟨12381173500564880940013025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132065850672692063360138933 12381173500564880940013025)
  ·
    refine ⟨9285880125423660705009769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12381173500564880940013025 9285880125423660705009769)
    ·
      refine ⟨6964410094067745528757327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9285880125423660705009769 6964410094067745528757327)
      ·
        refine ⟨10446615141101618293135991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6964410094067745528757327 10446615141101618293135991)
        ·
          refine ⟨15669922711652427439703987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10446615141101618293135991 15669922711652427439703987)
          ·
            refine ⟨23504884067478641159555981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15669922711652427439703987 23504884067478641159555981)
            ·
              refine ⟨8814331525304490434833493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23504884067478641159555981 8814331525304490434833493)
              ·
                refine ⟨103292947562161997283205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8814331525304490434833493 103292947562161997283205)
                ·
                  rfl

theorem cell23_5431382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 3, 8].length) (baseStart_5431382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431382 prefixEnd_5431382 := by exact prefixLift 5431382
  have htrace : WordTrace (prefixWord ++ tailWord_5431382) baseStart_5431382 baseEnd_5431382 := by
    simpa [prefixWord, tailWord_5431382, baseEnd_5431382] using wordTrace_append hprefix tailTrace_5431382
  have hstable : (prefixWord ++ tailWord_5431382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431382).length < 2 ^ (prefixWord ++ tailWord_5431382).sum := by decide
  have hdescent : baseEnd_5431382 < baseStart_5431382 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431385 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 5, 3, 2]
def baseStart_5431385 : Nat := 118140960795 + 5431385 * 2 ^ 59
def prefixEnd_5431385 : Nat := 4983230072969 + 3 ^ 40 * 5431385 * 2
def baseEnd_5431385 : Nat := 2788911124620337414909021

theorem tailTrace_5431385 : CollatzResearch.WordTrace tailWord_5431385 prefixEnd_5431385 2788911124620337414909021 := by
  unfold tailWord_5431385
  simp only [CollatzResearch.WordTrace]
  refine ⟨198098885428027226552567609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132065923618684817701711739 198098885428027226552567609)
  ·
    refine ⟨148574164071020419914425707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198098885428027226552567609 148574164071020419914425707)
    ·
      refine ⟨222861246106530629871638561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148574164071020419914425707 222861246106530629871638561)
      ·
        refine ⟨167145934579897972403728921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222861246106530629871638561 167145934579897972403728921)
        ·
          refine ⟨125359450934923479302796691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 167145934579897972403728921 125359450934923479302796691)
          ·
            refine ⟨188039176402385218954195037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 125359450934923479302796691 188039176402385218954195037)
            ·
              refine ⟨70514691150894457107823139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 188039176402385218954195037 70514691150894457107823139)
              ·
                refine ⟨105772036726341685661734709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70514691150894457107823139 105772036726341685661734709)
                ·
                  refine ⟨9916128443094533030787629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 105772036726341685661734709 9916128443094533030787629)
                  ·
                    refine ⟨3718548166160449886545361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9916128443094533030787629 3718548166160449886545361)
                    ·
                      refine ⟨2788911124620337414909021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718548166160449886545361 2788911124620337414909021)
                      ·
                        rfl

theorem cell23_5431385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 3, 2].length) (baseStart_5431385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431385 prefixEnd_5431385 := by exact prefixLift 5431385
  have htrace : WordTrace (prefixWord ++ tailWord_5431385) baseStart_5431385 baseEnd_5431385 := by
    simpa [prefixWord, tailWord_5431385, baseEnd_5431385] using wordTrace_append hprefix tailTrace_5431385
  have hstable : (prefixWord ++ tailWord_5431385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431385).length < 2 ^ (prefixWord ++ tailWord_5431385).sum := by decide
  have hdescent : baseEnd_5431385 < baseStart_5431385 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431392 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 2, 1, 3]
def baseStart_5431392 : Nat := 118140960795 + 5431392 * 2 ^ 59
def prefixEnd_5431392 : Nat := 4983230072969 + 3 ^ 40 * 5431392 * 2
def baseEnd_5431392 : Nat := 2788914718984918887521489

theorem tailTrace_5431392 : CollatzResearch.WordTrace tailWord_5431392 prefixEnd_5431392 2788914718984918887521489 := by
  unfold tailWord_5431392
  simp only [CollatzResearch.WordTrace]
  refine ⟨99049570369500933374036215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132066093826001244498714953 99049570369500933374036215)
  ·
    refine ⟨148574355554251400061054323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99049570369500933374036215 148574355554251400061054323)
    ·
      refine ⟨222861533331377100091581485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148574355554251400061054323 222861533331377100091581485)
      ·
        refine ⟨83573074999266412534343057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222861533331377100091581485 83573074999266412534343057)
        ·
          refine ⟨62679806249449809400757293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83573074999266412534343057 62679806249449809400757293)
          ·
            refine ⟨23504927343543678525283985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62679806249449809400757293 23504927343543678525283985)
            ·
              refine ⟨17628695507657758893962989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23504927343543678525283985 17628695507657758893962989)
              ·
                refine ⟨6610760815371659585236121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17628695507657758893962989 6610760815371659585236121)
                ·
                  refine ⟨4958070611528744688927091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6610760815371659585236121 4958070611528744688927091)
                  ·
                    refine ⟨7437105917293117033390637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4958070611528744688927091 7437105917293117033390637)
                    ·
                      refine ⟨2788914718984918887521489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7437105917293117033390637 2788914718984918887521489)
                      ·
                        rfl

theorem cell23_5431392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_5431392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431392 prefixEnd_5431392 := by exact prefixLift 5431392
  have htrace : WordTrace (prefixWord ++ tailWord_5431392) baseStart_5431392 baseEnd_5431392 := by
    simpa [prefixWord, tailWord_5431392, baseEnd_5431392] using wordTrace_append hprefix tailTrace_5431392
  have hstable : (prefixWord ++ tailWord_5431392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431392).length < 2 ^ (prefixWord ++ tailWord_5431392).sum := by decide
  have hdescent : baseEnd_5431392 < baseStart_5431392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431455 : List Nat := [1, 1, 2, 6, 1, 1, 2, 2, 7]
def baseStart_5431455 : Nat := 118140960795 + 5431455 * 2 ^ 59
def prefixEnd_5431455 : Nat := 4983230072969 + 3 ^ 40 * 5431455 * 2
def baseEnd_5431455 : Nat := 309883007585128015670411

theorem tailTrace_5431455 : CollatzResearch.WordTrace tailWord_5431455 prefixEnd_5431455 309883007585128015670411 := by
  unfold tailWord_5431455
  simp only [CollatzResearch.WordTrace]
  refine ⟨198101438537773628507615819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132067625691849085671743879 198101438537773628507615819)
  ·
    refine ⟨297152157806660442761423729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198101438537773628507615819 297152157806660442761423729)
    ·
      refine ⟨222864118354995332071067797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297152157806660442761423729 222864118354995332071067797)
      ·
        refine ⟨10446755547890406190831303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 222864118354995332071067797 10446755547890406190831303)
        ·
          refine ⟨15670133321835609286246955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10446755547890406190831303 15670133321835609286246955)
          ·
            refine ⟨23505199982753413929370433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15670133321835609286246955 23505199982753413929370433)
            ·
              refine ⟨17628899987065060447027825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23505199982753413929370433 17628899987065060447027825)
              ·
                refine ⟨13221674990298795335270869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17628899987065060447027825 13221674990298795335270869)
                ·
                  refine ⟨309883007585128015670411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13221674990298795335270869 309883007585128015670411)
                  ·
                    rfl

theorem cell23_5431455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 2, 2, 7].length) (baseStart_5431455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431455 prefixEnd_5431455 := by exact prefixLift 5431455
  have htrace : WordTrace (prefixWord ++ tailWord_5431455) baseStart_5431455 baseEnd_5431455 := by
    simpa [prefixWord, tailWord_5431455, baseEnd_5431455] using wordTrace_append hprefix tailTrace_5431455
  have hstable : (prefixWord ++ tailWord_5431455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431455).length < 2 ^ (prefixWord ++ tailWord_5431455).sum := by decide
  have hdescent : baseEnd_5431455 < baseStart_5431455 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431475 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 7, 2]
def baseStart_5431475 : Nat := 118140960795 + 5431475 * 2 ^ 59
def prefixEnd_5431475 : Nat := 4983230072969 + 3 ^ 40 * 5431475 * 2
def baseEnd_5431475 : Nat := 2788957337879242062783607

theorem tailTrace_5431475 : CollatzResearch.WordTrace tailWord_5431475 prefixEnd_5431475 2788957337879242062783607 := by
  unfold tailWord_5431475
  simp only [CollatzResearch.WordTrace]
  refine ⟨198102167997701171923343879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132068111998467447948895919 198102167997701171923343879)
  ·
    refine ⟨297153251996551757885015819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198102167997701171923343879 297153251996551757885015819)
    ·
      refine ⟨445729877994827636827523729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297153251996551757885015819 445729877994827636827523729)
      ·
        refine ⟨334297408496120727620642797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445729877994827636827523729 334297408496120727620642797)
        ·
          refine ⟨125361528186045272857741049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334297408496120727620642797 125361528186045272857741049)
          ·
            refine ⟨94021146139533954643305787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125361528186045272857741049 94021146139533954643305787)
            ·
              refine ⟨141031719209300931964958681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94021146139533954643305787 141031719209300931964958681)
              ·
                refine ⟨105773789406975698973719011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 141031719209300931964958681 105773789406975698973719011)
                ·
                  refine ⟨158660684110463548460578517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 105773789406975698973719011 158660684110463548460578517)
                  ·
                    refine ⟨3718609783838989417044809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 158660684110463548460578517 3718609783838989417044809)
                    ·
                      refine ⟨2788957337879242062783607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718609783838989417044809 2788957337879242062783607)
                      ·
                        rfl

theorem cell23_5431475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 7, 2].length) (baseStart_5431475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431475 prefixEnd_5431475 := by exact prefixLift 5431475
  have htrace : WordTrace (prefixWord ++ tailWord_5431475) baseStart_5431475 baseEnd_5431475 := by
    simpa [prefixWord, tailWord_5431475, baseEnd_5431475] using wordTrace_append hprefix tailTrace_5431475
  have hstable : (prefixWord ++ tailWord_5431475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431475).length < 2 ^ (prefixWord ++ tailWord_5431475).sum := by decide
  have hdescent : baseEnd_5431475 < baseStart_5431475 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431489 : List Nat := [1, 2, 6, 1, 2, 2, 1, 1, 7]
def baseStart_5431489 : Nat := 118140960795 + 5431489 * 2 ^ 59
def prefixEnd_5431489 : Nat := 4983230072969 + 3 ^ 40 * 5431489 * 2
def baseEnd_5431489 : Nat := 309884947400933889778727

theorem tailTrace_5431489 : CollatzResearch.WordTrace tailWord_5431489 prefixEnd_5431489 309884947400933889778727 := by
  unfold tailWord_5431489
  simp only [CollatzResearch.WordTrace]
  refine ⟨198102678619650452314353521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132068452413100301542902347 198102678619650452314353521)
  ·
    refine ⟨148577008964737839235765141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198102678619650452314353521 148577008964737839235765141)
    ·
      refine ⟨6964547295222086214176491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148577008964737839235765141 6964547295222086214176491)
      ·
        refine ⟨10446820942833129321264737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6964547295222086214176491 10446820942833129321264737)
        ·
          refine ⟨7835115707124846990948553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10446820942833129321264737 7835115707124846990948553)
          ·
            refine ⟨5876336780343635243211415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7835115707124846990948553 5876336780343635243211415)
            ·
              refine ⟨8814505170515452864817123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876336780343635243211415 8814505170515452864817123)
              ·
                refine ⟨13221757755773179297225685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8814505170515452864817123 13221757755773179297225685)
                ·
                  refine ⟨309884947400933889778727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13221757755773179297225685 309884947400933889778727)
                  ·
                    rfl

theorem cell23_5431489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 1, 1, 7].length) (baseStart_5431489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431489 prefixEnd_5431489 := by exact prefixLift 5431489
  have htrace : WordTrace (prefixWord ++ tailWord_5431489) baseStart_5431489 baseEnd_5431489 := by
    simpa [prefixWord, tailWord_5431489, baseEnd_5431489] using wordTrace_append hprefix tailTrace_5431489
  have hstable : (prefixWord ++ tailWord_5431489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431489).length < 2 ^ (prefixWord ++ tailWord_5431489).sum := by decide
  have hdescent : baseEnd_5431489 < baseStart_5431489 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431500 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 2, 2, 2]
def baseStart_5431500 : Nat := 118140960795 + 5431500 * 2 ^ 59
def prefixEnd_5431500 : Nat := 4983230072969 + 3 ^ 40 * 5431500 * 2
def baseEnd_5431500 : Nat := 2788970174895604464970993

theorem tailTrace_5431500 : CollatzResearch.WordTrace tailWord_5431500 prefixEnd_5431500 2788970174895604464970993 := by
  unfold tailWord_5431500
  simp only [CollatzResearch.WordTrace]
  refine ⟨99051539911305300596501977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132068719881740400795335969 99051539911305300596501977)
  ·
    refine ⟨74288654933478975447376483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99051539911305300596501977 74288654933478975447376483)
    ·
      refine ⟨111432982400218463171064725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74288654933478975447376483 111432982400218463171064725)
      ·
        refine ⟨5223421050010240461143659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 111432982400218463171064725 5223421050010240461143659)
        ·
          refine ⟨7835131575015360691715489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223421050010240461143659 7835131575015360691715489)
          ·
            refine ⟨5876348681261520518786617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7835131575015360691715489 5876348681261520518786617)
            ·
              refine ⟨4407261510946140389089963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5876348681261520518786617 4407261510946140389089963)
              ·
                refine ⟨6610892266419210583634945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4407261510946140389089963 6610892266419210583634945)
                ·
                  refine ⟨4958169199814407937726209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6610892266419210583634945 4958169199814407937726209)
                  ·
                    refine ⟨3718626899860805953294657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958169199814407937726209 3718626899860805953294657)
                    ·
                      refine ⟨2788970174895604464970993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718626899860805953294657 2788970174895604464970993)
                      ·
                        rfl

theorem cell23_5431500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_5431500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431500 prefixEnd_5431500 := by exact prefixLift 5431500
  have htrace : WordTrace (prefixWord ++ tailWord_5431500) baseStart_5431500 baseEnd_5431500 := by
    simpa [prefixWord, tailWord_5431500, baseEnd_5431500] using wordTrace_append hprefix tailTrace_5431500
  have hstable : (prefixWord ++ tailWord_5431500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431500).length < 2 ^ (prefixWord ++ tailWord_5431500).sum := by decide
  have hdescent : baseEnd_5431500 < baseStart_5431500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431665 : List Nat := [1, 2, 2, 2, 1, 2, 1, 3, 2, 7]
def baseStart_5431665 : Nat := 118140960795 + 5431665 * 2 ^ 59
def prefixEnd_5431665 : Nat := 4983230072969 + 3 ^ 40 * 5431665 * 2
def baseEnd_5431665 : Nat := 929684966401198773135911

theorem tailTrace_5431665 : CollatzResearch.WordTrace tailWord_5431665 prefixEnd_5431665 929684966401198773135911 := by
  unfold tailWord_5431665
  simp only [CollatzResearch.WordTrace]
  refine ⟨198109097867012834372760449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132072731911341889581840299 198109097867012834372760449)
  ·
    refine ⟨148581823400259625779570337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198109097867012834372760449 148581823400259625779570337)
    ·
      refine ⟨111436367550194719334677753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148581823400259625779570337 111436367550194719334677753)
      ·
        refine ⟨83577275662646039501008315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 111436367550194719334677753 83577275662646039501008315)
        ·
          refine ⟨125365913493969059251512473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83577275662646039501008315 125365913493969059251512473)
          ·
            refine ⟨94024435120476794438634355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125365913493969059251512473 94024435120476794438634355)
            ·
              refine ⟨141036652680715191657951533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94024435120476794438634355 141036652680715191657951533)
              ·
                refine ⟨52888744755268196871731825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 141036652680715191657951533 52888744755268196871731825)
                ·
                  refine ⟨39666558566451147653798869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 52888744755268196871731825 39666558566451147653798869)
                  ·
                    refine ⟨929684966401198773135911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39666558566451147653798869 929684966401198773135911)
                    ·
                      rfl

theorem cell23_5431665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 7].length) (baseStart_5431665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431665 prefixEnd_5431665 := by exact prefixLift 5431665
  have htrace : WordTrace (prefixWord ++ tailWord_5431665) baseStart_5431665 baseEnd_5431665 := by
    simpa [prefixWord, tailWord_5431665, baseEnd_5431665] using wordTrace_append hprefix tailTrace_5431665
  have hstable : (prefixWord ++ tailWord_5431665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431665).length < 2 ^ (prefixWord ++ tailWord_5431665).sum := by decide
  have hdescent : baseEnd_5431665 < baseStart_5431665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431679 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 3]
def baseStart_5431679 : Nat := 118140960795 + 5431679 * 2 ^ 59
def prefixEnd_5431679 : Nat := 4983230072969 + 3 ^ 40 * 5431679 * 2
def baseEnd_5431679 : Nat := 2789062087932759264632669

theorem tailTrace_5431679 : CollatzResearch.WordTrace tailWord_5431679 prefixEnd_5431679 2789062087932759264632669 := by
  unfold tailWord_5431679
  simp only [CollatzResearch.WordTrace]
  refine ⟨198109608488962114763770091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132073072325974743175846727 198109608488962114763770091)
  ·
    refine ⟨297164412733443172145655137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198109608488962114763770091 297164412733443172145655137)
    ·
      refine ⟨222873309550082379109241353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297164412733443172145655137 222873309550082379109241353)
      ·
        refine ⟨167154982162561784331931015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222873309550082379109241353 167154982162561784331931015)
        ·
          refine ⟨250732473243842676497896523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167154982162561784331931015 250732473243842676497896523)
          ·
            refine ⟨376098709865764014746844785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250732473243842676497896523 376098709865764014746844785)
            ·
              refine ⟨282074032399323011060133589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376098709865764014746844785 282074032399323011060133589)
              ·
                refine ⟨6611110134359133071721881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 282074032399323011060133589 6611110134359133071721881)
                ·
                  refine ⟨4958332600769349803791411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6611110134359133071721881 4958332600769349803791411)
                  ·
                    refine ⟨7437498901154024705687117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4958332600769349803791411 7437498901154024705687117)
                    ·
                      refine ⟨2789062087932759264632669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7437498901154024705687117 2789062087932759264632669)
                      ·
                        rfl

theorem cell23_5431679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 2, 1, 3].length) (baseStart_5431679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431679 prefixEnd_5431679 := by exact prefixLift 5431679
  have htrace : WordTrace (prefixWord ++ tailWord_5431679) baseStart_5431679 baseEnd_5431679 := by
    simpa [prefixWord, tailWord_5431679, baseEnd_5431679] using wordTrace_append hprefix tailTrace_5431679
  have hstable : (prefixWord ++ tailWord_5431679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431679).length < 2 ^ (prefixWord ++ tailWord_5431679).sum := by decide
  have hdescent : baseEnd_5431679 < baseStart_5431679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431683 : List Nat := [1, 1, 1, 3, 7, 1, 1, 2, 1, 2, 3]
def baseStart_5431683 : Nat := 118140960795 + 5431683 * 2 ^ 59
def prefixEnd_5431683 : Nat := 4983230072969 + 3 ^ 40 * 5431683 * 2
def baseEnd_5431683 : Nat := 2789064141855377248982651

theorem tailTrace_5431683 : CollatzResearch.WordTrace tailWord_5431683 prefixEnd_5431683 2789064141855377248982651 := by
  unfold tailWord_5431683
  simp only [CollatzResearch.WordTrace]
  refine ⟨198109754380947623446915703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132073169587298415631277135 198109754380947623446915703)
  ·
    refine ⟨297164631571421435170373555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198109754380947623446915703 297164631571421435170373555)
    ·
      refine ⟨445746947357132152755560333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297164631571421435170373555 445746947357132152755560333)
      ·
        refine ⟨167155105258924557283335125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 445746947357132152755560333 167155105258924557283335125)
        ·
          refine ⟨3917697779506044311328167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 167155105258924557283335125 3917697779506044311328167)
          ·
            refine ⟨5876546669259066466992251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917697779506044311328167 5876546669259066466992251)
            ·
              refine ⟨8814820003888599700488377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876546669259066466992251 8814820003888599700488377)
              ·
                refine ⟨6611115002916449775366283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8814820003888599700488377 6611115002916449775366283)
                ·
                  refine ⟨9916672504374674663049425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6611115002916449775366283 9916672504374674663049425)
                  ·
                    refine ⟨7437504378281005997287069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9916672504374674663049425 7437504378281005997287069)
                    ·
                      refine ⟨2789064141855377248982651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7437504378281005997287069 2789064141855377248982651)
                      ·
                        rfl

theorem cell23_5431683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 1, 2, 1, 2, 3].length) (baseStart_5431683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431683 prefixEnd_5431683 := by exact prefixLift 5431683
  have htrace : WordTrace (prefixWord ++ tailWord_5431683) baseStart_5431683 baseEnd_5431683 := by
    simpa [prefixWord, tailWord_5431683, baseEnd_5431683] using wordTrace_append hprefix tailTrace_5431683
  have hstable : (prefixWord ++ tailWord_5431683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431683).length < 2 ^ (prefixWord ++ tailWord_5431683).sum := by decide
  have hdescent : baseEnd_5431683 < baseStart_5431683 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431685 : List Nat := [1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 8]
def baseStart_5431685 : Nat := 118140960795 + 5431685 * 2 ^ 59
def prefixEnd_5431685 : Nat := 4983230072969 + 3 ^ 40 * 5431685 * 2
def baseEnd_5431685 : Nat := 2789065168816686241157641

theorem tailTrace_5431685 : CollatzResearch.WordTrace tailWord_5431685 prefixEnd_5431685 2789065168816686241157641 := by
  unfold tailWord_5431685
  simp only [CollatzResearch.WordTrace]
  refine ⟨198109827326940377788488509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132073218217960251858992339 198109827326940377788488509)
  ·
    refine ⟨74291185247602641670683191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198109827326940377788488509 74291185247602641670683191)
    ·
      refine ⟨111436777871403962506024787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74291185247602641670683191 111436777871403962506024787)
      ·
        refine ⟨167155166807105943759037181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111436777871403962506024787 167155166807105943759037181)
        ·
          refine ⟨62683187552664728909638943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 167155166807105943759037181 62683187552664728909638943)
          ·
            refine ⟨94024781328997093364458415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62683187552664728909638943 94024781328997093364458415)
            ·
              refine ⟨141037171993495640046687623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94024781328997093364458415 141037171993495640046687623)
              ·
                refine ⟨211555757990243460070031435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141037171993495640046687623 211555757990243460070031435)
                ·
                  refine ⟨317333636985365190105047153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211555757990243460070031435 317333636985365190105047153)
                  ·
                    refine ⟨238000227739023892578785365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 317333636985365190105047153 238000227739023892578785365)
                    ·
                      refine ⟨2789065168816686241157641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 238000227739023892578785365 2789065168816686241157641)
                      ·
                        rfl

theorem cell23_5431685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 2, 8].length) (baseStart_5431685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431685 prefixEnd_5431685 := by exact prefixLift 5431685
  have htrace : WordTrace (prefixWord ++ tailWord_5431685) baseStart_5431685 baseEnd_5431685 := by
    simpa [prefixWord, tailWord_5431685, baseEnd_5431685] using wordTrace_append hprefix tailTrace_5431685
  have hstable : (prefixWord ++ tailWord_5431685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431685).length < 2 ^ (prefixWord ++ tailWord_5431685).sum := by decide
  have hdescent : baseEnd_5431685 < baseStart_5431685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431742 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 9]
def baseStart_5431742 : Nat := 118140960795 + 5431742 * 2 ^ 59
def prefixEnd_5431742 : Nat := 4983230072969 + 3 ^ 40 * 5431742 * 2
def baseEnd_5431742 : Nat := 309899381912665835349431

theorem tailTrace_5431742 : CollatzResearch.WordTrace tailWord_5431742 prefixEnd_5431742 309899381912665835349431 := by
  unfold tailWord_5431742
  simp only [CollatzResearch.WordTrace]
  refine ⟨24763988285966734565414185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132074604191822584348875653 24763988285966734565414185)
  ·
    refine ⟨18572991214475050924060639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 24763988285966734565414185 18572991214475050924060639)
    ·
      refine ⟨27859486821712576386090959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18572991214475050924060639 27859486821712576386090959)
      ·
        refine ⟨41789230232568864579136439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27859486821712576386090959 41789230232568864579136439)
        ·
          refine ⟨62683845348853296868704659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41789230232568864579136439 62683845348853296868704659)
          ·
            refine ⟨94025768023279945303056989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62683845348853296868704659 94025768023279945303056989)
            ·
              refine ⟨35259663008729979488646371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94025768023279945303056989 35259663008729979488646371)
              ·
                refine ⟨52889494513094969232969557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 35259663008729979488646371 52889494513094969232969557)
                ·
                  refine ⟨309899381912665835349431, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 52889494513094969232969557 309899381912665835349431)
                  ·
                    rfl

theorem cell23_5431742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 9].length) (baseStart_5431742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431742 prefixEnd_5431742 := by exact prefixLift 5431742
  have htrace : WordTrace (prefixWord ++ tailWord_5431742) baseStart_5431742 baseEnd_5431742 := by
    simpa [prefixWord, tailWord_5431742, baseEnd_5431742] using wordTrace_append hprefix tailTrace_5431742
  have hstable : (prefixWord ++ tailWord_5431742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431742).length < 2 ^ (prefixWord ++ tailWord_5431742).sum := by decide
  have hdescent : baseEnd_5431742 < baseStart_5431742 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431789 : List Nat := [1, 5, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_5431789 : Nat := 118140960795 + 5431789 * 2 ^ 59
def prefixEnd_5431789 : Nat := 4983230072969 + 3 ^ 40 * 5431789 * 2
def baseEnd_5431789 : Nat := 929706190268251278085721

theorem tailTrace_5431789 : CollatzResearch.WordTrace tailWord_5431789 prefixEnd_5431789 929706190268251278085721 := by
  unfold tailWord_5431789
  simp only [CollatzResearch.WordTrace]
  refine ⟨198113620518563603550274421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132075747012375735700182947 198113620518563603550274421)
  ·
    refine ⟨18573151923615337832838227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 198113620518563603550274421 18573151923615337832838227)
    ·
      refine ⟨27859727885423006749257341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18573151923615337832838227 27859727885423006749257341)
      ·
        refine ⟨10447397957033627530971503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27859727885423006749257341 10447397957033627530971503)
        ·
          refine ⟨15671096935550441296457255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10447397957033627530971503 15671096935550441296457255)
          ·
            refine ⟨23506645403325661944685883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15671096935550441296457255 23506645403325661944685883)
            ·
              refine ⟨35259968104988492917028825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23506645403325661944685883 35259968104988492917028825)
              ·
                refine ⟨26444976078741369687771619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35259968104988492917028825 26444976078741369687771619)
                ·
                  refine ⟨39667464118112054531657429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26444976078741369687771619 39667464118112054531657429)
                  ·
                    refine ⟨929706190268251278085721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 39667464118112054531657429 929706190268251278085721)
                    ·
                      rfl

theorem cell23_5431789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_5431789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431789 prefixEnd_5431789 := by exact prefixLift 5431789
  have htrace : WordTrace (prefixWord ++ tailWord_5431789) baseStart_5431789 baseEnd_5431789 := by
    simpa [prefixWord, tailWord_5431789, baseEnd_5431789] using wordTrace_append hprefix tailTrace_5431789
  have hstable : (prefixWord ++ tailWord_5431789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431789).length < 2 ^ (prefixWord ++ tailWord_5431789).sum := by decide
  have hdescent : baseEnd_5431789 < baseStart_5431789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431792 : List Nat := [2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4]
def baseStart_5431792 : Nat := 118140960795 + 5431792 * 2 ^ 59
def prefixEnd_5431792 : Nat := 4983230072969 + 3 ^ 40 * 5431792 * 2
def baseEnd_5431792 : Nat := 2789120111246717322519649

theorem tailTrace_5431792 : CollatzResearch.WordTrace tailWord_5431792 prefixEnd_5431792 2789120111246717322519649 := by
  unfold tailWord_5431792
  simp only [CollatzResearch.WordTrace]
  refine ⟨99056864968776367531316815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132075819958368490041755753 99056864968776367531316815)
  ·
    refine ⟨148585297453164551296975223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99056864968776367531316815 148585297453164551296975223)
    ·
      refine ⟨222877946179746826945462835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148585297453164551296975223 222877946179746826945462835)
      ·
        refine ⟨334316919269620240418194253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222877946179746826945462835 334316919269620240418194253)
        ·
          refine ⟨125368844726107590156822845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 334316919269620240418194253 125368844726107590156822845)
          ·
            refine ⟨47013316772290346308808567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125368844726107590156822845 47013316772290346308808567)
            ·
              refine ⟨70519975158435519463212851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47013316772290346308808567 70519975158435519463212851)
              ·
                refine ⟨105779962737653279194819277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70519975158435519463212851 105779962737653279194819277)
                ·
                  refine ⟨39667486026619979698057229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105779962737653279194819277 39667486026619979698057229)
                  ·
                    refine ⟨14875307259982492386771461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39667486026619979698057229 14875307259982492386771461)
                    ·
                      refine ⟨2789120111246717322519649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14875307259982492386771461 2789120111246717322519649)
                      ·
                        rfl

theorem cell23_5431792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 1, 3, 3, 4].length) (baseStart_5431792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431792 prefixEnd_5431792 := by exact prefixLift 5431792
  have htrace : WordTrace (prefixWord ++ tailWord_5431792) baseStart_5431792 baseEnd_5431792 := by
    simpa [prefixWord, tailWord_5431792, baseEnd_5431792] using wordTrace_append hprefix tailTrace_5431792
  have hstable : (prefixWord ++ tailWord_5431792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431792).length < 2 ^ (prefixWord ++ tailWord_5431792).sum := by decide
  have hdescent : baseEnd_5431792 < baseStart_5431792 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431809 : List Nat := [1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 4]
def baseStart_5431809 : Nat := 118140960795 + 5431809 * 2 ^ 59
def prefixEnd_5431809 : Nat := 4983230072969 + 3 ^ 40 * 5431809 * 2
def baseEnd_5431809 : Nat := 2789128840417843756007071

theorem tailTrace_5431809 : CollatzResearch.WordTrace tailWord_5431809 prefixEnd_5431809 2789128840417843756007071 := by
  unfold tailWord_5431809
  simp only [CollatzResearch.WordTrace]
  refine ⟨198114349978491146966002481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132076233318994097977334987 198114349978491146966002481)
  ·
    refine ⟨148585762483868360224501861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198114349978491146966002481 148585762483868360224501861)
    ·
      refine ⟨27859830465725317542094099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148585762483868360224501861 27859830465725317542094099)
      ·
        refine ⟨41789745698587976313141149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27859830465725317542094099 41789745698587976313141149)
        ·
          refine ⟨15671154636970491117427931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41789745698587976313141149 15671154636970491117427931)
          ·
            refine ⟨23506731955455736676141897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15671154636970491117427931 23506731955455736676141897)
            ·
              refine ⟨17630048966591802507106423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23506731955455736676141897 17630048966591802507106423)
              ·
                refine ⟨26445073449887703760659635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17630048966591802507106423 26445073449887703760659635)
                ·
                  refine ⟨39667610174831555640989453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26445073449887703760659635 39667610174831555640989453)
                  ·
                    refine ⟨14875353815561833365371045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 39667610174831555640989453 14875353815561833365371045)
                    ·
                      refine ⟨2789128840417843756007071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14875353815561833365371045 2789128840417843756007071)
                      ·
                        rfl

theorem cell23_5431809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 1, 1, 3, 4].length) (baseStart_5431809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431809 prefixEnd_5431809 := by exact prefixLift 5431809
  have htrace : WordTrace (prefixWord ++ tailWord_5431809) baseStart_5431809 baseEnd_5431809 := by
    simpa [prefixWord, tailWord_5431809, baseEnd_5431809] using wordTrace_append hprefix tailTrace_5431809
  have hstable : (prefixWord ++ tailWord_5431809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431809).length < 2 ^ (prefixWord ++ tailWord_5431809).sum := by decide
  have hdescent : baseEnd_5431809 < baseStart_5431809 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431810 : List Nat := [3, 4, 1, 2, 2, 2, 1, 3, 5]
def baseStart_5431810 : Nat := 118140960795 + 5431810 * 2 ^ 59
def prefixEnd_5431810 : Nat := 4983230072969 + 3 ^ 40 * 5431810 * 2
def baseEnd_5431810 : Nat := 309903261544277583566063

theorem tailTrace_5431810 : CollatzResearch.WordTrace tailWord_5431810 prefixEnd_5431810 309903261544277583566063 := by
  unfold tailWord_5431810
  simp only [CollatzResearch.WordTrace]
  refine ⟨49528596612871881034197221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132076257634325016091192589 49528596612871881034197221)
  ·
    refine ⟨9286611864913477693911979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49528596612871881034197221 9286611864913477693911979)
    ·
      refine ⟨13929917797370216540867969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9286611864913477693911979 13929917797370216540867969)
      ·
        refine ⟨10447438348027662405650977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13929917797370216540867969 10447438348027662405650977)
        ·
          refine ⟨7835578761020746804238233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10447438348027662405650977 7835578761020746804238233)
          ·
            refine ⟨5876684070765560103178675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7835578761020746804238233 5876684070765560103178675)
            ·
              refine ⟨8815026106148340154768013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876684070765560103178675 8815026106148340154768013)
              ·
                refine ⟨3305634789805627558038005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8815026106148340154768013 3305634789805627558038005)
                ·
                  refine ⟨309903261544277583566063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3305634789805627558038005 309903261544277583566063)
                  ·
                    rfl

theorem cell23_5431810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 2, 1, 3, 5].length) (baseStart_5431810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431810 prefixEnd_5431810 := by exact prefixLift 5431810
  have htrace : WordTrace (prefixWord ++ tailWord_5431810) baseStart_5431810 baseEnd_5431810 := by
    simpa [prefixWord, tailWord_5431810, baseEnd_5431810] using wordTrace_append hprefix tailTrace_5431810
  have hstable : (prefixWord ++ tailWord_5431810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431810).length < 2 ^ (prefixWord ++ tailWord_5431810).sum := by decide
  have hdescent : baseEnd_5431810 < baseStart_5431810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431836 : List Nat := [2, 2, 3, 1, 2, 2, 3, 1, 3, 4]
def baseStart_5431836 : Nat := 118140960795 + 5431836 * 2 ^ 59
def prefixEnd_5431836 : Nat := 4983230072969 + 3 ^ 40 * 5431836 * 2
def baseEnd_5431836 : Nat := 929714234798505050123149

theorem tailTrace_5431836 : CollatzResearch.WordTrace tailWord_5431836 prefixEnd_5431836 929714234798505050123149 := by
  unfold tailWord_5431836
  simp only [CollatzResearch.WordTrace]
  refine ⟨99057667374696665288617681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132076889832928887051490241 99057667374696665288617681)
  ·
    refine ⟨74293250531022498966463261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99057667374696665288617681 74293250531022498966463261)
    ·
      refine ⟨27859968949133437112423723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74293250531022498966463261 27859968949133437112423723)
      ·
        refine ⟨41789953423700155668635585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27859968949133437112423723 41789953423700155668635585)
        ·
          refine ⟨31342465067775116751476689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41789953423700155668635585 31342465067775116751476689)
          ·
            refine ⟨23506848800831337563607517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31342465067775116751476689 23506848800831337563607517)
            ·
              refine ⟨8815068300311751586352819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23506848800831337563607517 8815068300311751586352819)
              ·
                refine ⟨13222602450467627379529229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815068300311751586352819 13222602450467627379529229)
                ·
                  refine ⟨4958475918925360267323461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13222602450467627379529229 4958475918925360267323461)
                  ·
                    refine ⟨929714234798505050123149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4958475918925360267323461 929714234798505050123149)
                    ·
                      rfl

theorem cell23_5431836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_5431836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431836 prefixEnd_5431836 := by exact prefixLift 5431836
  have htrace : WordTrace (prefixWord ++ tailWord_5431836) baseStart_5431836 baseEnd_5431836 := by
    simpa [prefixWord, tailWord_5431836, baseEnd_5431836] using wordTrace_append hprefix tailTrace_5431836
  have hstable : (prefixWord ++ tailWord_5431836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431836).length < 2 ^ (prefixWord ++ tailWord_5431836).sum := by decide
  have hdescent : baseEnd_5431836 < baseStart_5431836 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431852 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 6]
def baseStart_5431852 : Nat := 118140960795 + 5431852 * 2 ^ 59
def prefixEnd_5431852 : Nat := 4983230072969 + 3 ^ 40 * 5431852 * 2
def baseEnd_5431852 : Nat := 2789150920085987087769373

theorem tailTrace_5431852 : CollatzResearch.WordTrace tailWord_5431852 prefixEnd_5431852 2789150920085987087769373 := by
  unfold tailWord_5431852
  simp only [CollatzResearch.WordTrace]
  refine ⟨99057959158667682654908905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132077278878223576873211873 99057959158667682654908905)
  ·
    refine ⟨74293469369000761991181679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99057959158667682654908905 74293469369000761991181679)
    ·
      refine ⟨111440204053501142986772519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74293469369000761991181679 111440204053501142986772519)
      ·
        refine ⟨167160306080251714480158779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111440204053501142986772519 167160306080251714480158779)
        ·
          refine ⟨250740459120377571720238169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167160306080251714480158779 250740459120377571720238169)
          ·
            refine ⟨188055344340283178790178627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250740459120377571720238169 188055344340283178790178627)
            ·
              refine ⟨282083016510424768185267941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188055344340283178790178627 282083016510424768185267941)
              ·
                refine ⟨52890565595704644034737739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 282083016510424768185267941 52890565595704644034737739)
                ·
                  refine ⟨79335848393556966052106609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 52890565595704644034737739 79335848393556966052106609)
                  ·
                    refine ⟨59501886295167724539079957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79335848393556966052106609 59501886295167724539079957)
                    ·
                      refine ⟨2789150920085987087769373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59501886295167724539079957 2789150920085987087769373)
                      ·
                        rfl

theorem cell23_5431852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 6].length) (baseStart_5431852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431852 prefixEnd_5431852 := by exact prefixLift 5431852
  have htrace : WordTrace (prefixWord ++ tailWord_5431852) baseStart_5431852 baseEnd_5431852 := by
    simpa [prefixWord, tailWord_5431852, baseEnd_5431852] using wordTrace_append hprefix tailTrace_5431852
  have hstable : (prefixWord ++ tailWord_5431852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431852).length < 2 ^ (prefixWord ++ tailWord_5431852).sum := by decide
  have hdescent : baseEnd_5431852 < baseStart_5431852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431860 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5431860 : Nat := 118140960795 + 5431860 * 2 ^ 59
def prefixEnd_5431860 : Nat := 4983230072969 + 3 ^ 40 * 5431860 * 2
def baseEnd_5431860 : Nat := 2789155027931223056469337

theorem tailTrace_5431860 : CollatzResearch.WordTrace tailWord_5431860 prefixEnd_5431860 2789155027931223056469337 := by
  unfold tailWord_5431860
  simp only [CollatzResearch.WordTrace]
  refine ⟨99058105050653191338054517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132077473400870921784072689 99058105050653191338054517)
  ·
    refine ⟨9286697348498736687942611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 99058105050653191338054517 9286697348498736687942611)
    ·
      refine ⟨13930046022748105031913917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9286697348498736687942611 13930046022748105031913917)
      ·
        refine ⟨5223767258530539386967719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13930046022748105031913917 5223767258530539386967719)
        ·
          refine ⟨7835650887795809080451579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5223767258530539386967719 7835650887795809080451579)
          ·
            refine ⟨11753476331693713620677369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835650887795809080451579 11753476331693713620677369)
            ·
              refine ⟨8815107248770285215508027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11753476331693713620677369 8815107248770285215508027)
              ·
                refine ⟨13222660873155427823262041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815107248770285215508027 13222660873155427823262041)
                ·
                  refine ⟨9916995654866570867446531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13222660873155427823262041 9916995654866570867446531)
                  ·
                    refine ⟨14875493482299856301169797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9916995654866570867446531 14875493482299856301169797)
                    ·
                      refine ⟨2789155027931223056469337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14875493482299856301169797 2789155027931223056469337)
                      ·
                        rfl

theorem cell23_5431860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5431860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431860 prefixEnd_5431860 := by exact prefixLift 5431860
  have htrace : WordTrace (prefixWord ++ tailWord_5431860) baseStart_5431860 baseEnd_5431860 := by
    simpa [prefixWord, tailWord_5431860, baseEnd_5431860] using wordTrace_append hprefix tailTrace_5431860
  have hstable : (prefixWord ++ tailWord_5431860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431860).length < 2 ^ (prefixWord ++ tailWord_5431860).sum := by decide
  have hdescent : baseEnd_5431860 < baseStart_5431860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431920 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 2, 3, 2]
def baseStart_5431920 : Nat := 118140960795 + 5431920 * 2 ^ 59
def prefixEnd_5431920 : Nat := 4983230072969 + 3 ^ 40 * 5431920 * 2
def baseEnd_5431920 : Nat := 2789185836770492821719061

theorem tailTrace_5431920 : CollatzResearch.WordTrace tailWord_5431920 prefixEnd_5431920 2789185836770492821719061 := by
  unfold tailWord_5431920
  simp only [CollatzResearch.WordTrace]
  refine ⟨99059199240544506461646607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132078932320726008615528809 99059199240544506461646607)
  ·
    refine ⟨148588798860816759692469911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99059199240544506461646607 148588798860816759692469911)
    ·
      refine ⟨222883198291225139538704867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148588798860816759692469911 222883198291225139538704867)
      ·
        refine ⟨334324797436837709308057301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222883198291225139538704867 334324797436837709308057301)
        ·
          refine ⟨7835737439925883811907593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 334324797436837709308057301 7835737439925883811907593)
          ·
            refine ⟨5876803079944412858930695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7835737439925883811907593 5876803079944412858930695)
            ·
              refine ⟨8815204619916619288396043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876803079944412858930695 8815204619916619288396043)
              ·
                refine ⟨13222806929874928932594065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815204619916619288396043 13222806929874928932594065)
                ·
                  refine ⟨9917105197406196699445549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13222806929874928932594065 9917105197406196699445549)
                  ·
                    refine ⟨3718914449027323762292081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9917105197406196699445549 3718914449027323762292081)
                    ·
                      refine ⟨2789185836770492821719061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718914449027323762292081 2789185836770492821719061)
                      ·
                        rfl

theorem cell23_5431920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 3, 2].length) (baseStart_5431920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431920 prefixEnd_5431920 := by exact prefixLift 5431920
  have htrace : WordTrace (prefixWord ++ tailWord_5431920) baseStart_5431920 baseEnd_5431920 := by
    simpa [prefixWord, tailWord_5431920, baseEnd_5431920] using wordTrace_append hprefix tailTrace_5431920
  have hstable : (prefixWord ++ tailWord_5431920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431920).length < 2 ^ (prefixWord ++ tailWord_5431920).sum := by decide
  have hdescent : baseEnd_5431920 < baseStart_5431920 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431933 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 4]
def baseStart_5431933 : Nat := 118140960795 + 5431933 * 2 ^ 59
def prefixEnd_5431933 : Nat := 4983230072969 + 3 ^ 40 * 5431933 * 2
def baseEnd_5431933 : Nat := 2789192512019001270856501

theorem tailTrace_5431933 : CollatzResearch.WordTrace tailWord_5431933 prefixEnd_5431933 2789192512019001270856501 := by
  unfold tailWord_5431933
  simp only [CollatzResearch.WordTrace]
  refine ⟨198118872630041916143516453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132079248420027944095677635 198118872630041916143516453)
  ·
    refine ⟨37147288618132859276909335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198118872630041916143516453 37147288618132859276909335)
    ·
      refine ⟨55720932927199288915364003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37147288618132859276909335 55720932927199288915364003)
      ·
        refine ⟨83581399390798933373046005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55720932927199288915364003 83581399390798933373046005)
        ·
          refine ⟨7835756192887400003723063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83581399390798933373046005 7835756192887400003723063)
          ·
            refine ⟨11753634289331100005584595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835756192887400003723063 11753634289331100005584595)
            ·
              refine ⟨17630451433996650008376893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11753634289331100005584595 17630451433996650008376893)
              ·
                refine ⟨6611419287748743753141335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17630451433996650008376893 6611419287748743753141335)
                ·
                  refine ⟨9917128931623115629712003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6611419287748743753141335 9917128931623115629712003)
                  ·
                    refine ⟨14875693397434673444568005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9917128931623115629712003 14875693397434673444568005)
                    ·
                      refine ⟨2789192512019001270856501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14875693397434673444568005 2789192512019001270856501)
                      ·
                        rfl

theorem cell23_5431933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 4].length) (baseStart_5431933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431933 prefixEnd_5431933 := by exact prefixLift 5431933
  have htrace : WordTrace (prefixWord ++ tailWord_5431933) baseStart_5431933 baseEnd_5431933 := by
    simpa [prefixWord, tailWord_5431933, baseEnd_5431933] using wordTrace_append hprefix tailTrace_5431933
  have hstable : (prefixWord ++ tailWord_5431933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431933).length < 2 ^ (prefixWord ++ tailWord_5431933).sum := by decide
  have hdescent : baseEnd_5431933 < baseStart_5431933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431950 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2]
def baseStart_5431950 : Nat := 118140960795 + 5431950 * 2 ^ 59
def prefixEnd_5431950 : Nat := 4983230072969 + 3 ^ 40 * 5431950 * 2
def baseEnd_5431950 : Nat := 2789201241190127704343923

theorem tailTrace_5431950 : CollatzResearch.WordTrace tailWord_5431950 prefixEnd_5431950 2789201241190127704343923 := by
  unfold tailWord_5431950
  simp only [CollatzResearch.WordTrace]
  refine ⟨24764936583872541005860663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132079661780653552031256869 24764936583872541005860663)
  ·
    refine ⟨37147404875808811508790995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24764936583872541005860663 37147404875808811508790995)
    ·
      refine ⟨55721107313713217263186493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37147404875808811508790995 55721107313713217263186493)
      ·
        refine ⟨20895415242642456473694935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55721107313713217263186493 20895415242642456473694935)
        ·
          refine ⟨31343122863963684710542403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20895415242642456473694935 31343122863963684710542403)
          ·
            refine ⟨47014684295945527065813605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31343122863963684710542403 47014684295945527065813605)
            ·
              refine ⟨8815253305489786324840051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47014684295945527065813605 8815253305489786324840051)
              ·
                refine ⟨13222879958234679487260077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815253305489786324840051 13222879958234679487260077)
                ·
                  refine ⟨4958579984338004807722529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13222879958234679487260077 4958579984338004807722529)
                  ·
                    refine ⟨3718934988253503605791897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958579984338004807722529 3718934988253503605791897)
                    ·
                      refine ⟨2789201241190127704343923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718934988253503605791897 2789201241190127704343923)
                      ·
                        rfl

theorem cell23_5431950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_5431950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431950 prefixEnd_5431950 := by exact prefixLift 5431950
  have htrace : WordTrace (prefixWord ++ tailWord_5431950) baseStart_5431950 baseEnd_5431950 := by
    simpa [prefixWord, tailWord_5431950, baseEnd_5431950] using wordTrace_append hprefix tailTrace_5431950
  have hstable : (prefixWord ++ tailWord_5431950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431950).length < 2 ^ (prefixWord ++ tailWord_5431950).sum := by decide
  have hdescent : baseEnd_5431950 < baseStart_5431950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5431990 : List Nat := [5, 1, 3, 1, 3, 1, 9]
def baseStart_5431990 : Nat := 118140960795 + 5431990 * 2 ^ 59
def prefixEnd_5431990 : Nat := 4983230072969 + 3 ^ 40 * 5431990 * 2
def baseEnd_5431990 : Nat := 34434836795263056146219

theorem tailTrace_5431990 : CollatzResearch.WordTrace tailWord_5431990 prefixEnd_5431990 34434836795263056146219 := by
  unfold tailWord_5431990
  simp only [CollatzResearch.WordTrace]
  refine ⟨12382559474427213429896339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 132080634393890276585560949 12382559474427213429896339)
  ·
    refine ⟨18573839211640820144844509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12382559474427213429896339 18573839211640820144844509)
    ·
      refine ⟨6965189704365307554316691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18573839211640820144844509 6965189704365307554316691)
      ·
        refine ⟨10447784556547961331475037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6965189704365307554316691 10447784556547961331475037)
        ·
          refine ⟨3917919208705485499303139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10447784556547961331475037 3917919208705485499303139)
          ·
            refine ⟨5876878813058228248954709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917919208705485499303139 5876878813058228248954709)
            ·
              refine ⟨34434836795263056146219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5876878813058228248954709 34434836795263056146219)
              ·
                rfl

theorem cell23_5431990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 9].length) (baseStart_5431990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5431990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5431990 prefixEnd_5431990 := by exact prefixLift 5431990
  have htrace : WordTrace (prefixWord ++ tailWord_5431990) baseStart_5431990 baseEnd_5431990 := by
    simpa [prefixWord, tailWord_5431990, baseEnd_5431990] using wordTrace_append hprefix tailTrace_5431990
  have hstable : (prefixWord ++ tailWord_5431990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5431990).length < 2 ^ (prefixWord ++ tailWord_5431990).sum := by decide
  have hdescent : baseEnd_5431990 < baseStart_5431990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5431990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432001 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 3, 2, 2]
def baseStart_5432001 : Nat := 118140960795 + 5432001 * 2 ^ 59
def prefixEnd_5432001 : Nat := 4983230072969 + 3 ^ 40 * 5432001 * 2
def baseEnd_5432001 : Nat := 2789227428703507004806189

theorem tailTrace_5432001 : CollatzResearch.WordTrace tailWord_5432001 prefixEnd_5432001 2789227428703507004806189 := by
  unfold tailWord_5432001
  simp only [CollatzResearch.WordTrace]
  refine ⟨198121352793795563756991857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132080901862530375837994571 198121352793795563756991857)
  ·
    refine ⟨148591014595346672817743893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198121352793795563756991857 148591014595346672817743893)
    ·
      refine ⟨6965203809156875288331745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 148591014595346672817743893 6965203809156875288331745)
      ·
        refine ⟨5223902856867656466248809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6965203809156875288331745 5223902856867656466248809)
        ·
          refine ⟨3917927142650742349686607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5223902856867656466248809 3917927142650742349686607)
          ·
            refine ⟨5876890713976113524529911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3917927142650742349686607 5876890713976113524529911)
            ·
              refine ⟨8815336070964170286794867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5876890713976113524529911 8815336070964170286794867)
              ·
                refine ⟨13223004106446255430192301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815336070964170286794867 13223004106446255430192301)
                ·
                  refine ⟨4958626539917345786322113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13223004106446255430192301 4958626539917345786322113)
                  ·
                    refine ⟨3718969904938009339741585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958626539917345786322113 3718969904938009339741585)
                    ·
                      refine ⟨2789227428703507004806189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718969904938009339741585 2789227428703507004806189)
                      ·
                        rfl

theorem cell23_5432001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_5432001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432001 prefixEnd_5432001 := by exact prefixLift 5432001
  have htrace : WordTrace (prefixWord ++ tailWord_5432001) baseStart_5432001 baseEnd_5432001 := by
    simpa [prefixWord, tailWord_5432001, baseEnd_5432001] using wordTrace_append hprefix tailTrace_5432001
  have hstable : (prefixWord ++ tailWord_5432001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432001).length < 2 ^ (prefixWord ++ tailWord_5432001).sum := by decide
  have hdescent : baseEnd_5432001 < baseStart_5432001 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432040 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 1, 4, 2]
def baseStart_5432040 : Nat := 118140960795 + 5432040 * 2 ^ 59
def prefixEnd_5432040 : Nat := 4983230072969 + 3 ^ 40 * 5432040 * 2
def baseEnd_5432040 : Nat := 2789247454449032352218509

theorem tailTrace_5432040 : CollatzResearch.WordTrace tailWord_5432040 prefixEnd_5432040 2789247454449032352218509 := by
  unfold tailWord_5432040
  simp only [CollatzResearch.WordTrace]
  refine ⟨99061387620327136708830787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132081850160436182278441049 99061387620327136708830787)
  ·
    refine ⟨148592081430490705063246181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99061387620327136708830787 148592081430490705063246181)
    ·
      refine ⟨27861015268217007199358659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 148592081430490705063246181 27861015268217007199358659)
      ·
        refine ⟨41791522902325510799037989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27861015268217007199358659 41791522902325510799037989)
        ·
          refine ⟨7835910544186033274819623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 41791522902325510799037989 7835910544186033274819623)
          ·
            refine ⟨11753865816279049912229435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7835910544186033274819623 11753865816279049912229435)
            ·
              refine ⟨17630798724418574868344153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11753865816279049912229435 17630798724418574868344153)
              ·
                refine ⟨13223099043313931151258115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17630798724418574868344153 13223099043313931151258115)
                ·
                  refine ⟨19834648564970896726887173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13223099043313931151258115 19834648564970896726887173)
                  ·
                    refine ⟨3718996605932043136291345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19834648564970896726887173 3718996605932043136291345)
                    ·
                      refine ⟨2789247454449032352218509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3718996605932043136291345 2789247454449032352218509)
                      ·
                        rfl

theorem cell23_5432040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_5432040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432040 prefixEnd_5432040 := by exact prefixLift 5432040
  have htrace : WordTrace (prefixWord ++ tailWord_5432040) baseStart_5432040 baseEnd_5432040 := by
    simpa [prefixWord, tailWord_5432040, baseEnd_5432040] using wordTrace_append hprefix tailTrace_5432040
  have hstable : (prefixWord ++ tailWord_5432040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432040).length < 2 ^ (prefixWord ++ tailWord_5432040).sum := by decide
  have hdescent : baseEnd_5432040 < baseStart_5432040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432056 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 2, 3, 3]
def baseStart_5432056 : Nat := 118140960795 + 5432056 * 2 ^ 59
def prefixEnd_5432056 : Nat := 4983230072969 + 3 ^ 40 * 5432056 * 2
def baseEnd_5432056 : Nat := 2789255670139504289618435

theorem tailTrace_5432056 : CollatzResearch.WordTrace tailWord_5432056 prefixEnd_5432056 2789255670139504289618435 := by
  unfold tailWord_5432056
  simp only [CollatzResearch.WordTrace]
  refine ⟨99061679404298154075122011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132082239205730872100162681 99061679404298154075122011)
  ·
    refine ⟨148592519106447231112683017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99061679404298154075122011 148592519106447231112683017)
    ·
      refine ⟨111444389329835423334512263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148592519106447231112683017 111444389329835423334512263)
      ·
        refine ⟨167166583994753135001768395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111444389329835423334512263 167166583994753135001768395)
        ·
          refine ⟨250749875992129702502652593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167166583994753135001768395 250749875992129702502652593)
          ·
            refine ⟨188062406994097276876989445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250749875992129702502652593 188062406994097276876989445)
            ·
              refine ⟨35261701311393239414435521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 188062406994097276876989445 35261701311393239414435521)
              ·
                refine ⟨26446275983544929560826641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35261701311393239414435521 26446275983544929560826641)
                ·
                  refine ⟨19834706987658697170619981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26446275983544929560826641 19834706987658697170619981)
                  ·
                    refine ⟨7438015120372011438982493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19834706987658697170619981 7438015120372011438982493)
                    ·
                      refine ⟨2789255670139504289618435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7438015120372011438982493 2789255670139504289618435)
                      ·
                        rfl

theorem cell23_5432056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 2, 3, 3].length) (baseStart_5432056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432056 prefixEnd_5432056 := by exact prefixLift 5432056
  have htrace : WordTrace (prefixWord ++ tailWord_5432056) baseStart_5432056 baseEnd_5432056 := by
    simpa [prefixWord, tailWord_5432056, baseEnd_5432056] using wordTrace_append hprefix tailTrace_5432056
  have hstable : (prefixWord ++ tailWord_5432056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432056).length < 2 ^ (prefixWord ++ tailWord_5432056).sum := by decide
  have hdescent : baseEnd_5432056 < baseStart_5432056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432089 : List Nat := [1, 2, 1, 2, 1, 1, 1, 3, 1, 10]
def baseStart_5432089 : Nat := 118140960795 + 5432089 * 2 ^ 59
def prefixEnd_5432089 : Nat := 4983230072969 + 3 ^ 40 * 5432089 * 2
def baseEnd_5432089 : Nat := 929757538333700886835261

theorem tailTrace_5432089 : CollatzResearch.WordTrace tailWord_5432089 prefixEnd_5432089 929757538333700886835261 := by
  unfold tailWord_5432089
  simp only [CollatzResearch.WordTrace]
  refine ⟨198124562417476754786195321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132083041611651169857463547 198124562417476754786195321)
  ·
    refine ⟨148593421813107566089646491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198124562417476754786195321 148593421813107566089646491)
    ·
      refine ⟨222890132719661349134469737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148593421813107566089646491 222890132719661349134469737)
      ·
        refine ⟨167167599539746011850852303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222890132719661349134469737 167167599539746011850852303)
        ·
          refine ⟨250751399309619017776278455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167167599539746011850852303 250751399309619017776278455)
          ·
            refine ⟨376127098964428526664417683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250751399309619017776278455 376127098964428526664417683)
            ·
              refine ⟨564190648446642789996626525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376127098964428526664417683 564190648446642789996626525)
              ·
                refine ⟨211571493167491046248734947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 564190648446642789996626525 211571493167491046248734947)
                ·
                  refine ⟨317357239751236569373102421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 211571493167491046248734947 317357239751236569373102421)
                  ·
                    refine ⟨929757538333700886835261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 317357239751236569373102421 929757538333700886835261)
                    ·
                      rfl

theorem cell23_5432089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 10].length) (baseStart_5432089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432089 prefixEnd_5432089 := by exact prefixLift 5432089
  have htrace : WordTrace (prefixWord ++ tailWord_5432089) baseStart_5432089 baseEnd_5432089 := by
    simpa [prefixWord, tailWord_5432089, baseEnd_5432089] using wordTrace_append hprefix tailTrace_5432089
  have hstable : (prefixWord ++ tailWord_5432089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432089).length < 2 ^ (prefixWord ++ tailWord_5432089).sum := by decide
  have hdescent : baseEnd_5432089 < baseStart_5432089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432113 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 4, 4, 2]
def baseStart_5432113 : Nat := 118140960795 + 5432113 * 2 ^ 59
def prefixEnd_5432113 : Nat := 4983230072969 + 3 ^ 40 * 5432113 * 2
def baseEnd_5432113 : Nat := 2789284938536810566605673

theorem tailTrace_5432113 : CollatzResearch.WordTrace tailWord_5432113 prefixEnd_5432113 2789284938536810566605673 := by
  unfold tailWord_5432113
  simp only [CollatzResearch.WordTrace]
  refine ⟨198125437769389806885068993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132083625179593204590045995 198125437769389806885068993)
  ·
    refine ⟨148594078327042355163801745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198125437769389806885068993 148594078327042355163801745)
    ·
      refine ⟨111445558745281766372851309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148594078327042355163801745 111445558745281766372851309)
      ·
        refine ⟨41792084529480662389819241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111445558745281766372851309 41792084529480662389819241)
        ·
          refine ⟨31344063397110496792364431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41792084529480662389819241 31344063397110496792364431)
          ·
            refine ⟨47016095095665745188546647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31344063397110496792364431 47016095095665745188546647)
            ·
              refine ⟨70524142643498617782819971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47016095095665745188546647 70524142643498617782819971)
              ·
                refine ⟨105786213965247926674229957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70524142643498617782819971 105786213965247926674229957)
                ·
                  refine ⟨19834915118483986251418117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 105786213965247926674229957 19834915118483986251418117)
                  ·
                    refine ⟨3719046584715747422140897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19834915118483986251418117 3719046584715747422140897)
                    ·
                      refine ⟨2789284938536810566605673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719046584715747422140897 2789284938536810566605673)
                      ·
                        rfl

theorem cell23_5432113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_5432113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432113 prefixEnd_5432113 := by exact prefixLift 5432113
  have htrace : WordTrace (prefixWord ++ tailWord_5432113) baseStart_5432113 baseEnd_5432113 := by
    simpa [prefixWord, tailWord_5432113, baseEnd_5432113] using wordTrace_append hprefix tailTrace_5432113
  have hstable : (prefixWord ++ tailWord_5432113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432113).length < 2 ^ (prefixWord ++ tailWord_5432113).sum := by decide
  have hdescent : baseEnd_5432113 < baseStart_5432113 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432174 : List Nat := [4, 1, 2, 3, 3, 1, 1, 1, 3, 4]
def baseStart_5432174 : Nat := 118140960795 + 5432174 * 2 ^ 59
def prefixEnd_5432174 : Nat := 4983230072969 + 3 ^ 40 * 5432174 * 2
def baseEnd_5432174 : Nat := 929772086952244942647631

theorem tailTrace_5432174 : CollatzResearch.WordTrace tailWord_5432174 prefixEnd_5432174 929772086952244942647631 := by
  unfold tailWord_5432174
  simp only [CollatzResearch.WordTrace]
  refine ⟨24765957827771101787879947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132085108414779209535359717 24765957827771101787879947)
  ·
    refine ⟨37148936741656652681819921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24765957827771101787879947 37148936741656652681819921)
    ·
      refine ⟨27861702556242489511364941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37148936741656652681819921 27861702556242489511364941)
      ·
        refine ⟨10448138458590933566761853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27861702556242489511364941 10448138458590933566761853)
        ·
          refine ⟨3918051921971600087535695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10448138458590933566761853 3918051921971600087535695)
          ·
            refine ⟨5877077882957400131303543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918051921971600087535695 5877077882957400131303543)
            ·
              refine ⟨8815616824436100196955315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5877077882957400131303543 8815616824436100196955315)
              ·
                refine ⟨13223425236654150295432973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8815616824436100196955315 13223425236654150295432973)
                ·
                  refine ⟨4958784463745306360787365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13223425236654150295432973 4958784463745306360787365)
                  ·
                    refine ⟨929772086952244942647631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4958784463745306360787365 929772086952244942647631)
                    ·
                      rfl

theorem cell23_5432174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_5432174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432174 prefixEnd_5432174 := by exact prefixLift 5432174
  have htrace : WordTrace (prefixWord ++ tailWord_5432174) baseStart_5432174 baseEnd_5432174 := by
    simpa [prefixWord, tailWord_5432174, baseEnd_5432174] using wordTrace_append hprefix tailTrace_5432174
  have hstable : (prefixWord ++ tailWord_5432174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432174).length < 2 ^ (prefixWord ++ tailWord_5432174).sum := by decide
  have hdescent : baseEnd_5432174 < baseStart_5432174 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432186 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4]
def baseStart_5432186 : Nat := 118140960795 + 5432186 * 2 ^ 59
def prefixEnd_5432186 : Nat := 4983230072969 + 3 ^ 40 * 5432186 * 2
def baseEnd_5432186 : Nat := 2789322422624588780992837

theorem tailTrace_5432186 : CollatzResearch.WordTrace tailWord_5432186 prefixEnd_5432186 2789322422624588780992837 := by
  unfold tailWord_5432186
  simp only [CollatzResearch.WordTrace]
  refine ⟨49532025074531335088119103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132085400198750226901650941 49532025074531335088119103)
  ·
    refine ⟨74298037611797002632178655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49532025074531335088119103 74298037611797002632178655)
    ·
      refine ⟨111447056417695503948267983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74298037611797002632178655 111447056417695503948267983)
      ·
        refine ⟨167170584626543255922401975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111447056417695503948267983 167170584626543255922401975)
        ·
          refine ⟨250755876939814883883602963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167170584626543255922401975 250755876939814883883602963)
          ·
            refine ⟨376133815409722325825404445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250755876939814883883602963 376133815409722325825404445)
            ·
              refine ⟨141050180778645872184526667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376133815409722325825404445 141050180778645872184526667)
              ·
                refine ⟨211575271167968808276790001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141050180778645872184526667 211575271167968808276790001)
                ·
                  refine ⟨158681453375976606207592501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211575271167968808276790001 158681453375976606207592501)
                  ·
                    refine ⟨14876386253997806831961797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 158681453375976606207592501 14876386253997806831961797)
                    ·
                      refine ⟨2789322422624588780992837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14876386253997806831961797 2789322422624588780992837)
                      ·
                        rfl

theorem cell23_5432186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 2, 5, 4].length) (baseStart_5432186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432186 prefixEnd_5432186 := by exact prefixLift 5432186
  have htrace : WordTrace (prefixWord ++ tailWord_5432186) baseStart_5432186 baseEnd_5432186 := by
    simpa [prefixWord, tailWord_5432186, baseEnd_5432186] using wordTrace_append hprefix tailTrace_5432186
  have hstable : (prefixWord ++ tailWord_5432186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432186).length < 2 ^ (prefixWord ++ tailWord_5432186).sum := by decide
  have hdescent : baseEnd_5432186 < baseStart_5432186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432200 : List Nat := [2, 1, 3, 3, 2, 1, 3, 2, 1, 5]
def baseStart_5432200 : Nat := 118140960795 + 5432200 * 2 ^ 59
def prefixEnd_5432200 : Nat := 4983230072969 + 3 ^ 40 * 5432200 * 2
def baseEnd_5432200 : Nat := 929776537117917242072591

theorem tailTrace_5432200 : CollatzResearch.WordTrace tailWord_5432200 prefixEnd_5432200 929776537117917242072591 := by
  unfold tailWord_5432200
  simp only [CollatzResearch.WordTrace]
  refine ⟨99064305460037310371743027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132085740613383080495657369 99064305460037310371743027)
  ·
    refine ⟨148596458190055965557614541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99064305460037310371743027 148596458190055965557614541)
    ·
      refine ⟨55723671821270987084105453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148596458190055965557614541 55723671821270987084105453)
      ·
        refine ⟨20896376932976620156539545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55723671821270987084105453 20896376932976620156539545)
        ·
          refine ⟨15672282699732465117404659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20896376932976620156539545 15672282699732465117404659)
          ·
            refine ⟨23508424049598697676106989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15672282699732465117404659 23508424049598697676106989)
            ·
              refine ⟨8815659018599511628540121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23508424049598697676106989 8815659018599511628540121)
              ·
                refine ⟨6611744263949633721405091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8815659018599511628540121 6611744263949633721405091)
                ·
                  refine ⟨9917616395924450582107637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6611744263949633721405091 9917616395924450582107637)
                  ·
                    refine ⟨929776537117917242072591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9917616395924450582107637 929776537117917242072591)
                    ·
                      rfl

theorem cell23_5432200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 3, 2, 1, 5].length) (baseStart_5432200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432200 prefixEnd_5432200 := by exact prefixLift 5432200
  have htrace : WordTrace (prefixWord ++ tailWord_5432200) baseStart_5432200 baseEnd_5432200 := by
    simpa [prefixWord, tailWord_5432200, baseEnd_5432200] using wordTrace_append hprefix tailTrace_5432200
  have hstable : (prefixWord ++ tailWord_5432200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432200).length < 2 ^ (prefixWord ++ tailWord_5432200).sum := by decide
  have hdescent : baseEnd_5432200 < baseStart_5432200 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432203 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 2, 6, 2]
def baseStart_5432203 : Nat := 118140960795 + 5432203 * 2 ^ 59
def prefixEnd_5432203 : Nat := 4983230072969 + 3 ^ 40 * 5432203 * 2
def baseEnd_5432203 : Nat := 2789331151795715214480259

theorem tailTrace_5432203 : CollatzResearch.WordTrace tailWord_5432203 prefixEnd_5432203 2789331151795715214480259 := by
  unfold tailWord_5432203
  simp only [CollatzResearch.WordTrace]
  refine ⟨198128720339063752255845263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132085813559375834837230175 198128720339063752255845263)
  ·
    refine ⟨297193080508595628383767895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198128720339063752255845263 297193080508595628383767895)
    ·
      refine ⟨445789620762893442575651843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297193080508595628383767895 445789620762893442575651843)
      ·
        refine ⟨668684431144340163863477765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445789620762893442575651843 668684431144340163863477765)
        ·
          refine ⟨125378330839563780724402081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 668684431144340163863477765 125378330839563780724402081)
          ·
            refine ⟨94033748129672835543301561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 125378330839563780724402081 94033748129672835543301561)
            ·
              refine ⟨70525311097254626657476171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 94033748129672835543301561 70525311097254626657476171)
              ·
                refine ⟨105787966645881939986214257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70525311097254626657476171 105787966645881939986214257)
                ·
                  refine ⟨79340974984411454989660693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 105787966645881939986214257 79340974984411454989660693)
                  ·
                    refine ⟨3719108202394286952640345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79340974984411454989660693 3719108202394286952640345)
                    ·
                      refine ⟨2789331151795715214480259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719108202394286952640345 2789331151795715214480259)
                      ·
                        rfl

theorem cell23_5432203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 6, 2].length) (baseStart_5432203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432203 prefixEnd_5432203 := by exact prefixLift 5432203
  have htrace : WordTrace (prefixWord ++ tailWord_5432203) baseStart_5432203 baseEnd_5432203 := by
    simpa [prefixWord, tailWord_5432203, baseEnd_5432203] using wordTrace_append hprefix tailTrace_5432203
  have hstable : (prefixWord ++ tailWord_5432203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432203).length < 2 ^ (prefixWord ++ tailWord_5432203).sum := by decide
  have hdescent : baseEnd_5432203 < baseStart_5432203 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432213 : List Nat := [1, 3, 2, 1, 1, 5, 1, 2, 1, 6]
def baseStart_5432213 : Nat := 118140960795 + 5432213 * 2 ^ 59
def prefixEnd_5432213 : Nat := 4983230072969 + 3 ^ 40 * 5432213 * 2
def baseEnd_5432213 : Nat := 929778762200753391785071

theorem tailTrace_5432213 : CollatzResearch.WordTrace tailWord_5432213 prefixEnd_5432213 929778762200753391785071 := by
  unfold tailWord_5432213
  simp only [CollatzResearch.WordTrace]
  refine ⟨198129085069027523963709293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132086056712685015975806195 198129085069027523963709293)
  ·
    refine ⟨74298406900885321486390985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198129085069027523963709293 74298406900885321486390985)
    ·
      refine ⟨55723805175663991114793239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74298406900885321486390985 55723805175663991114793239)
      ·
        refine ⟨83585707763495986672189859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55723805175663991114793239 83585707763495986672189859)
        ·
          refine ⟨125378561645243980008284789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83585707763495986672189859 125378561645243980008284789)
          ·
            refine ⟨11754240154241623125776699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 125378561645243980008284789 11754240154241623125776699)
            ·
              refine ⟨17631360231362434688665049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11754240154241623125776699 17631360231362434688665049)
              ·
                refine ⟨13223520173521826016498787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17631360231362434688665049 13223520173521826016498787)
                ·
                  refine ⟨19835280260282739024748181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13223520173521826016498787 19835280260282739024748181)
                  ·
                    refine ⟨929778762200753391785071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19835280260282739024748181 929778762200753391785071)
                    ·
                      rfl

theorem cell23_5432213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_5432213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432213 prefixEnd_5432213 := by exact prefixLift 5432213
  have htrace : WordTrace (prefixWord ++ tailWord_5432213) baseStart_5432213 baseEnd_5432213 := by
    simpa [prefixWord, tailWord_5432213, baseEnd_5432213] using wordTrace_append hprefix tailTrace_5432213
  have hstable : (prefixWord ++ tailWord_5432213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432213).length < 2 ^ (prefixWord ++ tailWord_5432213).sum := by decide
  have hdescent : baseEnd_5432213 < baseStart_5432213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432270 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_5432270 : Nat := 118140960795 + 5432270 * 2 ^ 59
def prefixEnd_5432270 : Nat := 4983230072969 + 3 ^ 40 * 5432270 * 2
def baseEnd_5432270 : Nat := 2789365554999566452342451

theorem tailTrace_5432270 : CollatzResearch.WordTrace tailWord_5432270 prefixEnd_5432270 2789365554999566452342451 := by
  unfold tailWord_5432270
  simp only [CollatzResearch.WordTrace]
  refine ⟨24766395503727627837316783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 132087442686547348465689509 24766395503727627837316783)
  ·
    refine ⟨37149593255591441755975175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 24766395503727627837316783 37149593255591441755975175)
    ·
      refine ⟨55724389883387162633962763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37149593255591441755975175 55724389883387162633962763)
      ·
        refine ⟨83586584825080743950944145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55724389883387162633962763 83586584825080743950944145)
        ·
          refine ⟨62689938618810557963208109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83586584825080743950944145 62689938618810557963208109)
          ·
            refine ⟨23508726982053959236203041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62689938618810557963208109 23508726982053959236203041)
            ·
              refine ⟨17631545236540469427152281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23508726982053959236203041 17631545236540469427152281)
              ·
                refine ⟨13223658927405352070364211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17631545236540469427152281 13223658927405352070364211)
                ·
                  refine ⟨19835488391108028105546317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13223658927405352070364211 19835488391108028105546317)
                  ·
                    refine ⟨7438308146665510539579869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 19835488391108028105546317 7438308146665510539579869)
                    ·
                      refine ⟨2789365554999566452342451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7438308146665510539579869 2789365554999566452342451)
                      ·
                        rfl

theorem cell23_5432270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_5432270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432270 prefixEnd_5432270 := by exact prefixLift 5432270
  have htrace : WordTrace (prefixWord ++ tailWord_5432270) baseStart_5432270 baseEnd_5432270 := by
    simpa [prefixWord, tailWord_5432270, baseEnd_5432270] using wordTrace_append hprefix tailTrace_5432270
  have hstable : (prefixWord ++ tailWord_5432270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432270).length < 2 ^ (prefixWord ++ tailWord_5432270).sum := by decide
  have hdescent : baseEnd_5432270 < baseStart_5432270 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432274 : List Nat := [3, 2, 2, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_5432274 : Nat := 118140960795 + 5432274 * 2 ^ 59
def prefixEnd_5432274 : Nat := 4983230072969 + 3 ^ 40 * 5432274 * 2
def baseEnd_5432274 : Nat := 2789367608922184436692433

theorem tailTrace_5432274 : CollatzResearch.WordTrace tailWord_5432274 prefixEnd_5432274 2789367608922184436692433 := by
  unfold tailWord_5432274
  simp only [CollatzResearch.WordTrace]
  refine ⟨49532827480451632845419969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132087539947871020921119917 49532827480451632845419969)
  ·
    refine ⟨37149620610338724634064977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 49532827480451632845419969 37149620610338724634064977)
    ·
      refine ⟨27862215457754043475548733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37149620610338724634064977 27862215457754043475548733)
      ·
        refine ⟨10448330796657766303330775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 27862215457754043475548733 10448330796657766303330775)
        ·
          refine ⟨15672496194986649454996163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10448330796657766303330775 15672496194986649454996163)
          ·
            refine ⟨23508744292479974182494245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15672496194986649454996163 23508744292479974182494245)
            ·
              refine ⟨4407889554839995159217671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 23508744292479974182494245 4407889554839995159217671)
              ·
                refine ⟨6611834332259992738826507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4407889554839995159217671 6611834332259992738826507)
                ·
                  refine ⟨9917751498389989108239761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6611834332259992738826507 9917751498389989108239761)
                  ·
                    refine ⟨7438313623792491831179821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9917751498389989108239761 7438313623792491831179821)
                    ·
                      refine ⟨2789367608922184436692433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7438313623792491831179821 2789367608922184436692433)
                      ·
                        rfl

theorem cell23_5432274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_5432274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432274 prefixEnd_5432274 := by exact prefixLift 5432274
  have htrace : WordTrace (prefixWord ++ tailWord_5432274) baseStart_5432274 baseEnd_5432274 := by
    simpa [prefixWord, tailWord_5432274, baseEnd_5432274] using wordTrace_append hprefix tailTrace_5432274
  have hstable : (prefixWord ++ tailWord_5432274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432274).length < 2 ^ (prefixWord ++ tailWord_5432274).sum := by decide
  have hdescent : baseEnd_5432274 < baseStart_5432274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432287 : List Nat := [1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 3]
def baseStart_5432287 : Nat := 118140960795 + 5432287 * 2 ^ 59
def prefixEnd_5432287 : Nat := 4983230072969 + 3 ^ 40 * 5432287 * 2
def baseEnd_5432287 : Nat := 2789374284170692885829873

theorem tailTrace_5432287 : CollatzResearch.WordTrace tailWord_5432287 prefixEnd_5432287 2789374284170692885829873 := by
  unfold tailWord_5432287
  simp only [CollatzResearch.WordTrace]
  refine ⟨198131784070759434601903115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132087856047172956401268743 198131784070759434601903115)
  ·
    refine ⟨297197676106139151902854673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198131784070759434601903115 297197676106139151902854673)
    ·
      refine ⟨222898257079604363927141005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297197676106139151902854673 222898257079604363927141005)
      ·
        refine ⟨83586846404851636472677877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222898257079604363927141005 83586846404851636472677877)
        ·
          refine ⟨7836266850454840919313551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 83586846404851636472677877 7836266850454840919313551)
          ·
            refine ⟨11754400275682261378970327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7836266850454840919313551 11754400275682261378970327)
            ·
              refine ⟨17631600413523392068455491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11754400275682261378970327 17631600413523392068455491)
              ·
                refine ⟨26447400620285088102683237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17631600413523392068455491 26447400620285088102683237)
                ·
                  refine ⟨4958887616303454019253107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 26447400620285088102683237 4958887616303454019253107)
                  ·
                    refine ⟨7438331424455181028879661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4958887616303454019253107 7438331424455181028879661)
                    ·
                      refine ⟨2789374284170692885829873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7438331424455181028879661 2789374284170692885829873)
                      ·
                        rfl

theorem cell23_5432287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_5432287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432287 prefixEnd_5432287 := by exact prefixLift 5432287
  have htrace : WordTrace (prefixWord ++ tailWord_5432287) baseStart_5432287 baseEnd_5432287 := by
    simpa [prefixWord, tailWord_5432287, baseEnd_5432287] using wordTrace_append hprefix tailTrace_5432287
  have hstable : (prefixWord ++ tailWord_5432287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432287).length < 2 ^ (prefixWord ++ tailWord_5432287).sum := by decide
  have hdescent : baseEnd_5432287 < baseStart_5432287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432303 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 2, 6]
def baseStart_5432303 : Nat := 118140960795 + 5432303 * 2 ^ 59
def prefixEnd_5432303 : Nat := 4983230072969 + 3 ^ 40 * 5432303 * 2
def baseEnd_5432303 : Nat := 929794166620388274409933

theorem tailTrace_5432303 : CollatzResearch.WordTrace tailWord_5432303 prefixEnd_5432303 929794166620388274409933 := by
  unfold tailWord_5432303
  simp only [CollatzResearch.WordTrace]
  refine ⟨198132367638701469334485563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132088245092467646222990375 198132367638701469334485563)
  ·
    refine ⟨297198551458052204001728345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198132367638701469334485563 297198551458052204001728345)
    ·
      refine ⟨222898913593539153001296259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297198551458052204001728345 222898913593539153001296259)
      ·
        refine ⟨334348370390308729501944389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222898913593539153001296259 334348370390308729501944389)
        ·
          refine ⟨62690319448182886781614573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334348370390308729501944389 62690319448182886781614573)
          ·
            refine ⟨23508869793068582543105465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 62690319448182886781614573 23508869793068582543105465)
            ·
              refine ⟨17631652344801436907329099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23508869793068582543105465 17631652344801436907329099)
              ·
                refine ⟨26447478517202155360993649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17631652344801436907329099 26447478517202155360993649)
                ·
                  refine ⟨19835608887901616520745237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26447478517202155360993649 19835608887901616520745237)
                  ·
                    refine ⟨929794166620388274409933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 19835608887901616520745237 929794166620388274409933)
                    ·
                      rfl

theorem cell23_5432303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 6].length) (baseStart_5432303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432303 prefixEnd_5432303 := by exact prefixLift 5432303
  have htrace : WordTrace (prefixWord ++ tailWord_5432303) baseStart_5432303 baseEnd_5432303 := by
    simpa [prefixWord, tailWord_5432303, baseEnd_5432303] using wordTrace_append hprefix tailTrace_5432303
  have hstable : (prefixWord ++ tailWord_5432303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432303).length < 2 ^ (prefixWord ++ tailWord_5432303).sum := by decide
  have hdescent : baseEnd_5432303 < baseStart_5432303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432313 : List Nat := [1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 5]
def baseStart_5432313 : Nat := 118140960795 + 5432313 * 2 ^ 59
def prefixEnd_5432313 : Nat := 4983230072969 + 3 ^ 40 * 5432313 * 2
def baseEnd_5432313 : Nat := 2789387634667709784104753

theorem tailTrace_5432313 : CollatzResearch.WordTrace tailWord_5432313 prefixEnd_5432313 2789387634667709784104753 := by
  unfold tailWord_5432313
  simp only [CollatzResearch.WordTrace]
  refine ⟨198132732368665241042349593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132088488245776827361566395 198132732368665241042349593)
  ·
    refine ⟨148599549276498930781762195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198132732368665241042349593 148599549276498930781762195)
    ·
      refine ⟨222899323914748396172643293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148599549276498930781762195 222899323914748396172643293)
      ·
        refine ⟨83587246468030648564741235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222899323914748396172643293 83587246468030648564741235)
        ·
          refine ⟨125380869702045972847111853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83587246468030648564741235 125380869702045972847111853)
          ·
            refine ⟨47017826138267239817666945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125380869702045972847111853 47017826138267239817666945)
            ·
              refine ⟨35263369603700429863250209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47017826138267239817666945 35263369603700429863250209)
              ·
                refine ⟨26447527202775322397437657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35263369603700429863250209 26447527202775322397437657)
                ·
                  refine ⟨19835645402081491798078243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26447527202775322397437657 19835645402081491798078243)
                  ·
                    refine ⟨29753468103122237697117365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19835645402081491798078243 29753468103122237697117365)
                    ·
                      refine ⟨2789387634667709784104753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29753468103122237697117365 2789387634667709784104753)
                      ·
                        rfl

theorem cell23_5432313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_5432313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432313 prefixEnd_5432313 := by exact prefixLift 5432313
  have htrace : WordTrace (prefixWord ++ tailWord_5432313) baseStart_5432313 baseEnd_5432313 := by
    simpa [prefixWord, tailWord_5432313, baseEnd_5432313] using wordTrace_append hprefix tailTrace_5432313
  have hstable : (prefixWord ++ tailWord_5432313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432313).length < 2 ^ (prefixWord ++ tailWord_5432313).sum := by decide
  have hdescent : baseEnd_5432313 < baseStart_5432313 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432322 : List Nat := [3, 4, 1, 3, 2, 1, 1, 3, 1, 2, 2]
def baseStart_5432322 : Nat := 118140960795 + 5432322 * 2 ^ 59
def prefixEnd_5432322 : Nat := 4983230072969 + 3 ^ 40 * 5432322 * 2
def baseEnd_5432322 : Nat := 2789392255993600248892213

theorem tailTrace_5432322 : CollatzResearch.WordTrace tailWord_5432322 prefixEnd_5432322 2789392255993600248892213 := by
  unfold tailWord_5432322
  simp only [CollatzResearch.WordTrace]
  refine ⟨49533265156408158894856805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132088707083755090386284813 49533265156408158894856805)
  ·
    refine ⟨9287487216826529792785651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 49533265156408158894856805 9287487216826529792785651)
    ·
      refine ⟨13931230825239794689178477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9287487216826529792785651 13931230825239794689178477)
      ·
        refine ⟨5224211559464923008441929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13931230825239794689178477 5224211559464923008441929)
        ·
          refine ⟨3918158669598692256331447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5224211559464923008441929 3918158669598692256331447)
          ·
            refine ⟨5877238004398038384497171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918158669598692256331447 5877238004398038384497171)
            ·
              refine ⟨8815857006597057576745757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5877238004398038384497171 8815857006597057576745757)
              ·
                refine ⟨3305946377473896591279659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8815857006597057576745757 3305946377473896591279659)
                ·
                  refine ⟨4958919566210844886919489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3305946377473896591279659 4958919566210844886919489)
                  ·
                    refine ⟨3719189674658133665189617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958919566210844886919489 3719189674658133665189617)
                    ·
                      refine ⟨2789392255993600248892213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719189674658133665189617 2789392255993600248892213)
                      ·
                        rfl

theorem cell23_5432322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 2, 2].length) (baseStart_5432322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432322 prefixEnd_5432322 := by exact prefixLift 5432322
  have htrace : WordTrace (prefixWord ++ tailWord_5432322) baseStart_5432322 baseEnd_5432322 := by
    simpa [prefixWord, tailWord_5432322, baseEnd_5432322] using wordTrace_append hprefix tailTrace_5432322
  have hstable : (prefixWord ++ tailWord_5432322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432322).length < 2 ^ (prefixWord ++ tailWord_5432322).sum := by decide
  have hdescent : baseEnd_5432322 < baseStart_5432322 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432327 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 6, 2, 2]
def baseStart_5432327 : Nat := 118140960795 + 5432327 * 2 ^ 59
def prefixEnd_5432327 : Nat := 4983230072969 + 3 ^ 40 * 5432327 * 2
def baseEnd_5432327 : Nat := 2789394823396872729329689

theorem tailTrace_5432327 : CollatzResearch.WordTrace tailWord_5432327 prefixEnd_5432327 2789394823396872729329689 := by
  unfold tailWord_5432327
  simp only [CollatzResearch.WordTrace]
  refine ⟨198133242990614521433359235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132088828660409680955572823 198133242990614521433359235)
  ·
    refine ⟨297199864485921782150038853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198133242990614521433359235 297199864485921782150038853)
    ·
      refine ⟨55724974591110334153132285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 297199864485921782150038853 55724974591110334153132285)
      ·
        refine ⟨20896865471666375307424607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 55724974591110334153132285 20896865471666375307424607)
        ·
          refine ⟨31345298207499562961136911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20896865471666375307424607 31345298207499562961136911)
          ·
            refine ⟨47017947311249344441705367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31345298207499562961136911 47017947311249344441705367)
            ·
              refine ⟨70526920966874016662558051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47017947311249344441705367 70526920966874016662558051)
              ·
                refine ⟨105790381450311024993837077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70526920966874016662558051 105790381450311024993837077)
                ·
                  refine ⟨4958924130483329296586113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 105790381450311024993837077 4958924130483329296586113)
                  ·
                    refine ⟨3719193097862496972439585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4958924130483329296586113 3719193097862496972439585)
                    ·
                      refine ⟨2789394823396872729329689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719193097862496972439585 2789394823396872729329689)
                      ·
                        rfl

theorem cell23_5432327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 2, 2].length) (baseStart_5432327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432327 prefixEnd_5432327 := by exact prefixLift 5432327
  have htrace : WordTrace (prefixWord ++ tailWord_5432327) baseStart_5432327 baseEnd_5432327 := by
    simpa [prefixWord, tailWord_5432327, baseEnd_5432327] using wordTrace_append hprefix tailTrace_5432327
  have hstable : (prefixWord ++ tailWord_5432327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432327).length < 2 ^ (prefixWord ++ tailWord_5432327).sum := by decide
  have hdescent : baseEnd_5432327 < baseStart_5432327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432330 : List Nat := [3, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_5432330 : Nat := 118140960795 + 5432330 * 2 ^ 59
def prefixEnd_5432330 : Nat := 4983230072969 + 3 ^ 40 * 5432330 * 2
def baseEnd_5432330 : Nat := 2789396363838836217592175

theorem tailTrace_5432330 : CollatzResearch.WordTrace tailWord_5432330 prefixEnd_5432330 2789396363838836217592175 := by
  unfold tailWord_5432330
  simp only [CollatzResearch.WordTrace]
  refine ⟨49533338102400913236429611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132088901606402435297145629 49533338102400913236429611)
  ·
    refine ⟨74300007153601369854644417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49533338102400913236429611 74300007153601369854644417)
    ·
      refine ⟨55725005365201027390983313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74300007153601369854644417 55725005365201027390983313)
      ·
        refine ⟨41793754023900770543237485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55725005365201027390983313 41793754023900770543237485)
        ·
          refine ⟨15672657758962788953714057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41793754023900770543237485 15672657758962788953714057)
          ·
            refine ⟨11754493319222091715285543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15672657758962788953714057 11754493319222091715285543)
            ·
              refine ⟨17631739978833137572928315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11754493319222091715285543 17631739978833137572928315)
              ·
                refine ⟨26447609968249706359392473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17631739978833137572928315 26447609968249706359392473)
                ·
                  refine ⟨19835707476187279769544355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26447609968249706359392473 19835707476187279769544355)
                  ·
                    refine ⟨29753561214280919654316533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 19835707476187279769544355 29753561214280919654316533)
                    ·
                      refine ⟨2789396363838836217592175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29753561214280919654316533 2789396363838836217592175)
                      ·
                        rfl

theorem cell23_5432330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_5432330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432330 prefixEnd_5432330 := by exact prefixLift 5432330
  have htrace : WordTrace (prefixWord ++ tailWord_5432330) baseStart_5432330 baseEnd_5432330 := by
    simpa [prefixWord, tailWord_5432330, baseEnd_5432330] using wordTrace_append hprefix tailTrace_5432330
  have hstable : (prefixWord ++ tailWord_5432330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432330).length < 2 ^ (prefixWord ++ tailWord_5432330).sum := by decide
  have hdescent : baseEnd_5432330 < baseStart_5432330 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432363 : List Nat := [1, 1, 1, 1, 2, 1, 5, 2, 4, 5]
def baseStart_5432363 : Nat := 118140960795 + 5432363 * 2 ^ 59
def prefixEnd_5432363 : Nat := 4983230072969 + 3 ^ 40 * 5432363 * 2
def baseEnd_5432363 : Nat := 929804436233478196159841

theorem tailTrace_5432363 : CollatzResearch.WordTrace tailWord_5432363 prefixEnd_5432363 929804436233478196159841 := by
  unfold tailWord_5432363
  simp only [CollatzResearch.WordTrace]
  refine ⟨198134556018484099581669743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132089704012322733054446495 198134556018484099581669743)
  ·
    refine ⟨297201834027726149372504615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198134556018484099581669743 297201834027726149372504615)
    ·
      refine ⟨445802751041589224058756923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297201834027726149372504615 445802751041589224058756923)
      ·
        refine ⟨668704126562383836088135385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445802751041589224058756923 668704126562383836088135385)
        ·
          refine ⟨501528094921787877066101539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 668704126562383836088135385 501528094921787877066101539)
          ·
            refine ⟨752292142382681815599152309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501528094921787877066101539 752292142382681815599152309)
            ·
              refine ⟨70527388348376420212420529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 752292142382681815599152309 70527388348376420212420529)
              ·
                refine ⟨52895541261282315159315397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 70527388348376420212420529 52895541261282315159315397)
                ·
                  refine ⟨9917913986490434092371637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 52895541261282315159315397 9917913986490434092371637)
                  ·
                    refine ⟨929804436233478196159841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9917913986490434092371637 929804436233478196159841)
                    ·
                      rfl

theorem cell23_5432363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 2, 4, 5].length) (baseStart_5432363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432363 prefixEnd_5432363 := by exact prefixLift 5432363
  have htrace : WordTrace (prefixWord ++ tailWord_5432363) baseStart_5432363 baseEnd_5432363 := by
    simpa [prefixWord, tailWord_5432363, baseEnd_5432363] using wordTrace_append hprefix tailTrace_5432363
  have hstable : (prefixWord ++ tailWord_5432363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432363).length < 2 ^ (prefixWord ++ tailWord_5432363).sum := by decide
  have hdescent : baseEnd_5432363 < baseStart_5432363 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432373 : List Nat := [1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5432373 : Nat := 118140960795 + 5432373 * 2 ^ 59
def prefixEnd_5432373 : Nat := 4983230072969 + 3 ^ 40 * 5432373 * 2
def baseEnd_5432373 : Nat := 2789418443506979549354477

theorem tailTrace_5432373 : CollatzResearch.WordTrace tailWord_5432373 prefixEnd_5432373 2789418443506979549354477 := by
  unfold tailWord_5432373
  simp only [CollatzResearch.WordTrace]
  refine ⟨198134920748447871289533773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132089947165631914193022515 198134920748447871289533773)
  ·
    refine ⟨74300595280667951733575165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198134920748447871289533773 74300595280667951733575165)
    ·
      refine ⟨27862723230250481900090687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 74300595280667951733575165 27862723230250481900090687)
      ·
        refine ⟨41794084845375722850136031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27862723230250481900090687 41794084845375722850136031)
        ·
          refine ⟨62691127268063584275204047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41794084845375722850136031 62691127268063584275204047)
          ·
            refine ⟨94036690902095376412806071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62691127268063584275204047 94036690902095376412806071)
            ·
              refine ⟨141055036353143064619209107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94036690902095376412806071 141055036353143064619209107)
              ·
                refine ⟨211582554529714596928813661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141055036353143064619209107 211582554529714596928813661)
                ·
                  refine ⟨79343457948642973848305123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211582554529714596928813661 79343457948642973848305123)
                  ·
                    refine ⟨119015186922964460772457685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 79343457948642973848305123 119015186922964460772457685)
                    ·
                      refine ⟨2789418443506979549354477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119015186922964460772457685 2789418443506979549354477)
                      ·
                        rfl

theorem cell23_5432373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5432373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432373 prefixEnd_5432373 := by exact prefixLift 5432373
  have htrace : WordTrace (prefixWord ++ tailWord_5432373) baseStart_5432373 baseEnd_5432373 := by
    simpa [prefixWord, tailWord_5432373, baseEnd_5432373] using wordTrace_append hprefix tailTrace_5432373
  have hstable : (prefixWord ++ tailWord_5432373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432373).length < 2 ^ (prefixWord ++ tailWord_5432373).sum := by decide
  have hdescent : baseEnd_5432373 < baseStart_5432373 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432380 : List Nat := [2, 2, 2, 2, 2, 2, 1, 3, 2, 5]
def baseStart_5432380 : Nat := 118140960795 + 5432380 * 2 ^ 59
def prefixEnd_5432380 : Nat := 4983230072969 + 3 ^ 40 * 5432380 * 2
def baseEnd_5432380 : Nat := 929807345957187007322315

theorem tailTrace_5432380 : CollatzResearch.WordTrace tailWord_5432380 prefixEnd_5432380 929807345957187007322315 := by
  unfold tailWord_5432380
  simp only [CollatzResearch.WordTrace]
  refine ⟨99067588029711255742519297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132090117372948340990025729 99067588029711255742519297)
  ·
    refine ⟨74300691022283441806889473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99067588029711255742519297 74300691022283441806889473)
    ·
      refine ⟨55725518266712581355167105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74300691022283441806889473 55725518266712581355167105)
      ·
        refine ⟨41794138700034436016375329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55725518266712581355167105 41794138700034436016375329)
        ·
          refine ⟨31345604025025827012281497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41794138700034436016375329 31345604025025827012281497)
          ·
            refine ⟨23509203018769370259211123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31345604025025827012281497 23509203018769370259211123)
            ·
              refine ⟨35263804528154055388816685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23509203018769370259211123 35263804528154055388816685)
              ·
                refine ⟨13223926698057770770806257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35263804528154055388816685 13223926698057770770806257)
                ·
                  refine ⟨9917945023543328078104693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13223926698057770770806257 9917945023543328078104693)
                  ·
                    refine ⟨929807345957187007322315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9917945023543328078104693 929807345957187007322315)
                    ·
                      rfl

theorem cell23_5432380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 3, 2, 5].length) (baseStart_5432380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432380 prefixEnd_5432380 := by exact prefixLift 5432380
  have htrace : WordTrace (prefixWord ++ tailWord_5432380) baseStart_5432380 baseEnd_5432380 := by
    simpa [prefixWord, tailWord_5432380, baseEnd_5432380] using wordTrace_append hprefix tailTrace_5432380
  have hstable : (prefixWord ++ tailWord_5432380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432380).length < 2 ^ (prefixWord ++ tailWord_5432380).sum := by decide
  have hdescent : baseEnd_5432380 < baseStart_5432380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432397 : List Nat := [1, 6, 1, 1, 1, 2, 2, 2, 2, 5]
def baseStart_5432397 : Nat := 118140960795 + 5432397 * 2 ^ 59
def prefixEnd_5432397 : Nat := 4983230072969 + 3 ^ 40 * 5432397 * 2
def baseEnd_5432397 : Nat := 929810255680895818484789

theorem tailTrace_5432397 : CollatzResearch.WordTrace tailWord_5432397 prefixEnd_5432397 929810255680895818484789 := by
  unfold tailWord_5432397
  simp only [CollatzResearch.WordTrace]
  refine ⟨198135796100360923388407445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132090530733573948925604963 198135796100360923388407445)
  ·
    refine ⟨9287615442204418283831599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198135796100360923388407445 9287615442204418283831599)
    ·
      refine ⟨13931423163306627425747399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9287615442204418283831599 13931423163306627425747399)
      ·
        refine ⟨20897134744959941138621099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13931423163306627425747399 20897134744959941138621099)
        ·
          refine ⟨31345702117439911707931649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 20897134744959941138621099 31345702117439911707931649)
          ·
            refine ⟨23509276588079933780948737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31345702117439911707931649 23509276588079933780948737)
            ·
              refine ⟨17631957441059950335711553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23509276588079933780948737 17631957441059950335711553)
              ·
                refine ⟨13223968080794962751783665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17631957441059950335711553 13223968080794962751783665)
                ·
                  refine ⟨9917976060596222063837749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13223968080794962751783665 9917976060596222063837749)
                  ·
                    refine ⟨929810255680895818484789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9917976060596222063837749 929810255680895818484789)
                    ·
                      rfl

theorem cell23_5432397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 2, 2, 5].length) (baseStart_5432397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432397 prefixEnd_5432397 := by exact prefixLift 5432397
  have htrace : WordTrace (prefixWord ++ tailWord_5432397) baseStart_5432397 baseEnd_5432397 := by
    simpa [prefixWord, tailWord_5432397, baseEnd_5432397] using wordTrace_append hprefix tailTrace_5432397
  have hstable : (prefixWord ++ tailWord_5432397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432397).length < 2 ^ (prefixWord ++ tailWord_5432397).sum := by decide
  have hdescent : baseEnd_5432397 < baseStart_5432397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432400 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 3, 6, 2]
def baseStart_5432400 : Nat := 118140960795 + 5432400 * 2 ^ 59
def prefixEnd_5432400 : Nat := 4983230072969 + 3 ^ 40 * 5432400 * 2
def baseEnd_5432400 : Nat := 2789432307484650943716853

theorem tailTrace_5432400 : CollatzResearch.WordTrace tailWord_5432400 prefixEnd_5432400 2789432307484650943716853 := by
  unfold tailWord_5432400
  simp only [CollatzResearch.WordTrace]
  refine ⟨99067952759675027450383327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132090603679566703267177769 99067952759675027450383327)
  ·
    refine ⟨148601929139512541175574991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99067952759675027450383327 148601929139512541175574991)
    ·
      refine ⟨222902893709268811763362487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148601929139512541175574991 222902893709268811763362487)
      ·
        refine ⟨334354340563903217645043731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222902893709268811763362487 334354340563903217645043731)
        ·
          refine ⟨501531510845854826467565597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334354340563903217645043731 501531510845854826467565597)
          ·
            refine ⟨188074316567195559925337099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 501531510845854826467565597 188074316567195559925337099)
            ·
              refine ⟨282111474850793339888005649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188074316567195559925337099 282111474850793339888005649)
              ·
                refine ⟨211583606138095004916004237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282111474850793339888005649 211583606138095004916004237)
                ·
                  refine ⟨79343852301785626843501589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211583606138095004916004237 79343852301785626843501589)
                  ·
                    refine ⟨3719243076646201258289137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 79343852301785626843501589 3719243076646201258289137)
                    ·
                      refine ⟨2789432307484650943716853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719243076646201258289137 2789432307484650943716853)
                      ·
                        rfl

theorem cell23_5432400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 6, 2].length) (baseStart_5432400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432400 prefixEnd_5432400 := by exact prefixLift 5432400
  have htrace : WordTrace (prefixWord ++ tailWord_5432400) baseStart_5432400 baseEnd_5432400 := by
    simpa [prefixWord, tailWord_5432400, baseEnd_5432400] using wordTrace_append hprefix tailTrace_5432400
  have hstable : (prefixWord ++ tailWord_5432400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432400).length < 2 ^ (prefixWord ++ tailWord_5432400).sum := by decide
  have hdescent : baseEnd_5432400 < baseStart_5432400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432420 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 1, 4, 3]
def baseStart_5432420 : Nat := 118140960795 + 5432420 * 2 ^ 59
def prefixEnd_5432420 : Nat := 4983230072969 + 3 ^ 40 * 5432420 * 2
def baseEnd_5432420 : Nat := 2789442577097740865466761

theorem tailTrace_5432420 : CollatzResearch.WordTrace tailWord_5432420 prefixEnd_5432420 2789442577097740865466761 := by
  unfold tailWord_5432420
  simp only [CollatzResearch.WordTrace]
  refine ⟨99068317489638799158247357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132091089986185065544329809 99068317489638799158247357)
  ·
    refine ⟨37150619058614549684342759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99068317489638799158247357 37150619058614549684342759)
    ·
      refine ⟨55725928587921824526514139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37150619058614549684342759 55725928587921824526514139)
      ·
        refine ⟨83588892881882736789771209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55725928587921824526514139 83588892881882736789771209)
        ·
          refine ⟨62691669661412052592328407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83588892881882736789771209 62691669661412052592328407)
          ·
            refine ⟨94037504492118078888492611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62691669661412052592328407 94037504492118078888492611)
            ·
              refine ⟨141056256738177118332738917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94037504492118078888492611 141056256738177118332738917)
              ·
                refine ⟨26448048138408209687388547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 141056256738177118332738917 26448048138408209687388547)
                ·
                  refine ⟨39672072207612314531082821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26448048138408209687388547 39672072207612314531082821)
                  ·
                    refine ⟨7438513538927308974578029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 39672072207612314531082821 7438513538927308974578029)
                    ·
                      refine ⟨2789442577097740865466761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7438513538927308974578029 2789442577097740865466761)
                      ·
                        rfl

theorem cell23_5432420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 1, 4, 3].length) (baseStart_5432420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432420 prefixEnd_5432420 := by exact prefixLift 5432420
  have htrace : WordTrace (prefixWord ++ tailWord_5432420) baseStart_5432420 baseEnd_5432420 := by
    simpa [prefixWord, tailWord_5432420, baseEnd_5432420] using wordTrace_append hprefix tailTrace_5432420
  have hstable : (prefixWord ++ tailWord_5432420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432420).length < 2 ^ (prefixWord ++ tailWord_5432420).sum := by decide
  have hdescent : baseEnd_5432420 < baseStart_5432420 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432443 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6]
def baseStart_5432443 : Nat := 118140960795 + 5432443 * 2 ^ 59
def prefixEnd_5432443 : Nat := 4983230072969 + 3 ^ 40 * 5432443 * 2
def baseEnd_5432443 : Nat := 2789454387152794275479155

theorem tailTrace_5432443 : CollatzResearch.WordTrace tailWord_5432443 prefixEnd_5432443 2789454387152794275479155 := by
  unfold tailWord_5432443
  simp only [CollatzResearch.WordTrace]
  refine ⟨198137473858194273244581983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132091649238796182163054655 198137473858194273244581983)
  ·
    refine ⟨297206210787291409866872975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198137473858194273244581983 297206210787291409866872975)
    ·
      refine ⟨445809316180937114800309463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297206210787291409866872975 445809316180937114800309463)
      ·
        refine ⟨668713974271405672200464195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445809316180937114800309463 668713974271405672200464195)
        ·
          refine ⟨1003070961407108508300696293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668713974271405672200464195 1003070961407108508300696293)
          ·
            refine ⟨188075805263832845306380555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1003070961407108508300696293 188075805263832845306380555)
            ·
              refine ⟨282113707895749267959570833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188075805263832845306380555 282113707895749267959570833)
              ·
                refine ⟨211585280921811950969678125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282113707895749267959570833 211585280921811950969678125)
                ·
                  refine ⟨79344480345679481613629297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211585280921811950969678125 79344480345679481613629297)
                  ·
                    refine ⟨59508360259259611210221973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 79344480345679481613629297 59508360259259611210221973)
                    ·
                      refine ⟨2789454387152794275479155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59508360259259611210221973 2789454387152794275479155)
                      ·
                        rfl

theorem cell23_5432443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 6].length) (baseStart_5432443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432443 prefixEnd_5432443 := by exact prefixLift 5432443
  have htrace : WordTrace (prefixWord ++ tailWord_5432443) baseStart_5432443 baseEnd_5432443 := by
    simpa [prefixWord, tailWord_5432443, baseEnd_5432443] using wordTrace_append hprefix tailTrace_5432443
  have hstable : (prefixWord ++ tailWord_5432443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432443).length < 2 ^ (prefixWord ++ tailWord_5432443).sum := by decide
  have hdescent : baseEnd_5432443 < baseStart_5432443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432444 : List Nat := [2, 2, 2, 1, 1, 3, 4, 3, 1, 4]
def baseStart_5432444 : Nat := 118140960795 + 5432444 * 2 ^ 59
def prefixEnd_5432444 : Nat := 4983230072969 + 3 ^ 40 * 5432444 * 2
def baseEnd_5432444 : Nat := 929818300211149590522217

theorem tailTrace_5432444 : CollatzResearch.WordTrace tailWord_5432444 prefixEnd_5432444 929818300211149590522217 := by
  unfold tailWord_5432444
  simp only [CollatzResearch.WordTrace]
  refine ⟨99068755165595325207684193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132091673554127100276912257 99068755165595325207684193)
  ·
    refine ⟨74301566374196493905763145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99068755165595325207684193 74301566374196493905763145)
    ·
      refine ⟨55726174780647370429322359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74301566374196493905763145 55726174780647370429322359)
      ·
        refine ⟨83589262170971055643983539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55726174780647370429322359 83589262170971055643983539)
        ·
          refine ⟨125383893256456583465975309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83589262170971055643983539 125383893256456583465975309)
          ·
            refine ⟨47018959971171218799740741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 125383893256456583465975309 47018959971171218799740741)
            ·
              refine ⟨8816054994594603524951389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47018959971171218799740741 8816054994594603524951389)
              ·
                refine ⟨3306020622972976321856771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8816054994594603524951389 3306020622972976321856771)
                ·
                  refine ⟨4959030934459464482785157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306020622972976321856771 4959030934459464482785157)
                  ·
                    refine ⟨929818300211149590522217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959030934459464482785157 929818300211149590522217)
                    ·
                      rfl

theorem cell23_5432444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 3, 1, 4].length) (baseStart_5432444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432444 prefixEnd_5432444 := by exact prefixLift 5432444
  have htrace : WordTrace (prefixWord ++ tailWord_5432444) baseStart_5432444 baseEnd_5432444 := by
    simpa [prefixWord, tailWord_5432444, baseEnd_5432444] using wordTrace_append hprefix tailTrace_5432444
  have hstable : (prefixWord ++ tailWord_5432444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432444).length < 2 ^ (prefixWord ++ tailWord_5432444).sum := by decide
  have hdescent : baseEnd_5432444 < baseStart_5432444 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432457 : List Nat := [1, 2, 1, 1, 4, 5, 1, 2, 6]
def baseStart_5432457 : Nat := 118140960795 + 5432457 * 2 ^ 59
def prefixEnd_5432457 : Nat := 4983230072969 + 3 ^ 40 * 5432457 * 2
def baseEnd_5432457 : Nat := 309940175097995246744899

theorem tailTrace_5432457 : CollatzResearch.WordTrace tailWord_5432457 prefixEnd_5432457 309940175097995246744899 := by
  unfold tailWord_5432457
  simp only [CollatzResearch.WordTrace]
  refine ⟨198137984480143553635591625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132091989653429035757061083 198137984480143553635591625)
  ·
    refine ⟨148603488360107665226693719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 198137984480143553635591625 148603488360107665226693719)
    ·
      refine ⟨222905232540161497840040579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148603488360107665226693719 222905232540161497840040579)
      ·
        refine ⟨334357848810242246760060869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222905232540161497840040579 334357848810242246760060869)
        ·
          refine ⟨62692096651920421267511413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 334357848810242246760060869 62692096651920421267511413)
          ·
            refine ⟨5877384061117539493829195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 62692096651920421267511413 5877384061117539493829195)
            ·
              refine ⟨8816076091676309240743793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5877384061117539493829195 8816076091676309240743793)
              ·
                refine ⟨6612057068757231930557845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8816076091676309240743793 6612057068757231930557845)
                ·
                  refine ⟨309940175097995246744899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6612057068757231930557845 309940175097995246744899)
                  ·
                    rfl

theorem cell23_5432457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 2, 6].length) (baseStart_5432457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432457 prefixEnd_5432457 := by exact prefixLift 5432457
  have htrace : WordTrace (prefixWord ++ tailWord_5432457) baseStart_5432457 baseEnd_5432457 := by
    simpa [prefixWord, tailWord_5432457, baseEnd_5432457] using wordTrace_append hprefix tailTrace_5432457
  have hstable : (prefixWord ++ tailWord_5432457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432457).length < 2 ^ (prefixWord ++ tailWord_5432457).sum := by decide
  have hdescent : baseEnd_5432457 < baseStart_5432457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432463 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 7]
def baseStart_5432463 : Nat := 118140960795 + 5432463 * 2 ^ 59
def prefixEnd_5432463 : Nat := 4983230072969 + 3 ^ 40 * 5432463 * 2
def baseEnd_5432463 : Nat := 2789464656765884197229063

theorem tailTrace_5432463 : CollatzResearch.WordTrace tailWord_5432463 prefixEnd_5432463 2789464656765884197229063 := by
  unfold tailWord_5432463
  simp only [CollatzResearch.WordTrace]
  refine ⟨198138203318121816660310043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132092135545414544440206695 198138203318121816660310043)
  ·
    refine ⟨297207304977182724990465065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198138203318121816660310043 297207304977182724990465065)
    ·
      refine ⟨222905478732887043742848799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297207304977182724990465065 222905478732887043742848799)
      ·
        refine ⟨334358218099330565614273199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222905478732887043742848799 334358218099330565614273199)
        ·
          refine ⟨501537327148995848421409799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334358218099330565614273199 501537327148995848421409799)
          ·
            refine ⟨752305990723493772632114699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501537327148995848421409799 752305990723493772632114699)
            ·
              refine ⟨1128458986085240658948172049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 752305990723493772632114699 1128458986085240658948172049)
              ·
                refine ⟨846344239563930494211129037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1128458986085240658948172049 846344239563930494211129037)
                ·
                  refine ⟨317379089836473935329173389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 846344239563930494211129037 317379089836473935329173389)
                  ·
                    refine ⟨119017158688677725748440021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 317379089836473935329173389 119017158688677725748440021)
                    ·
                      refine ⟨2789464656765884197229063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119017158688677725748440021 2789464656765884197229063)
                      ·
                        rfl

theorem cell23_5432463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 7].length) (baseStart_5432463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432463 prefixEnd_5432463 := by exact prefixLift 5432463
  have htrace : WordTrace (prefixWord ++ tailWord_5432463) baseStart_5432463 baseEnd_5432463 := by
    simpa [prefixWord, tailWord_5432463, baseEnd_5432463] using wordTrace_append hprefix tailTrace_5432463
  have hstable : (prefixWord ++ tailWord_5432463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432463).length < 2 ^ (prefixWord ++ tailWord_5432463).sum := by decide
  have hdescent : baseEnd_5432463 < baseStart_5432463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432467 : List Nat := [1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 3]
def baseStart_5432467 : Nat := 118140960795 + 5432467 * 2 ^ 59
def prefixEnd_5432467 : Nat := 4983230072969 + 3 ^ 40 * 5432467 * 2
def baseEnd_5432467 : Nat := 2789466710688502181579045

theorem tailTrace_5432467 : CollatzResearch.WordTrace tailWord_5432467 prefixEnd_5432467 2789466710688502181579045 := by
  unfold tailWord_5432467
  simp only [CollatzResearch.WordTrace]
  refine ⟨198138349210107325343455655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132092232806738216895637103 198138349210107325343455655)
  ·
    refine ⟨297207523815160988015183483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198138349210107325343455655 297207523815160988015183483)
    ·
      refine ⟨445811285722741482022775225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297207523815160988015183483 445811285722741482022775225)
      ·
        refine ⟨334358464292056111517081419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445811285722741482022775225 334358464292056111517081419)
        ·
          refine ⟨501537696438084167275622129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334358464292056111517081419 501537696438084167275622129)
          ·
            refine ⟨376153272328563125456716597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 501537696438084167275622129 376153272328563125456716597)
            ·
              refine ⟨35264369280802793011567181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 376153272328563125456716597 35264369280802793011567181)
              ·
                refine ⟨13224138480301047379337693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 35264369280802793011567181 13224138480301047379337693)
                ·
                  refine ⟨4959051930112892767251635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13224138480301047379337693 4959051930112892767251635)
                  ·
                    refine ⟨7438577895169339150877453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959051930112892767251635 7438577895169339150877453)
                    ·
                      refine ⟨2789466710688502181579045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7438577895169339150877453 2789466710688502181579045)
                      ·
                        rfl

theorem cell23_5432467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 5, 3, 3, 1, 3].length) (baseStart_5432467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432467 prefixEnd_5432467 := by exact prefixLift 5432467
  have htrace : WordTrace (prefixWord ++ tailWord_5432467) baseStart_5432467 baseEnd_5432467 := by
    simpa [prefixWord, tailWord_5432467, baseEnd_5432467] using wordTrace_append hprefix tailTrace_5432467
  have hstable : (prefixWord ++ tailWord_5432467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432467).length < 2 ^ (prefixWord ++ tailWord_5432467).sum := by decide
  have hdescent : baseEnd_5432467 < baseStart_5432467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432474 : List Nat := [3, 1, 1, 5, 1, 2, 3, 1, 6]
def baseStart_5432474 : Nat := 118140960795 + 5432474 * 2 ^ 59
def prefixEnd_5432474 : Nat := 4983230072969 + 3 ^ 40 * 5432474 * 2
def baseEnd_5432474 : Nat := 309941145005898183799057

theorem tailTrace_5432474 : CollatzResearch.WordTrace tailWord_5432474 prefixEnd_5432474 309941145005898183799057 := by
  unfold tailWord_5432474
  simp only [CollatzResearch.WordTrace]
  refine ⟨49534651130270491384740119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132092403014054643692640317 49534651130270491384740119)
  ·
    refine ⟨74301976695405737077110179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49534651130270491384740119 74301976695405737077110179)
    ·
      refine ⟨111452965043108605615665269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74301976695405737077110179 111452965043108605615665269)
      ·
        refine ⟨10448715472791431776468619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111452965043108605615665269 10448715472791431776468619)
        ·
          refine ⟨15673073209187147664702929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10448715472791431776468619 15673073209187147664702929)
          ·
            refine ⟨11754804906890360748527197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15673073209187147664702929 11754804906890360748527197)
            ·
              refine ⟨4408051840083885280697699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11754804906890360748527197 4408051840083885280697699)
              ·
                refine ⟨6612077760125827921046549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408051840083885280697699 6612077760125827921046549)
                ·
                  refine ⟨309941145005898183799057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6612077760125827921046549 309941145005898183799057)
                  ·
                    rfl

theorem cell23_5432474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 3, 1, 6].length) (baseStart_5432474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432474 prefixEnd_5432474 := by exact prefixLift 5432474
  have htrace : WordTrace (prefixWord ++ tailWord_5432474) baseStart_5432474 baseEnd_5432474 := by
    simpa [prefixWord, tailWord_5432474, baseEnd_5432474] using wordTrace_append hprefix tailTrace_5432474
  have hstable : (prefixWord ++ tailWord_5432474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432474).length < 2 ^ (prefixWord ++ tailWord_5432474).sum := by decide
  have hdescent : baseEnd_5432474 < baseStart_5432474 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432477 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_5432477 : Nat := 118140960795 + 5432477 * 2 ^ 59
def prefixEnd_5432477 : Nat := 4983230072969 + 3 ^ 40 * 5432477 * 2
def baseEnd_5432477 : Nat := 2789471845495047142453999

theorem tailTrace_5432477 : CollatzResearch.WordTrace tailWord_5432477 prefixEnd_5432477 2789471845495047142453999 := by
  unfold tailWord_5432477
  simp only [CollatzResearch.WordTrace]
  refine ⟨198138713940071097051319685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132092475960047398034213123 198138713940071097051319685)
  ·
    refine ⟨37151008863763330697122441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 198138713940071097051319685 37151008863763330697122441)
    ·
      refine ⟨27863256647822498022841831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37151008863763330697122441 27863256647822498022841831)
      ·
        refine ⟨41794884971733747034262747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27863256647822498022841831 41794884971733747034262747)
        ·
          refine ⟨62692327457600620551394121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41794884971733747034262747 62692327457600620551394121)
          ·
            refine ⟨47019245593200465413545591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62692327457600620551394121 47019245593200465413545591)
            ·
              refine ⟨70528868389800698120318387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 47019245593200465413545591 70528868389800698120318387)
              ·
                refine ⟨105793302584701047180477581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 70528868389800698120318387 105793302584701047180477581)
                ·
                  refine ⟨39672488469262892692679093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 105793302584701047180477581 39672488469262892692679093)
                  ·
                    refine ⟨3719295793993396189938665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 39672488469262892692679093 3719295793993396189938665)
                    ·
                      refine ⟨2789471845495047142453999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719295793993396189938665 2789471845495047142453999)
                      ·
                        rfl

theorem cell23_5432477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_5432477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432477 prefixEnd_5432477 := by exact prefixLift 5432477
  have htrace : WordTrace (prefixWord ++ tailWord_5432477) baseStart_5432477 baseEnd_5432477 := by
    simpa [prefixWord, tailWord_5432477, baseEnd_5432477] using wordTrace_append hprefix tailTrace_5432477
  have hstable : (prefixWord ++ tailWord_5432477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432477).length < 2 ^ (prefixWord ++ tailWord_5432477).sum := by decide
  have hdescent : baseEnd_5432477 < baseStart_5432477 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432484 : List Nat := [2, 3, 1, 2, 3, 1, 2, 2, 3, 1, 3]
def baseStart_5432484 : Nat := 118140960795 + 5432484 * 2 ^ 59
def prefixEnd_5432484 : Nat := 4983230072969 + 3 ^ 40 * 5432484 * 2
def baseEnd_5432484 : Nat := 2789475439859628615066467

theorem tailTrace_5432484 : CollatzResearch.WordTrace tailWord_5432484 prefixEnd_5432484 2789475439859628615066467 := by
  unfold tailWord_5432484
  simp only [CollatzResearch.WordTrace]
  refine ⟨99069484625522868623412253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132092646167363824831216337 99069484625522868623412253)
  ·
    refine ⟨37151056734571075733779595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 99069484625522868623412253 37151056734571075733779595)
    ·
      refine ⟨55726585101856613600669393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37151056734571075733779595 55726585101856613600669393)
      ·
        refine ⟨41794938826392460200502045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 55726585101856613600669393 41794938826392460200502045)
        ·
          refine ⟨15673102059897172575188267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 41794938826392460200502045 15673102059897172575188267)
          ·
            refine ⟨23509653089845758862782401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15673102059897172575188267 23509653089845758862782401)
            ·
              refine ⟨17632239817384319147086801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23509653089845758862782401 17632239817384319147086801)
              ·
                refine ⟨13224179863038239360315101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17632239817384319147086801 13224179863038239360315101)
                ·
                  refine ⟨4959067448639339760118163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13224179863038239360315101 4959067448639339760118163)
                  ·
                    refine ⟨7438601172959009640177245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959067448639339760118163 7438601172959009640177245)
                    ·
                      refine ⟨2789475439859628615066467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7438601172959009640177245 2789475439859628615066467)
                      ·
                        rfl

theorem cell23_5432484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 2, 2, 3, 1, 3].length) (baseStart_5432484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432484 prefixEnd_5432484 := by exact prefixLift 5432484
  have htrace : WordTrace (prefixWord ++ tailWord_5432484) baseStart_5432484 baseEnd_5432484 := by
    simpa [prefixWord, tailWord_5432484, baseEnd_5432484] using wordTrace_append hprefix tailTrace_5432484
  have hstable : (prefixWord ++ tailWord_5432484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432484).length < 2 ^ (prefixWord ++ tailWord_5432484).sum := by decide
  have hdescent : baseEnd_5432484 < baseStart_5432484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432517 : List Nat := [1, 3, 1, 1, 1, 1, 3, 6, 2, 4]
def baseStart_5432517 : Nat := 118140960795 + 5432517 * 2 ^ 59
def prefixEnd_5432517 : Nat := 4983230072969 + 3 ^ 40 * 5432517 * 2
def baseEnd_5432517 : Nat := 929830794907075661984605

theorem tailTrace_5432517 : CollatzResearch.WordTrace tailWord_5432517 prefixEnd_5432517 929830794907075661984605 := by
  unfold tailWord_5432517
  simp only [CollatzResearch.WordTrace]
  refine ⟨198140172859926183882775805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132093448573284122588517203 198140172859926183882775805)
  ·
    refine ⟨74302564822472318956040927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198140172859926183882775805 74302564822472318956040927)
    ·
      refine ⟨111453847233708478434061391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74302564822472318956040927 111453847233708478434061391)
      ·
        refine ⟨167180770850562717651092087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111453847233708478434061391 167180770850562717651092087)
        ·
          refine ⟨250771156275844076476638131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167180770850562717651092087 250771156275844076476638131)
          ·
            refine ⟨376156734413766114714957197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250771156275844076476638131 376156734413766114714957197)
            ·
              refine ⟨141058775405162293018108949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 376156734413766114714957197 141058775405162293018108949)
              ·
                refine ⟨6612130097116982485223857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 141058775405162293018108949 6612130097116982485223857)
                ·
                  refine ⟨4959097572837736863917893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6612130097116982485223857 4959097572837736863917893)
                  ·
                    refine ⟨929830794907075661984605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959097572837736863917893 929830794907075661984605)
                    ·
                      rfl

theorem cell23_5432517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 6, 2, 4].length) (baseStart_5432517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432517 prefixEnd_5432517 := by exact prefixLift 5432517
  have htrace : WordTrace (prefixWord ++ tailWord_5432517) baseStart_5432517 baseEnd_5432517 := by
    simpa [prefixWord, tailWord_5432517, baseEnd_5432517] using wordTrace_append hprefix tailTrace_5432517
  have hstable : (prefixWord ++ tailWord_5432517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432517).length < 2 ^ (prefixWord ++ tailWord_5432517).sum := by decide
  have hdescent : baseEnd_5432517 < baseStart_5432517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432520 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 1, 1, 6]
def baseStart_5432520 : Nat := 118140960795 + 5432520 * 2 ^ 59
def prefixEnd_5432520 : Nat := 4983230072969 + 3 ^ 40 * 5432520 * 2
def baseEnd_5432520 : Nat := 2789493925163190474216301

theorem tailTrace_5432520 : CollatzResearch.WordTrace tailWord_5432520 prefixEnd_5432520 2789493925163190474216301 := by
  unfold tailWord_5432520
  simp only [CollatzResearch.WordTrace]
  refine ⟨99070141139457657697567507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132093521519276876930090009 99070141139457657697567507)
  ·
    refine ⟨148605211709186486546351261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99070141139457657697567507 148605211709186486546351261)
    ·
      refine ⟨55726954390944932454881723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 148605211709186486546351261 55726954390944932454881723)
      ·
        refine ⟨83590431586417398682322585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55726954390944932454881723 83590431586417398682322585)
        ·
          refine ⟨62692823689813049011741939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83590431586417398682322585 62692823689813049011741939)
          ·
            refine ⟨94039235534719573517612909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62692823689813049011741939 94039235534719573517612909)
            ·
              refine ⟨35264713325519840069104841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 94039235534719573517612909 35264713325519840069104841)
              ·
                refine ⟨26448534994139880051828631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35264713325519840069104841 26448534994139880051828631)
                ·
                  refine ⟨39672802491209820077742947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26448534994139880051828631 39672802491209820077742947)
                  ·
                    refine ⟨59509203736814730116614421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39672802491209820077742947 59509203736814730116614421)
                    ·
                      refine ⟨2789493925163190474216301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59509203736814730116614421 2789493925163190474216301)
                      ·
                        rfl

theorem cell23_5432520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 1, 1, 6].length) (baseStart_5432520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432520 prefixEnd_5432520 := by exact prefixLift 5432520
  have htrace : WordTrace (prefixWord ++ tailWord_5432520) baseStart_5432520 baseEnd_5432520 := by
    simpa [prefixWord, tailWord_5432520, baseEnd_5432520] using wordTrace_append hprefix tailTrace_5432520
  have hstable : (prefixWord ++ tailWord_5432520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432520).length < 2 ^ (prefixWord ++ tailWord_5432520).sum := by decide
  have hdescent : baseEnd_5432520 < baseStart_5432520 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432525 : List Nat := [1, 6, 2, 2, 2, 1, 2, 1, 6]
def baseStart_5432525 : Nat := 118140960795 + 5432525 * 2 ^ 59
def prefixEnd_5432525 : Nat := 4983230072969 + 3 ^ 40 * 5432525 * 2
def baseEnd_5432525 : Nat := 309944054729606994961531

theorem tailTrace_5432525 : CollatzResearch.WordTrace tailWord_5432525 prefixEnd_5432525 309944054729606994961531 := by
  unfold tailWord_5432525
  simp only [CollatzResearch.WordTrace]
  refine ⟨198140464643897201249067029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132093643095931467499378019 198140464643897201249067029)
  ·
    refine ⟨9287834280182681308550017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 198140464643897201249067029 9287834280182681308550017)
    ·
      refine ⟨6965875710137010981412513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9287834280182681308550017 6965875710137010981412513)
      ·
        refine ⟨5224406782602758236059385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6965875710137010981412513 5224406782602758236059385)
        ·
          refine ⟨3918305086952068677044539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5224406782602758236059385 3918305086952068677044539)
          ·
            refine ⟨5877457630428103015566809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3918305086952068677044539 5877457630428103015566809)
            ·
              refine ⟨4408093222821077261675107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5877457630428103015566809 4408093222821077261675107)
              ·
                refine ⟨6612139834231615892512661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408093222821077261675107 6612139834231615892512661)
                ·
                  refine ⟨309944054729606994961531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6612139834231615892512661 309944054729606994961531)
                  ·
                    rfl

theorem cell23_5432525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 2, 1, 2, 1, 6].length) (baseStart_5432525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432525 prefixEnd_5432525 := by exact prefixLift 5432525
  have htrace : WordTrace (prefixWord ++ tailWord_5432525) baseStart_5432525 baseEnd_5432525 := by
    simpa [prefixWord, tailWord_5432525, baseEnd_5432525] using wordTrace_append hprefix tailTrace_5432525
  have hstable : (prefixWord ++ tailWord_5432525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432525).length < 2 ^ (prefixWord ++ tailWord_5432525).sum := by decide
  have hdescent : baseEnd_5432525 < baseStart_5432525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432544 : List Nat := [2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3]
def baseStart_5432544 : Nat := 118140960795 + 5432544 * 2 ^ 59
def prefixEnd_5432544 : Nat := 4983230072969 + 3 ^ 40 * 5432544 * 2
def baseEnd_5432544 : Nat := 2789506248698898380316191

theorem tailTrace_5432544 : CollatzResearch.WordTrace tailWord_5432544 prefixEnd_5432544 2789506248698898380316191 := by
  unfold tailWord_5432544
  simp only [CollatzResearch.WordTrace]
  refine ⟨99070578815414183747004343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132094105087218911662672457 99070578815414183747004343)
  ·
    refine ⟨148605868223121275620506515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99070578815414183747004343 148605868223121275620506515)
    ·
      refine ⟨222908802334681913430759773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148605868223121275620506515 222908802334681913430759773)
      ·
        refine ⟨83590800875505717536534915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 222908802334681913430759773 83590800875505717536534915)
        ·
          refine ⟨125386201313258576304802373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 83590800875505717536534915 125386201313258576304802373)
          ·
            refine ⟨23509912746235983057150445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 125386201313258576304802373 23509912746235983057150445)
            ·
              refine ⟨8816217279838493646431417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23509912746235983057150445 8816217279838493646431417)
              ·
                refine ⟨6612162959878870234823563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8816217279838493646431417 6612162959878870234823563)
                ·
                  refine ⟨9918244439818305352235345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612162959878870234823563 9918244439818305352235345)
                  ·
                    refine ⟨7438683329863729014176509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9918244439818305352235345 7438683329863729014176509)
                    ·
                      refine ⟨2789506248698898380316191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7438683329863729014176509 2789506248698898380316191)
                      ·
                        rfl

theorem cell23_5432544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_5432544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432544 prefixEnd_5432544 := by exact prefixLift 5432544
  have htrace : WordTrace (prefixWord ++ tailWord_5432544) baseStart_5432544 baseEnd_5432544 := by
    simpa [prefixWord, tailWord_5432544, baseEnd_5432544] using wordTrace_append hprefix tailTrace_5432544
  have hstable : (prefixWord ++ tailWord_5432544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432544).length < 2 ^ (prefixWord ++ tailWord_5432544).sum := by decide
  have hdescent : baseEnd_5432544 < baseStart_5432544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432564 : List Nat := [2, 6, 1, 2, 12]
def baseStart_5432564 : Nat := 118140960795 + 5432564 * 2 ^ 59
def prefixEnd_5432564 : Nat := 4983230072969 + 3 ^ 40 * 5432564 * 2
def baseEnd_5432564 : Nat := 3826497281635100551531

theorem tailTrace_5432564 : CollatzResearch.WordTrace tailWord_5432564 prefixEnd_5432564 3826497281635100551531 := by
  unfold tailWord_5432564
  simp only [CollatzResearch.WordTrace]
  refine ⟨99070943545377955454868373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132094591393837273939824497 99070943545377955454868373)
  ·
    refine ⟨4643950478689591661946955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 99070943545377955454868373 4643950478689591661946955)
    ·
      refine ⟨6965925718034387492920433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4643950478689591661946955 6965925718034387492920433)
      ·
        refine ⟨5224444288525790619690325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6965925718034387492920433 5224444288525790619690325)
        ·
          refine ⟨3826497281635100551531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5224444288525790619690325 3826497281635100551531)
          ·
            rfl

theorem cell23_5432564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 12].length) (baseStart_5432564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432564 prefixEnd_5432564 := by exact prefixLift 5432564
  have htrace : WordTrace (prefixWord ++ tailWord_5432564) baseStart_5432564 baseEnd_5432564 := by
    simpa [prefixWord, tailWord_5432564, baseEnd_5432564] using wordTrace_append hprefix tailTrace_5432564
  have hstable : (prefixWord ++ tailWord_5432564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432564).length < 2 ^ (prefixWord ++ tailWord_5432564).sum := by decide
  have hdescent : baseEnd_5432564 < baseStart_5432564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432575 : List Nat := [1, 1, 2, 2, 1, 7, 2, 2, 1, 2, 2]
def baseStart_5432575 : Nat := 118140960795 + 5432575 * 2 ^ 59
def prefixEnd_5432575 : Nat := 4983230072969 + 3 ^ 40 * 5432575 * 2
def baseEnd_5432575 : Nat := 2789522166599187759028549

theorem tailTrace_5432575 : CollatzResearch.WordTrace tailWord_5432575 prefixEnd_5432575 2789522166599187759028549 := by
  unfold tailWord_5432575
  simp only [CollatzResearch.WordTrace]
  refine ⟨198142288293716059788387179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132094858862477373192258119 198142288293716059788387179)
  ·
    refine ⟨297213432440574089682580769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198142288293716059788387179 297213432440574089682580769)
    ·
      refine ⟨222910074330430567261935577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 297213432440574089682580769 222910074330430567261935577)
      ·
        refine ⟨167182555747822925446451683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222910074330430567261935577 167182555747822925446451683)
        ·
          refine ⟨250773833621734388169677525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167182555747822925446451683 250773833621734388169677525)
          ·
            refine ⟨5877511725509399722726817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 250773833621734388169677525 5877511725509399722726817)
            ·
              refine ⟨4408133794132049792045113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5877511725509399722726817 4408133794132049792045113)
              ·
                refine ⟨3306100345599037344033835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408133794132049792045113 3306100345599037344033835)
                ·
                  refine ⟨4959150518398556016050753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306100345599037344033835 4959150518398556016050753)
                  ·
                    refine ⟨3719362888798917012038065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4959150518398556016050753 3719362888798917012038065)
                    ·
                      refine ⟨2789522166599187759028549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719362888798917012038065 2789522166599187759028549)
                      ·
                        rfl

theorem cell23_5432575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 2, 2].length) (baseStart_5432575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432575 prefixEnd_5432575 := by exact prefixLift 5432575
  have htrace : WordTrace (prefixWord ++ tailWord_5432575) baseStart_5432575 baseEnd_5432575 := by
    simpa [prefixWord, tailWord_5432575, baseEnd_5432575] using wordTrace_append hprefix tailTrace_5432575
  have hstable : (prefixWord ++ tailWord_5432575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432575).length < 2 ^ (prefixWord ++ tailWord_5432575).sum := by decide
  have hdescent : baseEnd_5432575 < baseStart_5432575 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432618 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5432618 : Nat := 118140960795 + 5432618 * 2 ^ 59
def prefixEnd_5432618 : Nat := 4983230072969 + 3 ^ 40 * 5432618 * 2
def baseEnd_5432618 : Nat := 2789544246267331090790851

theorem tailTrace_5432618 : CollatzResearch.WordTrace tailWord_5432618 prefixEnd_5432618 2789544246267331090790851 := by
  unfold tailWord_5432618
  simp only [CollatzResearch.WordTrace]
  refine ⟨49535964158140069533050627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 132095904421706852088135005 49535964158140069533050627)
  ·
    refine ⟨74303946237210104299575941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 49535964158140069533050627 74303946237210104299575941)
    ·
      refine ⟨13931989919476894556170489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 74303946237210104299575941 13931989919476894556170489)
      ·
        refine ⟨10448992439607670917127867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13931989919476894556170489 10448992439607670917127867)
        ·
          refine ⟨15673488659411506375691801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10448992439607670917127867 15673488659411506375691801)
          ·
            refine ⟨11755116494558629781768851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15673488659411506375691801 11755116494558629781768851)
            ·
              refine ⟨17632674741837944672653277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11755116494558629781768851 17632674741837944672653277)
              ·
                refine ⟨6612253028189229252244979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17632674741837944672653277 6612253028189229252244979)
                ·
                  refine ⟨9918379542283843878367469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6612253028189229252244979 9918379542283843878367469)
                  ·
                    refine ⟨3719392328356441454387801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9918379542283843878367469 3719392328356441454387801)
                    ·
                      refine ⟨2789544246267331090790851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719392328356441454387801 2789544246267331090790851)
                      ·
                        rfl

theorem cell23_5432618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5432618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432618 prefixEnd_5432618 := by exact prefixLift 5432618
  have htrace : WordTrace (prefixWord ++ tailWord_5432618) baseStart_5432618 baseEnd_5432618 := by
    simpa [prefixWord, tailWord_5432618, baseEnd_5432618] using wordTrace_append hprefix tailTrace_5432618
  have hstable : (prefixWord ++ tailWord_5432618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432618).length < 2 ^ (prefixWord ++ tailWord_5432618).sum := by decide
  have hdescent : baseEnd_5432618 < baseStart_5432618 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432620 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 11]
def baseStart_5432620 : Nat := 118140960795 + 5432620 * 2 ^ 59
def prefixEnd_5432620 : Nat := 4983230072969 + 3 ^ 40 * 5432620 * 2
def baseEnd_5432620 : Nat := 309949474803182231440649

theorem tailTrace_5432620 : CollatzResearch.WordTrace tailWord_5432620 prefixEnd_5432620 309949474803182231440649 := by
  unfold tailWord_5432620
  simp only [CollatzResearch.WordTrace]
  refine ⟨99071964789276516236887657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132095953052368688315850209 99071964789276516236887657)
  ·
    refine ⟨74303973591957387177665743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99071964789276516236887657 74303973591957387177665743)
    ·
      refine ⟨111455960387936080766498615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74303973591957387177665743 111455960387936080766498615)
      ·
        refine ⟨167183940581904121149747923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111455960387936080766498615 167183940581904121149747923)
        ·
          refine ⟨250775910872856181724621885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167183940581904121149747923 250775910872856181724621885)
          ·
            refine ⟨94040966577321068146733207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 250775910872856181724621885 94040966577321068146733207)
            ·
              refine ⟨141061449865981602220099811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 94040966577321068146733207 141061449865981602220099811)
              ·
                refine ⟨211592174798972403330149717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 141061449865981602220099811 211592174798972403330149717)
                ·
                  refine ⟨309949474803182231440649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 211592174798972403330149717 309949474803182231440649)
                  ·
                    rfl

theorem cell23_5432620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 11].length) (baseStart_5432620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432620 prefixEnd_5432620 := by exact prefixLift 5432620
  have htrace : WordTrace (prefixWord ++ tailWord_5432620) baseStart_5432620 baseEnd_5432620 := by
    simpa [prefixWord, tailWord_5432620, baseEnd_5432620] using wordTrace_append hprefix tailTrace_5432620
  have hstable : (prefixWord ++ tailWord_5432620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432620).length < 2 ^ (prefixWord ++ tailWord_5432620).sum := by decide
  have hdescent : baseEnd_5432620 < baseStart_5432620 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432627 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4]
def baseStart_5432627 : Nat := 118140960795 + 5432627 * 2 ^ 59
def prefixEnd_5432627 : Nat := 4983230072969 + 3 ^ 40 * 5432627 * 2
def baseEnd_5432627 : Nat := 2789548867593221555578309

theorem tailTrace_5432627 : CollatzResearch.WordTrace tailWord_5432627 prefixEnd_5432627 2789548867593221555578309 := by
  unfold tailWord_5432627
  simp only [CollatzResearch.WordTrace]
  refine ⟨198144184889527672669280135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132096123259685115112853423 198144184889527672669280135)
  ·
    refine ⟨297216277334291509003920203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198144184889527672669280135 297216277334291509003920203)
    ·
      refine ⟨445824416001437263505880305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297216277334291509003920203 445824416001437263505880305)
      ·
        refine ⟨334368312001077947629410229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 445824416001437263505880305 334368312001077947629410229)
        ·
          refine ⟨31347029250101057590257209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 334368312001077947629410229 31347029250101057590257209)
          ·
            refine ⟨23510271937575793192692907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31347029250101057590257209 23510271937575793192692907)
            ·
              refine ⟨35265407906363689789039361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 23510271937575793192692907 35265407906363689789039361)
              ·
                refine ⟨26449055929772767341779521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35265407906363689789039361 26449055929772767341779521)
                ·
                  refine ⟨19836791947329575506334641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26449055929772767341779521 19836791947329575506334641)
                  ·
                    refine ⟨14877593960497181629750981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19836791947329575506334641 14877593960497181629750981)
                    ·
                      refine ⟨2789548867593221555578309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14877593960497181629750981 2789548867593221555578309)
                      ·
                        rfl

theorem cell23_5432627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 4].length) (baseStart_5432627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432627 prefixEnd_5432627 := by exact prefixLift 5432627
  have htrace : WordTrace (prefixWord ++ tailWord_5432627) baseStart_5432627 baseEnd_5432627 := by
    simpa [prefixWord, tailWord_5432627, baseEnd_5432627] using wordTrace_append hprefix tailTrace_5432627
  have hstable : (prefixWord ++ tailWord_5432627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432627).length < 2 ^ (prefixWord ++ tailWord_5432627).sum := by decide
  have hdescent : baseEnd_5432627 < baseStart_5432627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432677 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 5]
def baseStart_5432677 : Nat := 118140960795 + 5432677 * 2 ^ 59
def prefixEnd_5432677 : Nat := 4983230072969 + 3 ^ 40 * 5432677 * 2
def baseEnd_5432677 : Nat := 2789574541625946359953079

theorem tailTrace_5432677 : CollatzResearch.WordTrace tailWord_5432677 prefixEnd_5432677 2789574541625946359953079 := by
  unfold tailWord_5432677
  simp only [CollatzResearch.WordTrace]
  refine ⟨198146008539346531208600285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132097339026231020805733523 198146008539346531208600285)
  ·
    refine ⟨74304753202254949203225107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198146008539346531208600285 74304753202254949203225107)
    ·
      refine ⟨111457129803382423804837661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74304753202254949203225107 111457129803382423804837661)
      ·
        refine ⟨41796423676268408926814123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 111457129803382423804837661 41796423676268408926814123)
        ·
          refine ⟨62694635514402613390221185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41796423676268408926814123 62694635514402613390221185)
          ·
            refine ⟨47020976635801960042665889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 62694635514402613390221185 47020976635801960042665889)
            ·
              refine ⟨35265732476851470031999417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 47020976635801960042665889 35265732476851470031999417)
              ·
                refine ⟨26449299357638602523999563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 35265732476851470031999417 26449299357638602523999563)
                ·
                  refine ⟨39673949036457903785999345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26449299357638602523999563 39673949036457903785999345)
                  ·
                    refine ⟨29755461777343427839499509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 39673949036457903785999345 29755461777343427839499509)
                    ·
                      refine ⟨2789574541625946359953079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 29755461777343427839499509 2789574541625946359953079)
                      ·
                        rfl

theorem cell23_5432677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_5432677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432677 prefixEnd_5432677 := by exact prefixLift 5432677
  have htrace : WordTrace (prefixWord ++ tailWord_5432677) baseStart_5432677 baseEnd_5432677 := by
    simpa [prefixWord, tailWord_5432677, baseEnd_5432677] using wordTrace_append hprefix tailTrace_5432677
  have hstable : (prefixWord ++ tailWord_5432677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432677).length < 2 ^ (prefixWord ++ tailWord_5432677).sum := by decide
  have hdescent : baseEnd_5432677 < baseStart_5432677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432684 : List Nat := [2, 2, 1, 1, 5, 2, 1, 2, 2, 5]
def baseStart_5432684 : Nat := 118140960795 + 5432684 * 2 ^ 59
def prefixEnd_5432684 : Nat := 4983230072969 + 3 ^ 40 * 5432684 * 2
def baseEnd_5432684 : Nat := 929859378663509277521849

theorem tailTrace_5432684 : CollatzResearch.WordTrace tailWord_5432684 prefixEnd_5432684 929859378663509277521849 := by
  unfold tailWord_5432684
  simp only [CollatzResearch.WordTrace]
  refine ⟨99073131925160585702052553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132097509233547447602736737 99073131925160585702052553)
  ·
    refine ⟨74304848943870439276539415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99073131925160585702052553 74304848943870439276539415)
    ·
      refine ⟨111457273415805658914809123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74304848943870439276539415 111457273415805658914809123)
      ·
        refine ⟨167185910123708488372213685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111457273415805658914809123 167185910123708488372213685)
        ·
          refine ⟨15673679074097670784895033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 167185910123708488372213685 15673679074097670784895033)
          ·
            refine ⟨11755259305573253088671275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15673679074097670784895033 11755259305573253088671275)
            ·
              refine ⟨17632888958359879633006913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11755259305573253088671275 17632888958359879633006913)
              ·
                refine ⟨13224666718769909724755185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17632888958359879633006913 13224666718769909724755185)
                ·
                  refine ⟨9918500039077432293566389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13224666718769909724755185 9918500039077432293566389)
                  ·
                    refine ⟨929859378663509277521849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9918500039077432293566389 929859378663509277521849)
                    ·
                      rfl

theorem cell23_5432684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 5].length) (baseStart_5432684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432684 prefixEnd_5432684 := by exact prefixLift 5432684
  have htrace : WordTrace (prefixWord ++ tailWord_5432684) baseStart_5432684 baseEnd_5432684 := by
    simpa [prefixWord, tailWord_5432684, baseEnd_5432684] using wordTrace_append hprefix tailTrace_5432684
  have hstable : (prefixWord ++ tailWord_5432684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432684).length < 2 ^ (prefixWord ++ tailWord_5432684).sum := by decide
  have hdescent : baseEnd_5432684 < baseStart_5432684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432704 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 2, 4, 2]
def baseStart_5432704 : Nat := 118140960795 + 5432704 * 2 ^ 59
def prefixEnd_5432704 : Nat := 4983230072969 + 3 ^ 40 * 5432704 * 2
def baseEnd_5432704 : Nat := 2789588405603617754315455

theorem tailTrace_5432704 : CollatzResearch.WordTrace tailWord_5432704 prefixEnd_5432704 2789588405603617754315455 := by
  unfold tailWord_5432704
  simp only [CollatzResearch.WordTrace]
  refine ⟨99073496655124357409916583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132097995540165809879888777 99073496655124357409916583)
  ·
    refine ⟨148610244982686536114874875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99073496655124357409916583 148610244982686536114874875)
    ·
      refine ⟨222915367474029804172312313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 148610244982686536114874875 222915367474029804172312313)
      ·
        refine ⟨167186525605522353129234235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 222915367474029804172312313 167186525605522353129234235)
        ·
          refine ⟨250779788408283529693851353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167186525605522353129234235 250779788408283529693851353)
          ·
            refine ⟨188084841306212647270388515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 250779788408283529693851353 188084841306212647270388515)
            ·
              refine ⟨282127261959318970905582773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 188084841306212647270388515 282127261959318970905582773)
              ·
                refine ⟨26449430808686153522398385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282127261959318970905582773 26449430808686153522398385)
                ·
                  refine ⟨19837073106514615141798789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26449430808686153522398385 19837073106514615141798789)
                  ·
                    refine ⟨3719451207471490339087273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 19837073106514615141798789 3719451207471490339087273)
                    ·
                      refine ⟨2789588405603617754315455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719451207471490339087273 2789588405603617754315455)
                      ·
                        rfl

theorem cell23_5432704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_5432704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432704 prefixEnd_5432704 := by exact prefixLift 5432704
  have htrace : WordTrace (prefixWord ++ tailWord_5432704) baseStart_5432704 baseEnd_5432704 := by
    simpa [prefixWord, tailWord_5432704, baseEnd_5432704] using wordTrace_append hprefix tailTrace_5432704
  have hstable : (prefixWord ++ tailWord_5432704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432704).length < 2 ^ (prefixWord ++ tailWord_5432704).sum := by decide
  have hdescent : baseEnd_5432704 < baseStart_5432704 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432748 : List Nat := [2, 2, 1, 1, 1, 1, 8, 2, 1, 4]
def baseStart_5432748 : Nat := 118140960795 + 5432748 * 2 ^ 59
def prefixEnd_5432748 : Nat := 4983230072969 + 3 ^ 40 * 5432748 * 2
def baseEnd_5432748 : Nat := 929870332917471860721751

theorem tailTrace_5432748 : CollatzResearch.WordTrace tailWord_5432748 prefixEnd_5432748 929870332917471860721751 := by
  unfold tailWord_5432748
  simp only [CollatzResearch.WordTrace]
  refine ⟨99074299061044655167217449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132099065414726206889623265 99074299061044655167217449)
  ·
    refine ⟨74305724295783491375413087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99074299061044655167217449 74305724295783491375413087)
    ·
      refine ⟨111458586443675237063119631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74305724295783491375413087 111458586443675237063119631)
      ·
        refine ⟨167187879665512855594679447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111458586443675237063119631 167187879665512855594679447)
        ·
          refine ⟨250781819498269283392019171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167187879665512855594679447 250781819498269283392019171)
          ·
            refine ⟨376172729247403925088028757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250781819498269283392019171 376172729247403925088028757)
            ·
              refine ⟨4408274170868014747125337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 376172729247403925088028757 4408274170868014747125337)
              ·
                refine ⟨3306205628151011060344003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4408274170868014747125337 3306205628151011060344003)
                ·
                  refine ⟨4959308442226516590516005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306205628151011060344003 4959308442226516590516005)
                  ·
                    refine ⟨929870332917471860721751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959308442226516590516005 929870332917471860721751)
                    ·
                      rfl

theorem cell23_5432748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 8, 2, 1, 4].length) (baseStart_5432748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432748 prefixEnd_5432748 := by exact prefixLift 5432748
  have htrace : WordTrace (prefixWord ++ tailWord_5432748) baseStart_5432748 baseEnd_5432748 := by
    simpa [prefixWord, tailWord_5432748, baseEnd_5432748] using wordTrace_append hprefix tailTrace_5432748
  have hstable : (prefixWord ++ tailWord_5432748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432748).length < 2 ^ (prefixWord ++ tailWord_5432748).sum := by decide
  have hdescent : baseEnd_5432748 < baseStart_5432748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432805 : List Nat := [1, 3, 1, 5, 1, 1, 2, 4, 1, 1, 3]
def baseStart_5432805 : Nat := 118140960795 + 5432805 * 2 ^ 59
def prefixEnd_5432805 : Nat := 4983230072969 + 3 ^ 40 * 5432805 * 2
def baseEnd_5432805 : Nat := 2789640267149721859152491

theorem tailTrace_5432805 : CollatzResearch.WordTrace tailWord_5432805 prefixEnd_5432805 2789640267149721859152491 := by
  unfold tailWord_5432805
  simp only [CollatzResearch.WordTrace]
  refine ⟨198150677082882809069259869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132100451388588539379506579 198150677082882809069259869)
  ·
    refine ⟨74306503906081053400972451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 198150677082882809069259869 74306503906081053400972451)
    ·
      refine ⟨111459755859121580101458677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 74306503906081053400972451 111459755859121580101458677)
      ·
        refine ⟨10449352111792648134511751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 111459755859121580101458677 10449352111792648134511751)
        ·
          refine ⟨15674028167688972201767627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10449352111792648134511751 15674028167688972201767627)
          ·
            refine ⟨23511042251533458302651441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15674028167688972201767627 23511042251533458302651441)
            ·
              refine ⟨17633281688650093726988581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 23511042251533458302651441 17633281688650093726988581)
              ·
                refine ⟨3306240316621892573810359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 17633281688650093726988581 3306240316621892573810359)
                ·
                  refine ⟨4959360474932838860715539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3306240316621892573810359 4959360474932838860715539)
                  ·
                    refine ⟨7439040712399258291073309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4959360474932838860715539 7439040712399258291073309)
                    ·
                      refine ⟨2789640267149721859152491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 7439040712399258291073309 2789640267149721859152491)
                      ·
                        rfl

theorem cell23_5432805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_5432805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432805 prefixEnd_5432805 := by exact prefixLift 5432805
  have htrace : WordTrace (prefixWord ++ tailWord_5432805) baseStart_5432805 baseEnd_5432805 := by
    simpa [prefixWord, tailWord_5432805, baseEnd_5432805] using wordTrace_append hprefix tailTrace_5432805
  have hstable : (prefixWord ++ tailWord_5432805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432805).length < 2 ^ (prefixWord ++ tailWord_5432805).sum := by decide
  have hdescent : baseEnd_5432805 < baseStart_5432805 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432824 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 1, 1, 6]
def baseStart_5432824 : Nat := 118140960795 + 5432824 * 2 ^ 59
def prefixEnd_5432824 : Nat := 4983230072969 + 3 ^ 40 * 5432824 * 2
def baseEnd_5432824 : Nat := 2789650023282157284814903

theorem tailTrace_5432824 : CollatzResearch.WordTrace tailWord_5432824 prefixEnd_5432824 2789650023282157284814903 := by
  unfold tailWord_5432824
  simp only [CollatzResearch.WordTrace]
  refine ⟨99075685034906987657100763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132100913379875983542801017 99075685034906987657100763)
  ·
    refine ⟨148613527552360481485651145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99075685034906987657100763 148613527552360481485651145)
    ·
      refine ⟨111460145664270361114238359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148613527552360481485651145 111460145664270361114238359)
      ·
        refine ⟨167190218496405541671357539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111460145664270361114238359 167190218496405541671357539)
        ·
          refine ⟨250785327744608312507036309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 167190218496405541671357539 250785327744608312507036309)
          ·
            refine ⟨11755562238028514648767327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 250785327744608312507036309 11755562238028514648767327)
            ·
              refine ⟨17633343357042771973150991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11755562238028514648767327 17633343357042771973150991)
              ·
                refine ⟨26450015035564157959726487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17633343357042771973150991 26450015035564157959726487)
                ·
                  refine ⟨39675022553346236939589731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 26450015035564157959726487 39675022553346236939589731)
                  ·
                    refine ⟨59512533830019355409384597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 39675022553346236939589731 59512533830019355409384597)
                    ·
                      refine ⟨2789650023282157284814903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 59512533830019355409384597 2789650023282157284814903)
                      ·
                        rfl

theorem cell23_5432824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 1, 1, 6].length) (baseStart_5432824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432824 prefixEnd_5432824 := by exact prefixLift 5432824
  have htrace : WordTrace (prefixWord ++ tailWord_5432824) baseStart_5432824 baseEnd_5432824 := by
    simpa [prefixWord, tailWord_5432824, baseEnd_5432824] using wordTrace_append hprefix tailTrace_5432824
  have hstable : (prefixWord ++ tailWord_5432824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432824).length < 2 ^ (prefixWord ++ tailWord_5432824).sum := by decide
  have hdescent : baseEnd_5432824 < baseStart_5432824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432827 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7]
def baseStart_5432827 : Nat := 118140960795 + 5432827 * 2 ^ 59
def prefixEnd_5432827 : Nat := 4983230072969 + 3 ^ 40 * 5432827 * 2
def baseEnd_5432827 : Nat := 2789651563724120773077389

theorem tailTrace_5432827 : CollatzResearch.WordTrace tailWord_5432827 prefixEnd_5432827 2789651563724120773077389 := by
  unfold tailWord_5432827
  simp only [CollatzResearch.WordTrace]
  refine ⟨198151479488803106826560735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132100986325868737884373823 198151479488803106826560735)
  ·
    refine ⟨297227219233204660239841103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198151479488803106826560735 297227219233204660239841103)
    ·
      refine ⟨445840828849806990359761655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297227219233204660239841103 445840828849806990359761655)
      ·
        refine ⟨668761243274710485539642483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445840828849806990359761655 668761243274710485539642483)
        ·
          refine ⟨1003141864912065728309463725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668761243274710485539642483 1003141864912065728309463725)
          ·
            refine ⟨376178199342024648116048897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1003141864912065728309463725 376178199342024648116048897)
            ·
              refine ⟨282133649506518486087036673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376178199342024648116048897 282133649506518486087036673)
              ·
                refine ⟨211600237129888864565277505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282133649506518486087036673 211600237129888864565277505)
                ·
                  refine ⟨158700177847416648423958129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 211600237129888864565277505 158700177847416648423958129)
                  ·
                    refine ⟨119025133385562486317968597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 158700177847416648423958129 119025133385562486317968597)
                    ·
                      refine ⟨2789651563724120773077389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 119025133385562486317968597 2789651563724120773077389)
                      ·
                        rfl

theorem cell23_5432827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 7].length) (baseStart_5432827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432827 prefixEnd_5432827 := by exact prefixLift 5432827
  have htrace : WordTrace (prefixWord ++ tailWord_5432827) baseStart_5432827 baseEnd_5432827 := by
    simpa [prefixWord, tailWord_5432827, baseEnd_5432827] using wordTrace_append hprefix tailTrace_5432827
  have hstable : (prefixWord ++ tailWord_5432827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432827).length < 2 ^ (prefixWord ++ tailWord_5432827).sum := by decide
  have hdescent : baseEnd_5432827 < baseStart_5432827 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432828 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 3, 2, 2]
def baseStart_5432828 : Nat := 118140960795 + 5432828 * 2 ^ 59
def prefixEnd_5432828 : Nat := 4983230072969 + 3 ^ 40 * 5432828 * 2
def baseEnd_5432828 : Nat := 2789652077204775269164885

theorem tailTrace_5432828 : CollatzResearch.WordTrace tailWord_5432828 prefixEnd_5432828 2789652077204775269164885 := by
  unfold tailWord_5432828
  simp only [CollatzResearch.WordTrace]
  refine ⟨99075757980899741998673569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132101010641199655998231425 99075757980899741998673569)
  ·
    refine ⟨74306818485674806499005177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 99075757980899741998673569 74306818485674806499005177)
    ·
      refine ⟨55730113864256104874253883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 74306818485674806499005177 55730113864256104874253883)
      ·
        refine ⟨83595170796384157311380825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 55730113864256104874253883 83595170796384157311380825)
        ·
          refine ⟨62696378097288117983535619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 83595170796384157311380825 62696378097288117983535619)
          ·
            refine ⟨94044567145932176975303429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 62696378097288117983535619 94044567145932176975303429)
            ·
              refine ⟨17633356339862283182869393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 94044567145932176975303429 17633356339862283182869393)
              ·
                refine ⟨13225017254896712387152045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 17633356339862283182869393 13225017254896712387152045)
                ·
                  refine ⟨4959381470586267145182017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13225017254896712387152045 4959381470586267145182017)
                  ·
                    refine ⟨3719536102939700358886513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4959381470586267145182017 3719536102939700358886513)
                    ·
                      refine ⟨2789652077204775269164885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719536102939700358886513 2789652077204775269164885)
                      ·
                        rfl

theorem cell23_5432828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 2, 2].length) (baseStart_5432828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432828 prefixEnd_5432828 := by exact prefixLift 5432828
  have htrace : WordTrace (prefixWord ++ tailWord_5432828) baseStart_5432828 baseEnd_5432828 := by
    simpa [prefixWord, tailWord_5432828, baseEnd_5432828] using wordTrace_append hprefix tailTrace_5432828
  have hstable : (prefixWord ++ tailWord_5432828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432828).length < 2 ^ (prefixWord ++ tailWord_5432828).sum := by decide
  have hdescent : baseEnd_5432828 < baseStart_5432828 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432872 : List Nat := [2, 1, 5, 2, 2, 2, 2, 1, 2, 4]
def baseStart_5432872 : Nat := 118140960795 + 5432872 * 2 ^ 59
def prefixEnd_5432872 : Nat := 4983230072969 + 3 ^ 40 * 5432872 * 2
def baseEnd_5432872 : Nat := 929891556784524365671561

theorem tailTrace_5432872 : CollatzResearch.WordTrace tailWord_5432872 prefixEnd_5432872 929891556784524365671561 := by
  unfold tailWord_5432872
  simp only [CollatzResearch.WordTrace]
  refine ⟨99076560386820039755974435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132102080515760053007965913 99076560386820039755974435)
  ·
    refine ⟨148614840580230059633961653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99076560386820039755974435 148614840580230059633961653)
    ·
      refine ⟨13932641304396568090683905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 148614840580230059633961653 13932641304396568090683905)
      ·
        refine ⟨10449480978297426068012929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 13932641304396568090683905 10449480978297426068012929)
        ·
          refine ⟨7837110733723069551009697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10449480978297426068012929 7837110733723069551009697)
          ·
            refine ⟨5877833050292302163257273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7837110733723069551009697 5877833050292302163257273)
            ·
              refine ⟨4408374787719226622442955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5877833050292302163257273 4408374787719226622442955)
              ·
                refine ⟨6612562181578839933664433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4408374787719226622442955 6612562181578839933664433)
                ·
                  refine ⟨4959421636184129950248325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6612562181578839933664433 4959421636184129950248325)
                  ·
                    refine ⟨929891556784524365671561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4959421636184129950248325 929891556784524365671561)
                    ·
                      rfl

theorem cell23_5432872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_5432872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432872 prefixEnd_5432872 := by exact prefixLift 5432872
  have htrace : WordTrace (prefixWord ++ tailWord_5432872) baseStart_5432872 baseEnd_5432872 := by
    simpa [prefixWord, tailWord_5432872, baseEnd_5432872] using wordTrace_append hprefix tailTrace_5432872
  have hstable : (prefixWord ++ tailWord_5432872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432872).length < 2 ^ (prefixWord ++ tailWord_5432872).sum := by decide
  have hdescent : baseEnd_5432872 < baseStart_5432872 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432888 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 3, 3, 2]
def baseStart_5432888 : Nat := 118140960795 + 5432888 * 2 ^ 59
def prefixEnd_5432888 : Nat := 4983230072969 + 3 ^ 40 * 5432888 * 2
def baseEnd_5432888 : Nat := 2789682886044045034414609

theorem tailTrace_5432888 : CollatzResearch.WordTrace tailWord_5432888 prefixEnd_5432888 2789682886044045034414609 := by
  unfold tailWord_5432888
  simp only [CollatzResearch.WordTrace]
  refine ⟨99076852170791057122265659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 132102469561054742829687545 99076852170791057122265659)
  ·
    refine ⟨148615278256186585683398489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 99076852170791057122265659 148615278256186585683398489)
    ·
      refine ⟨111461458692139939262548867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 148615278256186585683398489 111461458692139939262548867)
      ·
        refine ⟨167192188038209908893823301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 111461458692139939262548867 167192188038209908893823301)
        ·
          refine ⟨31348535257164357917591869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 167192188038209908893823301 31348535257164357917591869)
          ·
            refine ⟨11755700721436634219096951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31348535257164357917591869 11755700721436634219096951)
            ·
              refine ⟨17633551082154951328645427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11755700721436634219096951 17633551082154951328645427)
              ·
                refine ⟨26450326623232426992968141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17633551082154951328645427 26450326623232426992968141)
                ·
                  refine ⟨9918872483712160122363053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 26450326623232426992968141 9918872483712160122363053)
                  ·
                    refine ⟨3719577181392060045886145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9918872483712160122363053 3719577181392060045886145)
                    ·
                      refine ⟨2789682886044045034414609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3719577181392060045886145 2789682886044045034414609)
                      ·
                        rfl

theorem cell23_5432888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 3, 2].length) (baseStart_5432888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432888 prefixEnd_5432888 := by exact prefixLift 5432888
  have htrace : WordTrace (prefixWord ++ tailWord_5432888) baseStart_5432888 baseEnd_5432888 := by
    simpa [prefixWord, tailWord_5432888, baseEnd_5432888] using wordTrace_append hprefix tailTrace_5432888
  have hstable : (prefixWord ++ tailWord_5432888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432888).length < 2 ^ (prefixWord ++ tailWord_5432888).sum := by decide
  have hdescent : baseEnd_5432888 < baseStart_5432888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5432931 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4]
def baseStart_5432931 : Nat := 118140960795 + 5432931 * 2 ^ 59
def prefixEnd_5432931 : Nat := 4983230072969 + 3 ^ 40 * 5432931 * 2
def baseEnd_5432931 : Nat := 2789704965712188366176911

theorem tailTrace_5432931 : CollatzResearch.WordTrace tailWord_5432931 prefixEnd_5432931 2789704965712188366176911 := by
  unfold tailWord_5432931
  simp only [CollatzResearch.WordTrace]
  refine ⟨198155272680426332588346647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 132103515120284221725564431 198155272680426332588346647)
  ·
    refine ⟨297232909020639498882519971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 198155272680426332588346647 297232909020639498882519971)
    ·
      refine ⟨445849363530959248323779957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297232909020639498882519971 445849363530959248323779957)
      ·
        refine ⟨41798377831027429530354371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 445849363530959248323779957 41798377831027429530354371)
        ·
          refine ⟨62697566746541144295531557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41798377831027429530354371 62697566746541144295531557)
          ·
            refine ⟨11755793764976464555412167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62697566746541144295531557 11755793764976464555412167)
            ·
              refine ⟨17633690647464696833118251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11755793764976464555412167 17633690647464696833118251)
              ·
                refine ⟨26450535971197045249677377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 17633690647464696833118251 26450535971197045249677377)
                ·
                  refine ⟨19837901978397783937258033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 26450535971197045249677377 19837901978397783937258033)
                  ·
                    refine ⟨14878426483798337952943525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 19837901978397783937258033 14878426483798337952943525)
                    ·
                      refine ⟨2789704965712188366176911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 14878426483798337952943525 2789704965712188366176911)
                      ·
                        rfl

theorem cell23_5432931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_5432931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5432931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5432931 prefixEnd_5432931 := by exact prefixLift 5432931
  have htrace : WordTrace (prefixWord ++ tailWord_5432931) baseStart_5432931 baseEnd_5432931 := by
    simpa [prefixWord, tailWord_5432931, baseEnd_5432931] using wordTrace_append hprefix tailTrace_5432931
  have hstable : (prefixWord ++ tailWord_5432931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5432931).length < 2 ^ (prefixWord ++ tailWord_5432931).sum := by decide
  have hdescent : baseEnd_5432931 < baseStart_5432931 := by decide
  rcases family_descends (prefixWord ++ tailWord_5432931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
