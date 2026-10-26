import V185TrunkScan23Chunk0777

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4601390 : List Nat := [4, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_4601390 : Nat := 118140960795 + 4601390 * 2 ^ 59
def prefixEnd_4601390 : Nat := 4983230072969 + 3 ^ 40 * 4601390 * 2
def baseEnd_4601390 : Nat := 2362724748791857274163599

theorem tailTrace_4601390 : CollatzResearch.WordTrace tailWord_4601390 prefixEnd_4601390 2362724748791857274163599 := by
  unfold tailWord_4601390
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978310099994669961501203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111884320533304906461339749 20978310099994669961501203)
  ·
    refine ⟨31467465149992004942251805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20978310099994669961501203 31467465149992004942251805)
    ·
      refine ⟨11800299431247001853344427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31467465149992004942251805 11800299431247001853344427)
      ·
        refine ⟨17700449146870502780016641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11800299431247001853344427 17700449146870502780016641)
        ·
          refine ⟨13275336860152877085012481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17700449146870502780016641 13275336860152877085012481)
          ·
            refine ⟨9956502645114657813759361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13275336860152877085012481 9956502645114657813759361)
            ·
              refine ⟨7467376983835993360319521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9956502645114657813759361 7467376983835993360319521)
              ·
                refine ⟨5600532737876995020239641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7467376983835993360319521 5600532737876995020239641)
                ·
                  refine ⟨4200399553407746265179731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5600532737876995020239641 4200399553407746265179731)
                  ·
                    refine ⟨6300599330111619397769597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200399553407746265179731 6300599330111619397769597)
                    ·
                      refine ⟨2362724748791857274163599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300599330111619397769597 2362724748791857274163599)
                      ·
                        rfl

theorem cell23_4601390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_4601390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601390 prefixEnd_4601390 := by exact prefixLift 4601390
  have htrace : WordTrace (prefixWord ++ tailWord_4601390) baseStart_4601390 baseEnd_4601390 := by
    simpa [prefixWord, tailWord_4601390, baseEnd_4601390] using wordTrace_append hprefix tailTrace_4601390
  have hstable : (prefixWord ++ tailWord_4601390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601390).length < 2 ^ (prefixWord ++ tailWord_4601390).sum := by decide
  have hdescent : baseEnd_4601390 < baseStart_4601390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601392 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6]
def baseStart_4601392 : Nat := 118140960795 + 4601392 * 2 ^ 59
def prefixEnd_4601392 : Nat := 4983230072969 + 3 ^ 40 * 4601392 * 2
def baseEnd_4601392 : Nat := 2362725775753166266338589

theorem tailTrace_4601392 : CollatzResearch.WordTrace tailWord_4601392 prefixEnd_4601392 2362725775753166266338589 := by
  unfold tailWord_4601392
  simp only [CollatzResearch.WordTrace]
  refine ⟨83913276872975057016791215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111884369163966742689054953 83913276872975057016791215)
  ·
    refine ⟨125869915309462585525186823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83913276872975057016791215 125869915309462585525186823)
    ·
      refine ⟨188804872964193878287780235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125869915309462585525186823 188804872964193878287780235)
      ·
        refine ⟨283207309446290817431670353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188804872964193878287780235 283207309446290817431670353)
        ·
          refine ⟨212405482084718113073752765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283207309446290817431670353 212405482084718113073752765)
          ·
            refine ⟨79652055781769292402657287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212405482084718113073752765 79652055781769292402657287)
            ·
              refine ⟨119478083672653938603985931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79652055781769292402657287 119478083672653938603985931)
              ·
                refine ⟨179217125508980907905978897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119478083672653938603985931 179217125508980907905978897)
                ·
                  refine ⟨134412844131735680929484173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179217125508980907905978897 134412844131735680929484173)
                  ·
                    refine ⟨50404816549400880348556565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134412844131735680929484173 50404816549400880348556565)
                    ·
                      refine ⟨2362725775753166266338589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50404816549400880348556565 2362725775753166266338589)
                      ·
                        rfl

theorem cell23_4601392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 2, 3, 6].length) (baseStart_4601392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601392 prefixEnd_4601392 := by exact prefixLift 4601392
  have htrace : WordTrace (prefixWord ++ tailWord_4601392) baseStart_4601392 baseEnd_4601392 := by
    simpa [prefixWord, tailWord_4601392, baseEnd_4601392] using wordTrace_append hprefix tailTrace_4601392
  have hstable : (prefixWord ++ tailWord_4601392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601392).length < 2 ^ (prefixWord ++ tailWord_4601392).sum := by decide
  have hdescent : baseEnd_4601392 < baseStart_4601392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601399 : List Nat := [1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_4601399 : Nat := 118140960795 + 4601399 * 2 ^ 59
def prefixEnd_4601399 : Nat := 4983230072969 + 3 ^ 40 * 4601399 * 2
def baseEnd_4601399 : Nat := 2362729370117747738951057

theorem tailTrace_4601399 : CollatzResearch.WordTrace tailWord_4601399 prefixEnd_4601399 2362729370117747738951057 := by
  unfold tailWord_4601399
  simp only [CollatzResearch.WordTrace]
  refine ⟨167826809056924754229087251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111884539371283169486058167 167826809056924754229087251)
  ·
    refine ⟨251740213585387131343630877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167826809056924754229087251 251740213585387131343630877)
    ·
      refine ⟨94402580094520174253861579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251740213585387131343630877 94402580094520174253861579)
      ·
        refine ⟨141603870141780261380792369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94402580094520174253861579 141603870141780261380792369)
        ·
          refine ⟨106202902606335196035594277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141603870141780261380792369 106202902606335196035594277)
          ·
            refine ⟨19913044238687849256673927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106202902606335196035594277 19913044238687849256673927)
            ·
              refine ⟨29869566358031773885010891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19913044238687849256673927 29869566358031773885010891)
              ·
                refine ⟨44804349537047660827516337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29869566358031773885010891 44804349537047660827516337)
                ·
                  refine ⟨33603262152785745620637253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44804349537047660827516337 33603262152785745620637253)
                  ·
                    refine ⟨6300611653647327303869485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33603262152785745620637253 6300611653647327303869485)
                    ·
                      refine ⟨2362729370117747738951057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300611653647327303869485 2362729370117747738951057)
                      ·
                        rfl

theorem cell23_4601399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_4601399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601399 prefixEnd_4601399 := by exact prefixLift 4601399
  have htrace : WordTrace (prefixWord ++ tailWord_4601399) baseStart_4601399 baseEnd_4601399 := by
    simpa [prefixWord, tailWord_4601399, baseEnd_4601399] using wordTrace_append hprefix tailTrace_4601399
  have hstable : (prefixWord ++ tailWord_4601399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601399).length < 2 ^ (prefixWord ++ tailWord_4601399).sum := by decide
  have hdescent : baseEnd_4601399 < baseStart_4601399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601413 : List Nat := [1, 3, 1, 1, 1, 4, 1, 5, 2, 2, 2]
def baseStart_4601413 : Nat := 118140960795 + 4601413 * 2 ^ 59
def prefixEnd_4601413 : Nat := 4983230072969 + 3 ^ 40 * 4601413 * 2
def baseEnd_4601413 : Nat := 2362736558846910684175993

theorem tailTrace_4601413 : CollatzResearch.WordTrace tailWord_4601413 prefixEnd_4601413 2362736558846910684175993 := by
  unfold tailWord_4601413
  simp only [CollatzResearch.WordTrace]
  refine ⟨167827319678874034620096893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111884879785916023080064595 167827319678874034620096893)
  ·
    refine ⟨62935244879577762982536335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167827319678874034620096893 62935244879577762982536335)
    ·
      refine ⟨94402867319366644473804503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62935244879577762982536335 94402867319366644473804503)
      ·
        refine ⟨141604300979049966710706755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94402867319366644473804503 141604300979049966710706755)
        ·
          refine ⟨212406451468574950066060133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141604300979049966710706755 212406451468574950066060133)
          ·
            refine ⟨39826209650357803137386275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212406451468574950066060133 39826209650357803137386275)
            ·
              refine ⟨59739314475536704706079413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39826209650357803137386275 59739314475536704706079413)
              ·
                refine ⟨5600560732081566066194945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59739314475536704706079413 5600560732081566066194945)
                ·
                  refine ⟨4200420549061174549646209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5600560732081566066194945 4200420549061174549646209)
                  ·
                    refine ⟨3150315411795880912234657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4200420549061174549646209 3150315411795880912234657)
                    ·
                      refine ⟨2362736558846910684175993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150315411795880912234657 2362736558846910684175993)
                      ·
                        rfl

theorem cell23_4601413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 5, 2, 2, 2].length) (baseStart_4601413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601413 prefixEnd_4601413 := by exact prefixLift 4601413
  have htrace : WordTrace (prefixWord ++ tailWord_4601413) baseStart_4601413 baseEnd_4601413 := by
    simpa [prefixWord, tailWord_4601413, baseEnd_4601413] using wordTrace_append hprefix tailTrace_4601413
  have hstable : (prefixWord ++ tailWord_4601413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601413).length < 2 ^ (prefixWord ++ tailWord_4601413).sum := by decide
  have hdescent : baseEnd_4601413 < baseStart_4601413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601429 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 3]
def baseStart_4601429 : Nat := 118140960795 + 4601429 * 2 ^ 59
def prefixEnd_4601429 : Nat := 4983230072969 + 3 ^ 40 * 4601429 * 2
def baseEnd_4601429 : Nat := 2362744774537382621575919

theorem tailTrace_4601429 : CollatzResearch.WordTrace tailWord_4601429 prefixEnd_4601429 2362744774537382621575919 := by
  unfold tailWord_4601429
  simp only [CollatzResearch.WordTrace]
  refine ⟨167827903246816069352679341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111885268831210712901786227 167827903246816069352679341)
  ·
    refine ⟨62935463717556026007254753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167827903246816069352679341 62935463717556026007254753)
    ·
      refine ⟨47201597788167019505441065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62935463717556026007254753 47201597788167019505441065)
      ·
        refine ⟨35401198341125264629080799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47201597788167019505441065 35401198341125264629080799)
        ·
          refine ⟨53101797511687896943621199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35401198341125264629080799 53101797511687896943621199)
          ·
            refine ⟨79652696267531845415431799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53101797511687896943621199 79652696267531845415431799)
            ·
              refine ⟨119479044401297768123147699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79652696267531845415431799 119479044401297768123147699)
              ·
                refine ⟨179218566601946652184721549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119479044401297768123147699 179218566601946652184721549)
                ·
                  refine ⟨67206962475729994569270581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179218566601946652184721549 67206962475729994569270581)
                  ·
                    refine ⟨6300652732099686990869117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67206962475729994569270581 6300652732099686990869117)
                    ·
                      refine ⟨2362744774537382621575919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300652732099686990869117 2362744774537382621575919)
                      ·
                        rfl

theorem cell23_4601429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 3, 5, 3].length) (baseStart_4601429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601429 prefixEnd_4601429 := by exact prefixLift 4601429
  have htrace : WordTrace (prefixWord ++ tailWord_4601429) baseStart_4601429 baseEnd_4601429 := by
    simpa [prefixWord, tailWord_4601429, baseEnd_4601429] using wordTrace_append hprefix tailTrace_4601429
  have hstable : (prefixWord ++ tailWord_4601429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601429).length < 2 ^ (prefixWord ++ tailWord_4601429).sum := by decide
  have hdescent : baseEnd_4601429 < baseStart_4601429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601449 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 2, 5]
def baseStart_4601449 : Nat := 118140960795 + 4601449 * 2 ^ 59
def prefixEnd_4601449 : Nat := 4983230072969 + 3 ^ 40 * 4601449 * 2
def baseEnd_4601449 : Nat := 787585014716824181108609

theorem tailTrace_4601449 : CollatzResearch.WordTrace tailWord_4601449 prefixEnd_4601449 787585014716824181108609 := by
  unfold tailWord_4601449
  simp only [CollatzResearch.WordTrace]
  refine ⟨167828632706743612768407401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111885755137829075178938267 167828632706743612768407401)
  ·
    refine ⟨125871474530057709576305551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167828632706743612768407401 125871474530057709576305551)
    ·
      refine ⟨188807211795086564364458327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125871474530057709576305551 188807211795086564364458327)
      ·
        refine ⟨283210817692629846546687491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188807211795086564364458327 283210817692629846546687491)
        ·
          refine ⟨424816226538944769820031237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283210817692629846546687491 424816226538944769820031237)
          ·
            refine ⟨79653042476052144341255857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 424816226538944769820031237 79653042476052144341255857)
            ·
              refine ⟨59739781857039108255941893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79653042476052144341255857 59739781857039108255941893)
              ·
                refine ⟨11201209098194832797989105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59739781857039108255941893 11201209098194832797989105)
                ·
                  refine ⟨8400906823646124598491829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11201209098194832797989105 8400906823646124598491829)
                  ·
                    refine ⟨787585014716824181108609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8400906823646124598491829 787585014716824181108609)
                    ·
                      rfl

theorem cell23_4601449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 5].length) (baseStart_4601449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601449 prefixEnd_4601449 := by exact prefixLift 4601449
  have htrace : WordTrace (prefixWord ++ tailWord_4601449) baseStart_4601449 baseEnd_4601449 := by
    simpa [prefixWord, tailWord_4601449, baseEnd_4601449] using wordTrace_append hprefix tailTrace_4601449
  have hstable : (prefixWord ++ tailWord_4601449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601449).length < 2 ^ (prefixWord ++ tailWord_4601449).sum := by decide
  have hdescent : baseEnd_4601449 < baseStart_4601449 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601486 : List Nat := [4, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4601486 : Nat := 118140960795 + 4601486 * 2 ^ 59
def prefixEnd_4601486 : Nat := 4983230072969 + 3 ^ 40 * 4601486 * 2
def baseEnd_4601486 : Nat := 2362774042934688898563157

theorem tailTrace_4601486 : CollatzResearch.WordTrace tailWord_4601486 prefixEnd_4601486 2362774042934688898563157 := by
  unfold tailWord_4601486
  simp only [CollatzResearch.WordTrace]
  refine ⟨20978747775951196010938039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111886654805073045391669541 20978747775951196010938039)
  ·
    refine ⟨31468121663926794016407059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20978747775951196010938039 31468121663926794016407059)
    ·
      refine ⟨47202182495890191024610589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31468121663926794016407059 47202182495890191024610589)
      ·
        refine ⟨17700818435958821634228971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47202182495890191024610589 17700818435958821634228971)
        ·
          refine ⟨26551227653938232451343457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17700818435958821634228971 26551227653938232451343457)
          ·
            refine ⟨19913420740453674338507593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26551227653938232451343457 19913420740453674338507593)
            ·
              refine ⟨14935065555340255753880695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19913420740453674338507593 14935065555340255753880695)
              ·
                refine ⟨22402598333010383630821043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14935065555340255753880695 22402598333010383630821043)
                ·
                  refine ⟨33603897499515575446231565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22402598333010383630821043 33603897499515575446231565)
                  ·
                    refine ⟨12601461562318340792336837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33603897499515575446231565 12601461562318340792336837)
                    ·
                      refine ⟨2362774042934688898563157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12601461562318340792336837 2362774042934688898563157)
                      ·
                        rfl

theorem cell23_4601486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4601486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601486 prefixEnd_4601486 := by exact prefixLift 4601486
  have htrace : WordTrace (prefixWord ++ tailWord_4601486) baseStart_4601486 baseEnd_4601486 := by
    simpa [prefixWord, tailWord_4601486, baseEnd_4601486] using wordTrace_append hprefix tailTrace_4601486
  have hstable : (prefixWord ++ tailWord_4601486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601486).length < 2 ^ (prefixWord ++ tailWord_4601486).sum := by decide
  have hdescent : baseEnd_4601486 < baseStart_4601486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601509 : List Nat := [1, 3, 1, 2, 1, 2, 4, 1, 8]
def baseStart_4601509 : Nat := 118140960795 + 4601509 * 2 ^ 59
def prefixEnd_4601509 : Nat := 4983230072969 + 3 ^ 40 * 4601509 * 2
def baseEnd_4601509 : Nat := 262531761443304700952839

theorem tailTrace_4601509 : CollatzResearch.WordTrace tailWord_4601509 prefixEnd_4601509 262531761443304700952839 := by
  unfold tailWord_4601509
  simp only [CollatzResearch.WordTrace]
  refine ⟨167830821086526243015591581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111887214057684162010394387 167830821086526243015591581)
  ·
    refine ⟨62936557907447341130846843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167830821086526243015591581 62936557907447341130846843)
    ·
      refine ⟨94404836861171011696270265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62936557907447341130846843 94404836861171011696270265)
      ·
        refine ⟨70803627645878258772202699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94404836861171011696270265 70803627645878258772202699)
        ·
          refine ⟨106205441468817388158304049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70803627645878258772202699 106205441468817388158304049)
          ·
            refine ⟨79654081101613041118728037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106205441468817388158304049 79654081101613041118728037)
            ·
              refine ⟨14935140206552445209761507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79654081101613041118728037 14935140206552445209761507)
              ·
                refine ⟨22402710309828667814642261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14935140206552445209761507 22402710309828667814642261)
                ·
                  refine ⟨262531761443304700952839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22402710309828667814642261 262531761443304700952839)
                  ·
                    rfl

theorem cell23_4601509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 4, 1, 8].length) (baseStart_4601509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601509 prefixEnd_4601509 := by exact prefixLift 4601509
  have htrace : WordTrace (prefixWord ++ tailWord_4601509) baseStart_4601509 baseEnd_4601509 := by
    simpa [prefixWord, tailWord_4601509, baseEnd_4601509] using wordTrace_append hprefix tailTrace_4601509
  have hstable : (prefixWord ++ tailWord_4601509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601509).length < 2 ^ (prefixWord ++ tailWord_4601509).sum := by decide
  have hdescent : baseEnd_4601509 < baseStart_4601509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601529 : List Nat := [1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 6]
def baseStart_4601529 : Nat := 118140960795 + 4601529 * 2 ^ 59
def prefixEnd_4601529 : Nat := 4983230072969 + 3 ^ 40 * 4601529 * 2
def baseEnd_4601529 : Nat := 2362796122602832230325459

theorem tailTrace_4601529 : CollatzResearch.WordTrace tailWord_4601529 prefixEnd_4601529 2362796122602832230325459 := by
  unfold tailWord_4601529
  simp only [CollatzResearch.WordTrace]
  refine ⟨167831550546453786431319641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111887700364302524287546427 167831550546453786431319641)
  ·
    refine ⟨125873662909840339823489731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167831550546453786431319641 125873662909840339823489731)
    ·
      refine ⟨188810494364760509735234597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125873662909840339823489731 188810494364760509735234597)
      ·
        refine ⟨35401967693392595575356487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188810494364760509735234597 35401967693392595575356487)
        ·
          refine ⟨53102951540088893363034731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35401967693392595575356487 53102951540088893363034731)
          ·
            refine ⟨79654427310133340044552097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53102951540088893363034731 79654427310133340044552097)
            ·
              refine ⟨59740820482600005033414073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79654427310133340044552097 59740820482600005033414073)
              ·
                refine ⟨44805615361950003775060555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59740820482600005033414073 44805615361950003775060555)
                ·
                  refine ⟨67208423042925005662590833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44805615361950003775060555 67208423042925005662590833)
                  ·
                    refine ⟨50406317282193754246943125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67208423042925005662590833 50406317282193754246943125)
                    ·
                      refine ⟨2362796122602832230325459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50406317282193754246943125 2362796122602832230325459)
                      ·
                        rfl

theorem cell23_4601529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 2, 1, 2, 6].length) (baseStart_4601529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601529 prefixEnd_4601529 := by exact prefixLift 4601529
  have htrace : WordTrace (prefixWord ++ tailWord_4601529) baseStart_4601529 baseEnd_4601529 := by
    simpa [prefixWord, tailWord_4601529, baseEnd_4601529] using wordTrace_append hprefix tailTrace_4601529
  have hstable : (prefixWord ++ tailWord_4601529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601529).length < 2 ^ (prefixWord ++ tailWord_4601529).sum := by decide
  have hdescent : baseEnd_4601529 < baseStart_4601529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601599 : List Nat := [1, 1, 2, 2, 1, 3, 2, 11]
def baseStart_4601599 : Nat := 118140960795 + 4601599 * 2 ^ 59
def prefixEnd_4601599 : Nat := 4983230072969 + 3 ^ 40 * 4601599 * 2
def baseEnd_4601599 : Nat := 87512298749949887275931

theorem tailTrace_4601599 : CollatzResearch.WordTrace tailWord_4601599 prefixEnd_4601599 87512298749949887275931 := by
  unfold tailWord_4601599
  simp only [CollatzResearch.WordTrace]
  refine ⟨167834103656200188386367851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111889402437466792257578567 167834103656200188386367851)
  ·
    refine ⟨251751155484300282579551777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167834103656200188386367851 251751155484300282579551777)
    ·
      refine ⟨188813366613225211934663833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251751155484300282579551777 188813366613225211934663833)
      ·
        refine ⟨141610024959918908950997875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188813366613225211934663833 141610024959918908950997875)
        ·
          refine ⟨212415037439878363426496813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141610024959918908950997875 212415037439878363426496813)
          ·
            refine ⟨79655639039954386284936305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212415037439878363426496813 79655639039954386284936305)
            ·
              refine ⟨59741729279965789713702229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79655639039954386284936305 59741729279965789713702229)
              ·
                refine ⟨87512298749949887275931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 59741729279965789713702229 87512298749949887275931)
                ·
                  rfl

theorem cell23_4601599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 11].length) (baseStart_4601599 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601599 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601599 prefixEnd_4601599 := by exact prefixLift 4601599
  have htrace : WordTrace (prefixWord ++ tailWord_4601599) baseStart_4601599 baseEnd_4601599 := by
    simpa [prefixWord, tailWord_4601599, baseEnd_4601599] using wordTrace_append hprefix tailTrace_4601599
  have hstable : (prefixWord ++ tailWord_4601599).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601599).length < 2 ^ (prefixWord ++ tailWord_4601599).sum := by decide
  have hdescent : baseEnd_4601599 < baseStart_4601599 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601607 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 1, 5]
def baseStart_4601607 : Nat := 118140960795 + 4601607 * 2 ^ 59
def prefixEnd_4601607 : Nat := 4983230072969 + 3 ^ 40 * 4601607 * 2
def baseEnd_4601607 : Nat := 787612058031294308383367

theorem tailTrace_4601607 : CollatzResearch.WordTrace tailWord_4601607 prefixEnd_4601607 787612058031294308383367 := by
  unfold tailWord_4601607
  simp only [CollatzResearch.WordTrace]
  refine ⟨167834395440171205752659075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111889596960114137168439383 167834395440171205752659075)
  ·
    refine ⟨251751593160256808628988613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167834395440171205752659075 251751593160256808628988613)
    ·
      refine ⟨47203423717548151617935365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251751593160256808628988613 47203423717548151617935365)
      ·
        refine ⟨8850641947040278428362881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47203423717548151617935365 8850641947040278428362881)
        ·
          refine ⟨6637981460280208821272161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8850641947040278428362881 6637981460280208821272161)
          ·
            refine ⟨4978486095210156615954121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6637981460280208821272161 4978486095210156615954121)
            ·
              refine ⟨3733864571407617461965591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4978486095210156615954121 3733864571407617461965591)
              ·
                refine ⟨5600796857111426192948387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733864571407617461965591 5600796857111426192948387)
                ·
                  refine ⟨8401195285667139289422581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600796857111426192948387 8401195285667139289422581)
                  ·
                    refine ⟨787612058031294308383367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8401195285667139289422581 787612058031294308383367)
                    ·
                      rfl

theorem cell23_4601607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_4601607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601607 prefixEnd_4601607 := by exact prefixLift 4601607
  have htrace : WordTrace (prefixWord ++ tailWord_4601607) baseStart_4601607 baseEnd_4601607 := by
    simpa [prefixWord, tailWord_4601607, baseEnd_4601607] using wordTrace_append hprefix tailTrace_4601607
  have hstable : (prefixWord ++ tailWord_4601607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601607).length < 2 ^ (prefixWord ++ tailWord_4601607).sum := by decide
  have hdescent : baseEnd_4601607 < baseStart_4601607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601610 : List Nat := [3, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_4601610 : Nat := 118140960795 + 4601610 * 2 ^ 59
def prefixEnd_4601610 : Nat := 4983230072969 + 3 ^ 40 * 4601610 * 2
def baseEnd_4601610 : Nat := 2362837714535846413412587

theorem tailTrace_4601610 : CollatzResearch.WordTrace tailWord_4601610 prefixEnd_4601610 2362837714535846413412587 := by
  unfold tailWord_4601610
  simp only [CollatzResearch.WordTrace]
  refine ⟨41958626214790084316254571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111889669906106891510012189 41958626214790084316254571)
  ·
    refine ⟨62937939322185126474381857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41958626214790084316254571 62937939322185126474381857)
    ·
      refine ⟨47203454491638844855786393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62937939322185126474381857 47203454491638844855786393)
      ·
        refine ⟨35402590868729133641839795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47203454491638844855786393 35402590868729133641839795)
        ·
          refine ⟨53103886303093700462759693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35402590868729133641839795 53103886303093700462759693)
          ·
            refine ⟨19913957363660137673534885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53103886303093700462759693 19913957363660137673534885)
            ·
              refine ⟨3733867005686275813787791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19913957363660137673534885 3733867005686275813787791)
              ·
                refine ⟨5600800508529413720681687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3733867005686275813787791 5600800508529413720681687)
                ·
                  refine ⟨8401200762794120581022531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5600800508529413720681687 8401200762794120581022531)
                  ·
                    refine ⟨12601801144191180871533797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8401200762794120581022531 12601801144191180871533797)
                    ·
                      refine ⟨2362837714535846413412587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12601801144191180871533797 2362837714535846413412587)
                      ·
                        rfl

theorem cell23_4601610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_4601610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601610 prefixEnd_4601610 := by exact prefixLift 4601610
  have htrace : WordTrace (prefixWord ++ tailWord_4601610) baseStart_4601610 baseEnd_4601610 := by
    simpa [prefixWord, tailWord_4601610, baseEnd_4601610] using wordTrace_append hprefix tailTrace_4601610
  have hstable : (prefixWord ++ tailWord_4601610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601610).length < 2 ^ (prefixWord ++ tailWord_4601610).sum := by decide
  have hdescent : baseEnd_4601610 < baseStart_4601610 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601640 : List Nat := [2, 1, 5, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_4601640 : Nat := 118140960795 + 4601640 * 2 ^ 59
def prefixEnd_4601640 : Nat := 4983230072969 + 3 ^ 40 * 4601640 * 2
def baseEnd_4601640 : Nat := 2362853118955481296037449

theorem tailTrace_4601640 : CollatzResearch.WordTrace tailWord_4601640 prefixEnd_4601640 2362853118955481296037449 := by
  unfold tailWord_4601640
  simp only [CollatzResearch.WordTrace]
  refine ⟨83917799524525826194305187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111890399366034434925740249 83917799524525826194305187)
  ·
    refine ⟨125876699286788739291457781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83917799524525826194305187 125876699286788739291457781)
    ·
      refine ⟨11800940558136444308574167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125876699286788739291457781 11800940558136444308574167)
      ·
        refine ⟨17701410837204666462861251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11800940558136444308574167 17701410837204666462861251)
        ·
          refine ⟨26552116255806999694291877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17701410837204666462861251 26552116255806999694291877)
          ·
            refine ⟨4978521797963812442679727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26552116255806999694291877 4978521797963812442679727)
            ·
              refine ⟨7467782696945718664019591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978521797963812442679727 7467782696945718664019591)
              ·
                refine ⟨11201674045418577996029387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7467782696945718664019591 11201674045418577996029387)
                ·
                  refine ⟨16802511068127866994044081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11201674045418577996029387 16802511068127866994044081)
                  ·
                    refine ⟨12601883301095900245533061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16802511068127866994044081 12601883301095900245533061)
                    ·
                      refine ⟨2362853118955481296037449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12601883301095900245533061 2362853118955481296037449)
                      ·
                        rfl

theorem cell23_4601640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_4601640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601640 prefixEnd_4601640 := by exact prefixLift 4601640
  have htrace : WordTrace (prefixWord ++ tailWord_4601640) baseStart_4601640 baseEnd_4601640 := by
    simpa [prefixWord, tailWord_4601640, baseEnd_4601640] using wordTrace_append hprefix tailTrace_4601640
  have hstable : (prefixWord ++ tailWord_4601640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601640).length < 2 ^ (prefixWord ++ tailWord_4601640).sum := by decide
  have hdescent : baseEnd_4601640 < baseStart_4601640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601656 : List Nat := [2, 1, 2, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_4601656 : Nat := 118140960795 + 4601656 * 2 ^ 59
def prefixEnd_4601656 : Nat := 4983230072969 + 3 ^ 40 * 4601656 * 2
def baseEnd_4601656 : Nat := 2362861334645953233437375

theorem tailTrace_4601656 : CollatzResearch.WordTrace tailWord_4601656 prefixEnd_4601656 2362861334645953233437375 := by
  unfold tailWord_4601656
  simp only [CollatzResearch.WordTrace]
  refine ⟨83918091308496843560596411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111890788411329124747461881 83918091308496843560596411)
  ·
    refine ⟨125877136962745265340894617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83918091308496843560596411 125877136962745265340894617)
    ·
      refine ⟨94407852722058949005670963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125877136962745265340894617 94407852722058949005670963)
      ·
        refine ⟨141611779083088423508506445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94407852722058949005670963 141611779083088423508506445)
        ·
          refine ⟨53104417156158158815689917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141611779083088423508506445 53104417156158158815689917)
          ·
            refine ⟨19914156433559309555883719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53104417156158158815689917 19914156433559309555883719)
            ·
              refine ⟨29871234650338964333825579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19914156433559309555883719 29871234650338964333825579)
              ·
                refine ⟨44806851975508446500738369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29871234650338964333825579 44806851975508446500738369)
                ·
                  refine ⟨33605138981631334875553777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44806851975508446500738369 33605138981631334875553777)
                  ·
                    refine ⟨25203854236223501156665333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33605138981631334875553777 25203854236223501156665333)
                    ·
                      refine ⟨2362861334645953233437375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25203854236223501156665333 2362861334645953233437375)
                      ·
                        rfl

theorem cell23_4601656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_4601656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601656 prefixEnd_4601656 := by exact prefixLift 4601656
  have htrace : WordTrace (prefixWord ++ tailWord_4601656) baseStart_4601656 baseEnd_4601656 := by
    simpa [prefixWord, tailWord_4601656, baseEnd_4601656] using wordTrace_append hprefix tailTrace_4601656
  have hstable : (prefixWord ++ tailWord_4601656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601656).length < 2 ^ (prefixWord ++ tailWord_4601656).sum := by decide
  have hdescent : baseEnd_4601656 < baseStart_4601656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601661 : List Nat := [1, 4, 1, 4, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4601661 : Nat := 118140960795 + 4601661 * 2 ^ 59
def prefixEnd_4601661 : Nat := 4983230072969 + 3 ^ 40 * 4601661 * 2
def baseEnd_4601661 : Nat := 2362863902049225713874853

theorem tailTrace_4601661 : CollatzResearch.WordTrace tailWord_4601661 prefixEnd_4601661 2362863902049225713874853 := by
  unfold tailWord_4601661
  simp only [CollatzResearch.WordTrace]
  refine ⟨167836364981975572975124837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111890909987983715316749891 167836364981975572975124837)
  ·
    refine ⟨31469318434120419932835907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167836364981975572975124837 31469318434120419932835907)
    ·
      refine ⟨47203977651180629899253861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31469318434120419932835907 47203977651180629899253861)
      ·
        refine ⟨8850745809596368106110099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47203977651180629899253861 8850745809596368106110099)
        ·
          refine ⟨13276118714394552159165149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8850745809596368106110099 13276118714394552159165149)
          ·
            refine ⟨4978544517897957059686931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13276118714394552159165149 4978544517897957059686931)
            ·
              refine ⟨7467816776846935589530397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978544517897957059686931 7467816776846935589530397)
              ·
                refine ⟨2800431291317600846073899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7467816776846935589530397 2800431291317600846073899)
                ·
                  refine ⟨4200646936976401269110849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800431291317600846073899 4200646936976401269110849)
                  ·
                    refine ⟨3150485202732300951833137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4200646936976401269110849 3150485202732300951833137)
                    ·
                      refine ⟨2362863902049225713874853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150485202732300951833137 2362863902049225713874853)
                      ·
                        rfl

theorem cell23_4601661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4601661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601661 prefixEnd_4601661 := by exact prefixLift 4601661
  have htrace : WordTrace (prefixWord ++ tailWord_4601661) baseStart_4601661 baseEnd_4601661 := by
    simpa [prefixWord, tailWord_4601661, baseEnd_4601661] using wordTrace_append hprefix tailTrace_4601661
  have hstable : (prefixWord ++ tailWord_4601661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601661).length < 2 ^ (prefixWord ++ tailWord_4601661).sum := by decide
  have hdescent : baseEnd_4601661 < baseStart_4601661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601677 : List Nat := [1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_4601677 : Nat := 118140960795 + 4601677 * 2 ^ 59
def prefixEnd_4601677 : Nat := 4983230072969 + 3 ^ 40 * 4601677 * 2
def baseEnd_4601677 : Nat := 2362872117739697651274779

theorem tailTrace_4601677 : CollatzResearch.WordTrace tailWord_4601677 prefixEnd_4601677 2362872117739697651274779 := by
  unfold tailWord_4601677
  simp only [CollatzResearch.WordTrace]
  refine ⟨167836948549917607707707285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111891299033278405138471523 167836948549917607707707285)
  ·
    refine ⟨7867356963277387861298779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 167836948549917607707707285 7867356963277387861298779)
    ·
      refine ⟨11801035444916081791948169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7867356963277387861298779 11801035444916081791948169)
      ·
        refine ⟨8850776583687061343961127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11801035444916081791948169 8850776583687061343961127)
        ·
          refine ⟨13276164875530592015941691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8850776583687061343961127 13276164875530592015941691)
          ·
            refine ⟨19914247313295888023912537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13276164875530592015941691 19914247313295888023912537)
            ·
              refine ⟨14935685484971916017934403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19914247313295888023912537 14935685484971916017934403)
              ·
                refine ⟨22403528227457874026901605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14935685484971916017934403 22403528227457874026901605)
                ·
                  refine ⟨4200661542648351380044051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22403528227457874026901605 4200661542648351380044051)
                  ·
                    refine ⟨6300992313972527070066077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200661542648351380044051 6300992313972527070066077)
                    ·
                      refine ⟨2362872117739697651274779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6300992313972527070066077 2362872117739697651274779)
                      ·
                        rfl

theorem cell23_4601677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_4601677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601677 prefixEnd_4601677 := by exact prefixLift 4601677
  have htrace : WordTrace (prefixWord ++ tailWord_4601677) baseStart_4601677 baseEnd_4601677 := by
    simpa [prefixWord, tailWord_4601677, baseEnd_4601677] using wordTrace_append hprefix tailTrace_4601677
  have hstable : (prefixWord ++ tailWord_4601677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601677).length < 2 ^ (prefixWord ++ tailWord_4601677).sum := by decide
  have hdescent : baseEnd_4601677 < baseStart_4601677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601723 : List Nat := [1, 1, 1, 1, 1, 5, 1, 7, 5]
def baseStart_4601723 : Nat := 118140960795 + 4601723 * 2 ^ 59
def prefixEnd_4601723 : Nat := 4983230072969 + 3 ^ 40 * 4601723 * 2
def baseEnd_4601723 : Nat := 262543970872200496811063

theorem tailTrace_4601723 : CollatzResearch.WordTrace tailWord_4601723 prefixEnd_4601723 262543970872200496811063 := by
  unfold tailWord_4601723
  simp only [CollatzResearch.WordTrace]
  refine ⟨167838626307750957563881823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111892417538500638375921215 167838626307750957563881823)
  ·
    refine ⟨251757939461626436345822735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167838626307750957563881823 251757939461626436345822735)
    ·
      refine ⟨377636909192439654518734103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251757939461626436345822735 377636909192439654518734103)
      ·
        refine ⟨566455363788659481778101155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377636909192439654518734103 566455363788659481778101155)
        ·
          refine ⟨849683045682989222667151733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566455363788659481778101155 849683045682989222667151733)
          ·
            refine ⟨79657785532780239625045475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 849683045682989222667151733 79657785532780239625045475)
            ·
              refine ⟨119486678299170359437568213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79657785532780239625045475 119486678299170359437568213)
              ·
                refine ⟨2800469022636805299318005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 119486678299170359437568213 2800469022636805299318005)
                ·
                  refine ⟨262543970872200496811063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2800469022636805299318005 262543970872200496811063)
                  ·
                    rfl

theorem cell23_4601723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 7, 5].length) (baseStart_4601723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601723 prefixEnd_4601723 := by exact prefixLift 4601723
  have htrace : WordTrace (prefixWord ++ tailWord_4601723) baseStart_4601723 baseEnd_4601723 := by
    simpa [prefixWord, tailWord_4601723, baseEnd_4601723] using wordTrace_append hprefix tailTrace_4601723
  have hstable : (prefixWord ++ tailWord_4601723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601723).length < 2 ^ (prefixWord ++ tailWord_4601723).sum := by decide
  have hdescent : baseEnd_4601723 < baseStart_4601723 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601733 : List Nat := [1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 3]
def baseStart_4601733 : Nat := 118140960795 + 4601733 * 2 ^ 59
def prefixEnd_4601733 : Nat := 4983230072969 + 3 ^ 40 * 4601733 * 2
def baseEnd_4601733 : Nat := 2362900872656349432174521

theorem tailTrace_4601733 : CollatzResearch.WordTrace tailWord_4601733 prefixEnd_4601733 2362900872656349432174521 := by
  unfold tailWord_4601733
  simp only [CollatzResearch.WordTrace]
  refine ⟨167838991037714729271745853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111892660691809819514497235 167838991037714729271745853)
  ·
    refine ⟨62939621639143023476904695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167838991037714729271745853 62939621639143023476904695)
    ·
      refine ⟨94409432458714535215357043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62939621639143023476904695 94409432458714535215357043)
      ·
        refine ⟨141614148688071802823035565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94409432458714535215357043 141614148688071802823035565)
        ·
          refine ⟨53105305758026926058638337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141614148688071802823035565 53105305758026926058638337)
          ·
            refine ⟨39828979318520194543978753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53105305758026926058638337 39828979318520194543978753)
            ·
              refine ⟨29871734488890145907984065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39828979318520194543978753 29871734488890145907984065)
              ·
                refine ⟨22403800866667609430988049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29871734488890145907984065 22403800866667609430988049)
                ·
                  refine ⟨16802850650000707073241037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22403800866667609430988049 16802850650000707073241037)
                  ·
                    refine ⟨6301068993750265152465389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16802850650000707073241037 6301068993750265152465389)
                    ·
                      refine ⟨2362900872656349432174521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6301068993750265152465389 2362900872656349432174521)
                      ·
                        rfl

theorem cell23_4601733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 2, 2, 3, 3].length) (baseStart_4601733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601733 prefixEnd_4601733 := by exact prefixLift 4601733
  have htrace : WordTrace (prefixWord ++ tailWord_4601733) baseStart_4601733 baseEnd_4601733 := by
    simpa [prefixWord, tailWord_4601733, baseEnd_4601733] using wordTrace_append hprefix tailTrace_4601733
  have hstable : (prefixWord ++ tailWord_4601733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601733).length < 2 ^ (prefixWord ++ tailWord_4601733).sum := by decide
  have hdescent : baseEnd_4601733 < baseStart_4601733 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601783 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 7, 4]
def baseStart_4601783 : Nat := 118140960795 + 4601783 * 2 ^ 59
def prefixEnd_4601783 : Nat := 4983230072969 + 3 ^ 40 * 4601783 * 2
def baseEnd_4601783 : Nat := 787642182229691412183097

theorem tailTrace_4601783 : CollatzResearch.WordTrace tailWord_4601783 prefixEnd_4601783 787642182229691412183097 := by
  unfold tailWord_4601783
  simp only [CollatzResearch.WordTrace]
  refine ⟨167840814687533587811066003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111893876458355725207377335 167840814687533587811066003)
  ·
    refine ⟨251761222031300381716599005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167840814687533587811066003 251761222031300381716599005)
    ·
      refine ⟨94410458261737643143724627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251761222031300381716599005 94410458261737643143724627)
      ·
        refine ⟨141615687392606464715586941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94410458261737643143724627 141615687392606464715586941)
        ·
          refine ⟨53105882772227424268345103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141615687392606464715586941 53105882772227424268345103)
          ·
            refine ⟨79658824158341136402517655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53105882772227424268345103 79658824158341136402517655)
            ·
              refine ⟨119488236237511704603776483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79658824158341136402517655 119488236237511704603776483)
              ·
                refine ⟨179232354356267556905664725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119488236237511704603776483 179232354356267556905664725)
                ·
                  refine ⟨4200758305225020864976517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 179232354356267556905664725 4200758305225020864976517)
                  ·
                    refine ⟨787642182229691412183097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4200758305225020864976517 787642182229691412183097)
                    ·
                      rfl

theorem cell23_4601783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_4601783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601783 prefixEnd_4601783 := by exact prefixLift 4601783
  have htrace : WordTrace (prefixWord ++ tailWord_4601783) baseStart_4601783 baseEnd_4601783 := by
    simpa [prefixWord, tailWord_4601783, baseEnd_4601783] using wordTrace_append hprefix tailTrace_4601783
  have hstable : (prefixWord ++ tailWord_4601783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601783).length < 2 ^ (prefixWord ++ tailWord_4601783).sum := by decide
  have hdescent : baseEnd_4601783 < baseStart_4601783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601800 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 3, 4]
def baseStart_4601800 : Nat := 118140960795 + 4601800 * 2 ^ 59
def prefixEnd_4601800 : Nat := 4983230072969 + 3 ^ 40 * 4601800 * 2
def baseEnd_4601800 : Nat := 787645091953400223345571

theorem tailTrace_4601800 : CollatzResearch.WordTrace tailWord_4601800 prefixEnd_4601800 787645091953400223345571 := by
  unfold tailWord_4601800
  simp only [CollatzResearch.WordTrace]
  refine ⟨83920717364235999857217427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111894289818981333142956569 83920717364235999857217427)
  ·
    refine ⟨125881076046353999785826141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83920717364235999857217427 125881076046353999785826141)
    ·
      refine ⟨47205403517382749919684803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125881076046353999785826141 47205403517382749919684803)
      ·
        refine ⟨70808105276074124879527205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47205403517382749919684803 70808105276074124879527205)
        ·
          refine ⟨13276519739263898414911351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70808105276074124879527205 13276519739263898414911351)
          ·
            refine ⟨19914779608895847622367027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13276519739263898414911351 19914779608895847622367027)
            ·
              refine ⟨29872169413343771433550541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19914779608895847622367027 29872169413343771433550541)
              ·
                refine ⟨11202063530003914287581453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29872169413343771433550541 11202063530003914287581453)
                ·
                  refine ⟨4200773823751467857843045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11202063530003914287581453 4200773823751467857843045)
                  ·
                    refine ⟨787645091953400223345571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4200773823751467857843045 787645091953400223345571)
                    ·
                      rfl

theorem cell23_4601800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_4601800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601800 prefixEnd_4601800 := by exact prefixLift 4601800
  have htrace : WordTrace (prefixWord ++ tailWord_4601800) baseStart_4601800 baseEnd_4601800 := by
    simpa [prefixWord, tailWord_4601800, baseEnd_4601800] using wordTrace_append hprefix tailTrace_4601800
  have hstable : (prefixWord ++ tailWord_4601800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601800).length < 2 ^ (prefixWord ++ tailWord_4601800).sum := by decide
  have hdescent : baseEnd_4601800 < baseStart_4601800 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601840 : List Nat := [2, 1, 1, 1, 3, 2, 2, 2, 5, 1, 3]
def baseStart_4601840 : Nat := 118140960795 + 4601840 * 2 ^ 59
def prefixEnd_4601840 : Nat := 4983230072969 + 3 ^ 40 * 4601840 * 2
def baseEnd_4601840 : Nat := 2362955815086380513536529

theorem tailTrace_4601840 : CollatzResearch.WordTrace tailWord_4601840 prefixEnd_4601840 2362955815086380513536529 := by
  unfold tailWord_4601840
  simp only [CollatzResearch.WordTrace]
  refine ⟨83921446824163543272945487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111895262432218057697260649 83921446824163543272945487)
  ·
    refine ⟨125882170236245314909418231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83921446824163543272945487 125882170236245314909418231)
    ·
      refine ⟨188823255354367972364127347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125882170236245314909418231 188823255354367972364127347)
      ·
        refine ⟨283234883031551958546191021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188823255354367972364127347 283234883031551958546191021)
        ·
          refine ⟨106213081136831984454821633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283234883031551958546191021 106213081136831984454821633)
          ·
            refine ⟨79659810852623988341116225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106213081136831984454821633 79659810852623988341116225)
            ·
              refine ⟨59744858139467991255837169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79659810852623988341116225 59744858139467991255837169)
              ·
                refine ⟨44808643604600993441877877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59744858139467991255837169 44808643604600993441877877)
                ·
                  refine ⟨4200810337931343135176051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44808643604600993441877877 4200810337931343135176051)
                  ·
                    refine ⟨6301215506897014702764077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200810337931343135176051 6301215506897014702764077)
                    ·
                      refine ⟨2362955815086380513536529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6301215506897014702764077 2362955815086380513536529)
                      ·
                        rfl

theorem cell23_4601840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 2, 5, 1, 3].length) (baseStart_4601840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601840 prefixEnd_4601840 := by exact prefixLift 4601840
  have htrace : WordTrace (prefixWord ++ tailWord_4601840) baseStart_4601840 baseEnd_4601840 := by
    simpa [prefixWord, tailWord_4601840, baseEnd_4601840] using wordTrace_append hprefix tailTrace_4601840
  have hstable : (prefixWord ++ tailWord_4601840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601840).length < 2 ^ (prefixWord ++ tailWord_4601840).sum := by decide
  have hdescent : baseEnd_4601840 < baseStart_4601840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601880 : List Nat := [2, 1, 2, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_4601880 : Nat := 118140960795 + 4601880 * 2 ^ 59
def prefixEnd_4601880 : Nat := 4983230072969 + 3 ^ 40 * 4601880 * 2
def baseEnd_4601880 : Nat := 2362976354312560357036345

theorem tailTrace_4601880 : CollatzResearch.WordTrace tailWord_4601880 prefixEnd_4601880 2362976354312560357036345 := by
  unfold tailWord_4601880
  simp only [CollatzResearch.WordTrace]
  refine ⟨83922176284091086688673547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111896235045454782251564729 83922176284091086688673547)
  ·
    refine ⟨125883264426136630033010321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83922176284091086688673547 125883264426136630033010321)
    ·
      refine ⟨94412448319602472524757741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125883264426136630033010321 94412448319602472524757741)
      ·
        refine ⟨35404668119850927196784153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94412448319602472524757741 35404668119850927196784153)
        ·
          refine ⟨26553501089888195397588115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35404668119850927196784153 26553501089888195397588115)
          ·
            refine ⟨39830251634832293096382173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26553501089888195397588115 39830251634832293096382173)
            ·
              refine ⟨14936344363062109911143315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39830251634832293096382173 14936344363062109911143315)
              ·
                refine ⟨22404516544593164866714973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14936344363062109911143315 22404516544593164866714973)
                ·
                  refine ⟨8401693704222436825018115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22404516544593164866714973 8401693704222436825018115)
                  ·
                    refine ⟨12602540556333655237527173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8401693704222436825018115 12602540556333655237527173)
                    ·
                      refine ⟨2362976354312560357036345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12602540556333655237527173 2362976354312560357036345)
                      ·
                        rfl

theorem cell23_4601880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_4601880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601880 prefixEnd_4601880 := by exact prefixLift 4601880
  have htrace : WordTrace (prefixWord ++ tailWord_4601880) baseStart_4601880 baseEnd_4601880 := by
    simpa [prefixWord, tailWord_4601880, baseEnd_4601880] using wordTrace_append hprefix tailTrace_4601880
  have hstable : (prefixWord ++ tailWord_4601880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601880).length < 2 ^ (prefixWord ++ tailWord_4601880).sum := by decide
  have hdescent : baseEnd_4601880 < baseStart_4601880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601884 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_4601884 : Nat := 118140960795 + 4601884 * 2 ^ 59
def prefixEnd_4601884 : Nat := 4983230072969 + 3 ^ 40 * 4601884 * 2
def baseEnd_4601884 : Nat := 2362978408235178341386327

theorem tailTrace_4601884 : CollatzResearch.WordTrace tailWord_4601884 prefixEnd_4601884 2362978408235178341386327 := by
  unfold tailWord_4601884
  simp only [CollatzResearch.WordTrace]
  refine ⟨83922249230083841030246353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111896332306778454706995137 83922249230083841030246353)
  ·
    refine ⟨62941686922562880772684765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83922249230083841030246353 62941686922562880772684765)
    ·
      refine ⟨23603132595961080289756787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62941686922562880772684765 23603132595961080289756787)
      ·
        refine ⟨35404698893941620434635181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23603132595961080289756787 35404698893941620434635181)
        ·
          refine ⟨13276762085228107662988193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35404698893941620434635181 13276762085228107662988193)
          ·
            refine ⟨9957571563921080747241145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13276762085228107662988193 9957571563921080747241145)
            ·
              refine ⟨7468178672940810560430859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9957571563921080747241145 7468178672940810560430859)
              ·
                refine ⟨11202268009411215840646289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7468178672940810560430859 11202268009411215840646289)
                ·
                  refine ⟨8401701007058411880484717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11202268009411215840646289 8401701007058411880484717)
                  ·
                    refine ⟨3150637877646904455181769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8401701007058411880484717 3150637877646904455181769)
                    ·
                      refine ⟨2362978408235178341386327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150637877646904455181769 2362978408235178341386327)
                      ·
                        rfl

theorem cell23_4601884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_4601884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601884 prefixEnd_4601884 := by exact prefixLift 4601884
  have htrace : WordTrace (prefixWord ++ tailWord_4601884) baseStart_4601884 baseEnd_4601884 := by
    simpa [prefixWord, tailWord_4601884, baseEnd_4601884] using wordTrace_append hprefix tailTrace_4601884
  have hstable : (prefixWord ++ tailWord_4601884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601884).length < 2 ^ (prefixWord ++ tailWord_4601884).sum := by decide
  have hdescent : baseEnd_4601884 < baseStart_4601884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601890 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 1, 6]
def baseStart_4601890 : Nat := 118140960795 + 4601890 * 2 ^ 59
def prefixEnd_4601890 : Nat := 4983230072969 + 3 ^ 40 * 4601890 * 2
def baseEnd_4601890 : Nat := 787660496373035105970433

theorem tailTrace_4601890 : CollatzResearch.WordTrace tailWord_4601890 prefixEnd_4601890 787660496373035105970433 := by
  unfold tailWord_4601890
  simp only [CollatzResearch.WordTrace]
  refine ⟨41961179324536486271302781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111896478198763963390140749 41961179324536486271302781)
  ·
    refine ⟨15735442246701182351738543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41961179324536486271302781 15735442246701182351738543)
    ·
      refine ⟨23603163370051773527607815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15735442246701182351738543 23603163370051773527607815)
      ·
        refine ⟨35404745055077660291411723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23603163370051773527607815 35404745055077660291411723)
        ·
          refine ⟨53107117582616490437117585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35404745055077660291411723 53107117582616490437117585)
          ·
            refine ⟨39830338186962367827838189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53107117582616490437117585 39830338186962367827838189)
            ·
              refine ⟨14936376820110887935439321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39830338186962367827838189 14936376820110887935439321)
              ·
                refine ⟨11202282615083165951579491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14936376820110887935439321 11202282615083165951579491)
                ·
                  refine ⟨16803423922624748927369237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11202282615083165951579491 16803423922624748927369237)
                  ·
                    refine ⟨787660496373035105970433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16803423922624748927369237 787660496373035105970433)
                    ·
                      rfl

theorem cell23_4601890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_4601890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601890 prefixEnd_4601890 := by exact prefixLift 4601890
  have htrace : WordTrace (prefixWord ++ tailWord_4601890) baseStart_4601890 baseEnd_4601890 := by
    simpa [prefixWord, tailWord_4601890, baseEnd_4601890] using wordTrace_append hprefix tailTrace_4601890
  have hstable : (prefixWord ++ tailWord_4601890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601890).length < 2 ^ (prefixWord ++ tailWord_4601890).sum := by decide
  have hdescent : baseEnd_4601890 < baseStart_4601890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601908 : List Nat := [2, 5, 1, 2, 2, 1, 1, 4, 1, 1, 3]
def baseStart_4601908 : Nat := 118140960795 + 4601908 * 2 ^ 59
def prefixEnd_4601908 : Nat := 4983230072969 + 3 ^ 40 * 4601908 * 2
def baseEnd_4601908 : Nat := 2362990731770886247486217

theorem tailTrace_4601908 : CollatzResearch.WordTrace tailWord_4601908 prefixEnd_4601908 2362990731770886247486217 := by
  unfold tailWord_4601908
  simp only [CollatzResearch.WordTrace]
  refine ⟨83922686906040367079683189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111896915874720489439577585 83922686906040367079683189)
  ·
    refine ⟨7867751897441284413720299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83922686906040367079683189 7867751897441284413720299)
    ·
      refine ⟨11801627846161926620580449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7867751897441284413720299 11801627846161926620580449)
      ·
        refine ⟨8851220884621444965435337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11801627846161926620580449 8851220884621444965435337)
        ·
          refine ⟨6638415663466083724076503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8851220884621444965435337 6638415663466083724076503)
          ·
            refine ⟨9957623495199125586114755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638415663466083724076503 9957623495199125586114755)
            ·
              refine ⟨14936435242798688379172133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9957623495199125586114755 14936435242798688379172133)
              ·
                refine ⟨2800581608024754071094775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14936435242798688379172133 2800581608024754071094775)
                ·
                  refine ⟨4200872412037131106642163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800581608024754071094775 4200872412037131106642163)
                  ·
                    refine ⟨6301308618055696659963245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200872412037131106642163 6301308618055696659963245)
                    ·
                      refine ⟨2362990731770886247486217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6301308618055696659963245 2362990731770886247486217)
                      ·
                        rfl

theorem cell23_4601908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_4601908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601908 prefixEnd_4601908 := by exact prefixLift 4601908
  have htrace : WordTrace (prefixWord ++ tailWord_4601908) baseStart_4601908 baseEnd_4601908 := by
    simpa [prefixWord, tailWord_4601908, baseEnd_4601908] using wordTrace_append hprefix tailTrace_4601908
  have hstable : (prefixWord ++ tailWord_4601908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601908).length < 2 ^ (prefixWord ++ tailWord_4601908).sum := by decide
  have hdescent : baseEnd_4601908 < baseStart_4601908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601920 : List Nat := [2, 1, 1, 2, 2, 6, 1, 8]
def baseStart_4601920 : Nat := 118140960795 + 4601920 * 2 ^ 59
def prefixEnd_4601920 : Nat := 4983230072969 + 3 ^ 40 * 4601920 * 2
def baseEnd_4601920 : Nat := 87518403464397785205043

theorem tailTrace_4601920 : CollatzResearch.WordTrace tailWord_4601920 prefixEnd_4601920 87518403464397785205043 := by
  unfold tailWord_4601920
  simp only [CollatzResearch.WordTrace]
  refine ⟨83922905744018630104401607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111897207658691506805868809 83922905744018630104401607)
  ·
    refine ⟨125884358616027945156602411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83922905744018630104401607 125884358616027945156602411)
    ·
      refine ⟨188826537924041917734903617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125884358616027945156602411 188826537924041917734903617)
      ·
        refine ⟨141619903443031438301177713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188826537924041917734903617 141619903443031438301177713)
        ·
          refine ⟨106214927582273578725883285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141619903443031438301177713 106214927582273578725883285)
          ·
            refine ⟨4978824730419074002775779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106214927582273578725883285 4978824730419074002775779)
            ·
              refine ⟨7468237095628611004163669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4978824730419074002775779 7468237095628611004163669)
              ·
                refine ⟨87518403464397785205043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7468237095628611004163669 87518403464397785205043)
                ·
                  rfl

theorem cell23_4601920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 8].length) (baseStart_4601920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601920 prefixEnd_4601920 := by exact prefixLift 4601920
  have htrace : WordTrace (prefixWord ++ tailWord_4601920) baseStart_4601920 baseEnd_4601920 := by
    simpa [prefixWord, tailWord_4601920, baseEnd_4601920] using wordTrace_append hprefix tailTrace_4601920
  have hstable : (prefixWord ++ tailWord_4601920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601920).length < 2 ^ (prefixWord ++ tailWord_4601920).sum := by decide
  have hdescent : baseEnd_4601920 < baseStart_4601920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601948 : List Nat := [2, 2, 4, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_4601948 : Nat := 118140960795 + 4601948 * 2 ^ 59
def prefixEnd_4601948 : Nat := 4983230072969 + 3 ^ 40 * 4601948 * 2
def baseEnd_4601948 : Nat := 2363011270997066090986033

theorem tailTrace_4601948 : CollatzResearch.WordTrace tailWord_4601948 prefixEnd_4601948 2363011270997066090986033 := by
  unfold tailWord_4601948
  simp only [CollatzResearch.WordTrace]
  refine ⟨83923416365967910495411249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111897888487957213993881665 83923416365967910495411249)
  ·
    refine ⟨62942562274475932871558437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83923416365967910495411249 62942562274475932871558437)
    ·
      refine ⟨11801730426464237413417207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62942562274475932871558437 11801730426464237413417207)
      ·
        refine ⟨17702595639696356120125811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11801730426464237413417207 17702595639696356120125811)
        ·
          refine ⟨26553893459544534180188717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17702595639696356120125811 26553893459544534180188717)
          ·
            refine ⟨9957710047329200317570769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26553893459544534180188717 9957710047329200317570769)
            ·
              refine ⟨7468282535496900238178077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9957710047329200317570769 7468282535496900238178077)
              ·
                refine ⟨2800605950811337589316779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7468282535496900238178077 2800605950811337589316779)
                ·
                  refine ⟨4200908926217006383975169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800605950811337589316779 4200908926217006383975169)
                  ·
                    refine ⟨3150681694662754787981377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4200908926217006383975169 3150681694662754787981377)
                    ·
                      refine ⟨2363011270997066090986033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150681694662754787981377 2363011270997066090986033)
                      ·
                        rfl

theorem cell23_4601948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_4601948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601948 prefixEnd_4601948 := by exact prefixLift 4601948
  have htrace : WordTrace (prefixWord ++ tailWord_4601948) baseStart_4601948 baseEnd_4601948 := by
    simpa [prefixWord, tailWord_4601948, baseEnd_4601948] using wordTrace_append hprefix tailTrace_4601948
  have hstable : (prefixWord ++ tailWord_4601948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601948).length < 2 ^ (prefixWord ++ tailWord_4601948).sum := by decide
  have hdescent : baseEnd_4601948 < baseStart_4601948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601964 : List Nat := [2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 3]
def baseStart_4601964 : Nat := 118140960795 + 4601964 * 2 ^ 59
def prefixEnd_4601964 : Nat := 4983230072969 + 3 ^ 40 * 4601964 * 2
def baseEnd_4601964 : Nat := 2363019486687538028385959

theorem tailTrace_4601964 : CollatzResearch.WordTrace tailWord_4601964 prefixEnd_4601964 2363019486687538028385959 := by
  unfold tailWord_4601964
  simp only [CollatzResearch.WordTrace]
  refine ⟨83923708149938927861702473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111898277533251903815603297 83923708149938927861702473)
  ·
    refine ⟨62942781112454195896276855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83923708149938927861702473 62942781112454195896276855)
    ·
      refine ⟨94414171668681293844415283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62942781112454195896276855 94414171668681293844415283)
      ·
        refine ⟨141621257503021940766622925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94414171668681293844415283 141621257503021940766622925)
        ·
          refine ⟨53107971563633227787483597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141621257503021940766622925 53107971563633227787483597)
          ·
            refine ⟨19915489336362460420306349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53107971563633227787483597 19915489336362460420306349)
            ·
              refine ⟨7468308501135922657614881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19915489336362460420306349 7468308501135922657614881)
              ·
                refine ⟨5601231375851941993211161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7468308501135922657614881 5601231375851941993211161)
                ·
                  refine ⟨4200923531888956494908371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5601231375851941993211161 4200923531888956494908371)
                  ·
                    refine ⟨6301385297833434742362557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200923531888956494908371 6301385297833434742362557)
                    ·
                      refine ⟨2363019486687538028385959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6301385297833434742362557 2363019486687538028385959)
                      ·
                        rfl

theorem cell23_4601964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 3].length) (baseStart_4601964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601964 prefixEnd_4601964 := by exact prefixLift 4601964
  have htrace : WordTrace (prefixWord ++ tailWord_4601964) baseStart_4601964 baseEnd_4601964 := by
    simpa [prefixWord, tailWord_4601964, baseEnd_4601964] using wordTrace_append hprefix tailTrace_4601964
  have hstable : (prefixWord ++ tailWord_4601964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601964).length < 2 ^ (prefixWord ++ tailWord_4601964).sum := by decide
  have hdescent : baseEnd_4601964 < baseStart_4601964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601980 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 2, 6]
def baseStart_4601980 : Nat := 118140960795 + 4601980 * 2 ^ 59
def prefixEnd_4601980 : Nat := 4983230072969 + 3 ^ 40 * 4601980 * 2
def baseEnd_4601980 : Nat := 787675900792669988595295

theorem tailTrace_4601980 : CollatzResearch.WordTrace tailWord_4601980 prefixEnd_4601980 787675900792669988595295 := by
  unfold tailWord_4601980
  simp only [CollatzResearch.WordTrace]
  refine ⟨83923999933909945227993697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111898666578546593637324929 83923999933909945227993697)
  ·
    refine ⟨62942999950432458920995273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83923999933909945227993697 62942999950432458920995273)
    ·
      refine ⟨47207249962824344190746455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62942999950432458920995273 47207249962824344190746455)
      ·
        refine ⟨70810874944236516286119683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47207249962824344190746455 70810874944236516286119683)
        ·
          refine ⟨106216312416354774429179525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70810874944236516286119683 106216312416354774429179525)
          ·
            refine ⟨19915558578066520205471161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106216312416354774429179525 19915558578066520205471161)
            ·
              refine ⟨14936668933549890154103371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19915558578066520205471161 14936668933549890154103371)
              ·
                refine ⟨22405003400324835231155057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14936668933549890154103371 22405003400324835231155057)
                ·
                  refine ⟨16803752550243626423366293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22405003400324835231155057 16803752550243626423366293)
                  ·
                    refine ⟨787675900792669988595295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16803752550243626423366293 787675900792669988595295)
                    ·
                      rfl

theorem cell23_4601980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_4601980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601980 prefixEnd_4601980 := by exact prefixLift 4601980
  have htrace : WordTrace (prefixWord ++ tailWord_4601980) baseStart_4601980 baseEnd_4601980 := by
    simpa [prefixWord, tailWord_4601980, baseEnd_4601980] using wordTrace_append hprefix tailTrace_4601980
  have hstable : (prefixWord ++ tailWord_4601980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601980).length < 2 ^ (prefixWord ++ tailWord_4601980).sum := by decide
  have hdescent : baseEnd_4601980 < baseStart_4601980 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601981 : List Nat := [1, 4, 1, 1, 3, 3, 3, 1, 2, 1, 3]
def baseStart_4601981 : Nat := 118140960795 + 4601981 * 2 ^ 59
def prefixEnd_4601981 : Nat := 4983230072969 + 3 ^ 40 * 4601981 * 2
def baseEnd_4601981 : Nat := 2363028215858664461873381

theorem tailTrace_4601981 : CollatzResearch.WordTrace tailWord_4601981 prefixEnd_4601981 2363028215858664461873381 := by
  unfold tailWord_4601981
  simp only [CollatzResearch.WordTrace]
  refine ⟨167848036340816267626773797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111898690893877511751182531 167848036340816267626773797)
  ·
    refine ⟨31471506813903050180020087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167848036340816267626773797 31471506813903050180020087)
    ·
      refine ⟨47207260220854575270030131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31471506813903050180020087 47207260220854575270030131)
      ·
        refine ⟨70810890331281862905045197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47207260220854575270030131 70810890331281862905045197)
        ·
          refine ⟨26554083874230698589391949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70810890331281862905045197 26554083874230698589391949)
          ·
            refine ⟨9957781452836511971021981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26554083874230698589391949 9957781452836511971021981)
            ·
              refine ⟨3734168044813691989133243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9957781452836511971021981 3734168044813691989133243)
              ·
                refine ⟨5601252067220537983699865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734168044813691989133243 5601252067220537983699865)
                ·
                  refine ⟨4200939050415403487774899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5601252067220537983699865 4200939050415403487774899)
                  ·
                    refine ⟨6301408575623105231662349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4200939050415403487774899 6301408575623105231662349)
                    ·
                      refine ⟨2363028215858664461873381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6301408575623105231662349 2363028215858664461873381)
                      ·
                        rfl

theorem cell23_4601981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 3, 3, 1, 2, 1, 3].length) (baseStart_4601981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601981 prefixEnd_4601981 := by exact prefixLift 4601981
  have htrace : WordTrace (prefixWord ++ tailWord_4601981) baseStart_4601981 baseEnd_4601981 := by
    simpa [prefixWord, tailWord_4601981, baseEnd_4601981] using wordTrace_append hprefix tailTrace_4601981
  have hstable : (prefixWord ++ tailWord_4601981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601981).length < 2 ^ (prefixWord ++ tailWord_4601981).sum := by decide
  have hdescent : baseEnd_4601981 < baseStart_4601981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4601983 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_4601983 : Nat := 118140960795 + 4601983 * 2 ^ 59
def prefixEnd_4601983 : Nat := 4983230072969 + 3 ^ 40 * 4601983 * 2
def baseEnd_4601983 : Nat := 2363029242819973454048371

theorem tailTrace_4601983 : CollatzResearch.WordTrace tailWord_4601983 prefixEnd_4601983 2363029242819973454048371 := by
  unfold tailWord_4601983
  simp only [CollatzResearch.WordTrace]
  refine ⟨167848109286809021968346603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111898739524539347978897735 167848109286809021968346603)
  ·
    refine ⟨251772163930213532952519905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167848109286809021968346603 251772163930213532952519905)
    ·
      refine ⟨188829122947660149714389929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251772163930213532952519905 188829122947660149714389929)
      ·
        refine ⟨141621842210745112285792447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188829122947660149714389929 141621842210745112285792447)
        ·
          refine ⟨212432763316117668428688671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141621842210745112285792447 212432763316117668428688671)
          ·
            refine ⟨318649144974176502643033007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212432763316117668428688671 318649144974176502643033007)
            ·
              refine ⟨477973717461264753964549511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 318649144974176502643033007 477973717461264753964549511)
              ·
                refine ⟨716960576191897130946824267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 477973717461264753964549511 716960576191897130946824267)
                ·
                  refine ⟨1075440864287845696420236401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 716960576191897130946824267 1075440864287845696420236401)
                  ·
                    refine ⟨806580648215884272315177301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1075440864287845696420236401 806580648215884272315177301)
                    ·
                      refine ⟨2363029242819973454048371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 806580648215884272315177301 2363029242819973454048371)
                      ·
                        rfl

theorem cell23_4601983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_4601983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4601983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4601983 prefixEnd_4601983 := by exact prefixLift 4601983
  have htrace : WordTrace (prefixWord ++ tailWord_4601983) baseStart_4601983 baseEnd_4601983 := by
    simpa [prefixWord, tailWord_4601983, baseEnd_4601983] using wordTrace_append hprefix tailTrace_4601983
  have hstable : (prefixWord ++ tailWord_4601983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4601983).length < 2 ^ (prefixWord ++ tailWord_4601983).sum := by decide
  have hdescent : baseEnd_4601983 < baseStart_4601983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4601983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602007 : List Nat := [1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_4602007 : Nat := 118140960795 + 4602007 * 2 ^ 59
def prefixEnd_4602007 : Nat := 4983230072969 + 3 ^ 40 * 4602007 * 2
def baseEnd_4602007 : Nat := 2363041566355681360148261

theorem tailTrace_4602007 : CollatzResearch.WordTrace tailWord_4602007 prefixEnd_4602007 2363041566355681360148261 := by
  unfold tailWord_4602007
  simp only [CollatzResearch.WordTrace]
  refine ⟨167848984638722074067220275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111899323092481382711480183 167848984638722074067220275)
  ·
    refine ⟨251773476958083111100830413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167848984638722074067220275 251773476958083111100830413)
    ·
      refine ⟨94415053859281166662811405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251773476958083111100830413 94415053859281166662811405)
      ·
        refine ⟨35405645197230437498554277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94415053859281166662811405 35405645197230437498554277)
        ·
          refine ⟨6638558474480707030978927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35405645197230437498554277 6638558474480707030978927)
          ·
            refine ⟨9957837711721060546468391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6638558474480707030978927 9957837711721060546468391)
            ·
              refine ⟨14936756567581590819702587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9957837711721060546468391 14936756567581590819702587)
              ·
                refine ⟨22405134851372386229553881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14936756567581590819702587 22405134851372386229553881)
                ·
                  refine ⟨16803851138529289672165411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22405134851372386229553881 16803851138529289672165411)
                  ·
                    refine ⟨25205776707793934508248117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16803851138529289672165411 25205776707793934508248117)
                    ·
                      refine ⟨2363041566355681360148261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25205776707793934508248117 2363041566355681360148261)
                      ·
                        rfl

theorem cell23_4602007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_4602007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602007 prefixEnd_4602007 := by exact prefixLift 4602007
  have htrace : WordTrace (prefixWord ++ tailWord_4602007) baseStart_4602007 baseEnd_4602007 := by
    simpa [prefixWord, tailWord_4602007, baseEnd_4602007] using wordTrace_append hprefix tailTrace_4602007
  have hstable : (prefixWord ++ tailWord_4602007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602007).length < 2 ^ (prefixWord ++ tailWord_4602007).sum := by decide
  have hdescent : baseEnd_4602007 < baseStart_4602007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602040 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 4, 5]
def baseStart_4602040 : Nat := 118140960795 + 4602040 * 2 ^ 59
def prefixEnd_4602040 : Nat := 4983230072969 + 3 ^ 40 * 4602040 * 2
def baseEnd_4602040 : Nat := 787686170405759910345203

theorem tailTrace_4602040 : CollatzResearch.WordTrace tailWord_4602040 prefixEnd_4602040 787686170405759910345203 := by
  unfold tailWord_4602040
  simp only [CollatzResearch.WordTrace]
  refine ⟨83925094123801260351585787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111900125498401680468781049 83925094123801260351585787)
  ·
    refine ⟨125887641185701890527378681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83925094123801260351585787 125887641185701890527378681)
    ·
      refine ⟨94415730889276417895534011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125887641185701890527378681 94415730889276417895534011)
      ·
        refine ⟨141623596333914626843301017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94415730889276417895534011 141623596333914626843301017)
        ·
          refine ⟨106217697250435970132475763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141623596333914626843301017 106217697250435970132475763)
          ·
            refine ⟨159326545875653955198713645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106217697250435970132475763 159326545875653955198713645)
            ·
              refine ⟨59747454703370233199517617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159326545875653955198713645 59747454703370233199517617)
              ·
                refine ⟨44810591027527674899638213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59747454703370233199517617 44810591027527674899638213)
                ·
                  refine ⟨8401985817661439043682165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44810591027527674899638213 8401985817661439043682165)
                  ·
                    refine ⟨787686170405759910345203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8401985817661439043682165 787686170405759910345203)
                    ·
                      rfl

theorem cell23_4602040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 5].length) (baseStart_4602040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602040 prefixEnd_4602040 := by exact prefixLift 4602040
  have htrace : WordTrace (prefixWord ++ tailWord_4602040) baseStart_4602040 baseEnd_4602040 := by
    simpa [prefixWord, tailWord_4602040, baseEnd_4602040] using wordTrace_append hprefix tailTrace_4602040
  have hstable : (prefixWord ++ tailWord_4602040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602040).length < 2 ^ (prefixWord ++ tailWord_4602040).sum := by decide
  have hdescent : baseEnd_4602040 < baseStart_4602040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602080 : List Nat := [2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5]
def baseStart_4602080 : Nat := 118140960795 + 4602080 * 2 ^ 59
def prefixEnd_4602080 : Nat := 4983230072969 + 3 ^ 40 * 4602080 * 2
def baseEnd_4602080 : Nat := 2363079050443459574535425

theorem tailTrace_4602080 : CollatzResearch.WordTrace tailWord_4602080 prefixEnd_4602080 2363079050443459574535425 := by
  unfold tailWord_4602080
  simp only [CollatzResearch.WordTrace]
  refine ⟨83925823583728803767313847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111901098111638405023085129 83925823583728803767313847)
  ·
    refine ⟨125888735375593205650970771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83925823583728803767313847 125888735375593205650970771)
    ·
      refine ⟨188833103063389808476456157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125888735375593205650970771 188833103063389808476456157)
      ·
        refine ⟨70812413648771178178671059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188833103063389808476456157 70812413648771178178671059)
        ·
          refine ⟨106218620473156767268006589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70812413648771178178671059 106218620473156767268006589)
          ·
            refine ⟨39831982677433787725502471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106218620473156767268006589 39831982677433787725502471)
            ·
              refine ⟨59747974016150681588253707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39831982677433787725502471 59747974016150681588253707)
              ·
                refine ⟨89621961024226022382380561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59747974016150681588253707 89621961024226022382380561)
                ·
                  refine ⟨67216470768169516786785421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89621961024226022382380561 67216470768169516786785421)
                  ·
                    refine ⟨25206176538063568795044533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 67216470768169516786785421 25206176538063568795044533)
                    ·
                      refine ⟨2363079050443459574535425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25206176538063568795044533 2363079050443459574535425)
                      ·
                        rfl

theorem cell23_4602080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_4602080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602080 prefixEnd_4602080 := by exact prefixLift 4602080
  have htrace : WordTrace (prefixWord ++ tailWord_4602080) baseStart_4602080 baseEnd_4602080 := by
    simpa [prefixWord, tailWord_4602080, baseEnd_4602080] using wordTrace_append hprefix tailTrace_4602080
  have hstable : (prefixWord ++ tailWord_4602080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602080).length < 2 ^ (prefixWord ++ tailWord_4602080).sum := by decide
  have hdescent : baseEnd_4602080 < baseStart_4602080 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602097 : List Nat := [1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 3]
def baseStart_4602097 : Nat := 118140960795 + 4602097 * 2 ^ 59
def prefixEnd_4602097 : Nat := 4983230072969 + 3 ^ 40 * 4602097 * 2
def baseEnd_4602097 : Nat := 2363087779614586008022847

theorem tailTrace_4602097 : CollatzResearch.WordTrace tailWord_4602097 prefixEnd_4602097 2363087779614586008022847 := by
  unfold tailWord_4602097
  simp only [CollatzResearch.WordTrace]
  refine ⟨167852267208396019437996545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111901511472264012958664363 167852267208396019437996545)
  ·
    refine ⟨125889200406297014578497409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167852267208396019437996545 125889200406297014578497409)
    ·
      refine ⟨94416900304722760933873057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125889200406297014578497409 94416900304722760933873057)
      ·
        refine ⟨70812675228542070700404793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94416900304722760933873057 70812675228542070700404793)
        ·
          refine ⟨53109506421406553025303595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70812675228542070700404793 53109506421406553025303595)
          ·
            refine ⟨79664259632109829537955393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53109506421406553025303595 79664259632109829537955393)
            ·
              refine ⟨59748194724082372153466545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79664259632109829537955393 59748194724082372153466545)
              ·
                refine ⟨44811146043061779115099909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59748194724082372153466545 44811146043061779115099909)
                ·
                  refine ⟨8402089883074083584081233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44811146043061779115099909 8402089883074083584081233)
                  ·
                    refine ⟨6301567412305562688060925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8402089883074083584081233 6301567412305562688060925)
                    ·
                      refine ⟨2363087779614586008022847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6301567412305562688060925 2363087779614586008022847)
                      ·
                        rfl

theorem cell23_4602097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_4602097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602097 prefixEnd_4602097 := by exact prefixLift 4602097
  have htrace : WordTrace (prefixWord ++ tailWord_4602097) baseStart_4602097 baseEnd_4602097 := by
    simpa [prefixWord, tailWord_4602097, baseEnd_4602097] using wordTrace_append hprefix tailTrace_4602097
  have hstable : (prefixWord ++ tailWord_4602097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602097).length < 2 ^ (prefixWord ++ tailWord_4602097).sum := by decide
  have hdescent : baseEnd_4602097 < baseStart_4602097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602121 : List Nat := [1, 2, 1, 1, 3, 5, 2, 3, 1, 4]
def baseStart_4602121 : Nat := 118140960795 + 4602121 * 2 ^ 59
def prefixEnd_4602121 : Nat := 4983230072969 + 3 ^ 40 * 4602121 * 2
def baseEnd_4602121 : Nat := 787700034383431304707579

theorem tailTrace_4602121 : CollatzResearch.WordTrace tailWord_4602121 prefixEnd_4602121 787700034383431304707579 := by
  unfold tailWord_4602121
  simp only [CollatzResearch.WordTrace]
  refine ⟨167853142560309071536870217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111902095040206047691246811 167853142560309071536870217)
  ·
    refine ⟨125889856920231803652652663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167853142560309071536870217 125889856920231803652652663)
    ·
      refine ⟨188834785380347705478978995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125889856920231803652652663 188834785380347705478978995)
      ·
        refine ⟨283252178070521558218468493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188834785380347705478978995 283252178070521558218468493)
        ·
          refine ⟨106219566776445584331925685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283252178070521558218468493 106219566776445584331925685)
          ·
            refine ⟨9958084385291773531118033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106219566776445584331925685 9958084385291773531118033)
            ·
              refine ⟨7468563288968830148338525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9958084385291773531118033 7468563288968830148338525)
              ·
                refine ⟨2800711233363311305626947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7468563288968830148338525 2800711233363311305626947)
                ·
                  refine ⟨4201066850044966958440421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800711233363311305626947 4201066850044966958440421)
                  ·
                    refine ⟨787700034383431304707579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4201066850044966958440421 787700034383431304707579)
                    ·
                      rfl

theorem cell23_4602121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 4].length) (baseStart_4602121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602121 prefixEnd_4602121 := by exact prefixLift 4602121
  have htrace : WordTrace (prefixWord ++ tailWord_4602121) baseStart_4602121 baseEnd_4602121 := by
    simpa [prefixWord, tailWord_4602121, baseEnd_4602121] using wordTrace_append hprefix tailTrace_4602121
  have hstable : (prefixWord ++ tailWord_4602121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602121).length < 2 ^ (prefixWord ++ tailWord_4602121).sum := by decide
  have hdescent : baseEnd_4602121 < baseStart_4602121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602167 : List Nat := [1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_4602167 : Nat := 118140960795 + 4602167 * 2 ^ 59
def prefixEnd_4602167 : Nat := 4983230072969 + 3 ^ 40 * 4602167 * 2
def baseEnd_4602167 : Nat := 2363123723260400734147525

theorem tailTrace_4602167 : CollatzResearch.WordTrace tailWord_4602167 prefixEnd_4602167 2363123723260400734147525 := by
  unfold tailWord_4602167
  simp only [CollatzResearch.WordTrace]
  refine ⟨167854820318142421393044755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111903213545428280928696503 167854820318142421393044755)
  ·
    refine ⟨251782230477213632089567133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167854820318142421393044755 251782230477213632089567133)
    ·
      refine ⟨94418336428955112033587675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251782230477213632089567133 94418336428955112033587675)
      ·
        refine ⟨141627504643432668050381513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94418336428955112033587675 141627504643432668050381513)
        ·
          refine ⟨106220628482574501037786135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141627504643432668050381513 106220628482574501037786135)
          ·
            refine ⟨159330942723861751556679203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106220628482574501037786135 159330942723861751556679203)
            ·
              refine ⟨238996414085792627335018805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159330942723861751556679203 238996414085792627335018805)
              ·
                refine ⟨22405913820543058812658013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 238996414085792627335018805 22405913820543058812658013)
                ·
                  refine ⟨8402217682703647054746755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22405913820543058812658013 8402217682703647054746755)
                  ·
                    refine ⟨12603326524055470582120133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8402217682703647054746755 12603326524055470582120133)
                    ·
                      refine ⟨2363123723260400734147525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12603326524055470582120133 2363123723260400734147525)
                      ·
                        rfl

theorem cell23_4602167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_4602167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602167 prefixEnd_4602167 := by exact prefixLift 4602167
  have htrace : WordTrace (prefixWord ++ tailWord_4602167) baseStart_4602167 baseEnd_4602167 := by
    simpa [prefixWord, tailWord_4602167, baseEnd_4602167] using wordTrace_append hprefix tailTrace_4602167
  have hstable : (prefixWord ++ tailWord_4602167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602167).length < 2 ^ (prefixWord ++ tailWord_4602167).sum := by decide
  have hdescent : baseEnd_4602167 < baseStart_4602167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602184 : List Nat := [2, 1, 3, 1, 1, 2, 4, 3, 1, 1, 4]
def baseStart_4602184 : Nat := 118140960795 + 4602184 * 2 ^ 59
def prefixEnd_4602184 : Nat := 4983230072969 + 3 ^ 40 * 4602184 * 2
def baseEnd_4602184 : Nat := 2363132452431527167634947

theorem tailTrace_4602184 : CollatzResearch.WordTrace tailWord_4602184 prefixEnd_4602184 2363132452431527167634947 := by
  unfold tailWord_4602184
  simp only [CollatzResearch.WordTrace]
  refine ⟨83927720179540416648206803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111903626906053888864275737 83927720179540416648206803)
  ·
    refine ⟨125891580269310624972310205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83927720179540416648206803 125891580269310624972310205)
    ·
      refine ⟨47209342600991484364616327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125891580269310624972310205 47209342600991484364616327)
      ·
        refine ⟨70814013901487226546924491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47209342600991484364616327 70814013901487226546924491)
        ·
          refine ⟨106221020852230839820386737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70814013901487226546924491 106221020852230839820386737)
          ·
            refine ⟨79665765639173129865290053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106221020852230839820386737 79665765639173129865290053)
            ·
              refine ⟨14937331057344961849741885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79665765639173129865290053 14937331057344961849741885)
              ·
                refine ⟨5601499146504360693653207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14937331057344961849741885 5601499146504360693653207)
                ·
                  refine ⟨8402248719756541040479811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5601499146504360693653207 8402248719756541040479811)
                  ·
                    refine ⟨12603373079634811560719717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8402248719756541040479811 12603373079634811560719717)
                    ·
                      refine ⟨2363132452431527167634947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12603373079634811560719717 2363132452431527167634947)
                      ·
                        rfl

theorem cell23_4602184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 3, 1, 1, 4].length) (baseStart_4602184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602184 prefixEnd_4602184 := by exact prefixLift 4602184
  have htrace : WordTrace (prefixWord ++ tailWord_4602184) baseStart_4602184 baseEnd_4602184 := by
    simpa [prefixWord, tailWord_4602184, baseEnd_4602184] using wordTrace_append hprefix tailTrace_4602184
  have hstable : (prefixWord ++ tailWord_4602184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602184).length < 2 ^ (prefixWord ++ tailWord_4602184).sum := by decide
  have hdescent : baseEnd_4602184 < baseStart_4602184 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602194 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 4, 4]
def baseStart_4602194 : Nat := 118140960795 + 4602194 * 2 ^ 59
def prefixEnd_4602194 : Nat := 4983230072969 + 3 ^ 40 * 4602194 * 2
def baseEnd_4602194 : Nat := 787712529079357376169967

theorem tailTrace_4602194 : CollatzResearch.WordTrace tailWord_4602194 prefixEnd_4602194 787712529079357376169967 := by
  unfold tailWord_4602194
  simp only [CollatzResearch.WordTrace]
  refine ⟨41963951272261151251069409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111903870059363070002851757 41963951272261151251069409)
  ·
    refine ⟨31472963454195863438302057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41963951272261151251069409 31472963454195863438302057)
    ·
      refine ⟨23604722590646897578726543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31472963454195863438302057 23604722590646897578726543)
      ·
        refine ⟨35407083885970346368089815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23604722590646897578726543 35407083885970346368089815)
        ·
          refine ⟨53110625828955519552134723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35407083885970346368089815 53110625828955519552134723)
          ·
            refine ⟨79665938743433279328202085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53110625828955519552134723 79665938743433279328202085)
            ·
              refine ⟨14937363514393739874037891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79665938743433279328202085 14937363514393739874037891)
              ·
                refine ⟨22406045271590609811056837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14937363514393739874037891 22406045271590609811056837)
                ·
                  refine ⟨4201133488423239339573157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22406045271590609811056837 4201133488423239339573157)
                  ·
                    refine ⟨787712529079357376169967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4201133488423239339573157 787712529079357376169967)
                    ·
                      rfl

theorem cell23_4602194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_4602194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602194 prefixEnd_4602194 := by exact prefixLift 4602194
  have htrace : WordTrace (prefixWord ++ tailWord_4602194) baseStart_4602194 baseEnd_4602194 := by
    simpa [prefixWord, tailWord_4602194, baseEnd_4602194] using wordTrace_append hprefix tailTrace_4602194
  have hstable : (prefixWord ++ tailWord_4602194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602194).length < 2 ^ (prefixWord ++ tailWord_4602194).sum := by decide
  have hdescent : baseEnd_4602194 < baseStart_4602194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602218 : List Nat := [3, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_4602218 : Nat := 118140960795 + 4602218 * 2 ^ 59
def prefixEnd_4602218 : Nat := 4983230072969 + 3 ^ 40 * 4602218 * 2
def baseEnd_4602218 : Nat := 2363149910773780034609791

theorem tailTrace_4602218 : CollatzResearch.WordTrace tailWord_4602218 prefixEnd_4602218 2363149910773780034609791 := by
  unfold tailWord_4602218
  simp only [CollatzResearch.WordTrace]
  refine ⟨41964170110239414275787827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111904453627305104735434205 41964170110239414275787827)
  ·
    refine ⟨62946255165359121413681741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41964170110239414275787827 62946255165359121413681741)
    ·
      refine ⟨23604845687009670530130653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62946255165359121413681741 23604845687009670530130653)
      ·
        refine ⟨8851817132628626448798995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23604845687009670530130653 8851817132628626448798995)
        ·
          refine ⟨13277725698942939673198493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8851817132628626448798995 13277725698942939673198493)
          ·
            refine ⟨4979147137103602377449435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13277725698942939673198493 4979147137103602377449435)
            ·
              refine ⟨7468720705655403566174153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4979147137103602377449435 7468720705655403566174153)
              ·
                refine ⟨5601540529241552674630615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7468720705655403566174153 5601540529241552674630615)
                ·
                  refine ⟨8402310793862329011945923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5601540529241552674630615 8402310793862329011945923)
                  ·
                    refine ⟨12603466190793493517918885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8402310793862329011945923 12603466190793493517918885)
                    ·
                      refine ⟨2363149910773780034609791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12603466190793493517918885 2363149910773780034609791)
                      ·
                        rfl

theorem cell23_4602218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_4602218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602218 prefixEnd_4602218 := by exact prefixLift 4602218
  have htrace : WordTrace (prefixWord ++ tailWord_4602218) baseStart_4602218 baseEnd_4602218 := by
    simpa [prefixWord, tailWord_4602218, baseEnd_4602218] using wordTrace_append hprefix tailTrace_4602218
  have hstable : (prefixWord ++ tailWord_4602218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602218).length < 2 ^ (prefixWord ++ tailWord_4602218).sum := by decide
  have hdescent : baseEnd_4602218 < baseStart_4602218 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602251 : List Nat := [1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 3]
def baseStart_4602251 : Nat := 118140960795 + 4602251 * 2 ^ 59
def prefixEnd_4602251 : Nat := 4983230072969 + 3 ^ 40 * 4602251 * 2
def baseEnd_4602251 : Nat := 2363166855635378405497139

theorem tailTrace_4602251 : CollatzResearch.WordTrace tailWord_4602251 prefixEnd_4602251 2363166855635378405497139 := by
  unfold tailWord_4602251
  simp only [CollatzResearch.WordTrace]
  refine ⟨167857884049838103739102607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111905256033225402492735071 167857884049838103739102607)
  ·
    refine ⟨251786826074757155608653911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167857884049838103739102607 251786826074757155608653911)
    ·
      refine ⟨377680239112135733412980867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251786826074757155608653911 377680239112135733412980867)
      ·
        refine ⟨566520358668203600119471301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377680239112135733412980867 566520358668203600119471301)
        ·
          refine ⟨106222567250288175022400869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 566520358668203600119471301 106222567250288175022400869)
          ·
            refine ⟨19916731359429032816700163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106222567250288175022400869 19916731359429032816700163)
            ·
              refine ⟨29875097039143549225050245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19916731359429032816700163 29875097039143549225050245)
              ·
                refine ⟨5601580694839415479696921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29875097039143549225050245 5601580694839415479696921)
                ·
                  refine ⟨4201185521129561609772691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5601580694839415479696921 4201185521129561609772691)
                  ·
                    refine ⟨6301778281694342414659037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4201185521129561609772691 6301778281694342414659037)
                    ·
                      refine ⟨2363166855635378405497139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6301778281694342414659037 2363166855635378405497139)
                      ·
                        rfl

theorem cell23_4602251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 4, 2, 1, 3].length) (baseStart_4602251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602251 prefixEnd_4602251 := by exact prefixLift 4602251
  have htrace : WordTrace (prefixWord ++ tailWord_4602251) baseStart_4602251 baseEnd_4602251 := by
    simpa [prefixWord, tailWord_4602251, baseEnd_4602251] using wordTrace_append hprefix tailTrace_4602251
  have hstable : (prefixWord ++ tailWord_4602251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602251).length < 2 ^ (prefixWord ++ tailWord_4602251).sum := by decide
  have hdescent : baseEnd_4602251 < baseStart_4602251 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602252 : List Nat := [2, 2, 1, 2, 1, 6, 2, 2, 1, 2, 2]
def baseStart_4602252 : Nat := 118140960795 + 4602252 * 2 ^ 59
def prefixEnd_4602252 : Nat := 4983230072969 + 3 ^ 40 * 4602252 * 2
def baseEnd_4602252 : Nat := 2363167369116032901584635

theorem tailTrace_4602252 : CollatzResearch.WordTrace tailWord_4602252 prefixEnd_4602252 2363167369116032901584635 := by
  unfold tailWord_4602252
  simp only [CollatzResearch.WordTrace]
  refine ⟨83928960261417240454944505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111905280348556320606592673 83928960261417240454944505)
  ·
    refine ⟨62946720196062930341208379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83928960261417240454944505 62946720196062930341208379)
    ·
      refine ⟨94420080294094395511812569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62946720196062930341208379 94420080294094395511812569)
      ·
        refine ⟨70815060220570796633859427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94420080294094395511812569 70815060220570796633859427)
        ·
          refine ⟨106222590330856194950789141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70815060220570796633859427 106222590330856194950789141)
          ·
            refine ⟨4979183921758884138318241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106222590330856194950789141 4979183921758884138318241)
            ·
              refine ⟨3734387941319163103738681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4979183921758884138318241 3734387941319163103738681)
              ·
                refine ⟨2800790955989372327804011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3734387941319163103738681 2800790955989372327804011)
                ·
                  refine ⟨4201186433984058491706017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800790955989372327804011 4201186433984058491706017)
                  ·
                    refine ⟨3150889825488043868779513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4201186433984058491706017 3150889825488043868779513)
                    ·
                      refine ⟨2363167369116032901584635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150889825488043868779513 2363167369116032901584635)
                      ·
                        rfl

theorem cell23_4602252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_4602252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602252 prefixEnd_4602252 := by exact prefixLift 4602252
  have htrace : WordTrace (prefixWord ++ tailWord_4602252) baseStart_4602252 baseEnd_4602252 := by
    simpa [prefixWord, tailWord_4602252, baseEnd_4602252] using wordTrace_append hprefix tailTrace_4602252
  have hstable : (prefixWord ++ tailWord_4602252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602252).length < 2 ^ (prefixWord ++ tailWord_4602252).sum := by decide
  have hdescent : baseEnd_4602252 < baseStart_4602252 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602254 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 2, 7]
def baseStart_4602254 : Nat := 118140960795 + 4602254 * 2 ^ 59
def prefixEnd_4602254 : Nat := 4983230072969 + 3 ^ 40 * 4602254 * 2
def baseEnd_4602254 : Nat := 787722798692447297919875

theorem tailTrace_4602254 : CollatzResearch.WordTrace tailWord_4602254 prefixEnd_4602254 787722798692447297919875 := by
  unfold tailWord_4602254
  simp only [CollatzResearch.WordTrace]
  refine ⟨20982249183603404406432727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111905328979218156834307877 20982249183603404406432727)
  ·
    refine ⟨31473373775405106609649091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20982249183603404406432727 31473373775405106609649091)
    ·
      refine ⟨47210060663107659914473637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31473373775405106609649091 47210060663107659914473637)
      ·
        refine ⟨8851886374332686233963807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47210060663107659914473637 8851886374332686233963807)
        ·
          refine ⟨13277829561499029350945711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8851886374332686233963807 13277829561499029350945711)
          ·
            refine ⟨19916744342248544026418567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13277829561499029350945711 19916744342248544026418567)
            ·
              refine ⟨29875116513372816039627851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19916744342248544026418567 29875116513372816039627851)
              ·
                refine ⟨44812674770059224059441777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29875116513372816039627851 44812674770059224059441777)
                ·
                  refine ⟨33609506077544418044581333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44812674770059224059441777 33609506077544418044581333)
                  ·
                    refine ⟨787722798692447297919875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33609506077544418044581333 787722798692447297919875)
                    ·
                      rfl

theorem cell23_4602254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_4602254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602254 prefixEnd_4602254 := by exact prefixLift 4602254
  have htrace : WordTrace (prefixWord ++ tailWord_4602254) baseStart_4602254 baseEnd_4602254 := by
    simpa [prefixWord, tailWord_4602254, baseEnd_4602254] using wordTrace_append hprefix tailTrace_4602254
  have hstable : (prefixWord ++ tailWord_4602254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602254).length < 2 ^ (prefixWord ++ tailWord_4602254).sum := by decide
  have hdescent : baseEnd_4602254 < baseStart_4602254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602274 : List Nat := [3, 3, 1, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4602274 : Nat := 118140960795 + 4602274 * 2 ^ 59
def prefixEnd_4602274 : Nat := 4983230072969 + 3 ^ 40 * 4602274 * 2
def baseEnd_4602274 : Nat := 2363178665690431815509533

theorem tailTrace_4602274 : CollatzResearch.WordTrace tailWord_4602274 prefixEnd_4602274 2363178665690431815509533 := by
  unfold tailWord_4602274
  simp only [CollatzResearch.WordTrace]
  refine ⟨41964680732188694666797469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111905815285836519111459917 41964680732188694666797469)
  ·
    refine ⟨15736755274570760500049051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41964680732188694666797469 15736755274570760500049051)
    ·
      refine ⟨23605132911856140750073577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15736755274570760500049051 23605132911856140750073577)
      ·
        refine ⟨17703849683892105562555183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23605132911856140750073577 17703849683892105562555183)
        ·
          refine ⟨26555774525838158343832775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17703849683892105562555183 26555774525838158343832775)
          ·
            refine ⟨39833661788757237515749163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26555774525838158343832775 39833661788757237515749163)
            ·
              refine ⟨59750492683135856273623745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39833661788757237515749163 59750492683135856273623745)
              ·
                refine ⟨44812869512351892205217809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59750492683135856273623745 44812869512351892205217809)
                ·
                  refine ⟨33609652134263919153913357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44812869512351892205217809 33609652134263919153913357)
                  ·
                    refine ⟨12603619550348969682717509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33609652134263919153913357 12603619550348969682717509)
                    ·
                      refine ⟨2363178665690431815509533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12603619550348969682717509 2363178665690431815509533)
                      ·
                        rfl

theorem cell23_4602274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4602274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602274 prefixEnd_4602274 := by exact prefixLift 4602274
  have htrace : WordTrace (prefixWord ++ tailWord_4602274) baseStart_4602274 baseEnd_4602274 := by
    simpa [prefixWord, tailWord_4602274, baseEnd_4602274] using wordTrace_append hprefix tailTrace_4602274
  have hstable : (prefixWord ++ tailWord_4602274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602274).length < 2 ^ (prefixWord ++ tailWord_4602274).sum := by decide
  have hdescent : baseEnd_4602274 < baseStart_4602274 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602295 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 1, 3, 2]
def baseStart_4602295 : Nat := 118140960795 + 4602295 * 2 ^ 59
def prefixEnd_4602295 : Nat := 4983230072969 + 3 ^ 40 * 4602295 * 2
def baseEnd_4602295 : Nat := 2363189448784176233346937

theorem tailTrace_4602295 : CollatzResearch.WordTrace tailWord_4602295 prefixEnd_4602295 2363189448784176233346937 := by
  unfold tailWord_4602295
  simp only [CollatzResearch.WordTrace]
  refine ⟨167859488861678699253704339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111906325907785799502469559 167859488861678699253704339)
  ·
    refine ⟨251789233292518048880556509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167859488861678699253704339 251789233292518048880556509)
    ·
      refine ⟨94420962484694268330208691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251789233292518048880556509 94420962484694268330208691)
      ·
        refine ⟨141631443727041402495313037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94420962484694268330208691 141631443727041402495313037)
        ·
          refine ⟨53111791397640525935742389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141631443727041402495313037 53111791397640525935742389)
          ·
            refine ⟨4979230443528799306475849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 53111791397640525935742389 4979230443528799306475849)
            ·
              refine ⟨3734422832646599479856887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4979230443528799306475849 3734422832646599479856887)
              ·
                refine ⟨5601634248969899219785331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734422832646599479856887 5601634248969899219785331)
                ·
                  refine ⟨8402451373454848829677997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5601634248969899219785331 8402451373454848829677997)
                  ·
                    refine ⟨3150919265045568311129249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8402451373454848829677997 3150919265045568311129249)
                    ·
                      refine ⟨2363189448784176233346937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3150919265045568311129249 2363189448784176233346937)
                      ·
                        rfl

theorem cell23_4602295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_4602295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602295 prefixEnd_4602295 := by exact prefixLift 4602295
  have htrace : WordTrace (prefixWord ++ tailWord_4602295) baseStart_4602295 baseEnd_4602295 := by
    simpa [prefixWord, tailWord_4602295, baseEnd_4602295] using wordTrace_append hprefix tailTrace_4602295
  have hstable : (prefixWord ++ tailWord_4602295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602295).length < 2 ^ (prefixWord ++ tailWord_4602295).sum := by decide
  have hdescent : baseEnd_4602295 < baseStart_4602295 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602314 : List Nat := [3, 1, 2, 1, 2, 2, 4, 1, 7]
def baseStart_4602314 : Nat := 118140960795 + 4602314 * 2 ^ 59
def prefixEnd_4602314 : Nat := 4983230072969 + 3 ^ 40 * 4602314 * 2
def baseEnd_4602314 : Nat := 262577689435179073223261

theorem tailTrace_4602314 : CollatzResearch.WordTrace tailWord_4602314 prefixEnd_4602314 262577689435179073223261 := by
  unfold tailWord_4602314
  simp only [CollatzResearch.WordTrace]
  refine ⟨41965045462152466374661499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111906787899073243665763997 41965045462152466374661499)
  ·
    refine ⟨62947568193228699561992249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41965045462152466374661499 62947568193228699561992249)
    ·
      refine ⟨47210676144921524671494187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62947568193228699561992249 47210676144921524671494187)
      ·
        refine ⟨70816014217382287007241281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47210676144921524671494187 70816014217382287007241281)
        ·
          refine ⟨53112010663036715255430961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70816014217382287007241281 53112010663036715255430961)
          ·
            refine ⟨39834007997277536441573221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53112010663036715255430961 39834007997277536441573221)
            ·
              refine ⟨7468876499489538082794979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39834007997277536441573221 7468876499489538082794979)
              ·
                refine ⟨11203314749234307124192469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7468876499489538082794979 11203314749234307124192469)
                ·
                  refine ⟨262577689435179073223261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11203314749234307124192469 262577689435179073223261)
                  ·
                    rfl

theorem cell23_4602314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 4, 1, 7].length) (baseStart_4602314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602314 prefixEnd_4602314 := by exact prefixLift 4602314
  have htrace : WordTrace (prefixWord ++ tailWord_4602314) baseStart_4602314 baseEnd_4602314 := by
    simpa [prefixWord, tailWord_4602314, baseEnd_4602314] using wordTrace_append hprefix tailTrace_4602314
  have hstable : (prefixWord ++ tailWord_4602314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602314).length < 2 ^ (prefixWord ++ tailWord_4602314).sum := by decide
  have hdescent : baseEnd_4602314 < baseStart_4602314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602344 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 1, 7]
def baseStart_4602344 : Nat := 118140960795 + 4602344 * 2 ^ 59
def prefixEnd_4602344 : Nat := 4983230072969 + 3 ^ 40 * 4602344 * 2
def baseEnd_4602344 : Nat := 787738203112082180544737

theorem tailTrace_4602344 : CollatzResearch.WordTrace tailWord_4602344 prefixEnd_4602344 787738203112082180544737 := by
  unfold tailWord_4602344
  simp only [CollatzResearch.WordTrace]
  refine ⟨83930638019250590311119043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111907517359000787081492057 83930638019250590311119043)
  ·
    refine ⟨125895957028875885466678565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83930638019250590311119043 125895957028875885466678565)
    ·
      refine ⟨23605491942914228525002231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125895957028875885466678565 23605491942914228525002231)
      ·
        refine ⟨35408237914371342787503347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23605491942914228525002231 35408237914371342787503347)
        ·
          refine ⟨53112356871557014181255021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35408237914371342787503347 53112356871557014181255021)
          ·
            refine ⟨19917133826833880317970633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53112356871557014181255021 19917133826833880317970633)
            ·
              refine ⟨14937850370125410238477975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19917133826833880317970633 14937850370125410238477975)
              ·
                refine ⟨22406775555188115357716963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14937850370125410238477975 22406775555188115357716963)
                ·
                  refine ⟨33610163332782173036575445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22406775555188115357716963 33610163332782173036575445)
                  ·
                    refine ⟨787738203112082180544737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33610163332782173036575445 787738203112082180544737)
                    ·
                      rfl

theorem cell23_4602344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_4602344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602344 prefixEnd_4602344 := by exact prefixLift 4602344
  have htrace : WordTrace (prefixWord ++ tailWord_4602344) baseStart_4602344 baseEnd_4602344 := by
    simpa [prefixWord, tailWord_4602344, baseEnd_4602344] using wordTrace_append hprefix tailTrace_4602344
  have hstable : (prefixWord ++ tailWord_4602344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602344).length < 2 ^ (prefixWord ++ tailWord_4602344).sum := by decide
  have hdescent : baseEnd_4602344 < baseStart_4602344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602394 : List Nat := [3, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_4602394 : Nat := 118140960795 + 4602394 * 2 ^ 59
def prefixEnd_4602394 : Nat := 4983230072969 + 3 ^ 40 * 4602394 * 2
def baseEnd_4602394 : Nat := 2363240283368971346008981

theorem tailTrace_4602394 : CollatzResearch.WordTrace tailWord_4602394 prefixEnd_4602394 2363240283368971346008981 := by
  unfold tailWord_4602394
  simp only [CollatzResearch.WordTrace]
  refine ⟨41965774922080009790389559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111908733125546692774372157 41965774922080009790389559)
  ·
    refine ⟨62948662383120014685584339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41965774922080009790389559 62948662383120014685584339)
    ·
      refine ⟨94422993574680022028376509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62948662383120014685584339 94422993574680022028376509)
      ·
        refine ⟨35408622590505008260641191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94422993574680022028376509 35408622590505008260641191)
        ·
          refine ⟨53112933885757512390961787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35408622590505008260641191 53112933885757512390961787)
          ·
            refine ⟨79669400828636268586442681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53112933885757512390961787 79669400828636268586442681)
            ·
              refine ⟨59752050621477201439832011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79669400828636268586442681 59752050621477201439832011)
              ·
                refine ⟨89628075932215802159748017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59752050621477201439832011 89628075932215802159748017)
                ·
                  refine ⟨67221056949161851619811013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89628075932215802159748017 67221056949161851619811013)
                  ·
                    refine ⟨12603948177967847178714565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 67221056949161851619811013 12603948177967847178714565)
                    ·
                      refine ⟨2363240283368971346008981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12603948177967847178714565 2363240283368971346008981)
                      ·
                        rfl

theorem cell23_4602394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_4602394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602394 prefixEnd_4602394 := by exact prefixLift 4602394
  have htrace : WordTrace (prefixWord ++ tailWord_4602394) baseStart_4602394 baseEnd_4602394 := by
    simpa [prefixWord, tailWord_4602394, baseEnd_4602394] using wordTrace_append hprefix tailTrace_4602394
  have hstable : (prefixWord ++ tailWord_4602394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602394).length < 2 ^ (prefixWord ++ tailWord_4602394).sum := by decide
  have hdescent : baseEnd_4602394 < baseStart_4602394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602421 : List Nat := [1, 3, 3, 1, 1, 2, 4, 2, 6]
def baseStart_4602421 : Nat := 118140960795 + 4602421 * 2 ^ 59
def prefixEnd_4602421 : Nat := 4983230072969 + 3 ^ 40 * 4602421 * 2
def baseEnd_4602421 : Nat := 262583794149626971152373

theorem tailTrace_4602421 : CollatzResearch.WordTrace tailWord_4602421 prefixEnd_4602421 262583794149626971152373 := by
  unfold tailWord_4602421
  simp only [CollatzResearch.WordTrace]
  refine ⟨167864084459222222772791117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111909389639481481848527411 167864084459222222772791117)
  ·
    refine ⟨62949031672208333539796669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167864084459222222772791117 62949031672208333539796669)
    ·
      refine ⟨23605886877078125077423751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62949031672208333539796669 23605886877078125077423751)
      ·
        refine ⟨35408830315617187616135627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23605886877078125077423751 35408830315617187616135627)
        ·
          refine ⟨53113245473425781424203441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35408830315617187616135627 53113245473425781424203441)
          ·
            refine ⟨39834934105069336068152581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53113245473425781424203441 39834934105069336068152581)
            ·
              refine ⟨7469050144700500512778609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39834934105069336068152581 7469050144700500512778609)
              ·
                refine ⟨5601787608525375384583957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7469050144700500512778609 5601787608525375384583957)
                ·
                  refine ⟨262583794149626971152373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5601787608525375384583957 262583794149626971152373)
                  ·
                    rfl

theorem cell23_4602421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 4, 2, 6].length) (baseStart_4602421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602421 prefixEnd_4602421 := by exact prefixLift 4602421
  have htrace : WordTrace (prefixWord ++ tailWord_4602421) baseStart_4602421 baseEnd_4602421 := by
    simpa [prefixWord, tailWord_4602421, baseEnd_4602421] using wordTrace_append hprefix tailTrace_4602421
  have hstable : (prefixWord ++ tailWord_4602421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602421).length < 2 ^ (prefixWord ++ tailWord_4602421).sum := by decide
  have hdescent : baseEnd_4602421 < baseStart_4602421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602424 : List Nat := [2, 1, 2, 1, 4, 1, 2, 1, 1, 2, 6]
def baseStart_4602424 : Nat := 118140960795 + 4602424 * 2 ^ 59
def prefixEnd_4602424 : Nat := 4983230072969 + 3 ^ 40 * 4602424 * 2
def baseEnd_4602424 : Nat := 2363255687788606228633843

theorem tailTrace_4602424 : CollatzResearch.WordTrace tailWord_4602424 prefixEnd_4602424 2363255687788606228633843 := by
  unfold tailWord_4602424
  simp only [CollatzResearch.WordTrace]
  refine ⟨83932096939105677142575163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111909462585474236190100217 83932096939105677142575163)
  ·
    refine ⟨125898145408658515713862745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83932096939105677142575163 125898145408658515713862745)
    ·
      refine ⟨94423609056493886785397059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125898145408658515713862745 94423609056493886785397059)
      ·
        refine ⟨141635413584740830178095589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94423609056493886785397059 141635413584740830178095589)
        ·
          refine ⟨26556640047138905658392923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141635413584740830178095589 26556640047138905658392923)
          ·
            refine ⟨39834960070708358487589385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26556640047138905658392923 39834960070708358487589385)
            ·
              refine ⟨29876220053031268865692039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39834960070708358487589385 29876220053031268865692039)
              ·
                refine ⟨44814330079546903298538059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29876220053031268865692039 44814330079546903298538059)
                ·
                  refine ⟨67221495119320354947807089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44814330079546903298538059 67221495119320354947807089)
                  ·
                    refine ⟨50416121339490266210855317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67221495119320354947807089 50416121339490266210855317)
                    ·
                      refine ⟨2363255687788606228633843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50416121339490266210855317 2363255687788606228633843)
                      ·
                        rfl

theorem cell23_4602424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 1, 1, 2, 6].length) (baseStart_4602424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602424 prefixEnd_4602424 := by exact prefixLift 4602424
  have htrace : WordTrace (prefixWord ++ tailWord_4602424) baseStart_4602424 baseEnd_4602424 := by
    simpa [prefixWord, tailWord_4602424, baseEnd_4602424] using wordTrace_append hprefix tailTrace_4602424
  have hstable : (prefixWord ++ tailWord_4602424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602424).length < 2 ^ (prefixWord ++ tailWord_4602424).sum := by decide
  have hdescent : baseEnd_4602424 < baseStart_4602424 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602444 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4602444 : Nat := 118140960795 + 4602444 * 2 ^ 59
def prefixEnd_4602444 : Nat := 4983230072969 + 3 ^ 40 * 4602444 * 2
def baseEnd_4602444 : Nat := 2363265957401696150383751

theorem tailTrace_4602444 : CollatzResearch.WordTrace tailWord_4602444 prefixEnd_4602444 2363265957401696150383751 := by
  unfold tailWord_4602444
  simp only [CollatzResearch.WordTrace]
  refine ⟨83932461669069448850439193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111909948892092598467252257 83932461669069448850439193)
  ·
    refine ⟨62949346251802086637829395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83932461669069448850439193 62949346251802086637829395)
    ·
      refine ⟨94424019377703129956744093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62949346251802086637829395 94424019377703129956744093)
      ·
        refine ⟨35409007266638673733779035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94424019377703129956744093 35409007266638673733779035)
        ·
          refine ⟨53113510899958010600668553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35409007266638673733779035 53113510899958010600668553)
          ·
            refine ⟨39835133174968507950501415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53113510899958010600668553 39835133174968507950501415)
            ·
              refine ⟨59752699762452761925752123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39835133174968507950501415 59752699762452761925752123)
              ·
                refine ⟨89629049643679142888628185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59752699762452761925752123 89629049643679142888628185)
                ·
                  refine ⟨67221787232759357166471139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89629049643679142888628185 67221787232759357166471139)
                  ·
                    refine ⟨100832680849139035749706709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67221787232759357166471139 100832680849139035749706709)
                    ·
                      refine ⟨2363265957401696150383751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100832680849139035749706709 2363265957401696150383751)
                      ·
                        rfl

theorem cell23_4602444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4602444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602444 prefixEnd_4602444 := by exact prefixLift 4602444
  have htrace : WordTrace (prefixWord ++ tailWord_4602444) baseStart_4602444 baseEnd_4602444 := by
    simpa [prefixWord, tailWord_4602444, baseEnd_4602444] using wordTrace_append hprefix tailTrace_4602444
  have hstable : (prefixWord ++ tailWord_4602444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602444).length < 2 ^ (prefixWord ++ tailWord_4602444).sum := by decide
  have hdescent : baseEnd_4602444 < baseStart_4602444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602465 : List Nat := [1, 2, 3, 1, 1, 4, 1, 5, 1, 1, 3]
def baseStart_4602465 : Nat := 118140960795 + 4602465 * 2 ^ 59
def prefixEnd_4602465 : Nat := 4983230072969 + 3 ^ 40 * 4602465 * 2
def baseEnd_4602465 : Nat := 2363276740495440568221155

theorem tailTrace_4602465 : CollatzResearch.WordTrace tailWord_4602465 prefixEnd_4602465 2363276740495440568221155 := by
  unfold tailWord_4602465
  simp only [CollatzResearch.WordTrace]
  refine ⟨167865689271062818287392849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111910459514041878858261899 167865689271062818287392849)
  ·
    refine ⟨125899266953297113715544637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167865689271062818287392849 125899266953297113715544637)
    ·
      refine ⟨47212225107486417643329239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125899266953297113715544637 47212225107486417643329239)
      ·
        refine ⟨70818337661229626464993859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47212225107486417643329239 70818337661229626464993859)
        ·
          refine ⟨106227506491844439697490789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70818337661229626464993859 106227506491844439697490789)
          ·
            refine ⟨19917657467220832443279523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106227506491844439697490789 19917657467220832443279523)
            ·
              refine ⟨29876486200831248664919285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19917657467220832443279523 29876486200831248664919285)
              ·
                refine ⟨2800920581327929562336183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29876486200831248664919285 2800920581327929562336183)
                ·
                  refine ⟨4201380871991894343504275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2800920581327929562336183 4201380871991894343504275)
                  ·
                    refine ⟨6302071307987841515256413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4201380871991894343504275 6302071307987841515256413)
                    ·
                      refine ⟨2363276740495440568221155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302071307987841515256413 2363276740495440568221155)
                      ·
                        rfl

theorem cell23_4602465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 5, 1, 1, 3].length) (baseStart_4602465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602465 prefixEnd_4602465 := by exact prefixLift 4602465
  have htrace : WordTrace (prefixWord ++ tailWord_4602465) baseStart_4602465 baseEnd_4602465 := by
    simpa [prefixWord, tailWord_4602465, baseEnd_4602465] using wordTrace_append hprefix tailTrace_4602465
  have hstable : (prefixWord ++ tailWord_4602465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602465).length < 2 ^ (prefixWord ++ tailWord_4602465).sum := by decide
  have hdescent : baseEnd_4602465 < baseStart_4602465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602488 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 7, 2, 2]
def baseStart_4602488 : Nat := 118140960795 + 4602488 * 2 ^ 59
def prefixEnd_4602488 : Nat := 4983230072969 + 3 ^ 40 * 4602488 * 2
def baseEnd_4602488 : Nat := 2363288550550493978233549

theorem tailTrace_4602488 : CollatzResearch.WordTrace tailWord_4602488 prefixEnd_4602488 2363288550550493978233549 := by
  unfold tailWord_4602488
  simp only [CollatzResearch.WordTrace]
  refine ⟨83933264074989746607740059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111911018766652995476986745 83933264074989746607740059)
  ·
    refine ⟨125899896112484619911610089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83933264074989746607740059 125899896112484619911610089)
    ·
      refine ⟨94424922084363464933707567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125899896112484619911610089 94424922084363464933707567)
      ·
        refine ⟨141637383126545197400561351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94424922084363464933707567 141637383126545197400561351)
        ·
          refine ⟨212456074689817796100842027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141637383126545197400561351 212456074689817796100842027)
          ·
            refine ⟨318684112034726694151263041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212456074689817796100842027 318684112034726694151263041)
            ·
              refine ⟨239013084026045020613447281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 318684112034726694151263041 239013084026045020613447281)
              ·
                refine ⟨179259813019533765460085461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239013084026045020613447281 179259813019533765460085461)
                ·
                  refine ⟨4201401867645322627970753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 179259813019533765460085461 4201401867645322627970753)
                  ·
                    refine ⟨3151051400733991970978065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4201401867645322627970753 3151051400733991970978065)
                    ·
                      refine ⟨2363288550550493978233549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3151051400733991970978065 2363288550550493978233549)
                      ·
                        rfl

theorem cell23_4602488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 7, 2, 2].length) (baseStart_4602488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602488 prefixEnd_4602488 := by exact prefixLift 4602488
  have htrace : WordTrace (prefixWord ++ tailWord_4602488) baseStart_4602488 baseEnd_4602488 := by
    simpa [prefixWord, tailWord_4602488, baseEnd_4602488] using wordTrace_append hprefix tailTrace_4602488
  have hstable : (prefixWord ++ tailWord_4602488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602488).length < 2 ^ (prefixWord ++ tailWord_4602488).sum := by decide
  have hdescent : baseEnd_4602488 < baseStart_4602488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602491 : List Nat := [1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 3]
def baseStart_4602491 : Nat := 118140960795 + 4602491 * 2 ^ 59
def prefixEnd_4602491 : Nat := 4983230072969 + 3 ^ 40 * 4602491 * 2
def baseEnd_4602491 : Nat := 2363290090992457466496035

theorem tailTrace_4602491 : CollatzResearch.WordTrace tailWord_4602491 prefixEnd_4602491 2363290090992457466496035 := by
  unfold tailWord_4602491
  simp only [CollatzResearch.WordTrace]
  refine ⟨167866637568968624727839327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111911091712645749818559551 167866637568968624727839327)
  ·
    refine ⟨251799956353452937091758991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167866637568968624727839327 251799956353452937091758991)
    ·
      refine ⟨377699934530179405637638487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251799956353452937091758991 377699934530179405637638487)
      ·
        refine ⟨566549901795269108456457731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377699934530179405637638487 566549901795269108456457731)
        ·
          refine ⟨849824852692903662684686597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566549901795269108456457731 849824852692903662684686597)
          ·
            refine ⟨159342159879919436753378737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 849824852692903662684686597 159342159879919436753378737)
            ·
              refine ⟨119506619909939577565034053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159342159879919436753378737 119506619909939577565034053)
              ·
                refine ⟨22407491233113670793443885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 119506619909939577565034053 22407491233113670793443885)
                ·
                  refine ⟨8402809212417626547541457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22407491233113670793443885 8402809212417626547541457)
                  ·
                    refine ⟨6302106909313219910656093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8402809212417626547541457 6302106909313219910656093)
                    ·
                      refine ⟨2363290090992457466496035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302106909313219910656093 2363290090992457466496035)
                      ·
                        rfl

theorem cell23_4602491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 4, 3, 2, 3].length) (baseStart_4602491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602491 prefixEnd_4602491 := by exact prefixLift 4602491
  have htrace : WordTrace (prefixWord ++ tailWord_4602491) baseStart_4602491 baseEnd_4602491 := by
    simpa [prefixWord, tailWord_4602491, baseEnd_4602491] using wordTrace_append hprefix tailTrace_4602491
  have hstable : (prefixWord ++ tailWord_4602491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602491).length < 2 ^ (prefixWord ++ tailWord_4602491).sum := by decide
  have hdescent : baseEnd_4602491 < baseStart_4602491 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602501 : List Nat := [1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 6]
def baseStart_4602501 : Nat := 118140960795 + 4602501 * 2 ^ 59
def prefixEnd_4602501 : Nat := 4983230072969 + 3 ^ 40 * 4602501 * 2
def baseEnd_4602501 : Nat := 2363295225799002427370989

theorem tailTrace_4602501 : CollatzResearch.WordTrace tailWord_4602501 prefixEnd_4602501 2363295225799002427370989 := by
  unfold tailWord_4602501
  simp only [CollatzResearch.WordTrace]
  refine ⟨167867002298932396435703357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111911334865954930957135571 167867002298932396435703357)
  ·
    refine ⟨62950125862099648663388759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167867002298932396435703357 62950125862099648663388759)
    ·
      refine ⟨94425188793149472995083139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62950125862099648663388759 94425188793149472995083139)
      ·
        refine ⟨141637783189724209492624709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94425188793149472995083139 141637783189724209492624709)
        ·
          refine ⟨26557084348073289279867133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141637783189724209492624709 26557084348073289279867133)
          ·
            refine ⟨9958906630527483479950175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26557084348073289279867133 9958906630527483479950175)
            ·
              refine ⟨14938359945791225219925263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9958906630527483479950175 14938359945791225219925263)
              ·
                refine ⟨22407539918686837829887895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14938359945791225219925263 22407539918686837829887895)
                ·
                  refine ⟨33611309878030256744831843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22407539918686837829887895 33611309878030256744831843)
                  ·
                    refine ⟨50416964817045385117247765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33611309878030256744831843 50416964817045385117247765)
                    ·
                      refine ⟨2363295225799002427370989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50416964817045385117247765 2363295225799002427370989)
                      ·
                        rfl

theorem cell23_4602501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 1, 6].length) (baseStart_4602501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602501 prefixEnd_4602501 := by exact prefixLift 4602501
  have htrace : WordTrace (prefixWord ++ tailWord_4602501) baseStart_4602501 baseEnd_4602501 := by
    simpa [prefixWord, tailWord_4602501, baseEnd_4602501] using wordTrace_append hprefix tailTrace_4602501
  have hstable : (prefixWord ++ tailWord_4602501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602501).length < 2 ^ (prefixWord ++ tailWord_4602501).sum := by decide
  have hdescent : baseEnd_4602501 < baseStart_4602501 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602521 : List Nat := [1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 3]
def baseStart_4602521 : Nat := 118140960795 + 4602521 * 2 ^ 59
def prefixEnd_4602521 : Nat := 4983230072969 + 3 ^ 40 * 4602521 * 2
def baseEnd_4602521 : Nat := 2363305495412092349120897

theorem tailTrace_4602521 : CollatzResearch.WordTrace tailWord_4602521 prefixEnd_4602521 2363305495412092349120897 := by
  unfold tailWord_4602521
  simp only [CollatzResearch.WordTrace]
  refine ⟨167867731758859939851431417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111911821172573293234287611 167867731758859939851431417)
  ·
    refine ⟨125900798819144954888573563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167867731758859939851431417 125900798819144954888573563)
    ·
      refine ⟨188851198228717432332860345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125900798819144954888573563 188851198228717432332860345)
      ·
        refine ⟨141638398671538074249645259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188851198228717432332860345 141638398671538074249645259)
        ·
          refine ⟨212457598007307111374467889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141638398671538074249645259 212457598007307111374467889)
          ·
            refine ⟨159343198505480333530850917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212457598007307111374467889 159343198505480333530850917)
            ·
              refine ⟨29876849719777562537034547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159343198505480333530850917 29876849719777562537034547)
              ·
                refine ⟨44815274579666343805551821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29876849719777562537034547 44815274579666343805551821)
                ·
                  refine ⟨16805727967374878927081933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44815274579666343805551821 16805727967374878927081933)
                  ·
                    refine ⟨6302147987765579597655725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16805727967374878927081933 6302147987765579597655725)
                    ·
                      refine ⟨2363305495412092349120897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302147987765579597655725 2363305495412092349120897)
                      ·
                        rfl

theorem cell23_4602521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 1, 3, 3, 3].length) (baseStart_4602521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602521 prefixEnd_4602521 := by exact prefixLift 4602521
  have htrace : WordTrace (prefixWord ++ tailWord_4602521) baseStart_4602521 baseEnd_4602521 := by
    simpa [prefixWord, tailWord_4602521, baseEnd_4602521] using wordTrace_append hprefix tailTrace_4602521
  have hstable : (prefixWord ++ tailWord_4602521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602521).length < 2 ^ (prefixWord ++ tailWord_4602521).sum := by decide
  have hdescent : baseEnd_4602521 < baseStart_4602521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602528 : List Nat := [2, 1, 1, 4, 5, 1, 9]
def baseStart_4602528 : Nat := 118140960795 + 4602528 * 2 ^ 59
def prefixEnd_4602528 : Nat := 4983230072969 + 3 ^ 40 * 4602528 * 2
def baseEnd_4602528 : Nat := 29176655429341652120165

theorem tailTrace_4602528 : CollatzResearch.WordTrace tailWord_4602528 prefixEnd_4602528 29176655429341652120165 := by
  unfold tailWord_4602528
  simp only [CollatzResearch.WordTrace]
  refine ⟨83933993534917290023468119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111911991379889720031290825 83933993534917290023468119)
  ·
    refine ⟨125900990302375935035202179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83933993534917290023468119 125900990302375935035202179)
    ·
      refine ⟨188851485453563902552803269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125900990302375935035202179 188851485453563902552803269)
      ·
        refine ⟨35409653522543231728650613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188851485453563902552803269 35409653522543231728650613)
        ·
          refine ⟨3319655017738427974560995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35409653522543231728650613 3319655017738427974560995)
          ·
            refine ⟨4979482526607641961841493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3319655017738427974560995 4979482526607641961841493)
            ·
              refine ⟨29176655429341652120165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4979482526607641961841493 29176655429341652120165)
              ·
                rfl

theorem cell23_4602528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 5, 1, 9].length) (baseStart_4602528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602528 prefixEnd_4602528 := by exact prefixLift 4602528
  have htrace : WordTrace (prefixWord ++ tailWord_4602528) baseStart_4602528 baseEnd_4602528 := by
    simpa [prefixWord, tailWord_4602528, baseEnd_4602528] using wordTrace_append hprefix tailTrace_4602528
  have hstable : (prefixWord ++ tailWord_4602528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602528).length < 2 ^ (prefixWord ++ tailWord_4602528).sum := by decide
  have hdescent : baseEnd_4602528 < baseStart_4602528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602628 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4602628 : Nat := 118140960795 + 4602628 * 2 ^ 59
def prefixEnd_4602628 : Nat := 4983230072969 + 3 ^ 40 * 4602628 * 2
def baseEnd_4602628 : Nat := 2363360437842123430482905

theorem tailTrace_4602628 : CollatzResearch.WordTrace tailWord_4602628 prefixEnd_4602628 2363360437842123430482905 := by
  unfold tailWord_4602628
  simp only [CollatzResearch.WordTrace]
  refine ⟨83935817184736148562788269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111914422912981531417051025 83935817184736148562788269)
  ·
    refine ⟨31475931444276055711045601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83935817184736148562788269 31475931444276055711045601)
    ·
      refine ⟨23606948583207041783284201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31475931444276055711045601 23606948583207041783284201)
      ·
        refine ⟨17705211437405281337463151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23606948583207041783284201 17705211437405281337463151)
        ·
          refine ⟨26557817156107922006194727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17705211437405281337463151 26557817156107922006194727)
          ·
            refine ⟨39836725734161883009292091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26557817156107922006194727 39836725734161883009292091)
            ·
              refine ⟨59755088601242824513938137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39836725734161883009292091 59755088601242824513938137)
              ·
                refine ⟨44816316450932118385453603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59755088601242824513938137 44816316450932118385453603)
                ·
                  refine ⟨67224474676398177578180405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44816316450932118385453603 67224474676398177578180405)
                  ·
                    refine ⟨6302294500912329147954413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67224474676398177578180405 6302294500912329147954413)
                    ·
                      refine ⟨2363360437842123430482905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302294500912329147954413 2363360437842123430482905)
                      ·
                        rfl

theorem cell23_4602628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4602628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602628 prefixEnd_4602628 := by exact prefixLift 4602628
  have htrace : WordTrace (prefixWord ++ tailWord_4602628) baseStart_4602628 baseEnd_4602628 := by
    simpa [prefixWord, tailWord_4602628, baseEnd_4602628] using wordTrace_append hprefix tailTrace_4602628
  have hstable : (prefixWord ++ tailWord_4602628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602628).length < 2 ^ (prefixWord ++ tailWord_4602628).sum := by decide
  have hdescent : baseEnd_4602628 < baseStart_4602628 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602641 : List Nat := [1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 5]
def baseStart_4602641 : Nat := 118140960795 + 4602641 * 2 ^ 59
def prefixEnd_4602641 : Nat := 4983230072969 + 3 ^ 40 * 4602641 * 2
def baseEnd_4602641 : Nat := 2363367113090631879620345

theorem tailTrace_4602641 : CollatzResearch.WordTrace tailWord_4602641 prefixEnd_4602641 2363367113090631879620345 := by
  unfold tailWord_4602641
  simp only [CollatzResearch.WordTrace]
  refine ⟨167872108518425200345799777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111914739012283466897199851 167872108518425200345799777)
  ·
    refine ⟨125904081388818900259349833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167872108518425200345799777 125904081388818900259349833)
    ·
      refine ⟨94428061041614175194512375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125904081388818900259349833 94428061041614175194512375)
      ·
        refine ⟨141642091562421262791768563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94428061041614175194512375 141642091562421262791768563)
        ·
          refine ⟨212463137343631894187652845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141642091562421262791768563 212463137343631894187652845)
          ·
            refine ⟨79673676503861960320369817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212463137343631894187652845 79673676503861960320369817)
            ·
              refine ⟨59755257377896470240277363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79673676503861960320369817 59755257377896470240277363)
              ·
                refine ⟨89632886066844705360416045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59755257377896470240277363 89632886066844705360416045)
                ·
                  refine ⟨33612332275066764510156017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89632886066844705360416045 33612332275066764510156017)
                  ·
                    refine ⟨25209249206300073382617013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33612332275066764510156017 25209249206300073382617013)
                    ·
                      refine ⟨2363367113090631879620345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25209249206300073382617013 2363367113090631879620345)
                      ·
                        rfl

theorem cell23_4602641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_4602641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602641 prefixEnd_4602641 := by exact prefixLift 4602641
  have htrace : WordTrace (prefixWord ++ tailWord_4602641) baseStart_4602641 baseEnd_4602641 := by
    simpa [prefixWord, tailWord_4602641, baseEnd_4602641] using wordTrace_append hprefix tailTrace_4602641
  have hstable : (prefixWord ++ tailWord_4602641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602641).length < 2 ^ (prefixWord ++ tailWord_4602641).sum := by decide
  have hdescent : baseEnd_4602641 < baseStart_4602641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602651 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4]
def baseStart_4602651 : Nat := 118140960795 + 4602651 * 2 ^ 59
def prefixEnd_4602651 : Nat := 4983230072969 + 3 ^ 40 * 4602651 * 2
def baseEnd_4602651 : Nat := 2363372247897176840495299

theorem tailTrace_4602651 : CollatzResearch.WordTrace tailWord_4602651 prefixEnd_4602651 2363372247897176840495299 := by
  unfold tailWord_4602651
  simp only [CollatzResearch.WordTrace]
  refine ⟨167872473248388972053663807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111914982165592648035775871 167872473248388972053663807)
  ·
    refine ⟨251808709872583458080495711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167872473248388972053663807 251808709872583458080495711)
    ·
      refine ⟨377713064808875187120743567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251808709872583458080495711 377713064808875187120743567)
      ·
        refine ⟨566569597213312780681115351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377713064808875187120743567 566569597213312780681115351)
        ·
          refine ⟨849854395819969171021673027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566569597213312780681115351 849854395819969171021673027)
          ·
            refine ⟨1274781593729953756532509541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 849854395819969171021673027 1274781593729953756532509541)
            ·
              refine ⟨239021548824366329349845539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1274781593729953756532509541 239021548824366329349845539)
              ·
                refine ⟨358532323236549494024768309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239021548824366329349845539 358532323236549494024768309)
                ·
                  refine ⟨33612405303426515064822029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 358532323236549494024768309 33612405303426515064822029)
                  ·
                    refine ⟨12604651988784943149308261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33612405303426515064822029 12604651988784943149308261)
                    ·
                      refine ⟨2363372247897176840495299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12604651988784943149308261 2363372247897176840495299)
                      ·
                        rfl

theorem cell23_4602651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 5, 3, 4].length) (baseStart_4602651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602651 prefixEnd_4602651 := by exact prefixLift 4602651
  have htrace : WordTrace (prefixWord ++ tailWord_4602651) baseStart_4602651 baseEnd_4602651 := by
    simpa [prefixWord, tailWord_4602651, baseEnd_4602651] using wordTrace_append hprefix tailTrace_4602651
  have hstable : (prefixWord ++ tailWord_4602651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602651).length < 2 ^ (prefixWord ++ tailWord_4602651).sum := by decide
  have hdescent : baseEnd_4602651 < baseStart_4602651 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602688 : List Nat := [2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3]
def baseStart_4602688 : Nat := 118140960795 + 4602688 * 2 ^ 59
def prefixEnd_4602688 : Nat := 4983230072969 + 3 ^ 40 * 4602688 * 2
def baseEnd_4602688 : Nat := 2363391246681393195732629

theorem tailTrace_4602688 : CollatzResearch.WordTrace tailWord_4602688 prefixEnd_4602688 2363391246681393195732629 := by
  unfold tailWord_4602688
  simp only [CollatzResearch.WordTrace]
  refine ⟨83936911374627463686380359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111915881832836618248507145 83936911374627463686380359)
  ·
    refine ⟨125905367061941195529570539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83936911374627463686380359 125905367061941195529570539)
    ·
      refine ⟨188858050592911793294355809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125905367061941195529570539 188858050592911793294355809)
      ·
        refine ⟨141643537944683844970766857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188858050592911793294355809 141643537944683844970766857)
        ·
          refine ⟨106232653458512883728075143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141643537944683844970766857 106232653458512883728075143)
          ·
            refine ⟨159348980187769325592112715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106232653458512883728075143 159348980187769325592112715)
            ·
              refine ⟨239023470281653988388169073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159348980187769325592112715 239023470281653988388169073)
              ·
                refine ⟨179267602711240491291126805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239023470281653988388169073 179267602711240491291126805)
                ·
                  refine ⟨8403168877089398029271569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 179267602711240491291126805 8403168877089398029271569)
                  ·
                    refine ⟨6302376657817048521953677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8403168877089398029271569 6302376657817048521953677)
                    ·
                      refine ⟨2363391246681393195732629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302376657817048521953677 2363391246681393195732629)
                      ·
                        rfl

theorem cell23_4602688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 3].length) (baseStart_4602688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602688 prefixEnd_4602688 := by exact prefixLift 4602688
  have htrace : WordTrace (prefixWord ++ tailWord_4602688) baseStart_4602688 baseEnd_4602688 := by
    simpa [prefixWord, tailWord_4602688, baseEnd_4602688] using wordTrace_append hprefix tailTrace_4602688
  have hstable : (prefixWord ++ tailWord_4602688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602688).length < 2 ^ (prefixWord ++ tailWord_4602688).sum := by decide
  have hdescent : baseEnd_4602688 < baseStart_4602688 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602691 : List Nat := [1, 1, 1, 3, 1, 4, 1, 1, 10]
def baseStart_4602691 : Nat := 118140960795 + 4602691 * 2 ^ 59
def prefixEnd_4602691 : Nat := 4983230072969 + 3 ^ 40 * 4602691 * 2
def baseEnd_4602691 : Nat := 262599198569261853777235

theorem tailTrace_4602691 : CollatzResearch.WordTrace tailWord_4602691 prefixEnd_4602691 262599198569261853777235 := by
  unfold tailWord_4602691
  simp only [CollatzResearch.WordTrace]
  refine ⟨167873932168244058885119927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111915954778829372590079951 167873932168244058885119927)
  ·
    refine ⟨251810898252366088327679891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167873932168244058885119927 251810898252366088327679891)
    ·
      refine ⟨377716347378549132491519837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251810898252366088327679891 377716347378549132491519837)
      ·
        refine ⟨141643630266955924684319939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 377716347378549132491519837 141643630266955924684319939)
        ·
          refine ⟨212465445400433887026479909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141643630266955924684319939 212465445400433887026479909)
          ·
            refine ⟨39837271012581353817464983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212465445400433887026479909 39837271012581353817464983)
            ·
              refine ⟨59755906518872030726197475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39837271012581353817464983 59755906518872030726197475)
              ·
                refine ⟨89633859778308046089296213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59755906518872030726197475 89633859778308046089296213)
                ·
                  refine ⟨262599198569261853777235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 89633859778308046089296213 262599198569261853777235)
                  ·
                    rfl

theorem cell23_4602691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 1, 10].length) (baseStart_4602691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602691 prefixEnd_4602691 := by exact prefixLift 4602691
  have htrace : WordTrace (prefixWord ++ tailWord_4602691) baseStart_4602691 baseEnd_4602691 := by
    simpa [prefixWord, tailWord_4602691, baseEnd_4602691] using wordTrace_append hprefix tailTrace_4602691
  have hstable : (prefixWord ++ tailWord_4602691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602691).length < 2 ^ (prefixWord ++ tailWord_4602691).sum := by decide
  have hdescent : baseEnd_4602691 < baseStart_4602691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602725 : List Nat := [1, 3, 1, 3, 1, 1, 6, 1, 6]
def baseStart_4602725 : Nat := 118140960795 + 4602725 * 2 ^ 59
def prefixEnd_4602725 : Nat := 4983230072969 + 3 ^ 40 * 4602725 * 2
def baseEnd_4602725 : Nat := 262601138385067727885551

theorem tailTrace_4602725 : CollatzResearch.WordTrace tailWord_4602725 prefixEnd_4602725 262601138385067727885551 := by
  unfold tailWord_4602725
  simp only [CollatzResearch.WordTrace]
  refine ⟨167875172250120882691857629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111916781500080588461238419 167875172250120882691857629)
  ·
    refine ⟨62953189593795331009446611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167875172250120882691857629 62953189593795331009446611)
    ·
      refine ⟨94429784390692996514169917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62953189593795331009446611 94429784390692996514169917)
      ·
        refine ⟨35411169146509873692813719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94429784390692996514169917 35411169146509873692813719)
        ·
          refine ⟨53116753719764810539220579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35411169146509873692813719 53116753719764810539220579)
          ·
            refine ⟨79675130579647215808830869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53116753719764810539220579 79675130579647215808830869)
            ·
              refine ⟨3734771745920963241038947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79675130579647215808830869 3734771745920963241038947)
              ·
                refine ⟨5602157618881444861558421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734771745920963241038947 5602157618881444861558421)
                ·
                  refine ⟨262601138385067727885551, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5602157618881444861558421 262601138385067727885551)
                  ·
                    rfl

theorem cell23_4602725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_4602725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602725 prefixEnd_4602725 := by exact prefixLift 4602725
  have htrace : WordTrace (prefixWord ++ tailWord_4602725) baseStart_4602725 baseEnd_4602725 := by
    simpa [prefixWord, tailWord_4602725, baseEnd_4602725] using wordTrace_append hprefix tailTrace_4602725
  have hstable : (prefixWord ++ tailWord_4602725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602725).length < 2 ^ (prefixWord ++ tailWord_4602725).sum := by decide
  have hdescent : baseEnd_4602725 < baseStart_4602725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602735 : List Nat := [1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 3]
def baseStart_4602735 : Nat := 118140960795 + 4602735 * 2 ^ 59
def prefixEnd_4602735 : Nat := 4983230072969 + 3 ^ 40 * 4602735 * 2
def baseEnd_4602735 : Nat := 2363415380272154511844913

theorem tailTrace_4602735 : CollatzResearch.WordTrace tailWord_4602735 prefixEnd_4602735 2363415380272154511844913 := by
  unfold tailWord_4602735
  simp only [CollatzResearch.WordTrace]
  refine ⟨167875536980084654399721659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111917024653389769599814439 167875536980084654399721659)
  ·
    refine ⟨251813305470126981599582489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167875536980084654399721659 251813305470126981599582489)
    ·
      refine ⟨188859979102595236199686867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251813305470126981599582489 188859979102595236199686867)
      ·
        refine ⟨283289968653892854299530301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188859979102595236199686867 283289968653892854299530301)
        ·
          refine ⟨106233738245209820362323863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283289968653892854299530301 106233738245209820362323863)
          ·
            refine ⟨159350607367814730543485795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106233738245209820362323863 159350607367814730543485795)
            ·
              refine ⟨239025911051722095815228693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159350607367814730543485795 239025911051722095815228693)
              ·
                refine ⟨11204339580549473241338845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 239025911051722095815228693 11204339580549473241338845)
                ·
                  refine ⟨4201627342706052465502067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11204339580549473241338845 4201627342706052465502067)
                  ·
                    refine ⟨6302441014059078698253101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4201627342706052465502067 6302441014059078698253101)
                    ·
                      refine ⟨2363415380272154511844913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302441014059078698253101 2363415380272154511844913)
                      ·
                        rfl

theorem cell23_4602735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 6, 3, 1, 3].length) (baseStart_4602735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602735 prefixEnd_4602735 := by exact prefixLift 4602735
  have htrace : WordTrace (prefixWord ++ tailWord_4602735) baseStart_4602735 baseEnd_4602735 := by
    simpa [prefixWord, tailWord_4602735, baseEnd_4602735] using wordTrace_append hprefix tailTrace_4602735
  have hstable : (prefixWord ++ tailWord_4602735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602735).length < 2 ^ (prefixWord ++ tailWord_4602735).sum := by decide
  have hdescent : baseEnd_4602735 < baseStart_4602735 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602785 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 1, 6]
def baseStart_4602785 : Nat := 118140960795 + 4602785 * 2 ^ 59
def prefixEnd_4602785 : Nat := 4983230072969 + 3 ^ 40 * 4602785 * 2
def baseEnd_4602785 : Nat := 787813684768293105406561

theorem tailTrace_4602785 : CollatzResearch.WordTrace tailWord_4602785 prefixEnd_4602785 787813684768293105406561 := by
  unfold tailWord_4602785
  simp only [CollatzResearch.WordTrace]
  refine ⟨167877360629903512939041809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111918240419935675292694539 167877360629903512939041809)
  ·
    refine ⟨125908020472427634704281357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167877360629903512939041809 125908020472427634704281357)
    ·
      refine ⟨47215507677160363014105509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125908020472427634704281357 47215507677160363014105509)
      ·
        refine ⟨8852907689467568065144783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47215507677160363014105509 8852907689467568065144783)
        ·
          refine ⟨13279361534201352097717175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8852907689467568065144783 13279361534201352097717175)
          ·
            refine ⟨19919042301302028146575763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13279361534201352097717175 19919042301302028146575763)
            ·
              refine ⟨29878563451953042219863645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19919042301302028146575763 29878563451953042219863645)
              ·
                refine ⟨11204461294482390832448867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29878563451953042219863645 11204461294482390832448867)
                ·
                  refine ⟨16806691941723586248673301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11204461294482390832448867 16806691941723586248673301)
                  ·
                    refine ⟨787813684768293105406561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16806691941723586248673301 787813684768293105406561)
                    ·
                      rfl

theorem cell23_4602785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 6].length) (baseStart_4602785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602785 prefixEnd_4602785 := by exact prefixLift 4602785
  have htrace : WordTrace (prefixWord ++ tailWord_4602785) baseStart_4602785 baseEnd_4602785 := by
    simpa [prefixWord, tailWord_4602785, baseEnd_4602785] using wordTrace_append hprefix tailTrace_4602785
  have hstable : (prefixWord ++ tailWord_4602785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602785).length < 2 ^ (prefixWord ++ tailWord_4602785).sum := by decide
  have hdescent : baseEnd_4602785 < baseStart_4602785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602805 : List Nat := [1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 4]
def baseStart_4602805 : Nat := 118140960795 + 4602805 * 2 ^ 59
def prefixEnd_4602805 : Nat := 4983230072969 + 3 ^ 40 * 4602805 * 2
def baseEnd_4602805 : Nat := 2363451323917969237969591

theorem tailTrace_4602805 : CollatzResearch.WordTrace tailWord_4602805 prefixEnd_4602805 2363451323917969237969591 := by
  unfold tailWord_4602805
  simp only [CollatzResearch.WordTrace]
  refine ⟨167878090089831056354769869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111918726726554037569846579 167878090089831056354769869)
  ·
    refine ⟨62954283783686646133038701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167878090089831056354769869 62954283783686646133038701)
    ·
      refine ⟨23607856418882492299889513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62954283783686646133038701 23607856418882492299889513)
      ·
        refine ⟨17705892314161869224917135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23607856418882492299889513 17705892314161869224917135)
        ·
          refine ⟨26558838471242803837375703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17705892314161869224917135 26558838471242803837375703)
          ·
            refine ⟨39838257706864205756063555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26558838471242803837375703 39838257706864205756063555)
            ·
              refine ⟨59757386560296308634095333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39838257706864205756063555 59757386560296308634095333)
              ·
                refine ⟨11204509980055557868892875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59757386560296308634095333 11204509980055557868892875)
                ·
                  refine ⟨16806764970083336803339313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11204509980055557868892875 16806764970083336803339313)
                  ·
                    refine ⟨12605073727562502602504485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16806764970083336803339313 12605073727562502602504485)
                    ·
                      refine ⟨2363451323917969237969591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12605073727562502602504485 2363451323917969237969591)
                      ·
                        rfl

theorem cell23_4602805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 4, 1, 2, 4].length) (baseStart_4602805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602805 prefixEnd_4602805 := by exact prefixLift 4602805
  have htrace : WordTrace (prefixWord ++ tailWord_4602805) baseStart_4602805 baseEnd_4602805 := by
    simpa [prefixWord, tailWord_4602805, baseEnd_4602805] using wordTrace_append hprefix tailTrace_4602805
  have hstable : (prefixWord ++ tailWord_4602805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602805).length < 2 ^ (prefixWord ++ tailWord_4602805).sum := by decide
  have hdescent : baseEnd_4602805 < baseStart_4602805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602809 : List Nat := [1, 2, 1, 4, 2, 4, 2, 1, 1, 1, 4]
def baseStart_4602809 : Nat := 118140960795 + 4602809 * 2 ^ 59
def prefixEnd_4602809 : Nat := 4983230072969 + 3 ^ 40 * 4602809 * 2
def baseEnd_4602809 : Nat := 2363453377840587222319573

theorem tailTrace_4602809 : CollatzResearch.WordTrace tailWord_4602809 prefixEnd_4602809 2363453377840587222319573 := by
  unfold tailWord_4602809
  simp only [CollatzResearch.WordTrace]
  refine ⟨167878235981816565037915481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111918823987877710025276987 167878235981816565037915481)
  ·
    refine ⟨125908676986362423778436611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167878235981816565037915481 125908676986362423778436611)
    ·
      refine ⟨188863015479543635667654917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125908676986362423778436611 188863015479543635667654917)
      ·
        refine ⟨35411815402414431687685297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188863015479543635667654917 35411815402414431687685297)
        ·
          refine ⟨26558861551810823765763973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35411815402414431687685297 26558861551810823765763973)
          ·
            refine ⟨4979786540964529456080745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26558861551810823765763973 4979786540964529456080745)
            ·
              refine ⟨3734839905723397092060559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4979786540964529456080745 3734839905723397092060559)
              ·
                refine ⟨5602259858585095638090839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3734839905723397092060559 5602259858585095638090839)
                ·
                  refine ⟨8403389787877643457136259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5602259858585095638090839 8403389787877643457136259)
                  ·
                    refine ⟨12605084681816465185704389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8403389787877643457136259 12605084681816465185704389)
                    ·
                      refine ⟨2363453377840587222319573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12605084681816465185704389 2363453377840587222319573)
                      ·
                        rfl

theorem cell23_4602809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 1, 1, 1, 4].length) (baseStart_4602809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602809 prefixEnd_4602809 := by exact prefixLift 4602809
  have htrace : WordTrace (prefixWord ++ tailWord_4602809) baseStart_4602809 baseEnd_4602809 := by
    simpa [prefixWord, tailWord_4602809, baseEnd_4602809] using wordTrace_append hprefix tailTrace_4602809
  have hstable : (prefixWord ++ tailWord_4602809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602809).length < 2 ^ (prefixWord ++ tailWord_4602809).sum := by decide
  have hdescent : baseEnd_4602809 < baseStart_4602809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602842 : List Nat := [3, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_4602842 : Nat := 118140960795 + 4602842 * 2 ^ 59
def prefixEnd_4602842 : Nat := 4983230072969 + 3 ^ 40 * 4602842 * 2
def baseEnd_4602842 : Nat := 2363470322702185593206921

theorem tailTrace_4602842 : CollatzResearch.WordTrace tailWord_4602842 prefixEnd_4602842 2363470322702185593206921 := by
  unfold tailWord_4602842
  simp only [CollatzResearch.WordTrace]
  refine ⟨41969859897674252918466695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111919626393798007782577853 41969859897674252918466695)
  ·
    refine ⟨62954789846511379377700043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41969859897674252918466695 62954789846511379377700043)
    ·
      refine ⟨94432184769767069066550065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62954789846511379377700043 94432184769767069066550065)
      ·
        refine ⟨70824138577325301799912549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94432184769767069066550065 70824138577325301799912549)
        ·
          refine ⟨13279525983248494087483603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70824138577325301799912549 13279525983248494087483603)
          ·
            refine ⟨19919288974872741131225405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13279525983248494087483603 19919288974872741131225405)
            ·
              refine ⟨7469733365577277924209527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19919288974872741131225405 7469733365577277924209527)
              ·
                refine ⟨11204600048365916886314291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7469733365577277924209527 11204600048365916886314291)
                ·
                  refine ⟨16806900072548875329471437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11204600048365916886314291 16806900072548875329471437)
                  ·
                    refine ⟨6302587527205828248551789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16806900072548875329471437 6302587527205828248551789)
                    ·
                      refine ⟨2363470322702185593206921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302587527205828248551789 2363470322702185593206921)
                      ·
                        rfl

theorem cell23_4602842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_4602842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602842 prefixEnd_4602842 := by exact prefixLift 4602842
  have htrace : WordTrace (prefixWord ++ tailWord_4602842) baseStart_4602842 baseEnd_4602842 := by
    simpa [prefixWord, tailWord_4602842, baseEnd_4602842] using wordTrace_append hprefix tailTrace_4602842
  have hstable : (prefixWord ++ tailWord_4602842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602842).length < 2 ^ (prefixWord ++ tailWord_4602842).sum := by decide
  have hdescent : baseEnd_4602842 < baseStart_4602842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602855 : List Nat := [1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_4602855 : Nat := 118140960795 + 4602855 * 2 ^ 59
def prefixEnd_4602855 : Nat := 4983230072969 + 3 ^ 40 * 4602855 * 2
def baseEnd_4602855 : Nat := 2363476997950694042344361

theorem tailTrace_4602855 : CollatzResearch.WordTrace tailWord_4602855 prefixEnd_4602855 2363476997950694042344361 := by
  unfold tailWord_4602855
  simp only [CollatzResearch.WordTrace]
  refine ⟨167879913739649914894090019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111919942493099943262726679 167879913739649914894090019)
  ·
    refine ⟨251819870609474872341135029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167879913739649914894090019 251819870609474872341135029)
    ·
      refine ⟨23608112869638269281981409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 251819870609474872341135029 23608112869638269281981409)
      ·
        refine ⟨17706084652228701961486057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23608112869638269281981409 17706084652228701961486057)
        ·
          refine ⟨13279563489171526471114543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17706084652228701961486057 13279563489171526471114543)
          ·
            refine ⟨19919345233757289706671815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13279563489171526471114543 19919345233757289706671815)
            ·
              refine ⟨29879017850635934560007723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19919345233757289706671815 29879017850635934560007723)
              ·
                refine ⟨44818526775953901840011585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29879017850635934560007723 44818526775953901840011585)
                ·
                  refine ⟨33613895081965426380008689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44818526775953901840011585 33613895081965426380008689)
                  ·
                    refine ⟨25210421311474069785006517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33613895081965426380008689 25210421311474069785006517)
                    ·
                      refine ⟨2363476997950694042344361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25210421311474069785006517 2363476997950694042344361)
                      ·
                        rfl

theorem cell23_4602855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_4602855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602855 prefixEnd_4602855 := by exact prefixLift 4602855
  have htrace : WordTrace (prefixWord ++ tailWord_4602855) baseStart_4602855 baseEnd_4602855 := by
    simpa [prefixWord, tailWord_4602855, baseEnd_4602855] using wordTrace_append hprefix tailTrace_4602855
  have hstable : (prefixWord ++ tailWord_4602855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602855).length < 2 ^ (prefixWord ++ tailWord_4602855).sum := by decide
  have hdescent : baseEnd_4602855 < baseStart_4602855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602885 : List Nat := [1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 3]
def baseStart_4602885 : Nat := 118140960795 + 4602885 * 2 ^ 59
def prefixEnd_4602885 : Nat := 4983230072969 + 3 ^ 40 * 4602885 * 2
def baseEnd_4602885 : Nat := 2363492402370328924969223

theorem tailTrace_4602885 : CollatzResearch.WordTrace tailWord_4602885 prefixEnd_4602885 2363492402370328924969223 := by
  unfold tailWord_4602885
  simp only [CollatzResearch.WordTrace]
  refine ⟨167881007929541230017682109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111920671953027486678454739 167881007929541230017682109)
  ·
    refine ⟨62955377973577961256630791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167881007929541230017682109 62955377973577961256630791)
    ·
      refine ⟨94433066960366941884946187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62955377973577961256630791 94433066960366941884946187)
      ·
        refine ⟨141649600440550412827419281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94433066960366941884946187 141649600440550412827419281)
        ·
          refine ⟨106237200330412809620564461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141649600440550412827419281 106237200330412809620564461)
          ·
            refine ⟨39838950123904803607711673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106237200330412809620564461 39838950123904803607711673)
            ·
              refine ⟨29879212592928602705783755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39838950123904803607711673 29879212592928602705783755)
              ·
                refine ⟨44818818889392904058675633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29879212592928602705783755 44818818889392904058675633)
                ·
                  refine ⟨33614114167044678044006725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44818818889392904058675633 33614114167044678044006725)
                  ·
                    refine ⟨6302646406320877133251261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33614114167044678044006725 6302646406320877133251261)
                    ·
                      refine ⟨2363492402370328924969223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302646406320877133251261 2363492402370328924969223)
                      ·
                        rfl

theorem cell23_4602885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_4602885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602885 prefixEnd_4602885 := by exact prefixLift 4602885
  have htrace : WordTrace (prefixWord ++ tailWord_4602885) baseStart_4602885 baseEnd_4602885 := by
    simpa [prefixWord, tailWord_4602885, baseEnd_4602885] using wordTrace_append hprefix tailTrace_4602885
  have hstable : (prefixWord ++ tailWord_4602885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602885).length < 2 ^ (prefixWord ++ tailWord_4602885).sum := by decide
  have hdescent : baseEnd_4602885 < baseStart_4602885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602972 : List Nat := [2, 2, 4, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_4602972 : Nat := 118140960795 + 4602972 * 2 ^ 59
def prefixEnd_4602972 : Nat := 4983230072969 + 3 ^ 40 * 4602972 * 2
def baseEnd_4602972 : Nat := 2363537075187270084581323

theorem tailTrace_4602972 : CollatzResearch.WordTrace tailWord_4602972 prefixEnd_4602972 2363537075187270084581323 := by
  unfold tailWord_4602972
  simp only [CollatzResearch.WordTrace]
  refine ⟨83942090540113021938049585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111922787386817362584066113 83942090540113021938049585)
  ·
    refine ⟨62956567905084766453537189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83942090540113021938049585 62956567905084766453537189)
    ·
      refine ⟨11804356482203393710038223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62956567905084766453537189 11804356482203393710038223)
      ·
        refine ⟨17706534723305090565057335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11804356482203393710038223 17706534723305090565057335)
        ·
          refine ⟨26559802084957635847586003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17706534723305090565057335 26559802084957635847586003)
          ·
            refine ⟨39839703127436453771379005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26559802084957635847586003 39839703127436453771379005)
            ·
              refine ⟨14939888672788670164267127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39839703127436453771379005 14939888672788670164267127)
              ·
                refine ⟨22409833009183005246400691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14939888672788670164267127 22409833009183005246400691)
                ·
                  refine ⟨33614749513774507869601037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22409833009183005246400691 33614749513774507869601037)
                  ·
                    refine ⟨12605531067665440451100389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33614749513774507869601037 12605531067665440451100389)
                    ·
                      refine ⟨2363537075187270084581323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12605531067665440451100389 2363537075187270084581323)
                      ·
                        rfl

theorem cell23_4602972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_4602972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602972 prefixEnd_4602972 := by exact prefixLift 4602972
  have htrace : WordTrace (prefixWord ++ tailWord_4602972) baseStart_4602972 baseEnd_4602972 := by
    simpa [prefixWord, tailWord_4602972, baseEnd_4602972] using wordTrace_append hprefix tailTrace_4602972
  have hstable : (prefixWord ++ tailWord_4602972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602972).length < 2 ^ (prefixWord ++ tailWord_4602972).sum := by decide
  have hdescent : baseEnd_4602972 < baseStart_4602972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602985 : List Nat := [1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 6]
def baseStart_4602985 : Nat := 118140960795 + 4602985 * 2 ^ 59
def prefixEnd_4602985 : Nat := 4983230072969 + 3 ^ 40 * 4602985 * 2
def baseEnd_4602985 : Nat := 2363543750435778533718763

theorem tailTrace_4602985 : CollatzResearch.WordTrace tailWord_4602985 prefixEnd_4602985 2363543750435778533718763 := by
  unfold tailWord_4602985
  simp only [CollatzResearch.WordTrace]
  refine ⟨167884655229178947096322409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111923103486119298064214939 167884655229178947096322409)
  ·
    refine ⟨125913491421884210322241807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167884655229178947096322409 125913491421884210322241807)
    ·
      refine ⟨188870237132826315483362711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125913491421884210322241807 188870237132826315483362711)
      ·
        refine ⟨283305355699239473225044067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188870237132826315483362711 283305355699239473225044067)
        ·
          refine ⟨424958033548859209837566101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283305355699239473225044067 424958033548859209837566101)
          ·
            refine ⟨19919907822602775461135911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 424958033548859209837566101 19919907822602775461135911)
            ·
              refine ⟨29879861733904163191703867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19919907822602775461135911 29879861733904163191703867)
              ·
                refine ⟨44819792600856244787555801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29879861733904163191703867 44819792600856244787555801)
                ·
                  refine ⟨33614844450642183590666851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44819792600856244787555801 33614844450642183590666851)
                  ·
                    refine ⟨50422266675963275386000277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33614844450642183590666851 50422266675963275386000277)
                    ·
                      refine ⟨2363543750435778533718763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50422266675963275386000277 2363543750435778533718763)
                      ·
                        rfl

theorem cell23_4602985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 1, 2, 1, 6].length) (baseStart_4602985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602985 prefixEnd_4602985 := by exact prefixLift 4602985
  have htrace : WordTrace (prefixWord ++ tailWord_4602985) baseStart_4602985 baseEnd_4602985 := by
    simpa [prefixWord, tailWord_4602985, baseEnd_4602985] using wordTrace_append hprefix tailTrace_4602985
  have hstable : (prefixWord ++ tailWord_4602985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602985).length < 2 ^ (prefixWord ++ tailWord_4602985).sum := by decide
  have hdescent : baseEnd_4602985 < baseStart_4602985 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602989 : List Nat := [1, 5, 1, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_4602989 : Nat := 118140960795 + 4602989 * 2 ^ 59
def prefixEnd_4602989 : Nat := 4983230072969 + 3 ^ 40 * 4602989 * 2
def baseEnd_4602989 : Nat := 2363545804358396518068745

theorem tailTrace_4602989 : CollatzResearch.WordTrace tailWord_4602989 prefixEnd_4602989 2363545804358396518068745 := by
  unfold tailWord_4602989
  simp only [CollatzResearch.WordTrace]
  refine ⟨167884801121164455779468021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111923200747442970519645347 167884801121164455779468021)
  ·
    refine ⟨15739200105109167729325127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167884801121164455779468021 15739200105109167729325127)
    ·
      refine ⟨23608800157663751593987691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15739200105109167729325127 23608800157663751593987691)
      ·
        refine ⟨35413200236495627390981537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23608800157663751593987691 35413200236495627390981537)
        ·
          refine ⟨26559900177371720543236153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35413200236495627390981537 26559900177371720543236153)
          ·
            refine ⟨19919925133028790407427115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26559900177371720543236153 19919925133028790407427115)
            ·
              refine ⟨29879887699543185611140673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19919925133028790407427115 29879887699543185611140673)
              ·
                refine ⟨22409915774657389208355505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29879887699543185611140673 22409915774657389208355505)
                ·
                  refine ⟨16807436830993041906266629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22409915774657389208355505 16807436830993041906266629)
                  ·
                    refine ⟨3151394405811195357424993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16807436830993041906266629 3151394405811195357424993)
                    ·
                      refine ⟨2363545804358396518068745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3151394405811195357424993 2363545804358396518068745)
                      ·
                        rfl

theorem cell23_4602989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_4602989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602989 prefixEnd_4602989 := by exact prefixLift 4602989
  have htrace : WordTrace (prefixWord ++ tailWord_4602989) baseStart_4602989 baseEnd_4602989 := by
    simpa [prefixWord, tailWord_4602989, baseEnd_4602989] using wordTrace_append hprefix tailTrace_4602989
  have hstable : (prefixWord ++ tailWord_4602989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602989).length < 2 ^ (prefixWord ++ tailWord_4602989).sum := by decide
  have hdescent : baseEnd_4602989 < baseStart_4602989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602992 : List Nat := [2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3]
def baseStart_4602992 : Nat := 118140960795 + 4602992 * 2 ^ 59
def prefixEnd_4602992 : Nat := 4983230072969 + 3 ^ 40 * 4602992 * 2
def baseEnd_4602992 : Nat := 2363547344800360006331231

theorem tailTrace_4602992 : CollatzResearch.WordTrace tailWord_4602992 prefixEnd_4602992 2363547344800360006331231 := by
  unfold tailWord_4602992
  simp only [CollatzResearch.WordTrace]
  refine ⟨83942455270076793645913615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111923273693435724861218153 83942455270076793645913615)
  ·
    refine ⟨125913682905115190468870423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83942455270076793645913615 125913682905115190468870423)
    ·
      refine ⟨188870524357672785703305635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125913682905115190468870423 188870524357672785703305635)
      ·
        refine ⟨283305786536509178554958453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188870524357672785703305635 283305786536509178554958453)
        ·
          refine ⟨26559917487797735489527355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 283305786536509178554958453 26559917487797735489527355)
          ·
            refine ⟨39839876231696603234291033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26559917487797735489527355 39839876231696603234291033)
            ·
              refine ⟨29879907173772452425718275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39839876231696603234291033 29879907173772452425718275)
              ·
                refine ⟨44819860760658678638577413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29879907173772452425718275 44819860760658678638577413)
                ·
                  refine ⟨8403723892623502244733265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44819860760658678638577413 8403723892623502244733265)
                  ·
                    refine ⟨6302792919467626683549949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8403723892623502244733265 6302792919467626683549949)
                    ·
                      refine ⟨2363547344800360006331231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302792919467626683549949 2363547344800360006331231)
                      ·
                        rfl

theorem cell23_4602992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 1, 4, 2, 3].length) (baseStart_4602992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602992 prefixEnd_4602992 := by exact prefixLift 4602992
  have htrace : WordTrace (prefixWord ++ tailWord_4602992) baseStart_4602992 baseEnd_4602992 := by
    simpa [prefixWord, tailWord_4602992, baseEnd_4602992] using wordTrace_append hprefix tailTrace_4602992
  have hstable : (prefixWord ++ tailWord_4602992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602992).length < 2 ^ (prefixWord ++ tailWord_4602992).sum := by decide
  have hdescent : baseEnd_4602992 < baseStart_4602992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4602999 : List Nat := [1, 1, 3, 1, 1, 4, 1, 6, 1, 4]
def baseStart_4602999 : Nat := 118140960795 + 4602999 * 2 ^ 59
def prefixEnd_4602999 : Nat := 4983230072969 + 3 ^ 40 * 4602999 * 2
def baseEnd_4602999 : Nat := 787850313054980492981233

theorem tailTrace_4602999 : CollatzResearch.WordTrace tailWord_4602999 prefixEnd_4602999 787850313054980492981233 := by
  unfold tailWord_4602999
  simp only [CollatzResearch.WordTrace]
  refine ⟨167885165851128227487332051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111923443900752151658221367 167885165851128227487332051)
  ·
    refine ⟨251827748776692341230998077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167885165851128227487332051 251827748776692341230998077)
    ·
      refine ⟨94435405791259627961624279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251827748776692341230998077 94435405791259627961624279)
      ·
        refine ⟨141653108686889441942436419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94435405791259627961624279 141653108686889441942436419)
        ·
          refine ⟨212479663030334162913654629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141653108686889441942436419 212479663030334162913654629)
          ·
            refine ⟨39839936818187655546310243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212479663030334162913654629 39839936818187655546310243)
            ·
              refine ⟨59759905227281483319465365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39839936818187655546310243 59759905227281483319465365)
              ·
                refine ⟨2801245557528819530599939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59759905227281483319465365 2801245557528819530599939)
                ·
                  refine ⟨4201868336293229295899909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801245557528819530599939 4201868336293229295899909)
                  ·
                    refine ⟨787850313054980492981233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4201868336293229295899909 787850313054980492981233)
                    ·
                      rfl

theorem cell23_4602999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_4602999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4602999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4602999 prefixEnd_4602999 := by exact prefixLift 4602999
  have htrace : WordTrace (prefixWord ++ tailWord_4602999) baseStart_4602999 baseEnd_4602999 := by
    simpa [prefixWord, tailWord_4602999, baseEnd_4602999] using wordTrace_append hprefix tailTrace_4602999
  have hstable : (prefixWord ++ tailWord_4602999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4602999).length < 2 ^ (prefixWord ++ tailWord_4602999).sum := by decide
  have hdescent : baseEnd_4602999 < baseStart_4602999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4602999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603015 : List Nat := [1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_4603015 : Nat := 118140960795 + 4603015 * 2 ^ 59
def prefixEnd_4603015 : Nat := 4983230072969 + 3 ^ 40 * 4603015 * 2
def baseEnd_4603015 : Nat := 2363559154855413416343625

theorem tailTrace_4603015 : CollatzResearch.WordTrace tailWord_4603015 prefixEnd_4603015 2363559154855413416343625 := by
  unfold tailWord_4603015
  simp only [CollatzResearch.WordTrace]
  refine ⟨167885749419070262219914499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111923832946046841479942999 167885749419070262219914499)
  ·
    refine ⟨251828624128605393329871749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167885749419070262219914499 251828624128605393329871749)
    ·
      refine ⟨47217867024113511249350953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251828624128605393329871749 47217867024113511249350953)
      ·
        refine ⟨35413400268085133437013215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47217867024113511249350953 35413400268085133437013215)
        ·
          refine ⟨53120100402127700155519823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35413400268085133437013215 53120100402127700155519823)
          ·
            refine ⟨79680150603191550233279735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53120100402127700155519823 79680150603191550233279735)
            ·
              refine ⟨119520225904787325349919603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79680150603191550233279735 119520225904787325349919603)
              ·
                refine ⟨179280338857180988024879405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119520225904787325349919603 179280338857180988024879405)
                ·
                  refine ⟨67230127071442870509329777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179280338857180988024879405 67230127071442870509329777)
                  ·
                    refine ⟨50422595303582152881997333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67230127071442870509329777 50422595303582152881997333)
                    ·
                      refine ⟨2363559154855413416343625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50422595303582152881997333 2363559154855413416343625)
                      ·
                        rfl

theorem cell23_4603015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_4603015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603015 prefixEnd_4603015 := by exact prefixLift 4603015
  have htrace : WordTrace (prefixWord ++ tailWord_4603015) baseStart_4603015 baseEnd_4603015 := by
    simpa [prefixWord, tailWord_4603015, baseEnd_4603015] using wordTrace_append hprefix tailTrace_4603015
  have hstable : (prefixWord ++ tailWord_4603015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603015).length < 2 ^ (prefixWord ++ tailWord_4603015).sum := by decide
  have hdescent : baseEnd_4603015 < baseStart_4603015 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603050 : List Nat := [3, 1, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_4603050 : Nat := 118140960795 + 4603050 * 2 ^ 59
def prefixEnd_4603050 : Nat := 4983230072969 + 3 ^ 40 * 4603050 * 2
def baseEnd_4603050 : Nat := 787859042226106926468655

theorem tailTrace_4603050 : CollatzResearch.WordTrace tailWord_4603050 prefixEnd_4603050 787859042226106926468655 := by
  unfold tailWord_4603050
  simp only [CollatzResearch.WordTrace]
  refine ⟨41971756493485865799359651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111924683982628975464959069 41971756493485865799359651)
  ·
    refine ⟨62957634740228798699039477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41971756493485865799359651 62957634740228798699039477)
    ·
      refine ⟨5902278256896449878034951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62957634740228798699039477 5902278256896449878034951)
      ·
        refine ⟨8853417385344674817052427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5902278256896449878034951 8853417385344674817052427)
        ·
          refine ⟨13280126078017012225578641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8853417385344674817052427 13280126078017012225578641)
          ·
            refine ⟨9960094558512759169183981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13280126078017012225578641 9960094558512759169183981)
            ·
              refine ⟨3735035459442284688443993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9960094558512759169183981 3735035459442284688443993)
              ·
                refine ⟨2801276594581713516332995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3735035459442284688443993 2801276594581713516332995)
                ·
                  refine ⟨4201914891872570274499493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801276594581713516332995 4201914891872570274499493)
                  ·
                    refine ⟨787859042226106926468655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4201914891872570274499493 787859042226106926468655)
                    ·
                      rfl

theorem cell23_4603050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_4603050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603050 prefixEnd_4603050 := by exact prefixLift 4603050
  have htrace : WordTrace (prefixWord ++ tailWord_4603050) baseStart_4603050 baseEnd_4603050 := by
    simpa [prefixWord, tailWord_4603050, baseEnd_4603050] using wordTrace_append hprefix tailTrace_4603050
  have hstable : (prefixWord ++ tailWord_4603050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603050).length < 2 ^ (prefixWord ++ tailWord_4603050).sum := by decide
  have hdescent : baseEnd_4603050 < baseStart_4603050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603119 : List Nat := [1, 1, 2, 1, 7, 2, 1, 8]
def baseStart_4603119 : Nat := 118140960795 + 4603119 * 2 ^ 59
def prefixEnd_4603119 : Nat := 4983230072969 + 3 ^ 40 * 4603119 * 2
def baseEnd_4603119 : Nat := 87541205809017815164561

theorem tailTrace_4603119 : CollatzResearch.WordTrace tailWord_4603119 prefixEnd_4603119 87541205809017815164561 := by
  unfold tailWord_4603119
  simp only [CollatzResearch.WordTrace]
  refine ⟨167889542610693487981700411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111926361740462325321133607 167889542610693487981700411)
  ·
    refine ⟨251834313916040231972550617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167889542610693487981700411 251834313916040231972550617)
    ·
      refine ⟨188875735437030173979412963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251834313916040231972550617 188875735437030173979412963)
      ·
        refine ⟨283313603155545260969119445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188875735437030173979412963 283313603155545260969119445)
        ·
          refine ⟨6640162573958092053963737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 283313603155545260969119445 6640162573958092053963737)
          ·
            refine ⟨4980121930468569040472803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6640162573958092053963737 4980121930468569040472803)
            ·
              refine ⟨7470182895702853560709205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4980121930468569040472803 7470182895702853560709205)
              ·
                refine ⟨87541205809017815164561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7470182895702853560709205 87541205809017815164561)
                ·
                  rfl

theorem cell23_4603119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 7, 2, 1, 8].length) (baseStart_4603119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603119 prefixEnd_4603119 := by exact prefixLift 4603119
  have htrace : WordTrace (prefixWord ++ tailWord_4603119) baseStart_4603119 baseEnd_4603119 := by
    simpa [prefixWord, tailWord_4603119, baseEnd_4603119] using wordTrace_append hprefix tailTrace_4603119
  have hstable : (prefixWord ++ tailWord_4603119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603119).length < 2 ^ (prefixWord ++ tailWord_4603119).sum := by decide
  have hdescent : baseEnd_4603119 < baseStart_4603119 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603129 : List Nat := [1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 3]
def baseStart_4603129 : Nat := 118140960795 + 4603129 * 2 ^ 59
def prefixEnd_4603129 : Nat := 4983230072969 + 3 ^ 40 * 4603129 * 2
def baseEnd_4603129 : Nat := 2363617691650025970318101

theorem tailTrace_4603129 : CollatzResearch.WordTrace tailWord_4603129 prefixEnd_4603129 2363617691650025970318101 := by
  unfold tailWord_4603129
  simp only [CollatzResearch.WordTrace]
  refine ⟨167889907340657259689564441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111926604893771506459709627 167889907340657259689564441)
  ·
    refine ⟨125917430505492944767173331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167889907340657259689564441 125917430505492944767173331)
    ·
      refine ⟨188876145758239417150759997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125917430505492944767173331 188876145758239417150759997)
      ·
        refine ⟨70828554659339781431534999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188876145758239417150759997 70828554659339781431534999)
        ·
          refine ⟨106242831989009672147302499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70828554659339781431534999 106242831989009672147302499)
          ·
            refine ⟨159364247983514508220953749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106242831989009672147302499 159364247983514508220953749)
            ·
              refine ⟨7470199124227242572857207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159364247983514508220953749 7470199124227242572857207)
              ·
                refine ⟨11205298686340863859285811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7470199124227242572857207 11205298686340863859285811)
                ·
                  refine ⟨16807948029511295788928717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11205298686340863859285811 16807948029511295788928717)
                  ·
                    refine ⟨6302980511066735920848269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16807948029511295788928717 6302980511066735920848269)
                    ·
                      refine ⟨2363617691650025970318101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6302980511066735920848269 2363617691650025970318101)
                      ·
                        rfl

theorem cell23_4603129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 6, 1, 1, 3, 3].length) (baseStart_4603129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603129 prefixEnd_4603129 := by exact prefixLift 4603129
  have htrace : WordTrace (prefixWord ++ tailWord_4603129) baseStart_4603129 baseEnd_4603129 := by
    simpa [prefixWord, tailWord_4603129, baseEnd_4603129] using wordTrace_append hprefix tailTrace_4603129
  have hstable : (prefixWord ++ tailWord_4603129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603129).length < 2 ^ (prefixWord ++ tailWord_4603129).sum := by decide
  have hdescent : baseEnd_4603129 < baseStart_4603129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603276 : List Nat := [2, 2, 1, 2, 1, 3, 2, 2, 2, 4, 2]
def baseStart_4603276 : Nat := 118140960795 + 4603276 * 2 ^ 59
def prefixEnd_4603276 : Nat := 4983230072969 + 3 ^ 40 * 4603276 * 2
def baseEnd_4603276 : Nat := 2363693173306236895179925

theorem tailTrace_4603276 : CollatzResearch.WordTrace tailWord_4603276 prefixEnd_4603276 2363693173306236895179925 := by
  unfold tailWord_4603276
  simp only [CollatzResearch.WordTrace]
  refine ⟨83947634435562351897582841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111930179247416469196777121 83947634435562351897582841)
  ·
    refine ⟨62960725826671763923187131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83947634435562351897582841 62960725826671763923187131)
    ·
      refine ⟨94441088740007645884780697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62960725826671763923187131 94441088740007645884780697)
      ·
        refine ⟨70830816555005734413585523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94441088740007645884780697 70830816555005734413585523)
        ·
          refine ⟨106246224832508601620378285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70830816555005734413585523 106246224832508601620378285)
          ·
            refine ⟨39842334312190725607641857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106246224832508601620378285 39842334312190725607641857)
            ·
              refine ⟨29881750734143044205731393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39842334312190725607641857 29881750734143044205731393)
              ·
                refine ⟨22411313050607283154298545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29881750734143044205731393 22411313050607283154298545)
                ·
                  refine ⟨16808484787955462365723909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22411313050607283154298545 16808484787955462365723909)
                  ·
                    refine ⟨3151590897741649193573233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16808484787955462365723909 3151590897741649193573233)
                    ·
                      refine ⟨2363693173306236895179925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3151590897741649193573233 2363693173306236895179925)
                      ·
                        rfl

theorem cell23_4603276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_4603276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603276 prefixEnd_4603276 := by exact prefixLift 4603276
  have htrace : WordTrace (prefixWord ++ tailWord_4603276) baseStart_4603276 baseEnd_4603276 := by
    simpa [prefixWord, tailWord_4603276, baseEnd_4603276] using wordTrace_append hprefix tailTrace_4603276
  have hstable : (prefixWord ++ tailWord_4603276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603276).length < 2 ^ (prefixWord ++ tailWord_4603276).sum := by decide
  have hdescent : baseEnd_4603276 < baseStart_4603276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603293 : List Nat := [1, 4, 2, 1, 3, 2, 1, 1, 2, 4, 2]
def baseStart_4603293 : Nat := 118140960795 + 4603293 * 2 ^ 59
def prefixEnd_4603293 : Nat := 4983230072969 + 3 ^ 40 * 4603293 * 2
def baseEnd_4603293 : Nat := 2363701902477363328667347

theorem tailTrace_4603293 : CollatzResearch.WordTrace tailWord_4603293 prefixEnd_4603293 2363701902477363328667347 := by
  unfold tailWord_4603293
  simp only [CollatzResearch.WordTrace]
  refine ⟨167895888912063115698534533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111930592608042077132356355 167895888912063115698534533)
  ·
    refine ⟨31480479171011834193475225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167895888912063115698534533 31480479171011834193475225)
    ·
      refine ⟨23610359378258875645106419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31480479171011834193475225 23610359378258875645106419)
      ·
        refine ⟨35415539067388313467659629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23610359378258875645106419 35415539067388313467659629)
        ·
          refine ⟨13280827150270617550372361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35415539067388313467659629 13280827150270617550372361)
          ·
            refine ⟨9960620362702963162779271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13280827150270617550372361 9960620362702963162779271)
            ·
              refine ⟨14940930544054444744168907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9960620362702963162779271 14940930544054444744168907)
              ·
                refine ⟨22411395816081667116253361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14940930544054444744168907 22411395816081667116253361)
                ·
                  refine ⟨16808546862061250337190021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22411395816081667116253361 16808546862061250337190021)
                  ·
                    refine ⟨3151602536636484438223129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16808546862061250337190021 3151602536636484438223129)
                    ·
                      refine ⟨2363701902477363328667347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3151602536636484438223129 2363701902477363328667347)
                      ·
                        rfl

theorem cell23_4603293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_4603293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603293 prefixEnd_4603293 := by exact prefixLift 4603293
  have htrace : WordTrace (prefixWord ++ tailWord_4603293) baseStart_4603293 baseEnd_4603293 := by
    simpa [prefixWord, tailWord_4603293, baseEnd_4603293] using wordTrace_append hprefix tailTrace_4603293
  have hstable : (prefixWord ++ tailWord_4603293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603293).length < 2 ^ (prefixWord ++ tailWord_4603293).sum := by decide
  have hdescent : baseEnd_4603293 < baseStart_4603293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603299 : List Nat := [1, 1, 1, 4, 1, 3, 1, 5, 6]
def baseStart_4603299 : Nat := 118140960795 + 4603299 * 2 ^ 59
def prefixEnd_4603299 : Nat := 4983230072969 + 3 ^ 40 * 4603299 * 2
def baseEnd_4603299 : Nat := 262633887040143367243591

theorem tailTrace_4603299 : CollatzResearch.WordTrace tailWord_4603299 prefixEnd_4603299 262633887040143367243591 := by
  unfold tailWord_4603299
  simp only [CollatzResearch.WordTrace]
  refine ⟨167896107750041378723252951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111930738500027585815501967 167896107750041378723252951)
  ·
    refine ⟨251844161625062068084879427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167896107750041378723252951 251844161625062068084879427)
    ·
      refine ⟨377766242437593102127319141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251844161625062068084879427 377766242437593102127319141)
      ·
        refine ⟨70831170457048706648872339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 377766242437593102127319141 70831170457048706648872339)
        ·
          refine ⟨106246755685573059973308509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70831170457048706648872339 106246755685573059973308509)
          ·
            refine ⟨39842533382089897489990691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106246755685573059973308509 39842533382089897489990691)
            ·
              refine ⟨59763800073134846234986037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39842533382089897489990691 59763800073134846234986037)
              ·
                refine ⟨5602856256856391834529941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59763800073134846234986037 5602856256856391834529941)
                ·
                  refine ⟨262633887040143367243591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5602856256856391834529941 262633887040143367243591)
                  ·
                    rfl

theorem cell23_4603299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 5, 6].length) (baseStart_4603299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603299 prefixEnd_4603299 := by exact prefixLift 4603299
  have htrace : WordTrace (prefixWord ++ tailWord_4603299) baseStart_4603299 baseEnd_4603299 := by
    simpa [prefixWord, tailWord_4603299, baseEnd_4603299] using wordTrace_append hprefix tailTrace_4603299
  have hstable : (prefixWord ++ tailWord_4603299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603299).length < 2 ^ (prefixWord ++ tailWord_4603299).sum := by decide
  have hdescent : baseEnd_4603299 < baseStart_4603299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603350 : List Nat := [5, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_4603350 : Nat := 118140960795 + 4603350 * 2 ^ 59
def prefixEnd_4603350 : Nat := 4983230072969 + 3 ^ 40 * 4603350 * 2
def baseEnd_4603350 : Nat := 262636796763852178406065

theorem tailTrace_4603350 : CollatzResearch.WordTrace tailWord_4603350 prefixEnd_4603350 262636796763852178406065 := by
  unfold tailWord_4603350
  simp only [CollatzResearch.WordTrace]
  refine ⟨10493622992053538402084969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 111931978581904409622239669 10493622992053538402084969)
  ·
    refine ⟨7870217244040153801563727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10493622992053538402084969 7870217244040153801563727)
    ·
      refine ⟨11805325866060230702345591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7870217244040153801563727 11805325866060230702345591)
      ·
        refine ⟨17707988799090346053518387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11805325866060230702345591 17707988799090346053518387)
        ·
          refine ⟨26561983198635519080277581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17707988799090346053518387 26561983198635519080277581)
          ·
            refine ⟨9960743699488319655104093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26561983198635519080277581 9960743699488319655104093)
            ·
              refine ⟨3735278887308119870664035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9960743699488319655104093 3735278887308119870664035)
              ·
                refine ⟨5602918330962179805996053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735278887308119870664035 5602918330962179805996053)
                ·
                  refine ⟨262636796763852178406065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5602918330962179805996053 262636796763852178406065)
                  ·
                    rfl

theorem cell23_4603350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_4603350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603350 prefixEnd_4603350 := by exact prefixLift 4603350
  have htrace : WordTrace (prefixWord ++ tailWord_4603350) baseStart_4603350 baseEnd_4603350 := by
    simpa [prefixWord, tailWord_4603350, baseEnd_4603350] using wordTrace_append hprefix tailTrace_4603350
  have hstable : (prefixWord ++ tailWord_4603350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603350).length < 2 ^ (prefixWord ++ tailWord_4603350).sum := by decide
  have hdescent : baseEnd_4603350 < baseStart_4603350 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603363 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 1, 5]
def baseStart_4603363 : Nat := 118140960795 + 4603363 * 2 ^ 59
def prefixEnd_4603363 : Nat := 4983230072969 + 3 ^ 40 * 4603363 * 2
def baseEnd_4603363 : Nat := 787912615374392684930675

theorem tailTrace_4603363 : CollatzResearch.WordTrace tailWord_4603363 prefixEnd_4603363 787912615374392684930675 := by
  unfold tailWord_4603363
  simp only [CollatzResearch.WordTrace]
  refine ⟨167898442021809517653582743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111932294681206345102388495 167898442021809517653582743)
  ·
    refine ⟨251847663032714276480374115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167898442021809517653582743 251847663032714276480374115)
    ·
      refine ⟨377771494549071414720561173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251847663032714276480374115 377771494549071414720561173)
      ·
        refine ⟨17708038806987722565026305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 377771494549071414720561173 17708038806987722565026305)
        ·
          refine ⟨13281029105240791923769729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17708038806987722565026305 13281029105240791923769729)
          ·
            refine ⟨9960771828930593942827297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13281029105240791923769729 9960771828930593942827297)
            ·
              refine ⟨7470578871697945457120473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9960771828930593942827297 7470578871697945457120473)
              ·
                refine ⟨5602934153773459092840355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7470578871697945457120473 5602934153773459092840355)
                ·
                  refine ⟨8404401230660188639260533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5602934153773459092840355 8404401230660188639260533)
                  ·
                    refine ⟨787912615374392684930675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8404401230660188639260533 787912615374392684930675)
                    ·
                      rfl

theorem cell23_4603363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 5].length) (baseStart_4603363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603363 prefixEnd_4603363 := by exact prefixLift 4603363
  have htrace : WordTrace (prefixWord ++ tailWord_4603363) baseStart_4603363 baseEnd_4603363 := by
    simpa [prefixWord, tailWord_4603363, baseEnd_4603363] using wordTrace_append hprefix tailTrace_4603363
  have hstable : (prefixWord ++ tailWord_4603363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603363).length < 2 ^ (prefixWord ++ tailWord_4603363).sum := by decide
  have hdescent : baseEnd_4603363 < baseStart_4603363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603376 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 4, 4]
def baseStart_4603376 : Nat := 118140960795 + 4603376 * 2 ^ 59
def prefixEnd_4603376 : Nat := 4983230072969 + 3 ^ 40 * 4603376 * 2
def baseEnd_4603376 : Nat := 787914840457228834643155

theorem tailTrace_4603376 : CollatzResearch.WordTrace tailWord_4603376 prefixEnd_4603376 787914840457228834643155 := by
  unfold tailWord_4603376
  simp only [CollatzResearch.WordTrace]
  refine ⟨83949458085381210436902991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111932610780508280582537321 83949458085381210436902991)
  ·
    refine ⟨125924187128071815655354487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83949458085381210436902991 125924187128071815655354487)
    ·
      refine ⟨188886280692107723483031731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125924187128071815655354487 188886280692107723483031731)
      ·
        refine ⟨283329421038161585224547597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188886280692107723483031731 283329421038161585224547597)
        ·
          refine ⟨106248532889310594459205349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283329421038161585224547597 106248532889310594459205349)
          ·
            refine ⟨19921599916745736461101003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106248532889310594459205349 19921599916745736461101003)
            ·
              refine ⟨29882399875118604691651505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19921599916745736461101003 29882399875118604691651505)
              ·
                refine ⟨22411799906338953518738629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29882399875118604691651505 22411799906338953518738629)
                ·
                  refine ⟨4202212482438553784763493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22411799906338953518738629 4202212482438553784763493)
                  ·
                    refine ⟨787914840457228834643155, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202212482438553784763493 787914840457228834643155)
                    ·
                      rfl

theorem cell23_4603376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 4].length) (baseStart_4603376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603376 prefixEnd_4603376 := by exact prefixLift 4603376
  have htrace : WordTrace (prefixWord ++ tailWord_4603376) baseStart_4603376 baseEnd_4603376 := by
    simpa [prefixWord, tailWord_4603376, baseEnd_4603376] using wordTrace_append hprefix tailTrace_4603376
  have hstable : (prefixWord ++ tailWord_4603376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603376).length < 2 ^ (prefixWord ++ tailWord_4603376).sum := by decide
  have hdescent : baseEnd_4603376 < baseStart_4603376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603377 : List Nat := [1, 2, 2, 2, 3, 4, 1, 3, 1, 1, 3]
def baseStart_4603377 : Nat := 118140960795 + 4603377 * 2 ^ 59
def prefixEnd_4603377 : Nat := 4983230072969 + 3 ^ 40 * 4603377 * 2
def baseEnd_4603377 : Nat := 2363745034852341000016961

theorem tailTrace_4603377 : CollatzResearch.WordTrace tailWord_4603377 prefixEnd_4603377 2363745034852341000016961 := by
  unfold tailWord_4603377
  simp only [CollatzResearch.WordTrace]
  refine ⟨167898952643758798044592385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111932635095839198696394923 167898952643758798044592385)
  ·
    refine ⟨125924214482819098533444289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167898952643758798044592385 125924214482819098533444289)
    ·
      refine ⟨94443160862114323900083217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125924214482819098533444289 94443160862114323900083217)
      ·
        refine ⟨70832370646585742925062413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94443160862114323900083217 70832370646585742925062413)
        ·
          refine ⟨26562138992469653596898405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70832370646585742925062413 26562138992469653596898405)
          ·
            refine ⟨4980401061088060049418451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26562138992469653596898405 4980401061088060049418451)
            ·
              refine ⟨7470601591632090074127677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4980401061088060049418451 7470601591632090074127677)
              ·
                refine ⟨2801475596862033777797879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7470601591632090074127677 2801475596862033777797879)
                ·
                  refine ⟨4202213395293050666696819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801475596862033777797879 4202213395293050666696819)
                  ·
                    refine ⟨6303320092939576000045229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4202213395293050666696819 6303320092939576000045229)
                    ·
                      refine ⟨2363745034852341000016961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6303320092939576000045229 2363745034852341000016961)
                      ·
                        rfl

theorem cell23_4603377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_4603377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603377 prefixEnd_4603377 := by exact prefixLift 4603377
  have htrace : WordTrace (prefixWord ++ tailWord_4603377) baseStart_4603377 baseEnd_4603377 := by
    simpa [prefixWord, tailWord_4603377, baseEnd_4603377] using wordTrace_append hprefix tailTrace_4603377
  have hstable : (prefixWord ++ tailWord_4603377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603377).length < 2 ^ (prefixWord ++ tailWord_4603377).sum := by decide
  have hdescent : baseEnd_4603377 < baseStart_4603377 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603386 : List Nat := [3, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_4603386 : Nat := 118140960795 + 4603386 * 2 ^ 59
def prefixEnd_4603386 : Nat := 4983230072969 + 3 ^ 40 * 4603386 * 2
def baseEnd_4603386 : Nat := 2363749656178231464804419

theorem tailTrace_4603386 : CollatzResearch.WordTrace tailWord_4603386 prefixEnd_4603386 2363749656178231464804419 := by
  unfold tailWord_4603386
  simp only [CollatzResearch.WordTrace]
  refine ⟨41974820225181548145417503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111932853933817461721113341 41974820225181548145417503)
  ·
    refine ⟨62962230337772322218126255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41974820225181548145417503 62962230337772322218126255)
    ·
      refine ⟨94443345506658483327189383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62962230337772322218126255 94443345506658483327189383)
      ·
        refine ⟨141665018259987724990784075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94443345506658483327189383 141665018259987724990784075)
        ·
          refine ⟨212497527389981587486176113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141665018259987724990784075 212497527389981587486176113)
          ·
            refine ⟨159373145542486190614632085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212497527389981587486176113 159373145542486190614632085)
            ·
              refine ⟨7470616197304040185060879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 159373145542486190614632085 7470616197304040185060879)
              ·
                refine ⟨11205924295956060277591319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7470616197304040185060879 11205924295956060277591319)
                ·
                  refine ⟨16808886443934090416386979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11205924295956060277591319 16808886443934090416386979)
                  ·
                    refine ⟨25213329665901135624580469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16808886443934090416386979 25213329665901135624580469)
                    ·
                      refine ⟨2363749656178231464804419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25213329665901135624580469 2363749656178231464804419)
                      ·
                        rfl

theorem cell23_4603386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_4603386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603386 prefixEnd_4603386 := by exact prefixLift 4603386
  have htrace : WordTrace (prefixWord ++ tailWord_4603386) baseStart_4603386 baseEnd_4603386 := by
    simpa [prefixWord, tailWord_4603386, baseEnd_4603386] using wordTrace_append hprefix tailTrace_4603386
  have hstable : (prefixWord ++ tailWord_4603386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603386).length < 2 ^ (prefixWord ++ tailWord_4603386).sum := by decide
  have hdescent : baseEnd_4603386 < baseStart_4603386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603389 : List Nat := [1, 4, 1, 1, 1, 4, 11]
def baseStart_4603389 : Nat := 118140960795 + 4603389 * 2 ^ 59
def prefixEnd_4603389 : Nat := 4983230072969 + 3 ^ 40 * 4603389 * 2
def baseEnd_4603389 : Nat := 29182113538520925346505

theorem tailTrace_4603389 : CollatzResearch.WordTrace tailWord_4603389 prefixEnd_4603389 29182113538520925346505 := by
  unfold tailWord_4603389
  simp only [CollatzResearch.WordTrace]
  refine ⟨167899390319715324094029221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111932926879810216062686147 167899390319715324094029221)
  ·
    refine ⟨31481135684946623267630479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167899390319715324094029221 31481135684946623267630479)
    ·
      refine ⟨47221703527419934901445719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31481135684946623267630479 47221703527419934901445719)
      ·
        refine ⟨70832555291129902352168579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47221703527419934901445719 70832555291129902352168579)
        ·
          refine ⟨106248832936694853528252869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70832555291129902352168579 106248832936694853528252869)
          ·
            refine ⟨19921656175630285036547413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106248832936694853528252869 19921656175630285036547413)
            ·
              refine ⟨29182113538520925346505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19921656175630285036547413 29182113538520925346505)
              ·
                rfl

theorem cell23_4603389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 11].length) (baseStart_4603389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603389 prefixEnd_4603389 := by exact prefixLift 4603389
  have htrace : WordTrace (prefixWord ++ tailWord_4603389) baseStart_4603389 baseEnd_4603389 := by
    simpa [prefixWord, tailWord_4603389, baseEnd_4603389] using wordTrace_append hprefix tailTrace_4603389
  have hstable : (prefixWord ++ tailWord_4603389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603389).length < 2 ^ (prefixWord ++ tailWord_4603389).sum := by decide
  have hdescent : baseEnd_4603389 < baseStart_4603389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603400 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 3, 2, 2]
def baseStart_4603400 : Nat := 118140960795 + 4603400 * 2 ^ 59
def prefixEnd_4603400 : Nat := 4983230072969 + 3 ^ 40 * 4603400 * 2
def baseEnd_4603400 : Nat := 2363756844907394410029355

theorem tailTrace_4603400 : CollatzResearch.WordTrace tailWord_4603400 prefixEnd_4603400 2363756844907394410029355 := by
  unfold tailWord_4603400
  simp only [CollatzResearch.WordTrace]
  refine ⟨83949895761337736486339827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111933194348450315315119769 83949895761337736486339827)
  ·
    refine ⟨125924843642006604729509741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83949895761337736486339827 125924843642006604729509741)
    ·
      refine ⟨47221816365752476773566153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125924843642006604729509741 47221816365752476773566153)
      ·
        refine ⟨35416362274314357580174615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47221816365752476773566153 35416362274314357580174615)
        ·
          refine ⟨53124543411471536370261923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35416362274314357580174615 53124543411471536370261923)
          ·
            refine ⟨79686815117207304555392885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53124543411471536370261923 79686815117207304555392885)
            ·
              refine ⟨7470638917238184802068083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79686815117207304555392885 7470638917238184802068083)
              ·
                refine ⟨11205958375857277203102125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7470638917238184802068083 11205958375857277203102125)
                ·
                  refine ⟨4202234390946478951163297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11205958375857277203102125 4202234390946478951163297)
                  ·
                    refine ⟨3151675793209859213372473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4202234390946478951163297 3151675793209859213372473)
                    ·
                      refine ⟨2363756844907394410029355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3151675793209859213372473 2363756844907394410029355)
                      ·
                        rfl

theorem cell23_4603400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 3, 2, 2].length) (baseStart_4603400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603400 prefixEnd_4603400 := by exact prefixLift 4603400
  have htrace : WordTrace (prefixWord ++ tailWord_4603400) baseStart_4603400 baseEnd_4603400 := by
    simpa [prefixWord, tailWord_4603400, baseEnd_4603400] using wordTrace_append hprefix tailTrace_4603400
  have hstable : (prefixWord ++ tailWord_4603400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603400).length < 2 ^ (prefixWord ++ tailWord_4603400).sum := by decide
  have hdescent : baseEnd_4603400 < baseStart_4603400 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603409 : List Nat := [1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 6]
def baseStart_4603409 : Nat := 118140960795 + 4603409 * 2 ^ 59
def prefixEnd_4603409 : Nat := 4983230072969 + 3 ^ 40 * 4603409 * 2
def baseEnd_4603409 : Nat := 2363761466233284874816813

theorem tailTrace_4603409 : CollatzResearch.WordTrace tailWord_4603409 prefixEnd_4603409 2363761466233284874816813 := by
  unfold tailWord_4603409
  simp only [CollatzResearch.WordTrace]
  refine ⟨167900119779642867509757281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111933413186428578339838187 167900119779642867509757281)
  ·
    refine ⟨125925089834732150632317961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167900119779642867509757281 125925089834732150632317961)
    ·
      refine ⟨94443817376049112974238471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125925089834732150632317961 94443817376049112974238471)
      ·
        refine ⟨141665726064073669461357707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94443817376049112974238471 141665726064073669461357707)
        ·
          refine ⟨212498589096110504192036561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141665726064073669461357707 212498589096110504192036561)
          ·
            refine ⟨159373941822082878144027421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212498589096110504192036561 159373941822082878144027421)
            ·
              refine ⟨59765228183281079304010283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159373941822082878144027421 59765228183281079304010283)
              ·
                refine ⟨89647842274921618956015425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59765228183281079304010283 89647842274921618956015425)
                ·
                  refine ⟨67235881706191214217011569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89647842274921618956015425 67235881706191214217011569)
                  ·
                    refine ⟨50426911279643410662758677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 67235881706191214217011569 50426911279643410662758677)
                    ·
                      refine ⟨2363761466233284874816813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50426911279643410662758677 2363761466233284874816813)
                      ·
                        rfl

theorem cell23_4603409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_4603409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603409 prefixEnd_4603409 := by exact prefixLift 4603409
  have htrace : WordTrace (prefixWord ++ tailWord_4603409) baseStart_4603409 baseEnd_4603409 := by
    simpa [prefixWord, tailWord_4603409, baseEnd_4603409] using wordTrace_append hprefix tailTrace_4603409
  have hstable : (prefixWord ++ tailWord_4603409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603409).length < 2 ^ (prefixWord ++ tailWord_4603409).sum := by decide
  have hdescent : baseEnd_4603409 < baseStart_4603409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603450 : List Nat := [3, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_4603450 : Nat := 118140960795 + 4603450 * 2 ^ 59
def prefixEnd_4603450 : Nat := 4983230072969 + 3 ^ 40 * 4603450 * 2
def baseEnd_4603450 : Nat := 2363782518940119214404125

theorem tailTrace_4603450 : CollatzResearch.WordTrace tailWord_4603450 prefixEnd_4603450 2363782518940119214404125 := by
  unfold tailWord_4603450
  simp only [CollatzResearch.WordTrace]
  refine ⟨41975403793123582877999951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111934410114996221007999869 41975403793123582877999951)
  ·
    refine ⟨62963105689685374316999927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41975403793123582877999951 62963105689685374316999927)
    ·
      refine ⟨94444658534528061475499891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62963105689685374316999927 94444658534528061475499891)
      ·
        refine ⟨141666987801792092213249837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94444658534528061475499891 141666987801792092213249837)
        ·
          refine ⟨53125120425672034579968689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141666987801792092213249837 53125120425672034579968689)
          ·
            refine ⟨39843840319254025934976517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53125120425672034579968689 39843840319254025934976517)
            ·
              refine ⟨7470720059860129862808097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39843840319254025934976517 7470720059860129862808097)
              ·
                refine ⟨5603040044895097397106073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7470720059860129862808097 5603040044895097397106073)
                ·
                  refine ⟨4202280033671323047829555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5603040044895097397106073 4202280033671323047829555)
                  ·
                    refine ⟨6303420050506984571744333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4202280033671323047829555 6303420050506984571744333)
                    ·
                      refine ⟨2363782518940119214404125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6303420050506984571744333 2363782518940119214404125)
                      ·
                        rfl

theorem cell23_4603450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_4603450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603450 prefixEnd_4603450 := by exact prefixLift 4603450
  have htrace : WordTrace (prefixWord ++ tailWord_4603450) baseStart_4603450 baseEnd_4603450 := by
    simpa [prefixWord, tailWord_4603450, baseEnd_4603450] using wordTrace_append hprefix tailTrace_4603450
  have hstable : (prefixWord ++ tailWord_4603450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603450).length < 2 ^ (prefixWord ++ tailWord_4603450).sum := by decide
  have hdescent : baseEnd_4603450 < baseStart_4603450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603466 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 2, 6]
def baseStart_4603466 : Nat := 118140960795 + 4603466 * 2 ^ 59
def prefixEnd_4603466 : Nat := 4983230072969 + 3 ^ 40 * 4603466 * 2
def baseEnd_4603466 : Nat := 787930244876863717268017

theorem tailTrace_4603466 : CollatzResearch.WordTrace tailWord_4603466 prefixEnd_4603466 787930244876863717268017 := by
  unfold tailWord_4603466
  simp only [CollatzResearch.WordTrace]
  refine ⟨41975549685109091561145563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111934799160290910829721501 41975549685109091561145563)
  ·
    refine ⟨62963324527663637341718345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41975549685109091561145563 62963324527663637341718345)
    ·
      refine ⟨47222493395747728006288759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62963324527663637341718345 47222493395747728006288759)
      ·
        refine ⟨70833740093621592009433139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47222493395747728006288759 70833740093621592009433139)
        ·
          refine ⟨106250610140432388014149709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70833740093621592009433139 106250610140432388014149709)
          ·
            refine ⟨39843978802662145505306141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106250610140432388014149709 39843978802662145505306141)
            ·
              refine ⟨14941492050998304564489803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39843978802662145505306141 14941492050998304564489803)
              ·
                refine ⟨22412238076497456846734705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14941492050998304564489803 22412238076497456846734705)
                ·
                  refine ⟨16809178557373092635051029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22412238076497456846734705 16809178557373092635051029)
                  ·
                    refine ⟨787930244876863717268017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16809178557373092635051029 787930244876863717268017)
                    ·
                      rfl

theorem cell23_4603466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_4603466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603466 prefixEnd_4603466 := by exact prefixLift 4603466
  have htrace : WordTrace (prefixWord ++ tailWord_4603466) baseStart_4603466 baseEnd_4603466 := by
    simpa [prefixWord, tailWord_4603466, baseEnd_4603466] using wordTrace_append hprefix tailTrace_4603466
  have hstable : (prefixWord ++ tailWord_4603466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603466).length < 2 ^ (prefixWord ++ tailWord_4603466).sum := by decide
  have hdescent : baseEnd_4603466 < baseStart_4603466 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603513 : List Nat := [1, 2, 1, 3, 3, 1, 1, 6, 5]
def baseStart_4603513 : Nat := 118140960795 + 4603513 * 2 ^ 59
def prefixEnd_4603513 : Nat := 4983230072969 + 3 ^ 40 * 4603513 * 2
def baseEnd_4603513 : Nat := 262646096469039163101815

theorem tailTrace_4603513 : CollatzResearch.WordTrace tailWord_4603513 prefixEnd_4603513 262646096469039163101815 := by
  unfold tailWord_4603513
  simp only [CollatzResearch.WordTrace]
  refine ⟨167903912971266093271543193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111935941980844062181028795 167903912971266093271543193)
  ·
    refine ⟨125927934728449569953657395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167903912971266093271543193 125927934728449569953657395)
    ·
      refine ⟨188891902092674354930486093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125927934728449569953657395 188891902092674354930486093)
      ·
        refine ⟨70834463284752883098932285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188891902092674354930486093 70834463284752883098932285)
        ·
          refine ⟨26562923731782331162099607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70834463284752883098932285 26562923731782331162099607)
          ·
            refine ⟨39844385597673496743149411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26562923731782331162099607 39844385597673496743149411)
            ·
              refine ⟨59766578396510245114724117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39844385597673496743149411 59766578396510245114724117)
              ·
                refine ⟨2801558362336417739752693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59766578396510245114724117 2801558362336417739752693)
                ·
                  refine ⟨262646096469039163101815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2801558362336417739752693 262646096469039163101815)
                  ·
                    rfl

theorem cell23_4603513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 6, 5].length) (baseStart_4603513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603513 prefixEnd_4603513 := by exact prefixLift 4603513
  have htrace : WordTrace (prefixWord ++ tailWord_4603513) baseStart_4603513 baseEnd_4603513 := by
    simpa [prefixWord, tailWord_4603513, baseEnd_4603513] using wordTrace_append hprefix tailTrace_4603513
  have hstable : (prefixWord ++ tailWord_4603513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603513).length < 2 ^ (prefixWord ++ tailWord_4603513).sum := by decide
  have hdescent : baseEnd_4603513 < baseStart_4603513 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603524 : List Nat := [2, 3, 2, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_4603524 : Nat := 118140960795 + 4603524 * 2 ^ 59
def prefixEnd_4603524 : Nat := 4983230072969 + 3 ^ 40 * 4603524 * 2
def baseEnd_4603524 : Nat := 2363820516508551924878785

theorem tailTrace_4603524 : CollatzResearch.WordTrace tailWord_4603524 prefixEnd_4603524 2363820516508551924878785 := by
  unfold tailWord_4603524
  simp only [CollatzResearch.WordTrace]
  refine ⟨83952157087113121075096813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111936209449484161433462417 83952157087113121075096813)
  ·
    refine ⟨31482058907667420403161305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83952157087113121075096813 31482058907667420403161305)
    ·
      refine ⟨23611544180750565302370979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31482058907667420403161305 23611544180750565302370979)
      ·
        refine ⟨35417316271125847953556469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23611544180750565302370979 35417316271125847953556469)
        ·
          refine ⟨3320373400418048245645919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35417316271125847953556469 3320373400418048245645919)
          ·
            refine ⟨4980560100627072368468879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320373400418048245645919 4980560100627072368468879)
            ·
              refine ⟨7470840150940608552703319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4980560100627072368468879 7470840150940608552703319)
              ·
                refine ⟨11206260226410912829054979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7470840150940608552703319 11206260226410912829054979)
                ·
                  refine ⟨16809390339616369243582469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11206260226410912829054979 16809390339616369243582469)
                  ·
                    refine ⟨3151760688678069233171713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16809390339616369243582469 3151760688678069233171713)
                    ·
                      refine ⟨2363820516508551924878785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3151760688678069233171713 2363820516508551924878785)
                      ·
                        rfl

theorem cell23_4603524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_4603524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603524 prefixEnd_4603524 := by exact prefixLift 4603524
  have htrace : WordTrace (prefixWord ++ tailWord_4603524) baseStart_4603524 baseEnd_4603524 := by
    simpa [prefixWord, tailWord_4603524, baseEnd_4603524] using wordTrace_append hprefix tailTrace_4603524
  have hstable : (prefixWord ++ tailWord_4603524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603524).length < 2 ^ (prefixWord ++ tailWord_4603524).sum := by decide
  have hdescent : baseEnd_4603524 < baseStart_4603524 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603576 : List Nat := [2, 1, 2, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_4603576 : Nat := 118140960795 + 4603576 * 2 ^ 59
def prefixEnd_4603576 : Nat := 4983230072969 + 3 ^ 40 * 4603576 * 2
def baseEnd_4603576 : Nat := 2363847217502585721428545

theorem tailTrace_4603576 : CollatzResearch.WordTrace tailWord_4603576 prefixEnd_4603576 2363847217502585721428545 := by
  unfold tailWord_4603576
  simp only [CollatzResearch.WordTrace]
  refine ⟨83953105385018927515543291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111937473846691903354057721 83953105385018927515543291)
  ·
    refine ⟨125929658077528391273314937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83953105385018927515543291 125929658077528391273314937)
    ·
      refine ⟨94447243558146293454986203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125929658077528391273314937 94447243558146293454986203)
      ·
        refine ⟨141670865337219440182479305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94447243558146293454986203 141670865337219440182479305)
        ·
          refine ⟨106253149002914580136859479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141670865337219440182479305 106253149002914580136859479)
          ·
            refine ⟨159379723504371870205289219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106253149002914580136859479 159379723504371870205289219)
            ·
              refine ⟨239069585256557805307933829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159379723504371870205289219 239069585256557805307933829)
              ·
                refine ⟨44825547235604588495237593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239069585256557805307933829 44825547235604588495237593)
                ·
                  refine ⟨33619160426703441371428195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44825547235604588495237593 33619160426703441371428195)
                  ·
                    refine ⟨50428740640055162057142293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33619160426703441371428195 50428740640055162057142293)
                    ·
                      refine ⟨2363847217502585721428545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50428740640055162057142293 2363847217502585721428545)
                      ·
                        rfl

theorem cell23_4603576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_4603576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603576 prefixEnd_4603576 := by exact prefixLift 4603576
  have htrace : WordTrace (prefixWord ++ tailWord_4603576) baseStart_4603576 baseEnd_4603576 := by
    simpa [prefixWord, tailWord_4603576, baseEnd_4603576] using wordTrace_append hprefix tailTrace_4603576
  have hstable : (prefixWord ++ tailWord_4603576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603576).length < 2 ^ (prefixWord ++ tailWord_4603576).sum := by decide
  have hdescent : baseEnd_4603576 < baseStart_4603576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603583 : List Nat := [1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 3]
def baseStart_4603583 : Nat := 118140960795 + 4603583 * 2 ^ 59
def prefixEnd_4603583 : Nat := 4983230072969 + 3 ^ 40 * 4603583 * 2
def baseEnd_4603583 : Nat := 2363850811867167194041013

theorem tailTrace_4603583 : CollatzResearch.WordTrace tailWord_4603583 prefixEnd_4603583 2363850811867167194041013 := by
  unfold tailWord_4603583
  simp only [CollatzResearch.WordTrace]
  refine ⟨167906466081012495226591403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111937644054008330151060935 167906466081012495226591403)
  ·
    refine ⟨251859699121518742839887105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167906466081012495226591403 251859699121518742839887105)
    ·
      refine ⟨188894774341139057129915329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251859699121518742839887105 188894774341139057129915329)
      ·
        refine ⟨141671080755854292847436497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188894774341139057129915329 141671080755854292847436497)
        ·
          refine ⟨106253310566890719635577373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141671080755854292847436497 106253310566890719635577373)
          ·
            refine ⟨39844991462584019863341515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106253310566890719635577373 39844991462584019863341515)
            ·
              refine ⟨59767487193876029795012273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39844991462584019863341515 59767487193876029795012273)
              ·
                refine ⟨44825615395407022346259205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59767487193876029795012273 44825615395407022346259205)
                ·
                  refine ⟨8404802886638816689923601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44825615395407022346259205 8404802886638816689923601)
                  ·
                    refine ⟨6303602164979112517442701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8404802886638816689923601 6303602164979112517442701)
                    ·
                      refine ⟨2363850811867167194041013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6303602164979112517442701 2363850811867167194041013)
                      ·
                        rfl

theorem cell23_4603583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_4603583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603583 prefixEnd_4603583 := by exact prefixLift 4603583
  have htrace : WordTrace (prefixWord ++ tailWord_4603583) baseStart_4603583 baseEnd_4603583 := by
    simpa [prefixWord, tailWord_4603583, baseEnd_4603583] using wordTrace_append hprefix tailTrace_4603583
  have hstable : (prefixWord ++ tailWord_4603583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603583).length < 2 ^ (prefixWord ++ tailWord_4603583).sum := by decide
  have hdescent : baseEnd_4603583 < baseStart_4603583 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603597 : List Nat := [1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 4]
def baseStart_4603597 : Nat := 118140960795 + 4603597 * 2 ^ 59
def prefixEnd_4603597 : Nat := 4983230072969 + 3 ^ 40 * 4603597 * 2
def baseEnd_4603597 : Nat := 2363858000596330139265949

theorem tailTrace_4603597 : CollatzResearch.WordTrace tailWord_4603597 prefixEnd_4603597 2363858000596330139265949 := by
  unfold tailWord_4603597
  simp only [CollatzResearch.WordTrace]
  refine ⟨167906976702961775617601045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111937984468641183745067363 167906976702961775617601045)
  ·
    refine ⟨7870639532951333232075049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 167906976702961775617601045 7870639532951333232075049)
    ·
      refine ⟨5902979649713499924056287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7870639532951333232075049 5902979649713499924056287)
      ·
        refine ⟨8854469474570249886084431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5902979649713499924056287 8854469474570249886084431)
        ·
          refine ⟨13281704211855374829126647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8854469474570249886084431 13281704211855374829126647)
          ·
            refine ⟨19922556317783062243689971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13281704211855374829126647 19922556317783062243689971)
            ·
              refine ⟨29883834476674593365534957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19922556317783062243689971 29883834476674593365534957)
              ·
                refine ⟨11206437928752972512075609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29883834476674593365534957 11206437928752972512075609)
                ·
                  refine ⟨8404828446564729384056707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11206437928752972512075609 8404828446564729384056707)
                  ·
                    refine ⟨12607242669847094076085061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8404828446564729384056707 12607242669847094076085061)
                    ·
                      refine ⟨2363858000596330139265949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12607242669847094076085061 2363858000596330139265949)
                      ·
                        rfl

theorem cell23_4603597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 3, 2, 1, 4].length) (baseStart_4603597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603597 prefixEnd_4603597 := by exact prefixLift 4603597
  have htrace : WordTrace (prefixWord ++ tailWord_4603597) baseStart_4603597 baseEnd_4603597 := by
    simpa [prefixWord, tailWord_4603597, baseEnd_4603597] using wordTrace_append hprefix tailTrace_4603597
  have hstable : (prefixWord ++ tailWord_4603597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603597).length < 2 ^ (prefixWord ++ tailWord_4603597).sum := by decide
  have hdescent : baseEnd_4603597 < baseStart_4603597 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603624 : List Nat := [2, 1, 4, 1, 3, 1, 4, 2, 1, 4]
def baseStart_4603624 : Nat := 118140960795 + 4603624 * 2 ^ 59
def prefixEnd_4603624 : Nat := 4983230072969 + 3 ^ 40 * 4603624 * 2
def baseEnd_4603624 : Nat := 787957288191333844542775

theorem tailTrace_4603624 : CollatzResearch.WordTrace tailWord_4603624 prefixEnd_4603624 787957288191333844542775 := by
  unfold tailWord_4603624
  simp only [CollatzResearch.WordTrace]
  refine ⟨83953980736931979614416963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111938640982575972819222617 83953980736931979614416963)
  ·
    refine ⟨125930971105397969421625445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83953980736931979614416963 125930971105397969421625445)
    ·
      refine ⟨23612057082262119266554771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125930971105397969421625445 23612057082262119266554771)
      ·
        refine ⟨35418085623393178899832157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23612057082262119266554771 35418085623393178899832157)
        ·
          refine ⟨13281782108772442087437059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35418085623393178899832157 13281782108772442087437059)
          ·
            refine ⟨19922673163158663131155589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13281782108772442087437059 19922673163158663131155589)
            ·
              refine ⟨3735501218092249337091673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19922673163158663131155589 3735501218092249337091673)
              ·
                refine ⟨2801625913569187002818755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3735501218092249337091673 2801625913569187002818755)
                ·
                  refine ⟨4202438870353780504228133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801625913569187002818755 4202438870353780504228133)
                  ·
                    refine ⟨787957288191333844542775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202438870353780504228133 787957288191333844542775)
                    ·
                      rfl

theorem cell23_4603624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 4].length) (baseStart_4603624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603624 prefixEnd_4603624 := by exact prefixLift 4603624
  have htrace : WordTrace (prefixWord ++ tailWord_4603624) baseStart_4603624 baseEnd_4603624 := by
    simpa [prefixWord, tailWord_4603624, baseEnd_4603624] using wordTrace_append hprefix tailTrace_4603624
  have hstable : (prefixWord ++ tailWord_4603624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603624).length < 2 ^ (prefixWord ++ tailWord_4603624).sum := by decide
  have hdescent : baseEnd_4603624 < baseStart_4603624 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603633 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 3, 5]
def baseStart_4603633 : Nat := 118140960795 + 4603633 * 2 ^ 59
def prefixEnd_4603633 : Nat := 4983230072969 + 3 ^ 40 * 4603633 * 2
def baseEnd_4603633 : Nat := 787958828633297332805261

theorem tailTrace_4603633 : CollatzResearch.WordTrace tailWord_4603633 prefixEnd_4603633 787958828633297332805261 := by
  unfold tailWord_4603633
  simp only [CollatzResearch.WordTrace]
  refine ⟨167908289730831353765911553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111938859820554235843941035 167908289730831353765911553)
  ·
    refine ⟨125931217298123515324433665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167908289730831353765911553 125931217298123515324433665)
    ·
      refine ⟨94448412973592636493325249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125931217298123515324433665 94448412973592636493325249)
      ·
        refine ⟨70836309730194477369993937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94448412973592636493325249 70836309730194477369993937)
        ·
          refine ⟨53127232297645858027495453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70836309730194477369993937 53127232297645858027495453)
          ·
            refine ⟨19922712111617196760310795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53127232297645858027495453 19922712111617196760310795)
            ·
              refine ⟨29884068167425795140466193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19922712111617196760310795 29884068167425795140466193)
              ·
                refine ⟨22413051125569346355349645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29884068167425795140466193 22413051125569346355349645)
                ·
                  refine ⟨8404894172088504883256117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22413051125569346355349645 8404894172088504883256117)
                  ·
                    refine ⟨787958828633297332805261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8404894172088504883256117 787958828633297332805261)
                    ·
                      rfl

theorem cell23_4603633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 5].length) (baseStart_4603633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603633 prefixEnd_4603633 := by exact prefixLift 4603633
  have htrace : WordTrace (prefixWord ++ tailWord_4603633) baseStart_4603633 baseEnd_4603633 := by
    simpa [prefixWord, tailWord_4603633, baseEnd_4603633] using wordTrace_append hprefix tailTrace_4603633
  have hstable : (prefixWord ++ tailWord_4603633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603633).length < 2 ^ (prefixWord ++ tailWord_4603633).sum := by decide
  have hdescent : baseEnd_4603633 < baseStart_4603633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603650 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_4603650 : Nat := 118140960795 + 4603650 * 2 ^ 59
def prefixEnd_4603650 : Nat := 4983230072969 + 3 ^ 40 * 4603650 * 2
def baseEnd_4603650 : Nat := 787961738357006143967735

theorem tailTrace_4603650 : CollatzResearch.WordTrace tailWord_4603650 prefixEnd_4603650 787961738357006143967735 := by
  unfold tailWord_4603650
  simp only [CollatzResearch.WordTrace]
  refine ⟨41977227442942441417320101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111939273181179843779520269 41977227442942441417320101)
  ·
    refine ⟨7870730145551707765747519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41977227442942441417320101 7870730145551707765747519)
    ·
      refine ⟨11806095218327561648621279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7870730145551707765747519 11806095218327561648621279)
      ·
        refine ⟨17709142827491342472931919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11806095218327561648621279 17709142827491342472931919)
        ·
          refine ⟨26563714241237013709397879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17709142827491342472931919 26563714241237013709397879)
          ·
            refine ⟨39845571361855520564096819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26563714241237013709397879 39845571361855520564096819)
            ·
              refine ⟨59768357042783280846145229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39845571361855520564096819 59768357042783280846145229)
              ·
                refine ⟨22413133891043730317304461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59768357042783280846145229 22413133891043730317304461)
                ·
                  refine ⟨8404925209141398868989173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22413133891043730317304461 8404925209141398868989173)
                  ·
                    refine ⟨787961738357006143967735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8404925209141398868989173 787961738357006143967735)
                    ·
                      rfl

theorem cell23_4603650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_4603650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603650 prefixEnd_4603650 := by exact prefixLift 4603650
  have htrace : WordTrace (prefixWord ++ tailWord_4603650) baseStart_4603650 baseEnd_4603650 := by
    simpa [prefixWord, tailWord_4603650, baseEnd_4603650] using wordTrace_append hprefix tailTrace_4603650
  have hstable : (prefixWord ++ tailWord_4603650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603650).length < 2 ^ (prefixWord ++ tailWord_4603650).sum := by decide
  have hdescent : baseEnd_4603650 < baseStart_4603650 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603680 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 4, 4]
def baseStart_4603680 : Nat := 118140960795 + 4603680 * 2 ^ 59
def prefixEnd_4603680 : Nat := 4983230072969 + 3 ^ 40 * 4603680 * 2
def baseEnd_4603680 : Nat := 787966873163551104842689

theorem tailTrace_4603680 : CollatzResearch.WordTrace tailWord_4603680 prefixEnd_4603680 787966873163551104842689 := by
  unfold tailWord_4603680
  simp only [CollatzResearch.WordTrace]
  refine ⟨83955001980830540396436247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111940002641107387195248329 83955001980830540396436247)
  ·
    refine ⟨125932502971245810594654371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83955001980830540396436247 125932502971245810594654371)
    ·
      refine ⟨188898754456868715891981557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125932502971245810594654371 188898754456868715891981557)
      ·
        refine ⟨17709258230331442114873271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188898754456868715891981557 17709258230331442114873271)
        ·
          refine ⟨26563887345497163172309907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17709258230331442114873271 26563887345497163172309907)
          ·
            refine ⟨39845831018245744758464861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26563887345497163172309907 39845831018245744758464861)
            ·
              refine ⟨14942186631842154284424323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39845831018245744758464861 14942186631842154284424323)
              ·
                refine ⟨22413279947763231426636485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14942186631842154284424323 22413279947763231426636485)
                ·
                  refine ⟨4202489990205605892494341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22413279947763231426636485 4202489990205605892494341)
                  ·
                    refine ⟨787966873163551104842689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202489990205605892494341 787966873163551104842689)
                    ·
                      rfl

theorem cell23_4603680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_4603680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603680 prefixEnd_4603680 := by exact prefixLift 4603680
  have htrace : WordTrace (prefixWord ++ tailWord_4603680) baseStart_4603680 baseEnd_4603680 := by
    simpa [prefixWord, tailWord_4603680, baseEnd_4603680] using wordTrace_append hprefix tailTrace_4603680
  have hstable : (prefixWord ++ tailWord_4603680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603680).length < 2 ^ (prefixWord ++ tailWord_4603680).sum := by decide
  have hdescent : baseEnd_4603680 < baseStart_4603680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603683 : List Nat := [1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4]
def baseStart_4603683 : Nat := 118140960795 + 4603683 * 2 ^ 59
def prefixEnd_4603683 : Nat := 4983230072969 + 3 ^ 40 * 4603683 * 2
def baseEnd_4603683 : Nat := 2363902159932616802790553

theorem tailTrace_4603683 : CollatzResearch.WordTrace tailWord_4603683 prefixEnd_4603683 2363902159932616802790553 := by
  unfold tailWord_4603683
  simp only [CollatzResearch.WordTrace]
  refine ⟨167910113380650212305231703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111940075587100141536821135 167910113380650212305231703)
  ·
    refine ⟨251865170070975318457847555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167910113380650212305231703 251865170070975318457847555)
    ·
      refine ⟨377797755106462977686771333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251865170070975318457847555 377797755106462977686771333)
      ·
        refine ⟨70837079082461808316269625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 377797755106462977686771333 70837079082461808316269625)
        ·
          refine ⟨53127809311846356237202219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70837079082461808316269625 53127809311846356237202219)
          ·
            refine ⟨79691713967769534355803329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53127809311846356237202219 79691713967769534355803329)
            ·
              refine ⟨59768785475827150766852497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79691713967769534355803329 59768785475827150766852497)
              ·
                refine ⟨44826589106870363075139373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59768785475827150766852497 44826589106870363075139373)
                ·
                  refine ⟨16809970915076386153177265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44826589106870363075139373 16809970915076386153177265)
                  ·
                    refine ⟨12607478186307289614882949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16809970915076386153177265 12607478186307289614882949)
                    ·
                      refine ⟨2363902159932616802790553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12607478186307289614882949 2363902159932616802790553)
                      ·
                        rfl

theorem cell23_4603683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_4603683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603683 prefixEnd_4603683 := by exact prefixLift 4603683
  have htrace : WordTrace (prefixWord ++ tailWord_4603683) baseStart_4603683 baseEnd_4603683 := by
    simpa [prefixWord, tailWord_4603683, baseEnd_4603683] using wordTrace_append hprefix tailTrace_4603683
  have hstable : (prefixWord ++ tailWord_4603683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603683).length < 2 ^ (prefixWord ++ tailWord_4603683).sum := by decide
  have hdescent : baseEnd_4603683 < baseStart_4603683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603710 : List Nat := [4, 2, 1, 2, 2, 2, 1, 9]
def baseStart_4603710 : Nat := 118140960795 + 4603710 * 2 ^ 59
def prefixEnd_4603710 : Nat := 4983230072969 + 3 ^ 40 * 4603710 * 2
def baseEnd_4603710 : Nat := 87552445330010673968627

theorem tailTrace_4603710 : CollatzResearch.WordTrace tailWord_4603710 prefixEnd_4603710 87552445330010673968627 := by
  unfold tailWord_4603710
  simp only [CollatzResearch.WordTrace]
  refine ⟨20988887268944049489558073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111940732101034930610976389 20988887268944049489558073)
  ·
    refine ⟨15741665451708037117168555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20988887268944049489558073 15741665451708037117168555)
    ·
      refine ⟨23612498177562055675752833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15741665451708037117168555 23612498177562055675752833)
      ·
        refine ⟨17709373633171541756814625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23612498177562055675752833 17709373633171541756814625)
        ·
          refine ⟨13282030224878656317610969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17709373633171541756814625 13282030224878656317610969)
          ·
            refine ⟨9961522668658992238208227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13282030224878656317610969 9961522668658992238208227)
            ·
              refine ⟨14942284002988488357312341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9961522668658992238208227 14942284002988488357312341)
              ·
                refine ⟨87552445330010673968627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14942284002988488357312341 87552445330010673968627)
                ·
                  rfl

theorem cell23_4603710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_4603710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603710 prefixEnd_4603710 := by exact prefixLift 4603710
  have htrace : WordTrace (prefixWord ++ tailWord_4603710) baseStart_4603710 baseEnd_4603710 := by
    simpa [prefixWord, tailWord_4603710, baseEnd_4603710] using wordTrace_append hprefix tailTrace_4603710
  have hstable : (prefixWord ++ tailWord_4603710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603710).length < 2 ^ (prefixWord ++ tailWord_4603710).sum := by decide
  have hdescent : baseEnd_4603710 < baseStart_4603710 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603737 : List Nat := [1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 3]
def baseStart_4603737 : Nat := 118140960795 + 4603737 * 2 ^ 59
def prefixEnd_4603737 : Nat := 4983230072969 + 3 ^ 40 * 4603737 * 2
def baseEnd_4603737 : Nat := 2363929887887959591515305

theorem tailTrace_4603737 : CollatzResearch.WordTrace tailWord_4603737 prefixEnd_4603737 2363929887887959591515305 := by
  unfold tailWord_4603737
  simp only [CollatzResearch.WordTrace]
  refine ⟨167912082922454579527697465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111941388614969719685131643 167912082922454579527697465)
  ·
    refine ⟨125934062191840934645773099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167912082922454579527697465 125934062191840934645773099)
    ·
      refine ⟨188901093287761401968659649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125934062191840934645773099 188901093287761401968659649)
      ·
        refine ⟨141675819965821051476494737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188901093287761401968659649 141675819965821051476494737)
        ·
          refine ⟨106256864974365788607371053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141675819965821051476494737 106256864974365788607371053)
          ·
            refine ⟨39846324365387170727764145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106256864974365788607371053 39846324365387170727764145)
            ·
              refine ⟨29884743274040378045823109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39846324365387170727764145 29884743274040378045823109)
              ·
                refine ⟨5603389363882570883591833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29884743274040378045823109 5603389363882570883591833)
                ·
                  refine ⟨4202542022911928162693875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5603389363882570883591833 4202542022911928162693875)
                  ·
                    refine ⟨6303813034367892244040813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4202542022911928162693875 6303813034367892244040813)
                    ·
                      refine ⟨2363929887887959591515305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6303813034367892244040813 2363929887887959591515305)
                      ·
                        rfl

theorem cell23_4603737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 4, 2, 1, 3].length) (baseStart_4603737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603737 prefixEnd_4603737 := by exact prefixLift 4603737
  have htrace : WordTrace (prefixWord ++ tailWord_4603737) baseStart_4603737 baseEnd_4603737 := by
    simpa [prefixWord, tailWord_4603737, baseEnd_4603737] using wordTrace_append hprefix tailTrace_4603737
  have hstable : (prefixWord ++ tailWord_4603737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603737).length < 2 ^ (prefixWord ++ tailWord_4603737).sum := by decide
  have hdescent : baseEnd_4603737 < baseStart_4603737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603753 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 2, 6]
def baseStart_4603753 : Nat := 118140960795 + 4603753 * 2 ^ 59
def prefixEnd_4603753 : Nat := 4983230072969 + 3 ^ 40 * 4603753 * 2
def baseEnd_4603753 : Nat := 787979367859477176305077

theorem tailTrace_4603753 : CollatzResearch.WordTrace tailWord_4603753 prefixEnd_4603753 787979367859477176305077 := by
  unfold tailWord_4603753
  simp only [CollatzResearch.WordTrace]
  refine ⟨167912666490396614260279913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111941777660264409506853275 167912666490396614260279913)
  ·
    refine ⟨125934499867797460695209935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167912666490396614260279913 125934499867797460695209935)
    ·
      refine ⟨188901749801696191042814903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125934499867797460695209935 188901749801696191042814903)
      ·
        refine ⟨283352624702544286564222355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188901749801696191042814903 283352624702544286564222355)
        ·
          refine ⟨425028937053816429846333533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283352624702544286564222355 425028937053816429846333533)
          ·
            refine ⟨159385851395181161192375075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 425028937053816429846333533 159385851395181161192375075)
            ·
              refine ⟨239078777092771741788562613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159385851395181161192375075 239078777092771741788562613)
              ·
                refine ⟨22413635352447350792677745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239078777092771741788562613 22413635352447350792677745)
                ·
                  refine ⟨16810226514335513094508309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22413635352447350792677745 16810226514335513094508309)
                  ·
                    refine ⟨787979367859477176305077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16810226514335513094508309 787979367859477176305077)
                    ·
                      rfl

theorem cell23_4603753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 6].length) (baseStart_4603753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603753 prefixEnd_4603753 := by exact prefixLift 4603753
  have htrace : WordTrace (prefixWord ++ tailWord_4603753) baseStart_4603753 baseEnd_4603753 := by
    simpa [prefixWord, tailWord_4603753, baseEnd_4603753] using wordTrace_append hprefix tailTrace_4603753
  have hstable : (prefixWord ++ tailWord_4603753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603753).length < 2 ^ (prefixWord ++ tailWord_4603753).sum := by decide
  have hdescent : baseEnd_4603753 < baseStart_4603753 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603780 : List Nat := [2, 3, 2, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4603780 : Nat := 118140960795 + 4603780 * 2 ^ 59
def prefixEnd_4603780 : Nat := 4983230072969 + 3 ^ 40 * 4603780 * 2
def baseEnd_4603780 : Nat := 2363951967556102923277607

theorem tailTrace_4603780 : CollatzResearch.WordTrace tailWord_4603780 prefixEnd_4603780 2363951967556102923277607 := by
  unfold tailWord_4603780
  simp only [CollatzResearch.WordTrace]
  refine ⟨83956825630649398935756397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111942434174199198581008529 83956825630649398935756397)
  ·
    refine ⟨31483809611493524600908649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83956825630649398935756397 31483809611493524600908649)
    ·
      refine ⟨23612857208620143450681487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31483809611493524600908649 23612857208620143450681487)
      ·
        refine ⟨35419285812930215176022231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23612857208620143450681487 35419285812930215176022231)
        ·
          refine ⟨53128928719395322764033347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35419285812930215176022231 53128928719395322764033347)
          ·
            refine ⟨79693393079092984146050021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53128928719395322764033347 79693393079092984146050021)
            ·
              refine ⟨14942511202329934527384379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79693393079092984146050021 14942511202329934527384379)
              ·
                refine ⟨22413766803494901791076569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14942511202329934527384379 22413766803494901791076569)
                ·
                  refine ⟨16810325102621176343307427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22413766803494901791076569 16810325102621176343307427)
                  ·
                    refine ⟨25215487653931764514961141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16810325102621176343307427 25215487653931764514961141)
                    ·
                      refine ⟨2363951967556102923277607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25215487653931764514961141 2363951967556102923277607)
                      ·
                        rfl

theorem cell23_4603780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4603780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603780 prefixEnd_4603780 := by exact prefixLift 4603780
  have htrace : WordTrace (prefixWord ++ tailWord_4603780) baseStart_4603780 baseEnd_4603780 := by
    simpa [prefixWord, tailWord_4603780, baseEnd_4603780] using wordTrace_append hprefix tailTrace_4603780
  have hstable : (prefixWord ++ tailWord_4603780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603780).length < 2 ^ (prefixWord ++ tailWord_4603780).sum := by decide
  have hdescent : baseEnd_4603780 < baseStart_4603780 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603793 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 7]
def baseStart_4603793 : Nat := 118140960795 + 4603793 * 2 ^ 59
def prefixEnd_4603793 : Nat := 4983230072969 + 3 ^ 40 * 4603793 * 2
def baseEnd_4603793 : Nat := 2363958642804611372415047

theorem tailTrace_4603793 : CollatzResearch.WordTrace tailWord_4603793 prefixEnd_4603793 2363958642804611372415047 := by
  unfold tailWord_4603793
  simp only [CollatzResearch.WordTrace]
  refine ⟨167914125410251701091736033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111942750273501134061157355 167914125410251701091736033)
  ·
    refine ⟨125935594057688775818802025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167914125410251701091736033 125935594057688775818802025)
    ·
      refine ⟨94451695543266581864101519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125935594057688775818802025 94451695543266581864101519)
      ·
        refine ⟨141677543314899872796152279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94451695543266581864101519 141677543314899872796152279)
        ·
          refine ⟨212516314972349809194228419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141677543314899872796152279 212516314972349809194228419)
          ·
            refine ⟨318774472458524713791342629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 212516314972349809194228419 318774472458524713791342629)
            ·
              refine ⟨59770213585973383835876743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 318774472458524713791342629 59770213585973383835876743)
              ·
                refine ⟨89655320378960075753815115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59770213585973383835876743 89655320378960075753815115)
                ·
                  refine ⟨134482980568440113630722673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89655320378960075753815115 134482980568440113630722673)
                  ·
                    refine ⟨100862235426330085223042005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 134482980568440113630722673 100862235426330085223042005)
                    ·
                      refine ⟨2363958642804611372415047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100862235426330085223042005 2363958642804611372415047)
                      ·
                        rfl

theorem cell23_4603793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_4603793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603793 prefixEnd_4603793 := by exact prefixLift 4603793
  have htrace : WordTrace (prefixWord ++ tailWord_4603793) baseStart_4603793 baseEnd_4603793 := by
    simpa [prefixWord, tailWord_4603793, baseEnd_4603793] using wordTrace_append hprefix tailTrace_4603793
  have hstable : (prefixWord ++ tailWord_4603793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603793).length < 2 ^ (prefixWord ++ tailWord_4603793).sum := by decide
  have hdescent : baseEnd_4603793 < baseStart_4603793 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603807 : List Nat := [1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 4]
def baseStart_4603807 : Nat := 118140960795 + 4603807 * 2 ^ 59
def prefixEnd_4603807 : Nat := 4983230072969 + 3 ^ 40 * 4603807 * 2
def baseEnd_4603807 : Nat := 2363965831533774317639983

theorem tailTrace_4603807 : CollatzResearch.WordTrace tailWord_4603807 prefixEnd_4603807 2363965831533774317639983 := by
  unfold tailWord_4603807
  simp only [CollatzResearch.WordTrace]
  refine ⟨167914636032200981482745675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111943090688133987655163783 167914636032200981482745675)
  ·
    refine ⟨251871954048301472224118513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167914636032200981482745675 251871954048301472224118513)
    ·
      refine ⟨188903965536226104168088885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251871954048301472224118513 188903965536226104168088885)
      ·
        refine ⟨17709746769021197265758333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 188903965536226104168088885 17709746769021197265758333)
        ·
          refine ⟨6641155038382948974659375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17709746769021197265758333 6641155038382948974659375)
          ·
            refine ⟨9961732557574423461989063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6641155038382948974659375 9961732557574423461989063)
            ·
              refine ⟨14942598836361635192983595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9961732557574423461989063 14942598836361635192983595)
              ·
                refine ⟨22413898254542452789475393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14942598836361635192983595 22413898254542452789475393)
                ·
                  refine ⟨16810423690906839592106545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22413898254542452789475393 16810423690906839592106545)
                  ·
                    refine ⟨12607817768180129694079909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16810423690906839592106545 12607817768180129694079909)
                    ·
                      refine ⟨2363965831533774317639983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12607817768180129694079909 2363965831533774317639983)
                      ·
                        rfl

theorem cell23_4603807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_4603807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603807 prefixEnd_4603807 := by exact prefixLift 4603807
  have htrace : WordTrace (prefixWord ++ tailWord_4603807) baseStart_4603807 baseEnd_4603807 := by
    simpa [prefixWord, tailWord_4603807, baseEnd_4603807] using wordTrace_append hprefix tailTrace_4603807
  have hstable : (prefixWord ++ tailWord_4603807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603807).length < 2 ^ (prefixWord ++ tailWord_4603807).sum := by decide
  have hdescent : baseEnd_4603807 < baseStart_4603807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603880 : List Nat := [2, 1, 4, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_4603880 : Nat := 118140960795 + 4603880 * 2 ^ 59
def prefixEnd_4603880 : Nat := 4983230072969 + 3 ^ 40 * 4603880 * 2
def baseEnd_4603880 : Nat := 2364003315621552532027147

theorem tailTrace_4603880 : CollatzResearch.WordTrace tailWord_4603880 prefixEnd_4603880 2364003315621552532027147 := by
  unfold tailWord_4603880
  simp only [CollatzResearch.WordTrace]
  refine ⟨83958649280468257475076547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111944865707291009966768729 83958649280468257475076547)
  ·
    refine ⟨125937973920702386212614821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83958649280468257475076547 125937973920702386212614821)
    ·
      refine ⟨23613370110131697414865279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125937973920702386212614821 23613370110131697414865279)
      ·
        refine ⟨35420055165197546122297919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23613370110131697414865279 35420055165197546122297919)
        ·
          refine ⟨53130082747796319183446879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35420055165197546122297919 53130082747796319183446879)
          ·
            refine ⟨79695124121694478775170319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53130082747796319183446879 79695124121694478775170319)
            ·
              refine ⟨119542686182541718162755479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79695124121694478775170319 119542686182541718162755479)
              ·
                refine ⟨179314029273812577244133219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119542686182541718162755479 179314029273812577244133219)
                ·
                  refine ⟨268971043910718865866199829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179314029273812577244133219 268971043910718865866199829)
                  ·
                    refine ⟨12608017683314946837478117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 268971043910718865866199829 12608017683314946837478117)
                    ·
                      refine ⟨2364003315621552532027147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12608017683314946837478117 2364003315621552532027147)
                      ·
                        rfl

theorem cell23_4603880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_4603880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603880 prefixEnd_4603880 := by exact prefixLift 4603880
  have htrace : WordTrace (prefixWord ++ tailWord_4603880) baseStart_4603880 baseEnd_4603880 := by
    simpa [prefixWord, tailWord_4603880, baseEnd_4603880] using wordTrace_append hprefix tailTrace_4603880
  have hstable : (prefixWord ++ tailWord_4603880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603880).length < 2 ^ (prefixWord ++ tailWord_4603880).sum := by decide
  have hdescent : baseEnd_4603880 < baseStart_4603880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603887 : List Nat := [1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 3]
def baseStart_4603887 : Nat := 118140960795 + 4603887 * 2 ^ 59
def prefixEnd_4603887 : Nat := 4983230072969 + 3 ^ 40 * 4603887 * 2
def baseEnd_4603887 : Nat := 2364006909986134004639615

theorem tailTrace_4603887 : CollatzResearch.WordTrace tailWord_4603887 prefixEnd_4603887 2364006909986134004639615 := by
  unfold tailWord_4603887
  simp only [CollatzResearch.WordTrace]
  refine ⟨167917553871911155145657915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111945035914607436763771943 167917553871911155145657915)
  ·
    refine ⟨251876330807866732718486873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167917553871911155145657915 251876330807866732718486873)
    ·
      refine ⟨188907248105900049538865155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251876330807866732718486873 188907248105900049538865155)
      ·
        refine ⟨283360872158850074308297733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188907248105900049538865155 283360872158850074308297733)
        ·
          refine ⟨53130163529784388932805825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283360872158850074308297733 53130163529784388932805825)
          ·
            refine ⟨39847622647338291699604369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53130163529784388932805825 39847622647338291699604369)
            ·
              refine ⟨29885716985503718774703277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39847622647338291699604369 29885716985503718774703277)
              ·
                refine ⟨11207143869563894540513729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29885716985503718774703277 11207143869563894540513729)
                ·
                  refine ⟨8405357902172920905385297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11207143869563894540513729 8405357902172920905385297)
                  ·
                    refine ⟨6304018426629690679038973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8405357902172920905385297 6304018426629690679038973)
                    ·
                      refine ⟨2364006909986134004639615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6304018426629690679038973 2364006909986134004639615)
                      ·
                        rfl

theorem cell23_4603887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_4603887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603887 prefixEnd_4603887 := by exact prefixLift 4603887
  have htrace : WordTrace (prefixWord ++ tailWord_4603887) baseStart_4603887 baseEnd_4603887 := by
    simpa [prefixWord, tailWord_4603887, baseEnd_4603887] using wordTrace_append hprefix tailTrace_4603887
  have hstable : (prefixWord ++ tailWord_4603887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603887).length < 2 ^ (prefixWord ++ tailWord_4603887).sum := by decide
  have hdescent : baseEnd_4603887 < baseStart_4603887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603920 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 5, 5]
def baseStart_4603920 : Nat := 118140960795 + 4603920 * 2 ^ 59
def prefixEnd_4603920 : Nat := 4983230072969 + 3 ^ 40 * 4603920 * 2
def baseEnd_4603920 : Nat := 788007951615910791842321

theorem tailTrace_4603920 : CollatzResearch.WordTrace tailWord_4603920 prefixEnd_4603920 788007951615910791842321 := by
  unfold tailWord_4603920
  simp only [CollatzResearch.WordTrace]
  refine ⟨83959378740395800890804607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111945838320527734521072809 83959378740395800890804607)
  ·
    refine ⟨125939068110593701336206911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83959378740395800890804607 125939068110593701336206911)
    ·
      refine ⟨188908602165890552004310367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125939068110593701336206911 188908602165890552004310367)
      ·
        refine ⟨283362903248835828006465551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188908602165890552004310367 283362903248835828006465551)
        ·
          refine ⟨425044354873253742009698327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283362903248835828006465551 425044354873253742009698327)
          ·
            refine ⟨637566532309880613014547491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425044354873253742009698327 637566532309880613014547491)
            ·
              refine ⟨956349798464820919521821237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637566532309880613014547491 956349798464820919521821237)
              ·
                refine ⟨89657793606076961205170741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 956349798464820919521821237 89657793606076961205170741)
                ·
                  refine ⟨8405418150569715112984757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89657793606076961205170741 8405418150569715112984757)
                  ·
                    refine ⟨788007951615910791842321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8405418150569715112984757 788007951615910791842321)
                    ·
                      rfl

theorem cell23_4603920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_4603920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603920 prefixEnd_4603920 := by exact prefixLift 4603920
  have htrace : WordTrace (prefixWord ++ tailWord_4603920) baseStart_4603920 baseEnd_4603920 := by
    simpa [prefixWord, tailWord_4603920, baseEnd_4603920] using wordTrace_append hprefix tailTrace_4603920
  have hstable : (prefixWord ++ tailWord_4603920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603920).length < 2 ^ (prefixWord ++ tailWord_4603920).sum := by decide
  have hdescent : baseEnd_4603920 < baseStart_4603920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603967 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 4, 4]
def baseStart_4603967 : Nat := 118140960795 + 4603967 * 2 ^ 59
def prefixEnd_4603967 : Nat := 4983230072969 + 3 ^ 40 * 4603967 * 2
def baseEnd_4603967 : Nat := 788015996146164563879749

theorem tailTrace_4603967 : CollatzResearch.WordTrace tailWord_4603967 prefixEnd_4603967 788015996146164563879749 := by
  unfold tailWord_4603967
  simp only [CollatzResearch.WordTrace]
  refine ⟨167920471711621328808570155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111946981141080885872380103 167920471711621328808570155)
  ·
    refine ⟨251880707567431993212855233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167920471711621328808570155 251880707567431993212855233)
    ·
      refine ⟨188910530675573994909641425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251880707567431993212855233 188910530675573994909641425)
      ·
        refine ⟨141682898006680496182231069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188910530675573994909641425 141682898006680496182231069)
        ·
          refine ⟨53131086752505186068336651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141682898006680496182231069 53131086752505186068336651)
          ·
            refine ⟨79696630128757779102504977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53131086752505186068336651 79696630128757779102504977)
            ·
              refine ⟨59772472596568334326878733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79696630128757779102504977 59772472596568334326878733)
              ·
                refine ⟨22414677223713125372579525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59772472596568334326878733 22414677223713125372579525)
                ·
                  refine ⟨4202751979446211007358661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22414677223713125372579525 4202751979446211007358661)
                  ·
                    refine ⟨788015996146164563879749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4202751979446211007358661 788015996146164563879749)
                    ·
                      rfl

theorem cell23_4603967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_4603967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603967 prefixEnd_4603967 := by exact prefixLift 4603967
  have htrace : WordTrace (prefixWord ++ tailWord_4603967) baseStart_4603967 baseEnd_4603967 := by
    simpa [prefixWord, tailWord_4603967, baseEnd_4603967] using wordTrace_append hprefix tailTrace_4603967
  have hstable : (prefixWord ++ tailWord_4603967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603967).length < 2 ^ (prefixWord ++ tailWord_4603967).sum := by decide
  have hdescent : baseEnd_4603967 < baseStart_4603967 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603968 : List Nat := [2, 1, 1, 2, 2, 4, 4, 2, 1, 1, 3]
def baseStart_4603968 : Nat := 118140960795 + 4603968 * 2 ^ 59
def prefixEnd_4603968 : Nat := 4983230072969 + 3 ^ 40 * 4603968 * 2
def baseEnd_4603968 : Nat := 2364048501919148187726743

theorem tailTrace_4603968 : CollatzResearch.WordTrace tailWord_4603968 prefixEnd_4603968 2364048501919148187726743 := by
  unfold tailWord_4603968
  simp only [CollatzResearch.WordTrace]
  refine ⟨83960254092308852989678279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111947005456411803986237705 83960254092308852989678279)
  ·
    refine ⟨125940381138463279484517419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83960254092308852989678279 125940381138463279484517419)
    ·
      refine ⟨188910571707694919226776129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125940381138463279484517419 188910571707694919226776129)
      ·
        refine ⟨141682928780771189420082097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188910571707694919226776129 141682928780771189420082097)
        ·
          refine ⟨106262196585578392065061573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141682928780771189420082097 106262196585578392065061573)
          ·
            refine ⟨19924161859795948512199045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106262196585578392065061573 19924161859795948512199045)
            ·
              refine ⟨3735780348711740346037321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19924161859795948512199045 3735780348711740346037321)
              ·
                refine ⟨2801835261533805259527991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3735780348711740346037321 2801835261533805259527991)
                ·
                  refine ⟨4202752892300707889291987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2801835261533805259527991 4202752892300707889291987)
                  ·
                    refine ⟨6304129338451061833937981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4202752892300707889291987 6304129338451061833937981)
                    ·
                      refine ⟨2364048501919148187726743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6304129338451061833937981 2364048501919148187726743)
                      ·
                        rfl

theorem cell23_4603968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 4, 2, 1, 1, 3].length) (baseStart_4603968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603968 prefixEnd_4603968 := by exact prefixLift 4603968
  have htrace : WordTrace (prefixWord ++ tailWord_4603968) baseStart_4603968 baseEnd_4603968 := by
    simpa [prefixWord, tailWord_4603968, baseEnd_4603968] using wordTrace_append hprefix tailTrace_4603968
  have hstable : (prefixWord ++ tailWord_4603968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603968).length < 2 ^ (prefixWord ++ tailWord_4603968).sum := by decide
  have hdescent : baseEnd_4603968 < baseStart_4603968 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603977 : List Nat := [1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 3]
def baseStart_4603977 : Nat := 118140960795 + 4603977 * 2 ^ 59
def prefixEnd_4603977 : Nat := 4983230072969 + 3 ^ 40 * 4603977 * 2
def baseEnd_4603977 : Nat := 2364053123245038652514201

theorem tailTrace_4603977 : CollatzResearch.WordTrace tailWord_4603977 prefixEnd_4603977 2364053123245038652514201 := by
  unfold tailWord_4603977
  simp only [CollatzResearch.WordTrace]
  refine ⟨167920836441585100516434185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111947224294390067010956123 167920836441585100516434185)
  ·
    refine ⟨125940627331188825387325639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167920836441585100516434185 125940627331188825387325639)
    ·
      refine ⟨188910940996783238080988459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125940627331188825387325639 188910940996783238080988459)
      ·
        refine ⟨283366411495174857121482689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188910940996783238080988459 283366411495174857121482689)
        ·
          refine ⟨212524808621381142841112017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283366411495174857121482689 212524808621381142841112017)
          ·
            refine ⟨159393606466035857130834013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212524808621381142841112017 159393606466035857130834013)
            ·
              refine ⟨59772602424763446424062755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159393606466035857130834013 59772602424763446424062755)
              ·
                refine ⟨89658903637145169636094133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59772602424763446424062755 89658903637145169636094133)
                ·
                  refine ⟨8405522215982359653383825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89658903637145169636094133 8405522215982359653383825)
                  ·
                    refine ⟨6304141661986769740037869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8405522215982359653383825 6304141661986769740037869)
                    ·
                      refine ⟨2364053123245038652514201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6304141661986769740037869 2364053123245038652514201)
                      ·
                        rfl

theorem cell23_4603977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 3, 1, 5, 2, 3].length) (baseStart_4603977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603977 prefixEnd_4603977 := by exact prefixLift 4603977
  have htrace : WordTrace (prefixWord ++ tailWord_4603977) baseStart_4603977 baseEnd_4603977 := by
    simpa [prefixWord, tailWord_4603977, baseEnd_4603977] using wordTrace_append hprefix tailTrace_4603977
  have hstable : (prefixWord ++ tailWord_4603977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603977).length < 2 ^ (prefixWord ++ tailWord_4603977).sum := by decide
  have hdescent : baseEnd_4603977 < baseStart_4603977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4603994 : List Nat := [3, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_4603994 : Nat := 118140960795 + 4603994 * 2 ^ 59
def prefixEnd_4603994 : Nat := 4983230072969 + 3 ^ 40 * 4603994 * 2
def baseEnd_4603994 : Nat := 2364061852416165086001623

theorem tailTrace_4603994 : CollatzResearch.WordTrace tailWord_4603994 prefixEnd_4603994 2364061852416165086001623 := by
  unfold tailWord_4603994
  simp only [CollatzResearch.WordTrace]
  refine ⟨41980364120630878104950759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111947637655015674946535357 41980364120630878104950759)
  ·
    refine ⟨62970546180946317157426139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41980364120630878104950759 62970546180946317157426139)
    ·
      refine ⟨94455819271419475736139209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62970546180946317157426139 94455819271419475736139209)
      ·
        refine ⟨70841864453564606802104407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94455819271419475736139209 70841864453564606802104407)
        ·
          refine ⟨106262796680346910203156611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70841864453564606802104407 106262796680346910203156611)
          ·
            refine ⟨159394195020520365304734917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106262796680346910203156611 159394195020520365304734917)
            ·
              refine ⟨29886411566347568494637797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 159394195020520365304734917 29886411566347568494637797)
              ·
                refine ⟨5603702168690169092744587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29886411566347568494637797 5603702168690169092744587)
                ·
                  refine ⟨8405553253035253639116881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5603702168690169092744587 8405553253035253639116881)
                  ·
                    refine ⟨6304164939776440229337661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8405553253035253639116881 6304164939776440229337661)
                    ·
                      refine ⟨2364061852416165086001623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6304164939776440229337661 2364061852416165086001623)
                      ·
                        rfl

theorem cell23_4603994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_4603994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4603994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4603994 prefixEnd_4603994 := by exact prefixLift 4603994
  have htrace : WordTrace (prefixWord ++ tailWord_4603994) baseStart_4603994 baseEnd_4603994 := by
    simpa [prefixWord, tailWord_4603994, baseEnd_4603994] using wordTrace_append hprefix tailTrace_4603994
  have hstable : (prefixWord ++ tailWord_4603994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4603994).length < 2 ^ (prefixWord ++ tailWord_4603994).sum := by decide
  have hdescent : baseEnd_4603994 < baseStart_4603994 := by decide
  rcases family_descends (prefixWord ++ tailWord_4603994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604067 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 3]
def baseStart_4604067 : Nat := 118140960795 + 4604067 * 2 ^ 59
def prefixEnd_4604067 : Nat := 4983230072969 + 3 ^ 40 * 4604067 * 2
def baseEnd_4604067 : Nat := 2364099336503943300388787

theorem tailTrace_4604067 : CollatzResearch.WordTrace tailWord_4604067 prefixEnd_4604067 2364099336503943300388787 := by
  unfold tailWord_4604067
  simp only [CollatzResearch.WordTrace]
  refine ⟨167924119011259045887210455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111949412674172697258140303 167924119011259045887210455)
  ·
    refine ⟨251886178516888568830815683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167924119011259045887210455 251886178516888568830815683)
    ·
      refine ⟨377829267775332853246223525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251886178516888568830815683 377829267775332853246223525)
      ·
        refine ⟨70842987707874909983666911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 377829267775332853246223525 70842987707874909983666911)
        ·
          refine ⟨106264481561812364975500367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70842987707874909983666911 106264481561812364975500367)
          ·
            refine ⟨159396722342718547463250551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106264481561812364975500367 159396722342718547463250551)
            ·
              refine ⟨239095083514077821194875827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159396722342718547463250551 239095083514077821194875827)
              ·
                refine ⟨358642625271116731792313741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239095083514077821194875827 358642625271116731792313741)
                ·
                  refine ⟨134490984476668774422117653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 358642625271116731792313741 134490984476668774422117653)
                  ·
                    refine ⟨6304264897343848801036765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 134490984476668774422117653 6304264897343848801036765)
                    ·
                      refine ⟨2364099336503943300388787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6304264897343848801036765 2364099336503943300388787)
                      ·
                        rfl

theorem cell23_4604067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_4604067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604067 prefixEnd_4604067 := by exact prefixLift 4604067
  have htrace : WordTrace (prefixWord ++ tailWord_4604067) baseStart_4604067 baseEnd_4604067 := by
    simpa [prefixWord, tailWord_4604067, baseEnd_4604067] using wordTrace_append hprefix tailTrace_4604067
  have hstable : (prefixWord ++ tailWord_4604067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604067).length < 2 ^ (prefixWord ++ tailWord_4604067).sum := by decide
  have hdescent : baseEnd_4604067 < baseStart_4604067 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604092 : List Nat := [2, 2, 2, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_4604092 : Nat := 118140960795 + 4604092 * 2 ^ 59
def prefixEnd_4604092 : Nat := 4983230072969 + 3 ^ 40 * 4604092 * 2
def baseEnd_4604092 : Nat := 2364112173520305702576173

theorem tailTrace_4604092 : CollatzResearch.WordTrace tailWord_4604092 prefixEnd_4604092 2364112173520305702576173 := by
  unfold tailWord_4604092
  simp only [CollatzResearch.WordTrace]
  refine ⟨83962515418084237578435265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111950020557445650104580353 83962515418084237578435265)
  ·
    refine ⟨62971886563563178183826449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83962515418084237578435265 62971886563563178183826449)
    ·
      refine ⟨47228914922672383637869837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62971886563563178183826449 47228914922672383637869837)
      ·
        refine ⟨17710843096002143864201189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47228914922672383637869837 17710843096002143864201189)
        ·
          refine ⟨3320783080500401974537723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17710843096002143864201189 3320783080500401974537723)
          ·
            refine ⟨4981174620750602961806585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3320783080500401974537723 4981174620750602961806585)
            ·
              refine ⟨3735880965562952221354939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4981174620750602961806585 3735880965562952221354939)
              ·
                refine ⟨5603821448344428332032409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735880965562952221354939 5603821448344428332032409)
                ·
                  refine ⟨4202866086258321249024307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5603821448344428332032409 4202866086258321249024307)
                  ·
                    refine ⟨6304299129387481873536461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4202866086258321249024307 6304299129387481873536461)
                    ·
                      refine ⟨2364112173520305702576173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6304299129387481873536461 2364112173520305702576173)
                      ·
                        rfl

theorem cell23_4604092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_4604092 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604092 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604092 prefixEnd_4604092 := by exact prefixLift 4604092
  have htrace : WordTrace (prefixWord ++ tailWord_4604092) baseStart_4604092 baseEnd_4604092 := by
    simpa [prefixWord, tailWord_4604092, baseEnd_4604092] using wordTrace_append hprefix tailTrace_4604092
  have hstable : (prefixWord ++ tailWord_4604092).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604092).length < 2 ^ (prefixWord ++ tailWord_4604092).sum := by decide
  have hdescent : baseEnd_4604092 < baseStart_4604092 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604211 : List Nat := [1, 1, 1, 2, 5, 1, 5, 1, 6]
def baseStart_4604211 : Nat := 118140960795 + 4604211 * 2 ^ 59
def prefixEnd_4604211 : Nat := 4983230072969 + 3 ^ 40 * 4604211 * 2
def baseEnd_4604211 : Nat := 262685919746465637443125

theorem tailTrace_4604211 : CollatzResearch.WordTrace tailWord_4604211 prefixEnd_4604211 262685919746465637443125 := by
  unfold tailWord_4604211
  simp only [CollatzResearch.WordTrace]
  refine ⟨167929371122737358480452487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111952914081824905653634991 167929371122737358480452487)
  ·
    refine ⟨251894056684106037720678731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167929371122737358480452487 251894056684106037720678731)
    ·
      refine ⟨377841085026159056581018097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251894056684106037720678731 377841085026159056581018097)
      ·
        refine ⟨283380813769619292435763573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377841085026159056581018097 283380813769619292435763573)
        ·
          refine ⟨26566951290901808665852835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 283380813769619292435763573 26566951290901808665852835)
          ·
            refine ⟨39850426936352712998779253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26566951290901808665852835 39850426936352712998779253)
            ·
              refine ⟨3735977525283066843635555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39850426936352712998779253 3735977525283066843635555)
              ·
                refine ⟨5603966287924600265453333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3735977525283066843635555 5603966287924600265453333)
                ·
                  refine ⟨262685919746465637443125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5603966287924600265453333 262685919746465637443125)
                  ·
                    rfl

theorem cell23_4604211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 5, 1, 6].length) (baseStart_4604211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604211 prefixEnd_4604211 := by exact prefixLift 4604211
  have htrace : WordTrace (prefixWord ++ tailWord_4604211) baseStart_4604211 baseEnd_4604211 := by
    simpa [prefixWord, tailWord_4604211, baseEnd_4604211] using wordTrace_append hprefix tailTrace_4604211
  have hstable : (prefixWord ++ tailWord_4604211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604211).length < 2 ^ (prefixWord ++ tailWord_4604211).sum := by decide
  have hdescent : baseEnd_4604211 < baseStart_4604211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604231 : List Nat := [1, 1, 4, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_4604231 : Nat := 118140960795 + 4604231 * 2 ^ 59
def prefixEnd_4604231 : Nat := 4983230072969 + 3 ^ 40 * 4604231 * 2
def baseEnd_4604231 : Nat := 2364183547331280658738033

theorem tailTrace_4604231 : CollatzResearch.WordTrace tailWord_4604231 prefixEnd_4604231 2364183547331280658738033 := by
  unfold tailWord_4604231
  simp only [CollatzResearch.WordTrace]
  refine ⟨167930100582664901896180547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111953400388443267930787031 167930100582664901896180547)
  ·
    refine ⟨251895150873997352844270821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167930100582664901896180547 251895150873997352844270821)
    ·
      refine ⟨47230340788874503658300779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251895150873997352844270821 47230340788874503658300779)
      ·
        refine ⟨70845511183311755487451169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47230340788874503658300779 70845511183311755487451169)
        ·
          refine ⟨53134133387483816615588377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70845511183311755487451169 53134133387483816615588377)
          ·
            refine ⟨39850600040612862461691283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53134133387483816615588377 39850600040612862461691283)
            ·
              refine ⟨59775900060919293692536925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39850600040612862461691283 59775900060919293692536925)
              ·
                refine ⟨22415962522844735134701347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59775900060919293692536925 22415962522844735134701347)
                ·
                  refine ⟨33623943784267102702052021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22415962522844735134701347 33623943784267102702052021)
                  ·
                    refine ⟨3152244729775040878317377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33623943784267102702052021 3152244729775040878317377)
                    ·
                      refine ⟨2364183547331280658738033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152244729775040878317377 2364183547331280658738033)
                      ·
                        rfl

theorem cell23_4604231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_4604231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604231 prefixEnd_4604231 := by exact prefixLift 4604231
  have htrace : WordTrace (prefixWord ++ tailWord_4604231) baseStart_4604231 baseEnd_4604231 := by
    simpa [prefixWord, tailWord_4604231, baseEnd_4604231] using wordTrace_append hprefix tailTrace_4604231
  have hstable : (prefixWord ++ tailWord_4604231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604231).length < 2 ^ (prefixWord ++ tailWord_4604231).sum := by decide
  have hdescent : baseEnd_4604231 < baseStart_4604231 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604241 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 1, 5]
def baseStart_4604241 : Nat := 118140960795 + 4604241 * 2 ^ 59
def prefixEnd_4604241 : Nat := 4983230072969 + 3 ^ 40 * 4604241 * 2
def baseEnd_4604241 : Nat := 788062894045941873204329

theorem tailTrace_4604241 : CollatzResearch.WordTrace tailWord_4604241 prefixEnd_4604241 788062894045941873204329 := by
  unfold tailWord_4604241
  simp only [CollatzResearch.WordTrace]
  refine ⟨167930465312628673604044577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111953643541752449069363051 167930465312628673604044577)
  ·
    refine ⟨125947848984471505203033433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167930465312628673604044577 125947848984471505203033433)
    ·
      refine ⟨94460886738353628902275075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125947848984471505203033433 94460886738353628902275075)
      ·
        refine ⟨141691330107530443353412613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94460886738353628902275075 141691330107530443353412613)
        ·
          refine ⟨26567124395161958128764865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 141691330107530443353412613 26567124395161958128764865)
          ·
            refine ⟨19925343296371468596573649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26567124395161958128764865 19925343296371468596573649)
            ·
              refine ⟨14944007472278601447430237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19925343296371468596573649 14944007472278601447430237)
              ·
                refine ⟨5604002802104475542786339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14944007472278601447430237 5604002802104475542786339)
                ·
                  refine ⟨8406004203156713314179509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604002802104475542786339 8406004203156713314179509)
                  ·
                    refine ⟨788062894045941873204329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8406004203156713314179509 788062894045941873204329)
                    ·
                      rfl

theorem cell23_4604241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 5].length) (baseStart_4604241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604241 prefixEnd_4604241 := by exact prefixLift 4604241
  have htrace : WordTrace (prefixWord ++ tailWord_4604241) baseStart_4604241 baseEnd_4604241 := by
    simpa [prefixWord, tailWord_4604241, baseEnd_4604241] using wordTrace_append hprefix tailTrace_4604241
  have hstable : (prefixWord ++ tailWord_4604241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604241).length < 2 ^ (prefixWord ++ tailWord_4604241).sum := by decide
  have hdescent : baseEnd_4604241 < baseStart_4604241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604318 : List Nat := [4, 3, 1, 2, 1, 1, 3, 8]
def baseStart_4604318 : Nat := 118140960795 + 4604318 * 2 ^ 59
def prefixEnd_4604318 : Nat := 4983230072969 + 3 ^ 40 * 4604318 * 2
def baseEnd_4604318 : Nat := 87564008153637845124079

theorem tailTrace_4604318 : CollatzResearch.WordTrace tailWord_4604318 prefixEnd_4604318 87564008153637845124079 := by
  unfold tailWord_4604318
  simp only [CollatzResearch.WordTrace]
  refine ⟨20991659216668714469324701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111955515822233143836398405 20991659216668714469324701)
  ·
    refine ⟨7871872206250767925996763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20991659216668714469324701 7871872206250767925996763)
    ·
      refine ⟨11807808309376151888995145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7871872206250767925996763 11807808309376151888995145)
      ·
        refine ⟨8855856232032113916746359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11807808309376151888995145 8855856232032113916746359)
        ·
          refine ⟨13283784348048170875119539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8855856232032113916746359 13283784348048170875119539)
          ·
            refine ⟨19925676522072256312679309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13283784348048170875119539 19925676522072256312679309)
            ·
              refine ⟨7472128695777096117254741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19925676522072256312679309 7472128695777096117254741)
              ·
                refine ⟨87564008153637845124079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7472128695777096117254741 87564008153637845124079)
                ·
                  rfl

theorem cell23_4604318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 3, 8].length) (baseStart_4604318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604318 prefixEnd_4604318 := by exact prefixLift 4604318
  have htrace : WordTrace (prefixWord ++ tailWord_4604318) baseStart_4604318 baseEnd_4604318 := by
    simpa [prefixWord, tailWord_4604318, baseEnd_4604318] using wordTrace_append hprefix tailTrace_4604318
  have hstable : (prefixWord ++ tailWord_4604318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604318).length < 2 ^ (prefixWord ++ tailWord_4604318).sum := by decide
  have hdescent : baseEnd_4604318 < baseStart_4604318 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604338 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2]
def baseStart_4604338 : Nat := 118140960795 + 4604338 * 2 ^ 59
def prefixEnd_4604338 : Nat := 4983230072969 + 3 ^ 40 * 4604338 * 2
def baseEnd_4604338 : Nat := 2364238489761311740100041

theorem tailTrace_4604338 : CollatzResearch.WordTrace tailWord_4604338 prefixEnd_4604338 2364238489761311740100041 := by
  unfold tailWord_4604338
  simp only [CollatzResearch.WordTrace]
  refine ⟨41983500798319314792581417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111956002128851506113550445 41983500798319314792581417)
  ·
    refine ⟨31487625598739486094436063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41983500798319314792581417 31487625598739486094436063)
    ·
      refine ⟨47231438398109229141654095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31487625598739486094436063 47231438398109229141654095)
      ·
        refine ⟨70847157597163843712481143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47231438398109229141654095 70847157597163843712481143)
        ·
          refine ⟨106270736395745765568721715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70847157597163843712481143 106270736395745765568721715)
          ·
            refine ⟨159406104593618648353082573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106270736395745765568721715 159406104593618648353082573)
            ·
              refine ⟨59777289222606993132405965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159406104593618648353082573 59777289222606993132405965)
              ·
                refine ⟨22416483458477622424652237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59777289222606993132405965 22416483458477622424652237)
                ·
                  refine ⟨8406181296929108409244589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22416483458477622424652237 8406181296929108409244589)
                  ·
                    refine ⟨3152317986348415653466721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8406181296929108409244589 3152317986348415653466721)
                    ·
                      refine ⟨2364238489761311740100041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152317986348415653466721 2364238489761311740100041)
                      ·
                        rfl

theorem cell23_4604338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 3, 3, 2].length) (baseStart_4604338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604338 prefixEnd_4604338 := by exact prefixLift 4604338
  have htrace : WordTrace (prefixWord ++ tailWord_4604338) baseStart_4604338 baseEnd_4604338 := by
    simpa [prefixWord, tailWord_4604338, baseEnd_4604338] using wordTrace_append hprefix tailTrace_4604338
  have hstable : (prefixWord ++ tailWord_4604338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604338).length < 2 ^ (prefixWord ++ tailWord_4604338).sum := by decide
  have hdescent : baseEnd_4604338 < baseStart_4604338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604344 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 3, 8]
def baseStart_4604344 : Nat := 118140960795 + 4604344 * 2 ^ 59
def prefixEnd_4604344 : Nat := 4983230072969 + 3 ^ 40 * 4604344 * 2
def baseEnd_4604344 : Nat := 788080523548412905541671

theorem tailTrace_4604344 : CollatzResearch.WordTrace tailWord_4604344 prefixEnd_4604344 788080523548412905541671 := by
  unfold tailWord_4604344
  simp only [CollatzResearch.WordTrace]
  refine ⟨83967111015627761097522043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111956148020837014796696057 83967111015627761097522043)
  ·
    refine ⟨125950666523441641646283065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83967111015627761097522043 125950666523441641646283065)
    ·
      refine ⟨94462999892581231234712299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125950666523441641646283065 94462999892581231234712299)
      ·
        refine ⟨141694499838871846852068449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94462999892581231234712299 141694499838871846852068449)
        ·
          refine ⟨106270874879153885139051337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141694499838871846852068449 106270874879153885139051337)
          ·
            refine ⟨79703156159365413854288503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106270874879153885139051337 79703156159365413854288503)
            ·
              refine ⟨119554734239048120781432755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79703156159365413854288503 119554734239048120781432755)
              ·
                refine ⟨179332101358572181172149133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119554734239048120781432755 179332101358572181172149133)
                ·
                  refine ⟨67249538009464567939555925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 179332101358572181172149133 67249538009464567939555925)
                  ·
                    refine ⟨788080523548412905541671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 67249538009464567939555925 788080523548412905541671)
                    ·
                      rfl

theorem cell23_4604344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_4604344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604344 prefixEnd_4604344 := by exact prefixLift 4604344
  have htrace : WordTrace (prefixWord ++ tailWord_4604344) baseStart_4604344 baseEnd_4604344 := by
    simpa [prefixWord, tailWord_4604344, baseEnd_4604344] using wordTrace_append hprefix tailTrace_4604344
  have hstable : (prefixWord ++ tailWord_4604344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604344).length < 2 ^ (prefixWord ++ tailWord_4604344).sum := by decide
  have hdescent : baseEnd_4604344 < baseStart_4604344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604391 : List Nat := [1, 1, 5, 2, 1, 1, 1, 4, 7]
def baseStart_4604391 : Nat := 118140960795 + 4604391 * 2 ^ 59
def prefixEnd_4604391 : Nat := 4983230072969 + 3 ^ 40 * 4604391 * 2
def baseEnd_4604391 : Nat := 262696189359555559193033

theorem tailTrace_4604391 : CollatzResearch.WordTrace tailWord_4604391 prefixEnd_4604391 262696189359555559193033 := by
  unfold tailWord_4604391
  simp only [CollatzResearch.WordTrace]
  refine ⟨167935936262085249222005027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111957290841390166148003351 167935936262085249222005027)
  ·
    refine ⟨251903904393127873833007541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167935936262085249222005027 251903904393127873833007541)
    ·
      refine ⟨23615991036855738171844457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 251903904393127873833007541 23615991036855738171844457)
      ·
        refine ⟨17711993277641803628883343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23615991036855738171844457 17711993277641803628883343)
        ·
          refine ⟨26567989916462705443325015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17711993277641803628883343 26567989916462705443325015)
          ·
            refine ⟨39851984874694058164987523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26567989916462705443325015 39851984874694058164987523)
            ·
              refine ⟨59777977312041087247481285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39851984874694058164987523 59777977312041087247481285)
              ·
                refine ⟨11208370746007703858902741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59777977312041087247481285 11208370746007703858902741)
                ·
                  refine ⟨262696189359555559193033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11208370746007703858902741 262696189359555559193033)
                  ·
                    rfl

theorem cell23_4604391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 4, 7].length) (baseStart_4604391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604391 prefixEnd_4604391 := by exact prefixLift 4604391
  have htrace : WordTrace (prefixWord ++ tailWord_4604391) baseStart_4604391 baseEnd_4604391 := by
    simpa [prefixWord, tailWord_4604391, baseEnd_4604391] using wordTrace_append hprefix tailTrace_4604391
  have hstable : (prefixWord ++ tailWord_4604391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604391).length < 2 ^ (prefixWord ++ tailWord_4604391).sum := by decide
  have hdescent : baseEnd_4604391 < baseStart_4604391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604405 : List Nat := [1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 5]
def baseStart_4604405 : Nat := 118140960795 + 4604405 * 2 ^ 59
def prefixEnd_4604405 : Nat := 4983230072969 + 3 ^ 40 * 4604405 * 2
def baseEnd_4604405 : Nat := 2364272892965162977962233

theorem tailTrace_4604405 : CollatzResearch.WordTrace tailWord_4604405 prefixEnd_4604405 2364272892965162977962233 := by
  unfold tailWord_4604405
  simp only [CollatzResearch.WordTrace]
  refine ⟨167936446884034529613014669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111957631256023019742009779 167936446884034529613014669)
  ·
    refine ⟨62976167581512948604880501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167936446884034529613014669 62976167581512948604880501)
    ·
      refine ⟨5904015710766838931707547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62976167581512948604880501 5904015710766838931707547)
      ·
        refine ⟨8856023566150258397561321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904015710766838931707547 8856023566150258397561321)
        ·
          refine ⟨6642017674612693798170991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8856023566150258397561321 6642017674612693798170991)
          ·
            refine ⟨9963026511919040697256487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642017674612693798170991 9963026511919040697256487)
            ·
              refine ⟨14944539767878561045884731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9963026511919040697256487 14944539767878561045884731)
              ·
                refine ⟨22416809651817841568827097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14944539767878561045884731 22416809651817841568827097)
                ·
                  refine ⟨16812607238863381176620323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22416809651817841568827097 16812607238863381176620323)
                  ·
                    refine ⟨25218910858295071764930485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16812607238863381176620323 25218910858295071764930485)
                    ·
                      refine ⟨2364272892965162977962233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25218910858295071764930485 2364272892965162977962233)
                      ·
                        rfl

theorem cell23_4604405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_4604405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604405 prefixEnd_4604405 := by exact prefixLift 4604405
  have htrace : WordTrace (prefixWord ++ tailWord_4604405) baseStart_4604405 baseEnd_4604405 := by
    simpa [prefixWord, tailWord_4604405, baseEnd_4604405] using wordTrace_append hprefix tailTrace_4604405
  have hstable : (prefixWord ++ tailWord_4604405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604405).length < 2 ^ (prefixWord ++ tailWord_4604405).sum := by decide
  have hdescent : baseEnd_4604405 < baseStart_4604405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604421 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 4, 5]
def baseStart_4604421 : Nat := 118140960795 + 4604421 * 2 ^ 59
def prefixEnd_4604421 : Nat := 4983230072969 + 3 ^ 40 * 4604421 * 2
def baseEnd_4604421 : Nat := 788093702885211638454053

theorem tailTrace_4604421 : CollatzResearch.WordTrace tailWord_4604421 prefixEnd_4604421 788093702885211638454053 := by
  unfold tailWord_4604421
  simp only [CollatzResearch.WordTrace]
  refine ⟨167937030451976564345597117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111958020301317709563731411 167937030451976564345597117)
  ·
    refine ⟨62976386419491211629598919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167937030451976564345597117 62976386419491211629598919)
    ·
      refine ⟨94464579629236817444398379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62976386419491211629598919 94464579629236817444398379)
      ·
        refine ⟨141696869443855226166597569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94464579629236817444398379 141696869443855226166597569)
        ·
          refine ⟨106272652082891419624948177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141696869443855226166597569 106272652082891419624948177)
          ·
            refine ⟨79704489062168564718711133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106272652082891419624948177 79704489062168564718711133)
            ·
              refine ⟨29889183398313211769516675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79704489062168564718711133 29889183398313211769516675)
              ·
                refine ⟨44833775097469817654275013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29889183398313211769516675 44833775097469817654275013)
                ·
                  refine ⟨8406332830775590810176565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44833775097469817654275013 8406332830775590810176565)
                  ·
                    refine ⟨788093702885211638454053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8406332830775590810176565 788093702885211638454053)
                    ·
                      rfl

theorem cell23_4604421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_4604421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604421 prefixEnd_4604421 := by exact prefixLift 4604421
  have htrace : WordTrace (prefixWord ++ tailWord_4604421) baseStart_4604421 baseEnd_4604421 := by
    simpa [prefixWord, tailWord_4604421, baseEnd_4604421] using wordTrace_append hprefix tailTrace_4604421
  have hstable : (prefixWord ++ tailWord_4604421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604421).length < 2 ^ (prefixWord ++ tailWord_4604421).sum := by decide
  have hdescent : baseEnd_4604421 < baseStart_4604421 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604436 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4604436 : Nat := 118140960795 + 4604436 * 2 ^ 59
def prefixEnd_4604436 : Nat := 4983230072969 + 3 ^ 40 * 4604436 * 2
def baseEnd_4604436 : Nat := 2364288810865452356674591

theorem tailTrace_4604436 : CollatzResearch.WordTrace tailWord_4604436 prefixEnd_4604436 2364288810865452356674591 := by
  unfold tailWord_4604436
  simp only [CollatzResearch.WordTrace]
  refine ⟨83968788773461110953696581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111958385031281481271595441 83968788773461110953696581)
  ·
    refine ⟨15744147895023958303818109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83968788773461110953696581 15744147895023958303818109)
    ·
      refine ⟨5904055460633984363931791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15744147895023958303818109 5904055460633984363931791)
      ·
        refine ⟨8856083190950976545897687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904055460633984363931791 8856083190950976545897687)
        ·
          refine ⟨13284124786426464818846531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8856083190950976545897687 13284124786426464818846531)
          ·
            refine ⟨19926187179639697228269797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13284124786426464818846531 19926187179639697228269797)
            ·
              refine ⟨3736160096182443230300587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19926187179639697228269797 3736160096182443230300587)
              ·
                refine ⟨5604240144273664845450881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736160096182443230300587 5604240144273664845450881)
                ·
                  refine ⟨4203180108205248634088161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5604240144273664845450881 4203180108205248634088161)
                  ·
                    refine ⟨3152385081153936475566121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4203180108205248634088161 3152385081153936475566121)
                    ·
                      refine ⟨2364288810865452356674591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152385081153936475566121 2364288810865452356674591)
                      ·
                        rfl

theorem cell23_4604436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4604436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604436 prefixEnd_4604436 := by exact prefixLift 4604436
  have htrace : WordTrace (prefixWord ++ tailWord_4604436) baseStart_4604436 baseEnd_4604436 := by
    simpa [prefixWord, tailWord_4604436, baseEnd_4604436] using wordTrace_append hprefix tailTrace_4604436
  have hstable : (prefixWord ++ tailWord_4604436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604436).length < 2 ^ (prefixWord ++ tailWord_4604436).sum := by decide
  have hdescent : baseEnd_4604436 < baseStart_4604436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604471 : List Nat := [1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_4604471 : Nat := 118140960795 + 4604471 * 2 ^ 59
def prefixEnd_4604471 : Nat := 4983230072969 + 3 ^ 40 * 4604471 * 2
def baseEnd_4604471 : Nat := 2364306782688359719736929

theorem tailTrace_4604471 : CollatzResearch.WordTrace tailWord_4604471 prefixEnd_4604471 2364306782688359719736929 := by
  unfold tailWord_4604471
  simp only [CollatzResearch.WordTrace]
  refine ⟨167938854101795422884917267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111959236067863615256611511 167938854101795422884917267)
  ·
    refine ⟨251908281152693134327375901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167938854101795422884917267 251908281152693134327375901)
    ·
      refine ⟨94465605432259925372765963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251908281152693134327375901 94465605432259925372765963)
      ·
        refine ⟨141698408148389888059148945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94465605432259925372765963 141698408148389888059148945)
        ·
          refine ⟨106273806111292416044361709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141698408148389888059148945 106273806111292416044361709)
          ·
            refine ⟨39852677291734656016635641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106273806111292416044361709 39852677291734656016635641)
            ·
              refine ⟨29889507968800992012476731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39852677291734656016635641 29889507968800992012476731)
              ·
                refine ⟨44834261953201488018715097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29889507968800992012476731 44834261953201488018715097)
                ·
                  refine ⟨33625696464901116014036323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44834261953201488018715097 33625696464901116014036323)
                  ·
                    refine ⟨50438544697351674021054485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33625696464901116014036323 50438544697351674021054485)
                    ·
                      refine ⟨2364306782688359719736929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50438544697351674021054485 2364306782688359719736929)
                      ·
                        rfl

theorem cell23_4604471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_4604471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604471 prefixEnd_4604471 := by exact prefixLift 4604471
  have htrace : WordTrace (prefixWord ++ tailWord_4604471) baseStart_4604471 baseEnd_4604471 := by
    simpa [prefixWord, tailWord_4604471, baseEnd_4604471] using wordTrace_append hprefix tailTrace_4604471
  have hstable : (prefixWord ++ tailWord_4604471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604471).length < 2 ^ (prefixWord ++ tailWord_4604471).sum := by decide
  have hdescent : baseEnd_4604471 < baseStart_4604471 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604498 : List Nat := [3, 2, 2, 1, 2, 1, 1, 5, 6]
def baseStart_4604498 : Nat := 118140960795 + 4604498 * 2 ^ 59
def prefixEnd_4604498 : Nat := 4983230072969 + 3 ^ 40 * 4604498 * 2
def baseEnd_4604498 : Nat := 262702294074003457122145

theorem tailTrace_4604498 : CollatzResearch.WordTrace tailWord_4604498 prefixEnd_4604498 262702294074003457122145 := by
  unfold tailWord_4604498
  simp only [CollatzResearch.WordTrace]
  refine ⟨41984959718174401624037537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111959892581798404330766765 41984959718174401624037537)
  ·
    refine ⟨31488719788630801218028153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41984959718174401624037537 31488719788630801218028153)
    ·
      refine ⟨23616539841473100913521115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31488719788630801218028153 23616539841473100913521115)
      ·
        refine ⟨35424809762209651370281673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23616539841473100913521115 35424809762209651370281673)
        ·
          refine ⟨26568607321657238527711255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35424809762209651370281673 26568607321657238527711255)
          ·
            refine ⟨39852910982485857791566883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26568607321657238527711255 39852910982485857791566883)
            ·
              refine ⟨59779366473728786687350325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39852910982485857791566883 59779366473728786687350325)
              ·
                refine ⟨5604315606912073751939093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59779366473728786687350325 5604315606912073751939093)
                ·
                  refine ⟨262702294074003457122145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5604315606912073751939093 262702294074003457122145)
                  ·
                    rfl

theorem cell23_4604498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 5, 6].length) (baseStart_4604498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604498 prefixEnd_4604498 := by exact prefixLift 4604498
  have htrace : WordTrace (prefixWord ++ tailWord_4604498) baseStart_4604498 baseEnd_4604498 := by
    simpa [prefixWord, tailWord_4604498, baseEnd_4604498] using wordTrace_append hprefix tailTrace_4604498
  have hstable : (prefixWord ++ tailWord_4604498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604498).length < 2 ^ (prefixWord ++ tailWord_4604498).sum := by decide
  have hdescent : baseEnd_4604498 < baseStart_4604498 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604521 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 5]
def baseStart_4604521 : Nat := 118140960795 + 4604521 * 2 ^ 59
def prefixEnd_4604521 : Nat := 4983230072969 + 3 ^ 40 * 4604521 * 2
def baseEnd_4604521 : Nat := 2364332456721084524111699

theorem tailTrace_4604521 : CollatzResearch.WordTrace tailWord_4604521 prefixEnd_4604521 2364332456721084524111699 := by
  unfold tailWord_4604521
  simp only [CollatzResearch.WordTrace]
  refine ⟨167940677751614281424237417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111960451834409520949491611 167940677751614281424237417)
  ·
    refine ⟨125955508313710711068178063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167940677751614281424237417 125955508313710711068178063)
    ·
      refine ⟨188933262470566066602267095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125955508313710711068178063 188933262470566066602267095)
      ·
        refine ⟨283399893705849099903400643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188933262470566066602267095 283399893705849099903400643)
        ·
          refine ⟨425099840558773649855100965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283399893705849099903400643 425099840558773649855100965)
          ·
            refine ⟨79706220104770059347831431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 425099840558773649855100965 79706220104770059347831431)
            ·
              refine ⟨119559330157155089021747147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79706220104770059347831431 119559330157155089021747147)
              ·
                refine ⟨179338995235732633532620721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119559330157155089021747147 179338995235732633532620721)
                ·
                  refine ⟨134504246426799475149465541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179338995235732633532620721 134504246426799475149465541)
                  ·
                    refine ⟨25219546205024901590524789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 134504246426799475149465541 25219546205024901590524789)
                    ·
                      refine ⟨2364332456721084524111699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25219546205024901590524789 2364332456721084524111699)
                      ·
                        rfl

theorem cell23_4604521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 4, 5].length) (baseStart_4604521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604521 prefixEnd_4604521 := by exact prefixLift 4604521
  have htrace : WordTrace (prefixWord ++ tailWord_4604521) baseStart_4604521 baseEnd_4604521 := by
    simpa [prefixWord, tailWord_4604521, baseEnd_4604521] using wordTrace_append hprefix tailTrace_4604521
  have hstable : (prefixWord ++ tailWord_4604521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604521).length < 2 ^ (prefixWord ++ tailWord_4604521).sum := by decide
  have hdescent : baseEnd_4604521 < baseStart_4604521 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604535 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 2, 3, 2]
def baseStart_4604535 : Nat := 118140960795 + 4604535 * 2 ^ 59
def prefixEnd_4604535 : Nat := 4983230072969 + 3 ^ 40 * 4604535 * 2
def baseEnd_4604535 : Nat := 2364339645450247469336635

theorem tailTrace_4604535 : CollatzResearch.WordTrace tailWord_4604535 prefixEnd_4604535 2364339645450247469336635 := by
  unfold tailWord_4604535
  simp only [CollatzResearch.WordTrace]
  refine ⟨167941188373563561815247059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111960792249042374543498039 167941188373563561815247059)
  ·
    refine ⟨251911782560345342722870589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167941188373563561815247059 251911782560345342722870589)
    ·
      refine ⟨94466918460129503521076471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251911782560345342722870589 94466918460129503521076471)
      ·
        refine ⟨141700377690194255281614707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94466918460129503521076471 141700377690194255281614707)
        ·
          refine ⟨212550566535291382922422061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141700377690194255281614707 212550566535291382922422061)
          ·
            refine ⟨79706462450734268595908273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212550566535291382922422061 79706462450734268595908273)
            ·
              refine ⟨59779846838050701446931205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79706462450734268595908273 59779846838050701446931205)
              ·
                refine ⟨11208721282134506521299601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59779846838050701446931205 11208721282134506521299601)
                ·
                  refine ⟨8406540961600879890974701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11208721282134506521299601 8406540961600879890974701)
                  ·
                    refine ⟨3152452860600329959115513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8406540961600879890974701 3152452860600329959115513)
                    ·
                      refine ⟨2364339645450247469336635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152452860600329959115513 2364339645450247469336635)
                      ·
                        rfl

theorem cell23_4604535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_4604535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604535 prefixEnd_4604535 := by exact prefixLift 4604535
  have htrace : WordTrace (prefixWord ++ tailWord_4604535) baseStart_4604535 baseEnd_4604535 := by
    simpa [prefixWord, tailWord_4604535, baseEnd_4604535] using wordTrace_append hprefix tailTrace_4604535
  have hstable : (prefixWord ++ tailWord_4604535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604535).length < 2 ^ (prefixWord ++ tailWord_4604535).sum := by decide
  have hdescent : baseEnd_4604535 < baseStart_4604535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604562 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_4604562 : Nat := 118140960795 + 4604562 * 2 ^ 59
def prefixEnd_4604562 : Nat := 4983230072969 + 3 ^ 40 * 4604562 * 2
def baseEnd_4604562 : Nat := 788117836475972954566337

theorem tailTrace_4604562 : CollatzResearch.WordTrace tailWord_4604562 prefixEnd_4604562 788117836475972954566337 := by
  unfold tailWord_4604562
  simp only [CollatzResearch.WordTrace]
  refine ⟨41985543286116436356619985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111961448762977163617653293 41985543286116436356619985)
  ·
    refine ⟨31489157464587327267464989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41985543286116436356619985 31489157464587327267464989)
    ·
      refine ⟨11808434049220247725299371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31489157464587327267464989 11808434049220247725299371)
      ·
        refine ⟨17712651073830371587949057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11808434049220247725299371 17712651073830371587949057)
        ·
          refine ⟨13284488305372778690961793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17712651073830371587949057 13284488305372778690961793)
          ·
            refine ⟨9963366229029584018221345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13284488305372778690961793 9963366229029584018221345)
            ·
              refine ⟨7472524671772188013666009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9963366229029584018221345 7472524671772188013666009)
              ·
                refine ⟨5604393503829141010249507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7472524671772188013666009 5604393503829141010249507)
                ·
                  refine ⟨8406590255743711515374261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604393503829141010249507 8406590255743711515374261)
                  ·
                    refine ⟨788117836475972954566337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8406590255743711515374261 788117836475972954566337)
                    ·
                      rfl

theorem cell23_4604562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_4604562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604562 prefixEnd_4604562 := by exact prefixLift 4604562
  have htrace : WordTrace (prefixWord ++ tailWord_4604562) baseStart_4604562 baseEnd_4604562 := by
    simpa [prefixWord, tailWord_4604562, baseEnd_4604562] using wordTrace_append hprefix tailTrace_4604562
  have hstable : (prefixWord ++ tailWord_4604562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604562).length < 2 ^ (prefixWord ++ tailWord_4604562).sum := by decide
  have hdescent : baseEnd_4604562 < baseStart_4604562 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604568 : List Nat := [2, 1, 2, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_4604568 : Nat := 118140960795 + 4604568 * 2 ^ 59
def prefixEnd_4604568 : Nat := 4983230072969 + 3 ^ 40 * 4604568 * 2
def baseEnd_4604568 : Nat := 2364356590311845840223983

theorem tailTrace_4604568 : CollatzResearch.WordTrace tailWord_4604568 prefixEnd_4604568 2364356590311845840223983 := by
  unfold tailWord_4604568
  simp only [CollatzResearch.WordTrace]
  refine ⟨83971195991222004225599179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111961594654962672300798905 83971195991222004225599179)
  ·
    refine ⟨125956793986833006338398769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83971195991222004225599179 125956793986833006338398769)
    ·
      refine ⟨94467595490124754753799077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125956793986833006338398769 94467595490124754753799077)
      ·
        refine ⟨17712674154398391516337327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94467595490124754753799077 17712674154398391516337327)
        ·
          refine ⟨26569011231597587274505991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17712674154398391516337327 26569011231597587274505991)
          ·
            refine ⟨39853516847396380911758987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26569011231597587274505991 39853516847396380911758987)
            ·
              refine ⟨59780275271094571367638481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39853516847396380911758987 59780275271094571367638481)
              ·
                refine ⟨44835206453320928525728861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59780275271094571367638481 44835206453320928525728861)
                ·
                  refine ⟨16813202419995348197148323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44835206453320928525728861 16813202419995348197148323)
                  ·
                    refine ⟨25219803629993022295722485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16813202419995348197148323 25219803629993022295722485)
                    ·
                      refine ⟨2364356590311845840223983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25219803629993022295722485 2364356590311845840223983)
                      ·
                        rfl

theorem cell23_4604568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_4604568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604568 prefixEnd_4604568 := by exact prefixLift 4604568
  have htrace : WordTrace (prefixWord ++ tailWord_4604568) baseStart_4604568 baseEnd_4604568 := by
    simpa [prefixWord, tailWord_4604568, baseEnd_4604568] using wordTrace_append hprefix tailTrace_4604568
  have hstable : (prefixWord ++ tailWord_4604568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604568).length < 2 ^ (prefixWord ++ tailWord_4604568).sum := by decide
  have hdescent : baseEnd_4604568 < baseStart_4604568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604576 : List Nat := [2, 1, 1, 4, 4, 2, 1, 3, 1, 1, 3]
def baseStart_4604576 : Nat := 118140960795 + 4604576 * 2 ^ 59
def prefixEnd_4604576 : Nat := 4983230072969 + 3 ^ 40 * 4604576 * 2
def baseEnd_4604576 : Nat := 2364360698157081808923947

theorem tailTrace_4604576 : CollatzResearch.WordTrace tailWord_4604576 prefixEnd_4604576 2364360698157081808923947 := by
  unfold tailWord_4604576
  simp only [CollatzResearch.WordTrace]
  refine ⟨83971341883207512908744791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111961789177610017211659721 83971341883207512908744791)
  ·
    refine ⟨125957012824811269363117187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83971341883207512908744791 125957012824811269363117187)
    ·
      refine ⟨188935519237216904044675781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125957012824811269363117187 188935519237216904044675781)
      ·
        refine ⟨35425409856978169508376709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188935519237216904044675781 35425409856978169508376709)
        ·
          refine ⟨6642264348183406782820633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35425409856978169508376709 6642264348183406782820633)
          ·
            refine ⟨4981698261137555087115475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6642264348183406782820633 4981698261137555087115475)
            ·
              refine ⟨7472547391706332630673213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4981698261137555087115475 7472547391706332630673213)
              ·
                refine ⟨2802205271889874736502455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7472547391706332630673213 2802205271889874736502455)
                ·
                  refine ⟨4203307907834812104753683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802205271889874736502455 4203307907834812104753683)
                  ·
                    refine ⟨6304961861752218157130525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4203307907834812104753683 6304961861752218157130525)
                    ·
                      refine ⟨2364360698157081808923947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6304961861752218157130525 2364360698157081808923947)
                      ·
                        rfl

theorem cell23_4604576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_4604576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604576 prefixEnd_4604576 := by exact prefixLift 4604576
  have htrace : WordTrace (prefixWord ++ tailWord_4604576) baseStart_4604576 baseEnd_4604576 := by
    simpa [prefixWord, tailWord_4604576, baseEnd_4604576] using wordTrace_append hprefix tailTrace_4604576
  have hstable : (prefixWord ++ tailWord_4604576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604576).length < 2 ^ (prefixWord ++ tailWord_4604576).sum := by decide
  have hdescent : baseEnd_4604576 < baseStart_4604576 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604586 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2]
def baseStart_4604586 : Nat := 118140960795 + 4604586 * 2 ^ 59
def prefixEnd_4604586 : Nat := 4983230072969 + 3 ^ 40 * 4604586 * 2
def baseEnd_4604586 : Nat := 2364365832963626769798901

theorem tailTrace_4604586 : CollatzResearch.WordTrace tailWord_4604586 prefixEnd_4604586 2364365832963626769798901 := by
  unfold tailWord_4604586
  simp only [CollatzResearch.WordTrace]
  refine ⟨41985762124094699381338403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111962032330919198350235741 41985762124094699381338403)
  ·
    refine ⟨62978643186142049072007605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41985762124094699381338403 62978643186142049072007605)
    ·
      refine ⟨5904247798700817100500713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62978643186142049072007605 5904247798700817100500713)
      ·
        refine ⟨4428185849025612825375535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5904247798700817100500713 4428185849025612825375535)
        ·
          refine ⟨6642278773538419238063303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4428185849025612825375535 6642278773538419238063303)
          ·
            refine ⟨9963418160307628857094955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642278773538419238063303 9963418160307628857094955)
            ·
              refine ⟨14945127240461443285642433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9963418160307628857094955 14945127240461443285642433)
              ·
                refine ⟨11208845430346082464231825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14945127240461443285642433 11208845430346082464231825)
                ·
                  refine ⟨8406634072759561848173869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11208845430346082464231825 8406634072759561848173869)
                  ·
                    refine ⟨3152487777284835693065201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8406634072759561848173869 3152487777284835693065201)
                    ·
                      refine ⟨2364365832963626769798901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152487777284835693065201 2364365832963626769798901)
                      ·
                        rfl

theorem cell23_4604586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_4604586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604586 prefixEnd_4604586 := by exact prefixLift 4604586
  have htrace : WordTrace (prefixWord ++ tailWord_4604586) baseStart_4604586 baseEnd_4604586 := by
    simpa [prefixWord, tailWord_4604586, baseEnd_4604586] using wordTrace_append hprefix tailTrace_4604586
  have hstable : (prefixWord ++ tailWord_4604586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604586).length < 2 ^ (prefixWord ++ tailWord_4604586).sum := by decide
  have hdescent : baseEnd_4604586 < baseStart_4604586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604593 : List Nat := [1, 2, 2, 6, 1, 1, 3, 2, 1, 1, 3]
def baseStart_4604593 : Nat := 118140960795 + 4604593 * 2 ^ 59
def prefixEnd_4604593 : Nat := 4983230072969 + 3 ^ 40 * 4604593 * 2
def baseEnd_4604593 : Nat := 2364369427328208242411369

theorem tailTrace_4604593 : CollatzResearch.WordTrace tailWord_4604593 prefixEnd_4604593 2364369427328208242411369 := by
  unfold tailWord_4604593
  simp only [CollatzResearch.WordTrace]
  refine ⟨167943303807353437720858433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111962202538235625147238955 167943303807353437720858433)
  ·
    refine ⟨125957477855515078290643825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167943303807353437720858433 125957477855515078290643825)
    ·
      refine ⟨94468108391636308717982869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125957477855515078290643825 94468108391636308717982869)
      ·
        refine ⟨4428192580857951971155447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 94468108391636308717982869 4428192580857951971155447)
        ·
          refine ⟨6642288871286927956733171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4428192580857951971155447 6642288871286927956733171)
          ·
            refine ⟨9963433306930391935099757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6642288871286927956733171 9963433306930391935099757)
            ·
              refine ⟨3736287490098896975662409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9963433306930391935099757 3736287490098896975662409)
              ·
                refine ⟨2802215617574172731746807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3736287490098896975662409 2802215617574172731746807)
                ·
                  refine ⟨4203323426361259097620211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802215617574172731746807 4203323426361259097620211)
                  ·
                    refine ⟨6304985139541888646430317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4203323426361259097620211 6304985139541888646430317)
                    ·
                      refine ⟨2364369427328208242411369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6304985139541888646430317 2364369427328208242411369)
                      ·
                        rfl

theorem cell23_4604593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_4604593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604593 prefixEnd_4604593 := by exact prefixLift 4604593
  have htrace : WordTrace (prefixWord ++ tailWord_4604593) baseStart_4604593 baseEnd_4604593 := by
    simpa [prefixWord, tailWord_4604593, baseEnd_4604593] using wordTrace_append hprefix tailTrace_4604593
  have hstable : (prefixWord ++ tailWord_4604593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604593).length < 2 ^ (prefixWord ++ tailWord_4604593).sum := by decide
  have hdescent : baseEnd_4604593 < baseStart_4604593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604615 : List Nat := [1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_4604615 : Nat := 118140960795 + 4604615 * 2 ^ 59
def prefixEnd_4604615 : Nat := 4983230072969 + 3 ^ 40 * 4604615 * 2
def baseEnd_4604615 : Nat := 2364380723902607156336267

theorem tailTrace_4604615 : CollatzResearch.WordTrace tailWord_4604615 prefixEnd_4604615 2364380723902607156336267 := by
  unfold tailWord_4604615
  simp only [CollatzResearch.WordTrace]
  refine ⟨167944106213273735478159299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111962737475515823652106199 167944106213273735478159299)
  ·
    refine ⟨251916159319910603217238949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167944106213273735478159299 251916159319910603217238949)
    ·
      refine ⟨47234279872483238103232303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251916159319910603217238949 47234279872483238103232303)
      ·
        refine ⟨70851419808724857154848455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47234279872483238103232303 70851419808724857154848455)
        ·
          refine ⟨106277129713087285732272683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70851419808724857154848455 106277129713087285732272683)
          ·
            refine ⟨159415694569630928598409025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106277129713087285732272683 159415694569630928598409025)
            ·
              refine ⟨119561770927223196448806769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159415694569630928598409025 119561770927223196448806769)
              ·
                refine ⟨89671328195417397336605077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119561770927223196448806769 89671328195417397336605077)
                ·
                  refine ⟨4203343509160190500153363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 89671328195417397336605077 4203343509160190500153363)
                  ·
                    refine ⟨6305015263740285750230045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4203343509160190500153363 6305015263740285750230045)
                    ·
                      refine ⟨2364380723902607156336267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305015263740285750230045 2364380723902607156336267)
                      ·
                        rfl

theorem cell23_4604615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_4604615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604615 prefixEnd_4604615 := by exact prefixLift 4604615
  have htrace : WordTrace (prefixWord ++ tailWord_4604615) baseStart_4604615 baseEnd_4604615 := by
    simpa [prefixWord, tailWord_4604615, baseEnd_4604615] using wordTrace_append hprefix tailTrace_4604615
  have hstable : (prefixWord ++ tailWord_4604615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604615).length < 2 ^ (prefixWord ++ tailWord_4604615).sum := by decide
  have hdescent : baseEnd_4604615 < baseStart_4604615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604636 : List Nat := [2, 2, 5, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4604636 : Nat := 118140960795 + 4604636 * 2 ^ 59
def prefixEnd_4604636 : Nat := 4983230072969 + 3 ^ 40 * 4604636 * 2
def baseEnd_4604636 : Nat := 2364391506996351574173671

theorem tailTrace_4604636 : CollatzResearch.WordTrace tailWord_4604636 prefixEnd_4604636 2364391506996351574173671 := by
  unfold tailWord_4604636
  simp only [CollatzResearch.WordTrace]
  refine ⟨83972436073098828032336881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111963248097465104043115841 83972436073098828032336881)
  ·
    refine ⟨62979327054824121024252661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83972436073098828032336881 62979327054824121024252661)
    ·
      refine ⟨5904311911389761346023687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62979327054824121024252661 5904311911389761346023687)
      ·
        refine ⟨8856467867084642019035531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5904311911389761346023687 8856467867084642019035531)
        ·
          refine ⟨13284701800626963028553297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8856467867084642019035531 13284701800626963028553297)
          ·
            refine ⟨9963526350470222271414973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13284701800626963028553297 9963526350470222271414973)
            ·
              refine ⟨3736322381426333351780615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9963526350470222271414973 3736322381426333351780615)
              ·
                refine ⟨5604483572139500027670923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736322381426333351780615 5604483572139500027670923)
                ·
                  refine ⟨8406725358209250041506385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604483572139500027670923 8406725358209250041506385)
                  ·
                    refine ⟨6305044018656937531129789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8406725358209250041506385 6305044018656937531129789)
                    ·
                      refine ⟨2364391506996351574173671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305044018656937531129789 2364391506996351574173671)
                      ·
                        rfl

theorem cell23_4604636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4604636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604636 prefixEnd_4604636 := by exact prefixLift 4604636
  have htrace : WordTrace (prefixWord ++ tailWord_4604636) baseStart_4604636 baseEnd_4604636 := by
    simpa [prefixWord, tailWord_4604636, baseEnd_4604636] using wordTrace_append hprefix tailTrace_4604636
  have hstable : (prefixWord ++ tailWord_4604636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604636).length < 2 ^ (prefixWord ++ tailWord_4604636).sum := by decide
  have hdescent : baseEnd_4604636 < baseStart_4604636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604705 : List Nat := [1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 3]
def baseStart_4604705 : Nat := 118140960795 + 4604705 * 2 ^ 59
def prefixEnd_4604705 : Nat := 4983230072969 + 3 ^ 40 * 4604705 * 2
def baseEnd_4604705 : Nat := 2364426937161511804210853

theorem tailTrace_4604705 : CollatzResearch.WordTrace tailWord_4604705 prefixEnd_4604705 2364426937161511804210853 := by
  unfold tailWord_4604705
  simp only [CollatzResearch.WordTrace]
  refine ⟨167947388782947680848935569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111964925855298453899290379 167947388782947680848935569)
  ·
    refine ⟨125960541587210760636701677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167947388782947680848935569 125960541587210760636701677)
    ·
      refine ⟨47235203095204035238763129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125960541587210760636701677 47235203095204035238763129)
      ·
        refine ⟨35426402321403026429072347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47235203095204035238763129 35426402321403026429072347)
        ·
          refine ⟨53139603482104539643608521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35426402321403026429072347 53139603482104539643608521)
          ·
            refine ⟨39854702611578404732706391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53139603482104539643608521 39854702611578404732706391)
            ·
              refine ⟨59782053917367607099059587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39854702611578404732706391 59782053917367607099059587)
              ·
                refine ⟨89673080876051410648589381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59782053917367607099059587 89673080876051410648589381)
                ·
                  refine ⟨16813702664259639496610509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89673080876051410648589381 16813702664259639496610509)
                  ·
                    refine ⟨6305138499097364811228941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16813702664259639496610509 6305138499097364811228941)
                    ·
                      refine ⟨2364426937161511804210853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305138499097364811228941 2364426937161511804210853)
                      ·
                        rfl

theorem cell23_4604705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_4604705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604705 prefixEnd_4604705 := by exact prefixLift 4604705
  have htrace : WordTrace (prefixWord ++ tailWord_4604705) baseStart_4604705 baseEnd_4604705 := by
    simpa [prefixWord, tailWord_4604705, baseEnd_4604705] using wordTrace_append hprefix tailTrace_4604705
  have hstable : (prefixWord ++ tailWord_4604705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604705).length < 2 ^ (prefixWord ++ tailWord_4604705).sum := by decide
  have hdescent : baseEnd_4604705 < baseStart_4604705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604706 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_4604706 : Nat := 118140960795 + 4604706 * 2 ^ 59
def prefixEnd_4604706 : Nat := 4983230072969 + 3 ^ 40 * 4604706 * 2
def baseEnd_4604706 : Nat := 2364427450642166300298349

theorem tailTrace_4604706 : CollatzResearch.WordTrace tailWord_4604706 prefixEnd_4604706 2364427450642166300298349 := by
  unfold tailWord_4604706
  simp only [CollatzResearch.WordTrace]
  refine ⟨41986856313986014504930493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111964950170629372013147981 41986856313986014504930493)
  ·
    refine ⟨15745071117744755439348935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41986856313986014504930493 15745071117744755439348935)
    ·
      refine ⟨23617606676617133159023403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15745071117744755439348935 23617606676617133159023403)
      ·
        refine ⟨35426410014925699738535105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23617606676617133159023403 35426410014925699738535105)
        ·
          refine ⟨26569807511194274803901329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35426410014925699738535105 26569807511194274803901329)
          ·
            refine ⟨19927355633395706102925997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26569807511194274803901329 19927355633395706102925997)
            ·
              refine ⟨7472758362523389788597249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19927355633395706102925997 7472758362523389788597249)
              ·
                refine ⟨5604568771892542341447937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7472758362523389788597249 5604568771892542341447937)
                ·
                  refine ⟨4203426578919406756085953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5604568771892542341447937 4203426578919406756085953)
                  ·
                    refine ⟨3152569934189555067064465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4203426578919406756085953 3152569934189555067064465)
                    ·
                      refine ⟨2364427450642166300298349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152569934189555067064465 2364427450642166300298349)
                      ·
                        rfl

theorem cell23_4604706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_4604706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604706 prefixEnd_4604706 := by exact prefixLift 4604706
  have htrace : WordTrace (prefixWord ++ tailWord_4604706) baseStart_4604706 baseEnd_4604706 := by
    simpa [prefixWord, tailWord_4604706, baseEnd_4604706] using wordTrace_append hprefix tailTrace_4604706
  have hstable : (prefixWord ++ tailWord_4604706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604706).length < 2 ^ (prefixWord ++ tailWord_4604706).sum := by decide
  have hdescent : baseEnd_4604706 < baseStart_4604706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604712 : List Nat := [2, 1, 5, 1, 1, 1, 1, 6, 5]
def baseStart_4604712 : Nat := 118140960795 + 4604712 * 2 ^ 59
def prefixEnd_4604712 : Nat := 4983230072969 + 3 ^ 40 * 4604712 * 2
def baseEnd_4604712 : Nat := 262714503502899252980369

theorem tailTrace_4604712 : CollatzResearch.WordTrace tailWord_4604712 prefixEnd_4604712 262714503502899252980369 := by
  unfold tailWord_4604712
  simp only [CollatzResearch.WordTrace]
  refine ⟨83973822046961160522220195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111965096062614880696293593 83973822046961160522220195)
  ·
    refine ⟨125960733070441740783330293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83973822046961160522220195 125960733070441740783330293)
    ·
      refine ⟨11808818725353913198437215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125960733070441740783330293 11808818725353913198437215)
      ·
        refine ⟨17713228088030869797655823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11808818725353913198437215 17713228088030869797655823)
        ·
          refine ⟨26569842132046304696483735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17713228088030869797655823 26569842132046304696483735)
          ·
            refine ⟨39854763198069457044725603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26569842132046304696483735 39854763198069457044725603)
            ·
              refine ⟨59782144797104185567088405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39854763198069457044725603 59782144797104185567088405)
              ·
                refine ⟨2802288037364258698457269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59782144797104185567088405 2802288037364258698457269)
                ·
                  refine ⟨262714503502899252980369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2802288037364258698457269 262714503502899252980369)
                  ·
                    rfl

theorem cell23_4604712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 6, 5].length) (baseStart_4604712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604712 prefixEnd_4604712 := by exact prefixLift 4604712
  have htrace : WordTrace (prefixWord ++ tailWord_4604712) baseStart_4604712 baseEnd_4604712 := by
    simpa [prefixWord, tailWord_4604712, baseEnd_4604712] using wordTrace_append hprefix tailTrace_4604712
  have hstable : (prefixWord ++ tailWord_4604712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604712).length < 2 ^ (prefixWord ++ tailWord_4604712).sum := by decide
  have hdescent : baseEnd_4604712 < baseStart_4604712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604725 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 1, 7]
def baseStart_4604725 : Nat := 118140960795 + 4604725 * 2 ^ 59
def prefixEnd_4604725 : Nat := 4983230072969 + 3 ^ 40 * 4604725 * 2
def baseEnd_4604725 : Nat := 788145735591533908653587

theorem tailTrace_4604725 : CollatzResearch.WordTrace tailWord_4604725 prefixEnd_4604725 788145735591533908653587 := by
  unfold tailWord_4604725
  simp only [CollatzResearch.WordTrace]
  refine ⟨167948118242875224264663629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111965412161916816176442419 167948118242875224264663629)
  ·
    refine ⟨62980544341078209099248861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167948118242875224264663629 62980544341078209099248861)
    ·
      refine ⟨23617704127904328412218323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62980544341078209099248861 23617704127904328412218323)
      ·
        refine ⟨35426556191856492618327485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23617704127904328412218323 35426556191856492618327485)
        ·
          refine ⟨13284958571946184731872807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35426556191856492618327485 13284958571946184731872807)
          ·
            refine ⟨19927437857919277097809211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13284958571946184731872807 19927437857919277097809211)
            ·
              refine ⟨29891156786878915646713817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19927437857919277097809211 29891156786878915646713817)
              ·
                refine ⟨22418367590159186735035363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29891156786878915646713817 22418367590159186735035363)
                ·
                  refine ⟨33627551385238780102553045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22418367590159186735035363 33627551385238780102553045)
                  ·
                    refine ⟨788145735591533908653587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33627551385238780102553045 788145735591533908653587)
                    ·
                      rfl

theorem cell23_4604725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_4604725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604725 prefixEnd_4604725 := by exact prefixLift 4604725
  have htrace : WordTrace (prefixWord ++ tailWord_4604725) baseStart_4604725 baseEnd_4604725 := by
    simpa [prefixWord, tailWord_4604725, baseEnd_4604725] using wordTrace_append hprefix tailTrace_4604725
  have hstable : (prefixWord ++ tailWord_4604725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604725).length < 2 ^ (prefixWord ++ tailWord_4604725).sum := by decide
  have hdescent : baseEnd_4604725 < baseStart_4604725 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604745 : List Nat := [1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 4]
def baseStart_4604745 : Nat := 118140960795 + 4604745 * 2 ^ 59
def prefixEnd_4604745 : Nat := 4983230072969 + 3 ^ 40 * 4604745 * 2
def baseEnd_4604745 : Nat := 2364447476387691647710669

theorem tailTrace_4604745 : CollatzResearch.WordTrace tailWord_4604745 prefixEnd_4604745 2364447476387691647710669 := by
  unfold tailWord_4604745
  simp only [CollatzResearch.WordTrace]
  refine ⟨167948847702802767680391689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111965898468535178453594459 167948847702802767680391689)
  ·
    refine ⟨125961635777102075760293767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167948847702802767680391689 125961635777102075760293767)
    ·
      refine ⟨188942453665653113640440651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125961635777102075760293767 188942453665653113640440651)
      ·
        refine ⟨283413680498479670460660977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188942453665653113640440651 283413680498479670460660977)
        ·
          refine ⟨212560260373859752845495733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283413680498479670460660977 212560260373859752845495733)
          ·
            refine ⟨19927524410049351829265225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 212560260373859752845495733 19927524410049351829265225)
            ·
              refine ⟨14945643307537013871948919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19927524410049351829265225 14945643307537013871948919)
              ·
                refine ⟨22418464961305520807923379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14945643307537013871948919 22418464961305520807923379)
                ·
                  refine ⟨33627697441958281211885069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22418464961305520807923379 33627697441958281211885069)
                  ·
                    refine ⟨12610386540734355454456901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33627697441958281211885069 12610386540734355454456901)
                    ·
                      refine ⟨2364447476387691647710669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12610386540734355454456901 2364447476387691647710669)
                      ·
                        rfl

theorem cell23_4604745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 2, 1, 1, 3, 4].length) (baseStart_4604745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604745 prefixEnd_4604745 := by exact prefixLift 4604745
  have htrace : WordTrace (prefixWord ++ tailWord_4604745) baseStart_4604745 baseEnd_4604745 := by
    simpa [prefixWord, tailWord_4604745, baseEnd_4604745] using wordTrace_append hprefix tailTrace_4604745
  have hstable : (prefixWord ++ tailWord_4604745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604745).length < 2 ^ (prefixWord ++ tailWord_4604745).sum := by decide
  have hdescent : baseEnd_4604745 < baseStart_4604745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604755 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 5, 4]
def baseStart_4604755 : Nat := 118140960795 + 4604755 * 2 ^ 59
def prefixEnd_4604755 : Nat := 4983230072969 + 3 ^ 40 * 4604755 * 2
def baseEnd_4604755 : Nat := 788150870398078869528541

theorem tailTrace_4604755 : CollatzResearch.WordTrace tailWord_4604755 prefixEnd_4604755 788150870398078869528541 := by
  unfold tailWord_4604755
  simp only [CollatzResearch.WordTrace]
  refine ⟨167949212432766539388255719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111966141621844359592170479 167949212432766539388255719)
  ·
    refine ⟨251923818649149809082383579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167949212432766539388255719 251923818649149809082383579)
    ·
      refine ⟨377885727973724713623575369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251923818649149809082383579 377885727973724713623575369)
      ·
        refine ⟨283414295980293535217681527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377885727973724713623575369 283414295980293535217681527)
        ·
          refine ⟨425121443970440302826522291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283414295980293535217681527 425121443970440302826522291)
          ·
            refine ⟨637682165955660454239783437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425121443970440302826522291 637682165955660454239783437)
            ·
              refine ⟨239130812233372670339918789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 637682165955660454239783437 239130812233372670339918789)
              ·
                refine ⟨44837027293757375688734773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 239130812233372670339918789 44837027293757375688734773)
                ·
                  refine ⟨4203471308789753970818885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44837027293757375688734773 4203471308789753970818885)
                  ·
                    refine ⟨788150870398078869528541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4203471308789753970818885 788150870398078869528541)
                    ·
                      rfl

theorem cell23_4604755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 4].length) (baseStart_4604755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604755 prefixEnd_4604755 := by exact prefixLift 4604755
  have htrace : WordTrace (prefixWord ++ tailWord_4604755) baseStart_4604755 baseEnd_4604755 := by
    simpa [prefixWord, tailWord_4604755, baseEnd_4604755] using wordTrace_append hprefix tailTrace_4604755
  have hstable : (prefixWord ++ tailWord_4604755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604755).length < 2 ^ (prefixWord ++ tailWord_4604755).sum := by decide
  have hdescent : baseEnd_4604755 < baseStart_4604755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604762 : List Nat := [3, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4]
def baseStart_4604762 : Nat := 118140960795 + 4604762 * 2 ^ 59
def prefixEnd_4604762 : Nat := 4983230072969 + 3 ^ 40 * 4604762 * 2
def baseEnd_4604762 : Nat := 2364456205558818081198091

theorem tailTrace_4604762 : CollatzResearch.WordTrace tailWord_4604762 prefixEnd_4604762 2364456205558818081198091 := by
  unfold tailWord_4604762
  simp only [CollatzResearch.WordTrace]
  refine ⟨41987366935935294895940135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111966311829160786389173693 41987366935935294895940135)
  ·
    refine ⟨62981050403902942343910203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41987366935935294895940135 62981050403902942343910203)
    ·
      refine ⟨94471575605854413515865305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62981050403902942343910203 94471575605854413515865305)
      ·
        refine ⟨70853681704390810136898979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94471575605854413515865305 70853681704390810136898979)
        ·
          refine ⟨106280522556586215205348469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70853681704390810136898979 106280522556586215205348469)
          ·
            refine ⟨9963798989679957675501419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106280522556586215205348469 9963798989679957675501419)
            ·
              refine ⟨14945698484519936513252129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9963798989679957675501419 14945698484519936513252129)
              ·
                refine ⟨11209273863389952384939097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14945698484519936513252129 11209273863389952384939097)
                ·
                  refine ⟨8406955397542464288704323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11209273863389952384939097 8406955397542464288704323)
                  ·
                    refine ⟨12610433096313696433056485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8406955397542464288704323 12610433096313696433056485)
                    ·
                      refine ⟨2364456205558818081198091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12610433096313696433056485 2364456205558818081198091)
                      ·
                        rfl

theorem cell23_4604762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 2, 2, 1, 4].length) (baseStart_4604762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604762 prefixEnd_4604762 := by exact prefixLift 4604762
  have htrace : WordTrace (prefixWord ++ tailWord_4604762) baseStart_4604762 baseEnd_4604762 := by
    simpa [prefixWord, tailWord_4604762, baseEnd_4604762] using wordTrace_append hprefix tailTrace_4604762
  have hstable : (prefixWord ++ tailWord_4604762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604762).length < 2 ^ (prefixWord ++ tailWord_4604762).sum := by decide
  have hdescent : baseEnd_4604762 < baseStart_4604762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604795 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 3]
def baseStart_4604795 : Nat := 118140960795 + 4604795 * 2 ^ 59
def prefixEnd_4604795 : Nat := 4983230072969 + 3 ^ 40 * 4604795 * 2
def baseEnd_4604795 : Nat := 2364473150420416452085439

theorem tailTrace_4604795 : CollatzResearch.WordTrace tailWord_4604795 prefixEnd_4604795 2364473150420416452085439 := by
  unfold tailWord_4604795
  simp only [CollatzResearch.WordTrace]
  refine ⟨167950671352621626219711839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111967114235081084146474559 167950671352621626219711839)
  ·
    refine ⟨251926007028932439329567759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167950671352621626219711839 251926007028932439329567759)
    ·
      refine ⟨377889010543398658994351639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251926007028932439329567759 377889010543398658994351639)
      ·
        refine ⟨566833515815097988491527459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377889010543398658994351639 566833515815097988491527459)
        ·
          refine ⟨850250273722646982737291189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566833515815097988491527459 850250273722646982737291189)
          ·
            refine ⟨79710963161498154631621049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 850250273722646982737291189 79710963161498154631621049)
            ·
              refine ⟨59783222371123615973715787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79710963161498154631621049 59783222371123615973715787)
              ·
                refine ⟨89674833556685423960573681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59783222371123615973715787 89674833556685423960573681)
                ·
                  refine ⟨67256125167514067970430261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89674833556685423960573681 67256125167514067970430261)
                  ·
                    refine ⟨6305261734454443872227837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67256125167514067970430261 6305261734454443872227837)
                    ·
                      refine ⟨2364473150420416452085439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305261734454443872227837 2364473150420416452085439)
                      ·
                        rfl

theorem cell23_4604795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 2, 5, 3].length) (baseStart_4604795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604795 prefixEnd_4604795 := by exact prefixLift 4604795
  have htrace : WordTrace (prefixWord ++ tailWord_4604795) baseStart_4604795 baseEnd_4604795 := by
    simpa [prefixWord, tailWord_4604795, baseEnd_4604795] using wordTrace_append hprefix tailTrace_4604795
  have hstable : (prefixWord ++ tailWord_4604795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604795).length < 2 ^ (prefixWord ++ tailWord_4604795).sum := by decide
  have hdescent : baseEnd_4604795 < baseStart_4604795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604829 : List Nat := [1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 3]
def baseStart_4604829 : Nat := 118140960795 + 4604829 * 2 ^ 59
def prefixEnd_4604829 : Nat := 4983230072969 + 3 ^ 40 * 4604829 * 2
def baseEnd_4604829 : Nat := 2364490608762669319060283

theorem tailTrace_4604829 : CollatzResearch.WordTrace tailWord_4604829 prefixEnd_4604829 2364490608762669319060283 := by
  unfold tailWord_4604829
  simp only [CollatzResearch.WordTrace]
  refine ⟨167951911434498450026449541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111967940956332300017633027 167951911434498450026449541)
  ·
    refine ⟨31490983393968459379959289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167951911434498450026449541 31490983393968459379959289)
    ·
      refine ⟨23618237545476344534969467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31490983393968459379959289 23618237545476344534969467)
      ·
        refine ⟨35427356318214516802454201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23618237545476344534969467 35427356318214516802454201)
        ·
          refine ⟨26570517238660887601840651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35427356318214516802454201 26570517238660887601840651)
          ·
            refine ⟨39855775857991331402760977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26570517238660887601840651 39855775857991331402760977)
            ·
              refine ⟨29891831893493498552070733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39855775857991331402760977 29891831893493498552070733)
              ·
                refine ⟨11209436960060061957026525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29891831893493498552070733 11209436960060061957026525)
                ·
                  refine ⟨4203538860022523233884947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11209436960060061957026525 4203538860022523233884947)
                  ·
                    refine ⟨6305308290033784850827421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4203538860022523233884947 6305308290033784850827421)
                    ·
                      refine ⟨2364490608762669319060283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305308290033784850827421 2364490608762669319060283)
                      ·
                        rfl

theorem cell23_4604829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_4604829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604829 prefixEnd_4604829 := by exact prefixLift 4604829
  have htrace : WordTrace (prefixWord ++ tailWord_4604829) baseStart_4604829 baseEnd_4604829 := by
    simpa [prefixWord, tailWord_4604829, baseEnd_4604829] using wordTrace_append hprefix tailTrace_4604829
  have hstable : (prefixWord ++ tailWord_4604829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604829).length < 2 ^ (prefixWord ++ tailWord_4604829).sum := by decide
  have hdescent : baseEnd_4604829 < baseStart_4604829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604856 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 2, 3, 2]
def baseStart_4604856 : Nat := 118140960795 + 4604856 * 2 ^ 59
def prefixEnd_4604856 : Nat := 4983230072969 + 3 ^ 40 * 4604856 * 2
def baseEnd_4604856 : Nat := 2364504472740340713422659

theorem tailTrace_4604856 : CollatzResearch.WordTrace tailWord_4604856 prefixEnd_4604856 2364504472740340713422659 := by
  unfold tailWord_4604856
  simp only [CollatzResearch.WordTrace]
  refine ⟨83976448102700316818841211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111968597470267089091788281 83976448102700316818841211)
  ·
    refine ⟨125964672154050475228261817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83976448102700316818841211 125964672154050475228261817)
    ·
      refine ⟨94473504115537856421196363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125964672154050475228261817 94473504115537856421196363)
      ·
        refine ⟨141710256173306784631794545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94473504115537856421196363 141710256173306784631794545)
        ·
          refine ⟨106282692129980088473845909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141710256173306784631794545 106282692129980088473845909)
          ·
            refine ⟨4982001193592816647211527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 106282692129980088473845909 4982001193592816647211527)
            ·
              refine ⟨7473001790389224970817291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982001193592816647211527 7473001790389224970817291)
              ·
                refine ⟨11209502685583837456225937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7473001790389224970817291 11209502685583837456225937)
                ·
                  refine ⟨8407127014187878092169453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11209502685583837456225937 8407127014187878092169453)
                  ·
                    refine ⟨3152672630320454284563545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8407127014187878092169453 3152672630320454284563545)
                    ·
                      refine ⟨2364504472740340713422659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152672630320454284563545 2364504472740340713422659)
                      ·
                        rfl

theorem cell23_4604856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 2, 3, 2].length) (baseStart_4604856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604856 prefixEnd_4604856 := by exact prefixLift 4604856
  have htrace : WordTrace (prefixWord ++ tailWord_4604856) baseStart_4604856 baseEnd_4604856 := by
    simpa [prefixWord, tailWord_4604856, baseEnd_4604856] using wordTrace_append hprefix tailTrace_4604856
  have hstable : (prefixWord ++ tailWord_4604856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604856).length < 2 ^ (prefixWord ++ tailWord_4604856).sum := by decide
  have hdescent : baseEnd_4604856 < baseStart_4604856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604862 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_4604862 : Nat := 118140960795 + 4604862 * 2 ^ 59
def prefixEnd_4604862 : Nat := 4983230072969 + 3 ^ 40 * 4604862 * 2
def baseEnd_4604862 : Nat := 788169184541422563315877

theorem tailTrace_4604862 : CollatzResearch.WordTrace tailWord_4604862 prefixEnd_4604862 788169184541422563315877 := by
  unfold tailWord_4604862
  simp only [CollatzResearch.WordTrace]
  refine ⟨20994139380422362082800105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111968743362252597774933893 20994139380422362082800105)
  ·
    refine ⟨15745604535316771562100079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20994139380422362082800105 15745604535316771562100079)
    ·
      refine ⟨23618406802975157343150119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15745604535316771562100079 23618406802975157343150119)
      ·
        refine ⟨35427610204462736014725179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23618406802975157343150119 35427610204462736014725179)
        ·
          refine ⟨53141415306694104022087769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35427610204462736014725179 53141415306694104022087769)
          ·
            refine ⟨39856061480020578016565827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53141415306694104022087769 39856061480020578016565827)
            ·
              refine ⟨59784092220030867024848741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39856061480020578016565827 59784092220030867024848741)
              ·
                refine ⟨11209517291255787567159139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59784092220030867024848741 11209517291255787567159139)
                ·
                  refine ⟨16814275936883681350738709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11209517291255787567159139 16814275936883681350738709)
                  ·
                    refine ⟨788169184541422563315877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16814275936883681350738709 788169184541422563315877)
                    ·
                      rfl

theorem cell23_4604862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_4604862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604862 prefixEnd_4604862 := by exact prefixLift 4604862
  have htrace : WordTrace (prefixWord ++ tailWord_4604862) baseStart_4604862 baseEnd_4604862 := by
    simpa [prefixWord, tailWord_4604862, baseEnd_4604862] using wordTrace_append hprefix tailTrace_4604862
  have hstable : (prefixWord ++ tailWord_4604862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604862).length < 2 ^ (prefixWord ++ tailWord_4604862).sum := by decide
  have hdescent : baseEnd_4604862 < baseStart_4604862 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604875 : List Nat := [1, 1, 1, 1, 3, 6, 10]
def baseStart_4604875 : Nat := 118140960795 + 4604875 * 2 ^ 59
def prefixEnd_4604875 : Nat := 4983230072969 + 3 ^ 40 * 4604875 * 2
def baseEnd_4604875 : Nat := 29191533689787359741791

theorem tailTrace_4604875 : CollatzResearch.WordTrace tailWord_4604875 prefixEnd_4604875 29191533689787359741791 := by
  unfold tailWord_4604875
  simp only [CollatzResearch.WordTrace]
  refine ⟨167953589192331799882624079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111969059461554533255082719 167953589192331799882624079)
  ·
    refine ⟨251930383788497699823936119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167953589192331799882624079 251930383788497699823936119)
    ·
      refine ⟨377895575682746549735904179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251930383788497699823936119 377895575682746549735904179)
      ·
        refine ⟨566843363524119824603856269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377895575682746549735904179 566843363524119824603856269)
        ·
          refine ⟨212566261321544934226446101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 566843363524119824603856269 212566261321544934226446101)
          ·
            refine ⟨9964043499447418791864661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 212566261321544934226446101 9964043499447418791864661)
            ·
              refine ⟨29191533689787359741791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 9964043499447418791864661 29191533689787359741791)
              ·
                rfl

theorem cell23_4604875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 10].length) (baseStart_4604875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604875 prefixEnd_4604875 := by exact prefixLift 4604875
  have htrace : WordTrace (prefixWord ++ tailWord_4604875) baseStart_4604875 baseEnd_4604875 := by
    simpa [prefixWord, tailWord_4604875, baseEnd_4604875] using wordTrace_append hprefix tailTrace_4604875
  have hstable : (prefixWord ++ tailWord_4604875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604875).length < 2 ^ (prefixWord ++ tailWord_4604875).sum := by decide
  have hdescent : baseEnd_4604875 < baseStart_4604875 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604879 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 2, 4]
def baseStart_4604879 : Nat := 118140960795 + 4604879 * 2 ^ 59
def prefixEnd_4604879 : Nat := 4983230072969 + 3 ^ 40 * 4604879 * 2
def baseEnd_4604879 : Nat := 788172094265131374478351

theorem tailTrace_4604879 : CollatzResearch.WordTrace tailWord_4604879 prefixEnd_4604879 788172094265131374478351 := by
  unfold tailWord_4604879
  simp only [CollatzResearch.WordTrace]
  refine ⟨167953735084317308565769691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111969156722878205710513127 167953735084317308565769691)
  ·
    refine ⟨251930602626475962848654537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167953735084317308565769691 251930602626475962848654537)
    ·
      refine ⟨188947951969856972136490903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251930602626475962848654537 188947951969856972136490903)
      ·
        refine ⟨283421927954785458204736355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188947951969856972136490903 283421927954785458204736355)
        ·
          refine ⟨425132891932178187307104533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283421927954785458204736355 425132891932178187307104533)
          ·
            refine ⟨19928104309320852530020525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 425132891932178187307104533 19928104309320852530020525)
            ·
              refine ⟨7473039115995319698757697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19928104309320852530020525 7473039115995319698757697)
              ·
                refine ⟨5604779336996489774068273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7473039115995319698757697 5604779336996489774068273)
                ·
                  refine ⟨4203584502747367330551205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5604779336996489774068273 4203584502747367330551205)
                  ·
                    refine ⟨788172094265131374478351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4203584502747367330551205 788172094265131374478351)
                    ·
                      rfl

theorem cell23_4604879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_4604879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604879 prefixEnd_4604879 := by exact prefixLift 4604879
  have htrace : WordTrace (prefixWord ++ tailWord_4604879) baseStart_4604879 baseEnd_4604879 := by
    simpa [prefixWord, tailWord_4604879, baseEnd_4604879] using wordTrace_append hprefix tailTrace_4604879
  have hstable : (prefixWord ++ tailWord_4604879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604879).length < 2 ^ (prefixWord ++ tailWord_4604879).sum := by decide
  have hdescent : baseEnd_4604879 < baseStart_4604879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604906 : List Nat := [3, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3]
def baseStart_4604906 : Nat := 118140960795 + 4604906 * 2 ^ 59
def prefixEnd_4604906 : Nat := 4983230072969 + 3 ^ 40 * 4604906 * 2
def baseEnd_4604906 : Nat := 2364530146773065517797429

theorem tailTrace_4604906 : CollatzResearch.WordTrace tailWord_4604906 prefixEnd_4604906 2364530146773065517797429 := by
  unfold tailWord_4604906
  simp only [CollatzResearch.WordTrace]
  refine ⟨41988679963804873044250643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111969813236812994784668381 41988679963804873044250643)
  ·
    refine ⟨62983019945707309566375965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41988679963804873044250643 62983019945707309566375965)
    ·
      refine ⟨23618632479640241087390987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62983019945707309566375965 23618632479640241087390987)
      ·
        refine ⟨35427948719460361631086481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23618632479640241087390987 35427948719460361631086481)
        ·
          refine ⟨26570961539595271223314861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35427948719460361631086481 26570961539595271223314861)
          ·
            refine ⟨9964110577348226708743073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26570961539595271223314861 9964110577348226708743073)
            ·
              refine ⟨7473082933011170031557305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9964110577348226708743073 7473082933011170031557305)
              ·
                refine ⟨5604812199758377523667979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7473082933011170031557305 5604812199758377523667979)
                ·
                  refine ⟨8407218299637566285501969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604812199758377523667979 8407218299637566285501969)
                  ·
                    refine ⟨6305413724728174714126477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8407218299637566285501969 6305413724728174714126477)
                    ·
                      refine ⟨2364530146773065517797429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305413724728174714126477 2364530146773065517797429)
                      ·
                        rfl

theorem cell23_4604906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_4604906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604906 prefixEnd_4604906 := by exact prefixLift 4604906
  have htrace : WordTrace (prefixWord ++ tailWord_4604906) baseStart_4604906 baseEnd_4604906 := by
    simpa [prefixWord, tailWord_4604906, baseEnd_4604906] using wordTrace_append hprefix tailTrace_4604906
  have hstable : (prefixWord ++ tailWord_4604906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604906).length < 2 ^ (prefixWord ++ tailWord_4604906).sum := by decide
  have hdescent : baseEnd_4604906 < baseStart_4604906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604926 : List Nat := [4, 2, 2, 2, 3, 1, 9]
def baseStart_4604926 : Nat := 118140960795 + 4604926 * 2 ^ 59
def prefixEnd_4604926 : Nat := 4983230072969 + 3 ^ 40 * 4604926 * 2
def baseEnd_4604926 : Nat := 29191856992421672093177

theorem tailTrace_4604926 : CollatzResearch.WordTrace tailWord_4604926 prefixEnd_4604926 29191856992421672093177 := by
  unfold tailWord_4604926
  simp only [CollatzResearch.WordTrace]
  refine ⟨20994431164393379449091329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111970299543431357061820421 20994431164393379449091329)
  ·
    refine ⟨15745823373295034586818497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20994431164393379449091329 15745823373295034586818497)
    ·
      refine ⟨11809367529971275940113873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15745823373295034586818497 11809367529971275940113873)
      ·
        refine ⟨8857025647478456955085405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11809367529971275940113873 8857025647478456955085405)
        ·
          refine ⟨3321384617804421358157027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8857025647478456955085405 3321384617804421358157027)
          ·
            refine ⟨4982076926706632037235541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3321384617804421358157027 4982076926706632037235541)
            ·
              refine ⟨29191856992421672093177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4982076926706632037235541 29191856992421672093177)
              ·
                rfl

theorem cell23_4604926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 3, 1, 9].length) (baseStart_4604926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604926 prefixEnd_4604926 := by exact prefixLift 4604926
  have htrace : WordTrace (prefixWord ++ tailWord_4604926) baseStart_4604926 baseEnd_4604926 := by
    simpa [prefixWord, tailWord_4604926, baseEnd_4604926] using wordTrace_append hprefix tailTrace_4604926
  have hstable : (prefixWord ++ tailWord_4604926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604926).length < 2 ^ (prefixWord ++ tailWord_4604926).sum := by decide
  have hdescent : baseEnd_4604926 < baseStart_4604926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4604963 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 1, 3, 2]
def baseStart_4604963 : Nat := 118140960795 + 4604963 * 2 ^ 59
def prefixEnd_4604963 : Nat := 4983230072969 + 3 ^ 40 * 4604963 * 2
def baseEnd_4604963 : Nat := 2364559415170371794784667

theorem tailTrace_4604963 : CollatzResearch.WordTrace tailWord_4604963 prefixEnd_4604963 2364559415170371794784667 := by
  unfold tailWord_4604963
  simp only [CollatzResearch.WordTrace]
  refine ⟨167956798816012990911827543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111971199210675327274551695 167956798816012990911827543)
  ·
    refine ⟨251935198224019486367741315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167956798816012990911827543 251935198224019486367741315)
    ·
      refine ⟨377902797336029229551611973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251935198224019486367741315 377902797336029229551611973)
      ·
        refine ⟨70856774500505480540927245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 377902797336029229551611973 70856774500505480540927245)
        ·
          refine ⟨26571290437689555202847717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70856774500505480540927245 26571290437689555202847717)
          ·
            refine ⟨4982116957066791600533947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26571290437689555202847717 4982116957066791600533947)
            ·
              refine ⟨7473175435600187400800921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982116957066791600533947 7473175435600187400800921)
              ·
                refine ⟨5604881576700140550600691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7473175435600187400800921 5604881576700140550600691)
                ·
                  refine ⟨8407322365050210825901037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5604881576700140550600691 8407322365050210825901037)
                  ·
                    refine ⟨3152745886893829059712889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8407322365050210825901037 3152745886893829059712889)
                    ·
                      refine ⟨2364559415170371794784667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152745886893829059712889 2364559415170371794784667)
                      ·
                        rfl

theorem cell23_4604963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_4604963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4604963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4604963 prefixEnd_4604963 := by exact prefixLift 4604963
  have htrace : WordTrace (prefixWord ++ tailWord_4604963) baseStart_4604963 baseEnd_4604963 := by
    simpa [prefixWord, tailWord_4604963, baseEnd_4604963] using wordTrace_append hprefix tailTrace_4604963
  have hstable : (prefixWord ++ tailWord_4604963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4604963).length < 2 ^ (prefixWord ++ tailWord_4604963).sum := by decide
  have hdescent : baseEnd_4604963 < baseStart_4604963 := by decide
  rcases family_descends (prefixWord ++ tailWord_4604963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605066 : List Nat := [3, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2]
def baseStart_4605066 : Nat := 118140960795 + 4605066 * 2 ^ 59
def prefixEnd_4605066 : Nat := 4983230072969 + 3 ^ 40 * 4605066 * 2
def baseEnd_4605066 : Nat := 2364612303677784891796693

theorem tailTrace_4605066 : CollatzResearch.WordTrace tailWord_4605066 prefixEnd_4605066 2364612303677784891796693 := by
  unfold tailWord_4605066
  simp only [CollatzResearch.WordTrace]
  refine ⟨41990138883659959875706763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111973703689759893001884701 41990138883659959875706763)
  ·
    refine ⟨62985208325489939813560145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41990138883659959875706763 62985208325489939813560145)
    ·
      refine ⟨47238906244117454860170109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62985208325489939813560145 47238906244117454860170109)
      ·
        refine ⟨17714589841544045572563791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47238906244117454860170109 17714589841544045572563791)
        ·
          refine ⟨26571884762316068358845687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17714589841544045572563791 26571884762316068358845687)
          ·
            refine ⟨39857827143474102538268531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26571884762316068358845687 39857827143474102538268531)
            ·
              refine ⟨59786740715211153807402797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39857827143474102538268531 59786740715211153807402797)
              ·
                refine ⟨22420027768204182677776049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59786740715211153807402797 22420027768204182677776049)
                ·
                  refine ⟨16815020826153137008332037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22420027768204182677776049 16815020826153137008332037)
                  ·
                    refine ⟨3152816404903713189062257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16815020826153137008332037 3152816404903713189062257)
                    ·
                      refine ⟨2364612303677784891796693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152816404903713189062257 2364612303677784891796693)
                      ·
                        rfl

theorem cell23_4605066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 1, 3, 2, 4, 2].length) (baseStart_4605066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605066 prefixEnd_4605066 := by exact prefixLift 4605066
  have htrace : WordTrace (prefixWord ++ tailWord_4605066) baseStart_4605066 baseEnd_4605066 := by
    simpa [prefixWord, tailWord_4605066, baseEnd_4605066] using wordTrace_append hprefix tailTrace_4605066
  have hstable : (prefixWord ++ tailWord_4605066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605066).length < 2 ^ (prefixWord ++ tailWord_4605066).sum := by decide
  have hdescent : baseEnd_4605066 < baseStart_4605066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605093 : List Nat := [1, 3, 1, 2, 1, 4, 3, 3, 1, 4]
def baseStart_4605093 : Nat := 118140960795 + 4605093 * 2 ^ 59
def prefixEnd_4605093 : Nat := 4983230072969 + 3 ^ 40 * 4605093 * 2
def baseEnd_4605093 : Nat := 788208722551818762053023

theorem tailTrace_4605093 : CollatzResearch.WordTrace tailWord_4605093 prefixEnd_4605093 788208722551818762053023 := by
  unfold tailWord_4605093
  simp only [CollatzResearch.WordTrace]
  refine ⟨167961540305542023114059933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111974360203694682076039955 167961540305542023114059933)
  ·
    refine ⟨62985577614578258667772475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167961540305542023114059933 62985577614578258667772475)
    ·
      refine ⟨94478366421867388001658713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62985577614578258667772475 94478366421867388001658713)
      ·
        refine ⟨70858774816400541001244035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94478366421867388001658713 70858774816400541001244035)
        ·
          refine ⟨106288162224600811501866053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70858774816400541001244035 106288162224600811501866053)
          ·
            refine ⟨19929030417112652156599885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106288162224600811501866053 19929030417112652156599885)
            ·
              refine ⟨7473386406417244558724957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19929030417112652156599885 7473386406417244558724957)
              ·
                refine ⟨2802519902406466709521859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7473386406417244558724957 2802519902406466709521859)
                ·
                  refine ⟨4203779853609700064282789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802519902406466709521859 4203779853609700064282789)
                  ·
                    refine ⟨788208722551818762053023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4203779853609700064282789 788208722551818762053023)
                    ·
                      rfl

theorem cell23_4605093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 4].length) (baseStart_4605093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605093 prefixEnd_4605093 := by exact prefixLift 4605093
  have htrace : WordTrace (prefixWord ++ tailWord_4605093) baseStart_4605093 baseEnd_4605093 := by
    simpa [prefixWord, tailWord_4605093, baseEnd_4605093] using wordTrace_append hprefix tailTrace_4605093
  have hstable : (prefixWord ++ tailWord_4605093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605093).length < 2 ^ (prefixWord ++ tailWord_4605093).sum := by decide
  have hdescent : baseEnd_4605093 < baseStart_4605093 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605139 : List Nat := [1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 4]
def baseStart_4605139 : Nat := 118140960795 + 4605139 * 2 ^ 59
def prefixEnd_4605139 : Nat := 4983230072969 + 3 ^ 40 * 4605139 * 2
def baseEnd_4605139 : Nat := 2364649787765563106183857

theorem tailTrace_4605139 : CollatzResearch.WordTrace tailWord_4605139 prefixEnd_4605139 2364649787765563106183857 := by
  unfold tailWord_4605139
  simp only [CollatzResearch.WordTrace]
  refine ⟨167963218063375372970234471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111975478708916915313489647 167963218063375372970234471)
  ·
    refine ⟨251944827095063059455351707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167963218063375372970234471 251944827095063059455351707)
    ·
      refine ⟨377917240642594589183027561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251944827095063059455351707 377917240642594589183027561)
      ·
        refine ⟨283437930481945941887270671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377917240642594589183027561 283437930481945941887270671)
        ·
          refine ⟨425156895722918912830906007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283437930481945941887270671 425156895722918912830906007)
          ·
            refine ⟨637735343584378369246359011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425156895722918912830906007 637735343584378369246359011)
            ·
              refine ⟨956603015376567553869538517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637735343584378369246359011 956603015376567553869538517)
              ·
                refine ⟨22420383172888302043817309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 956603015376567553869538517 22420383172888302043817309)
                ·
                  refine ⟨8407643689833113266431491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22420383172888302043817309 8407643689833113266431491)
                  ·
                    refine ⟨12611465534749669899647237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8407643689833113266431491 12611465534749669899647237)
                    ·
                      refine ⟨2364649787765563106183857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12611465534749669899647237 2364649787765563106183857)
                      ·
                        rfl

theorem cell23_4605139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 4].length) (baseStart_4605139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605139 prefixEnd_4605139 := by exact prefixLift 4605139
  have htrace : WordTrace (prefixWord ++ tailWord_4605139) baseStart_4605139 baseEnd_4605139 := by
    simpa [prefixWord, tailWord_4605139, baseEnd_4605139] using wordTrace_append hprefix tailTrace_4605139
  have hstable : (prefixWord ++ tailWord_4605139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605139).length < 2 ^ (prefixWord ++ tailWord_4605139).sum := by decide
  have hdescent : baseEnd_4605139 < baseStart_4605139 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605153 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 1, 5]
def baseStart_4605153 : Nat := 118140960795 + 4605153 * 2 ^ 59
def prefixEnd_4605153 : Nat := 4983230072969 + 3 ^ 40 * 4605153 * 2
def baseEnd_4605153 : Nat := 788218992164908683802931

theorem tailTrace_4605153 : CollatzResearch.WordTrace tailWord_4605153 prefixEnd_4605153 788218992164908683802931 := by
  unfold tailWord_4605153
  simp only [CollatzResearch.WordTrace]
  refine ⟨167963728685324653361244113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111975819123549768907496075 167963728685324653361244113)
  ·
    refine ⟨125972796513993490020933085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167963728685324653361244113 125972796513993490020933085)
    ·
      refine ⟨47239798692747558757849907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125972796513993490020933085 47239798692747558757849907)
      ·
        refine ⟨70859698039121338136774861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47239798692747558757849907 70859698039121338136774861)
        ·
          refine ⟨26572386764670501801290573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70859698039121338136774861 26572386764670501801290573)
          ·
            refine ⟨9964645036751438175483965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26572386764670501801290573 9964645036751438175483965)
            ·
              refine ⟨3736741888781789315806487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9964645036751438175483965 3736741888781789315806487)
              ·
                refine ⟨5605112833172683973709731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736741888781789315806487 5605112833172683973709731)
                ·
                  refine ⟨8407669249759025960564597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605112833172683973709731 8407669249759025960564597)
                  ·
                    refine ⟨788218992164908683802931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8407669249759025960564597 788218992164908683802931)
                    ·
                      rfl

theorem cell23_4605153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 5].length) (baseStart_4605153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605153 prefixEnd_4605153 := by exact prefixLift 4605153
  have htrace : WordTrace (prefixWord ++ tailWord_4605153) baseStart_4605153 baseEnd_4605153 := by
    simpa [prefixWord, tailWord_4605153, baseEnd_4605153] using wordTrace_append hprefix tailTrace_4605153
  have hstable : (prefixWord ++ tailWord_4605153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605153).length < 2 ^ (prefixWord ++ tailWord_4605153).sum := by decide
  have hdescent : baseEnd_4605153 < baseStart_4605153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605156 : List Nat := [2, 3, 1, 1, 1, 2, 2, 5, 1, 1, 4]
def baseStart_4605156 : Nat := 118140960795 + 4605156 * 2 ^ 59
def prefixEnd_4605156 : Nat := 4983230072969 + 3 ^ 40 * 4605156 * 2
def baseEnd_4605156 : Nat := 2364658516936689539671279

theorem tailTrace_4605156 : CollatzResearch.WordTrace tailWord_4605156 prefixEnd_4605156 2364658516936689539671279 := by
  unfold tailWord_4605156
  simp only [CollatzResearch.WordTrace]
  refine ⟨83981919052156892436801661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111975892069542523249068881 83981919052156892436801661)
  ·
    refine ⟨31493219644558834663800623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83981919052156892436801661 31493219644558834663800623)
    ·
      refine ⟨47239829466838251995700935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31493219644558834663800623 47239829466838251995700935)
      ·
        refine ⟨70859744200257377993551403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47239829466838251995700935 70859744200257377993551403)
        ·
          refine ⟨106289616300386066990327105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70859744200257377993551403 106289616300386066990327105)
          ·
            refine ⟨79717212225289550242745329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106289616300386066990327105 79717212225289550242745329)
            ·
              refine ⟨59787909168967162682058997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79717212225289550242745329 59787909168967162682058997)
              ·
                refine ⟨5605116484590671501443031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59787909168967162682058997 5605116484590671501443031)
                ·
                  refine ⟨8407674726886007252164547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605116484590671501443031 8407674726886007252164547)
                  ·
                    refine ⟨12611512090329010878246821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8407674726886007252164547 12611512090329010878246821)
                    ·
                      refine ⟨2364658516936689539671279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12611512090329010878246821 2364658516936689539671279)
                      ·
                        rfl

theorem cell23_4605156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 5, 1, 1, 4].length) (baseStart_4605156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605156 prefixEnd_4605156 := by exact prefixLift 4605156
  have htrace : WordTrace (prefixWord ++ tailWord_4605156) baseStart_4605156 baseEnd_4605156 := by
    simpa [prefixWord, tailWord_4605156, baseEnd_4605156] using wordTrace_append hprefix tailTrace_4605156
  have hstable : (prefixWord ++ tailWord_4605156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605156).length < 2 ^ (prefixWord ++ tailWord_4605156).sum := by decide
  have hdescent : baseEnd_4605156 < baseStart_4605156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605166 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 4, 4]
def baseStart_4605166 : Nat := 118140960795 + 4605166 * 2 ^ 59
def prefixEnd_4605166 : Nat := 4983230072969 + 3 ^ 40 * 4605166 * 2
def baseEnd_4605166 : Nat := 788221217247744833515411

theorem tailTrace_4605166 : CollatzResearch.WordTrace tailWord_4605166 prefixEnd_4605166 788221217247744833515411 := by
  unfold tailWord_4605166
  simp only [CollatzResearch.WordTrace]
  refine ⟨20995525354284694572683419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111976135222851704387644901 20995525354284694572683419)
  ·
    refine ⟨31493288031427041859025129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20995525354284694572683419 31493288031427041859025129)
    ·
      refine ⟨23619966023570281394268847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31493288031427041859025129 23619966023570281394268847)
      ·
        refine ⟨35429949035355422091403271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23619966023570281394268847 35429949035355422091403271)
        ·
          refine ⟨53144923553033133137104907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35429949035355422091403271 53144923553033133137104907)
          ·
            refine ⟨79717385329549699705657361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53144923553033133137104907 79717385329549699705657361)
            ·
              refine ⟨59788038997162274779243021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79717385329549699705657361 59788038997162274779243021)
              ·
                refine ⟨22420514623935853042216133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59788038997162274779243021 22420514623935853042216133)
                ·
                  refine ⟨4203846491987972445415525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22420514623935853042216133 4203846491987972445415525)
                  ·
                    refine ⟨788221217247744833515411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4203846491987972445415525 788221217247744833515411)
                    ·
                      rfl

theorem cell23_4605166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_4605166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605166 prefixEnd_4605166 := by exact prefixLift 4605166
  have htrace : WordTrace (prefixWord ++ tailWord_4605166) baseStart_4605166 baseEnd_4605166 := by
    simpa [prefixWord, tailWord_4605166, baseEnd_4605166] using wordTrace_append hprefix tailTrace_4605166
  have hstable : (prefixWord ++ tailWord_4605166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605166).length < 2 ^ (prefixWord ++ tailWord_4605166).sum := by decide
  have hdescent : baseEnd_4605166 < baseStart_4605166 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605169 : List Nat := [1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 4]
def baseStart_4605169 : Nat := 118140960795 + 4605169 * 2 ^ 59
def prefixEnd_4605169 : Nat := 4983230072969 + 3 ^ 40 * 4605169 * 2
def baseEnd_4605169 : Nat := 2364665192185197988808719

theorem tailTrace_4605169 : CollatzResearch.WordTrace tailWord_4605169 prefixEnd_4605169 2364665192185197988808719 := by
  unfold tailWord_4605169
  simp only [CollatzResearch.WordTrace]
  refine ⟨167964312253266688093826561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111976208168844458729217707 167964312253266688093826561)
  ·
    refine ⟨125973234189950016070369921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167964312253266688093826561 125973234189950016070369921)
    ·
      refine ⟨94479925642462512052777441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125973234189950016070369921 94479925642462512052777441)
      ·
        refine ⟨70859944231846884039583081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94479925642462512052777441 70859944231846884039583081)
        ·
          refine ⟨53144958173885163029687311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70859944231846884039583081 53144958173885163029687311)
          ·
            refine ⟨79717437260827744544530967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53144958173885163029687311 79717437260827744544530967)
            ·
              refine ⟨119576155891241616816796451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79717437260827744544530967 119576155891241616816796451)
              ·
                refine ⟨179364233836862425225194677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119576155891241616816796451 179364233836862425225194677)
                ·
                  refine ⟨16815396922205852364862001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 179364233836862425225194677 16815396922205852364862001)
                  ·
                    refine ⟨12611547691654389273646501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16815396922205852364862001 12611547691654389273646501)
                    ·
                      refine ⟨2364665192185197988808719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12611547691654389273646501 2364665192185197988808719)
                      ·
                        rfl

theorem cell23_4605169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_4605169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605169 prefixEnd_4605169 := by exact prefixLift 4605169
  have htrace : WordTrace (prefixWord ++ tailWord_4605169) baseStart_4605169 baseEnd_4605169 := by
    simpa [prefixWord, tailWord_4605169, baseEnd_4605169] using wordTrace_append hprefix tailTrace_4605169
  have hstable : (prefixWord ++ tailWord_4605169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605169).length < 2 ^ (prefixWord ++ tailWord_4605169).sum := by decide
  have hdescent : baseEnd_4605169 < baseStart_4605169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605196 : List Nat := [2, 2, 1, 2, 2, 4, 3, 7]
def baseStart_4605196 : Nat := 118140960795 + 4605196 * 2 ^ 59
def prefixEnd_4605196 : Nat := 4983230072969 + 3 ^ 40 * 4605196 * 2
def baseEnd_4605196 : Nat := 87580705783809977154485

theorem tailTrace_4605196 : CollatzResearch.WordTrace tailWord_4605196 prefixEnd_4605196 87580705783809977154485 := by
  unfold tailWord_4605196
  simp only [CollatzResearch.WordTrace]
  refine ⟨83982648512084435852529721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111976864682779247803372961 83982648512084435852529721)
  ·
    refine ⟨62986986384063326889397291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83982648512084435852529721 62986986384063326889397291)
    ·
      refine ⟨94480479576094990334095937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62986986384063326889397291 94480479576094990334095937)
      ·
        refine ⟨70860359682071242750571953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94480479576094990334095937 70860359682071242750571953)
        ·
          refine ⟨53145269761553432062928965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70860359682071242750571953 53145269761553432062928965)
          ·
            refine ⟨9964738080291268511799181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53145269761553432062928965 9964738080291268511799181)
            ·
              refine ⟨3736776780109225691924693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9964738080291268511799181 3736776780109225691924693)
              ·
                refine ⟨87580705783809977154485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3736776780109225691924693 87580705783809977154485)
                ·
                  rfl

theorem cell23_4605196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 3, 7].length) (baseStart_4605196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605196 prefixEnd_4605196 := by exact prefixLift 4605196
  have htrace : WordTrace (prefixWord ++ tailWord_4605196) baseStart_4605196 baseEnd_4605196 := by
    simpa [prefixWord, tailWord_4605196, baseEnd_4605196] using wordTrace_append hprefix tailTrace_4605196
  have hstable : (prefixWord ++ tailWord_4605196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605196).length < 2 ^ (prefixWord ++ tailWord_4605196).sum := by decide
  have hdescent : baseEnd_4605196 < baseStart_4605196 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605207 : List Nat := [1, 1, 3, 4, 1, 1, 4, 3, 1, 2, 2]
def baseStart_4605207 : Nat := 118140960795 + 4605207 * 2 ^ 59
def prefixEnd_4605207 : Nat := 4983230072969 + 3 ^ 40 * 4605207 * 2
def baseEnd_4605207 : Nat := 2364684704450068840133545

theorem tailTrace_4605207 : CollatzResearch.WordTrace tailWord_4605207 prefixEnd_4605207 2364684704450068840133545 := by
  unfold tailWord_4605207
  simp only [CollatzResearch.WordTrace]
  refine ⟨167965698227129020583709875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111977132151419347055806583 167965698227129020583709875)
  ·
    refine ⟨251948547340693530875564813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167965698227129020583709875 251948547340693530875564813)
    ·
      refine ⟨94480705252760074078336805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251948547340693530875564813 94480705252760074078336805)
      ·
        refine ⟨17715132234892513889688151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94480705252760074078336805 17715132234892513889688151)
        ·
          refine ⟨26572698352338770834532227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17715132234892513889688151 26572698352338770834532227)
          ·
            refine ⟨39859047528508156251798341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26572698352338770834532227 39859047528508156251798341)
            ·
              refine ⟨7473571411595279297212189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39859047528508156251798341 7473571411595279297212189)
              ·
                refine ⟨2802589279348229736454571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7473571411595279297212189 2802589279348229736454571)
                ·
                  refine ⟨4203883919022344604681857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802589279348229736454571 4203883919022344604681857)
                  ·
                    refine ⟨3152912939266758453511393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4203883919022344604681857 3152912939266758453511393)
                    ·
                      refine ⟨2364684704450068840133545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152912939266758453511393 2364684704450068840133545)
                      ·
                        rfl

theorem cell23_4605207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_4605207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605207 prefixEnd_4605207 := by exact prefixLift 4605207
  have htrace : WordTrace (prefixWord ++ tailWord_4605207) baseStart_4605207 baseEnd_4605207 := by
    simpa [prefixWord, tailWord_4605207, baseEnd_4605207] using wordTrace_append hprefix tailTrace_4605207
  have hstable : (prefixWord ++ tailWord_4605207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605207).length < 2 ^ (prefixWord ++ tailWord_4605207).sum := by decide
  have hdescent : baseEnd_4605207 < baseStart_4605207 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605210 : List Nat := [3, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3]
def baseStart_4605210 : Nat := 118140960795 + 4605210 * 2 ^ 59
def prefixEnd_4605210 : Nat := 4983230072969 + 3 ^ 40 * 4605210 * 2
def baseEnd_4605210 : Nat := 2364686244892032328396031

theorem tailTrace_4605210 : CollatzResearch.WordTrace tailWord_4605210 prefixEnd_4605210 2364686244892032328396031 := by
  unfold tailWord_4605210
  simp only [CollatzResearch.WordTrace]
  refine ⟨41991451911529538024017271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111977205097412101397379389 41991451911529538024017271)
  ·
    refine ⟨62987177867294307036025907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41991451911529538024017271 62987177867294307036025907)
    ·
      refine ⟨94480766800941460554038861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62987177867294307036025907 94480766800941460554038861)
      ·
        refine ⟨35430287550353047707764573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 94480766800941460554038861 35430287550353047707764573)
        ·
          refine ⟨13286357831382392890411715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35430287550353047707764573 13286357831382392890411715)
          ·
            refine ⟨19929536747073589335617573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13286357831382392890411715 19929536747073589335617573)
            ·
              refine ⟨3736788140076298000428295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19929536747073589335617573 3736788140076298000428295)
              ·
                refine ⟨5605182210114447000642443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736788140076298000428295 5605182210114447000642443)
                ·
                  refine ⟨8407773315171670500963665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605182210114447000642443 8407773315171670500963665)
                  ·
                    refine ⟨6305829986378752875722749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8407773315171670500963665 6305829986378752875722749)
                    ·
                      refine ⟨2364686244892032328396031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305829986378752875722749 2364686244892032328396031)
                      ·
                        rfl

theorem cell23_4605210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 4, 1, 1, 2, 3].length) (baseStart_4605210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605210 prefixEnd_4605210 := by exact prefixLift 4605210
  have htrace : WordTrace (prefixWord ++ tailWord_4605210) baseStart_4605210 baseEnd_4605210 := by
    simpa [prefixWord, tailWord_4605210, baseEnd_4605210] using wordTrace_append hprefix tailTrace_4605210
  have hstable : (prefixWord ++ tailWord_4605210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605210).length < 2 ^ (prefixWord ++ tailWord_4605210).sum := by decide
  have hdescent : baseEnd_4605210 < baseStart_4605210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605266 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3]
def baseStart_4605266 : Nat := 118140960795 + 4605266 * 2 ^ 59
def prefixEnd_4605266 : Nat := 4983230072969 + 3 ^ 40 * 4605266 * 2
def baseEnd_4605266 : Nat := 2364714999808684109295773

theorem tailTrace_4605266 : CollatzResearch.WordTrace tailWord_4605266 prefixEnd_4605266 2364714999808684109295773 := by
  unfold tailWord_4605266
  simp only [CollatzResearch.WordTrace]
  refine ⟨41991962533478818415026913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111978566755943515773405101 41991962533478818415026913)
  ·
    refine ⟨31493971900109113811270185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41991962533478818415026913 31493971900109113811270185)
    ·
      refine ⟨23620478925081835358452639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31493971900109113811270185 23620478925081835358452639)
      ·
        refine ⟨35430718387622753037678959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23620478925081835358452639 35430718387622753037678959)
        ·
          refine ⟨53146077581434129556518439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35430718387622753037678959 53146077581434129556518439)
          ·
            refine ⟨79719116372151194334777659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53146077581434129556518439 79719116372151194334777659)
            ·
              refine ⟨119578674558226791502166489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79719116372151194334777659 119578674558226791502166489)
              ·
                refine ⟨89684005918670093626624867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119578674558226791502166489 89684005918670093626624867)
                ·
                  refine ⟨134526008878005140439937301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89684005918670093626624867 134526008878005140439937301)
                  ·
                    refine ⟨6305906666156490958122061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 134526008878005140439937301 6305906666156490958122061)
                    ·
                      refine ⟨2364714999808684109295773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305906666156490958122061 2364714999808684109295773)
                      ·
                        rfl

theorem cell23_4605266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_4605266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605266 prefixEnd_4605266 := by exact prefixLift 4605266
  have htrace : WordTrace (prefixWord ++ tailWord_4605266) baseStart_4605266 baseEnd_4605266 := by
    simpa [prefixWord, tailWord_4605266, baseEnd_4605266] using wordTrace_append hprefix tailTrace_4605266
  have hstable : (prefixWord ++ tailWord_4605266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605266).length < 2 ^ (prefixWord ++ tailWord_4605266).sum := by decide
  have hdescent : baseEnd_4605266 < baseStart_4605266 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605279 : List Nat := [1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_4605279 : Nat := 118140960795 + 4605279 * 2 ^ 59
def prefixEnd_4605279 : Nat := 4983230072969 + 3 ^ 40 * 4605279 * 2
def baseEnd_4605279 : Nat := 2364721675057192558433213

theorem tailTrace_4605279 : CollatzResearch.WordTrace tailWord_4605279 prefixEnd_4605279 2364721675057192558433213 := by
  unfold tailWord_4605279
  simp only [CollatzResearch.WordTrace]
  refine ⟨167968324282868176880330891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111978882855245451253553927 167968324282868176880330891)
  ·
    refine ⟨251952486424302265320496337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167968324282868176880330891 251952486424302265320496337)
    ·
      refine ⟨188964364818226698990372253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251952486424302265320496337 188964364818226698990372253)
      ·
        refine ⟨70861636806835012121389595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188964364818226698990372253 70861636806835012121389595)
        ·
          refine ⟨106292455210252518182084393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70861636806835012121389595 106292455210252518182084393)
          ·
            refine ⟨79719341407689388636563295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106292455210252518182084393 79719341407689388636563295)
            ·
              refine ⟨119579012111534082954844943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79719341407689388636563295 119579012111534082954844943)
              ·
                refine ⟨179368518167301124432267415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119579012111534082954844943 179368518167301124432267415)
                ·
                  refine ⟨269052777250951686648401123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179368518167301124432267415 269052777250951686648401123)
                  ·
                    refine ⟨403579165876427529972601685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 269052777250951686648401123 403579165876427529972601685)
                    ·
                      refine ⟨2364721675057192558433213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 403579165876427529972601685 2364721675057192558433213)
                      ·
                        rfl

theorem cell23_4605279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_4605279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605279 prefixEnd_4605279 := by exact prefixLift 4605279
  have htrace : WordTrace (prefixWord ++ tailWord_4605279) baseStart_4605279 baseEnd_4605279 := by
    simpa [prefixWord, tailWord_4605279, baseEnd_4605279] using wordTrace_append hprefix tailTrace_4605279
  have hstable : (prefixWord ++ tailWord_4605279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605279).length < 2 ^ (prefixWord ++ tailWord_4605279).sum := by decide
  have hdescent : baseEnd_4605279 < baseStart_4605279 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605280 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 4, 2, 2]
def baseStart_4605280 : Nat := 118140960795 + 4605280 * 2 ^ 59
def prefixEnd_4605280 : Nat := 4983230072969 + 3 ^ 40 * 4605280 * 2
def baseEnd_4605280 : Nat := 2364722188537847054520709

theorem tailTrace_4605280 : CollatzResearch.WordTrace tailWord_4605280 prefixEnd_4605280 2364722188537847054520709 := by
  unfold tailWord_4605280
  simp only [CollatzResearch.WordTrace]
  refine ⟨83984180377932277025558647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111978907170576369367411529 83984180377932277025558647)
  ·
    refine ⟨125976270566898415538337971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83984180377932277025558647 125976270566898415538337971)
    ·
      refine ⟨188964405850347623307506957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125976270566898415538337971 188964405850347623307506957)
      ·
        refine ⟨70861652193880358740315109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 188964405850347623307506957 70861652193880358740315109)
        ·
          refine ⟨13286559786352567263809083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70861652193880358740315109 13286559786352567263809083)
          ·
            refine ⟨19929839679528850895713625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13286559786352567263809083 19929839679528850895713625)
            ·
              refine ⟨14947379759646638171785219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19929839679528850895713625 14947379759646638171785219)
              ·
                refine ⟨22421069639469957257677829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14947379759646638171785219 22421069639469957257677829)
                ·
                  refine ⟨4203950557400616985814593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22421069639469957257677829 4203950557400616985814593)
                  ·
                    refine ⟨3152962918050462739360945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4203950557400616985814593 3152962918050462739360945)
                    ·
                      refine ⟨2364722188537847054520709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152962918050462739360945 2364722188537847054520709)
                      ·
                        rfl

theorem cell23_4605280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_4605280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605280 prefixEnd_4605280 := by exact prefixLift 4605280
  have htrace : WordTrace (prefixWord ++ tailWord_4605280) baseStart_4605280 baseEnd_4605280 := by
    simpa [prefixWord, tailWord_4605280, baseEnd_4605280] using wordTrace_append hprefix tailTrace_4605280
  have hstable : (prefixWord ++ tailWord_4605280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605280).length < 2 ^ (prefixWord ++ tailWord_4605280).sum := by decide
  have hdescent : baseEnd_4605280 < baseStart_4605280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605289 : List Nat := [1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 8]
def baseStart_4605289 : Nat := 118140960795 + 4605289 * 2 ^ 59
def prefixEnd_4605289 : Nat := 4983230072969 + 3 ^ 40 * 4605289 * 2
def baseEnd_4605289 : Nat := 2364726809863737519308167

theorem tailTrace_4605289 : CollatzResearch.WordTrace tailWord_4605289 prefixEnd_4605289 2364726809863737519308167 := by
  unfold tailWord_4605289
  simp only [CollatzResearch.WordTrace]
  refine ⟨167968689012831948588194921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111979126008554632392129947 167968689012831948588194921)
  ·
    refine ⟨125976516759623961441146191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167968689012831948588194921 125976516759623961441146191)
    ·
      refine ⟨188964775139435942161719287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125976516759623961441146191 188964775139435942161719287)
      ·
        refine ⟨283447162709153913242578931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188964775139435942161719287 283447162709153913242578931)
        ·
          refine ⟨425170744063730869863868397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283447162709153913242578931 425170744063730869863868397)
          ·
            refine ⟨159439029023899076198950649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 425170744063730869863868397 159439029023899076198950649)
            ·
              refine ⟨119579271767924307149212987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159439029023899076198950649 119579271767924307149212987)
              ·
                refine ⟨179368907651886460723819481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119579271767924307149212987 179368907651886460723819481)
                ·
                  refine ⟨134526680738914845542864611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179368907651886460723819481 134526680738914845542864611)
                  ·
                    refine ⟨201790021108372268314296917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 134526680738914845542864611 201790021108372268314296917)
                    ·
                      refine ⟨2364726809863737519308167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 201790021108372268314296917 2364726809863737519308167)
                      ·
                        rfl

theorem cell23_4605289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 1, 2, 1, 8].length) (baseStart_4605289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605289 prefixEnd_4605289 := by exact prefixLift 4605289
  have htrace : WordTrace (prefixWord ++ tailWord_4605289) baseStart_4605289 baseEnd_4605289 := by
    simpa [prefixWord, tailWord_4605289, baseEnd_4605289] using wordTrace_append hprefix tailTrace_4605289
  have hstable : (prefixWord ++ tailWord_4605289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605289).length < 2 ^ (prefixWord ++ tailWord_4605289).sum := by decide
  have hdescent : baseEnd_4605289 < baseStart_4605289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605296 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3]
def baseStart_4605296 : Nat := 118140960795 + 4605296 * 2 ^ 59
def prefixEnd_4605296 : Nat := 4983230072969 + 3 ^ 40 * 4605296 * 2
def baseEnd_4605296 : Nat := 2364730404228318991920635

theorem tailTrace_4605296 : CollatzResearch.WordTrace tailWord_4605296 prefixEnd_4605296 2364730404228318991920635 := by
  unfold tailWord_4605296
  simp only [CollatzResearch.WordTrace]
  refine ⟨83984472161903294391849871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111979296215871059189133161 83984472161903294391849871)
  ·
    refine ⟨125976708242854941587774807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83984472161903294391849871 125976708242854941587774807)
    ·
      refine ⟨188965062364282412381662211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125976708242854941587774807 188965062364282412381662211)
      ·
        refine ⟨283447593546423618572493317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188965062364282412381662211 283447593546423618572493317)
        ·
          refine ⟨53146423789954428482342497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283447593546423618572493317 53146423789954428482342497)
          ·
            refine ⟨39859817842465821361756873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53146423789954428482342497 39859817842465821361756873)
            ·
              refine ⟨29894863381849366021317655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39859817842465821361756873 29894863381849366021317655)
              ·
                refine ⟨44842295072774049031976483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29894863381849366021317655 44842295072774049031976483)
                ·
                  refine ⟨67263442609161073547964725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44842295072774049031976483 67263442609161073547964725)
                  ·
                    refine ⟨6305947744608850645121693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67263442609161073547964725 6305947744608850645121693)
                    ·
                      refine ⟨2364730404228318991920635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6305947744608850645121693 2364730404228318991920635)
                      ·
                        rfl

theorem cell23_4605296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 1, 5, 3].length) (baseStart_4605296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605296 prefixEnd_4605296 := by exact prefixLift 4605296
  have htrace : WordTrace (prefixWord ++ tailWord_4605296) baseStart_4605296 baseEnd_4605296 := by
    simpa [prefixWord, tailWord_4605296, baseEnd_4605296] using wordTrace_append hprefix tailTrace_4605296
  have hstable : (prefixWord ++ tailWord_4605296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605296).length < 2 ^ (prefixWord ++ tailWord_4605296).sum := by decide
  have hdescent : baseEnd_4605296 < baseStart_4605296 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605297 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 2, 2, 2]
def baseStart_4605297 : Nat := 118140960795 + 4605297 * 2 ^ 59
def prefixEnd_4605297 : Nat := 4983230072969 + 3 ^ 40 * 4605297 * 2
def baseEnd_4605297 : Nat := 2364730917708973488008131

theorem tailTrace_4605297 : CollatzResearch.WordTrace tailWord_4605297 prefixEnd_4605297 2364730917708973488008131 := by
  unfold tailWord_4605297
  simp only [CollatzResearch.WordTrace]
  refine ⟨167968980796802965954486145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111979320531201977302990763 167968980796802965954486145)
  ·
    refine ⟨125976735597602224465864609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167968980796802965954486145 125976735597602224465864609)
    ·
      refine ⟨94482551698201668349398457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125976735597602224465864609 94482551698201668349398457)
      ·
        refine ⟨70861913773651251262048843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94482551698201668349398457 70861913773651251262048843)
        ·
          refine ⟨106292870660476876893073265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70861913773651251262048843 106292870660476876893073265)
          ·
            refine ⟨79719652995357657669804949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106292870660476876893073265 79719652995357657669804949)
            ·
              refine ⟨3736858734157390203272107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79719652995357657669804949 3736858734157390203272107)
              ·
                refine ⟨5605288101236085304908161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3736858734157390203272107 5605288101236085304908161)
                ·
                  refine ⟨4203966075927063978681121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605288101236085304908161 4203966075927063978681121)
                  ·
                    refine ⟨3152974556945297984010841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4203966075927063978681121 3152974556945297984010841)
                    ·
                      refine ⟨2364730917708973488008131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3152974556945297984010841 2364730917708973488008131)
                      ·
                        rfl

theorem cell23_4605297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_4605297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605297 prefixEnd_4605297 := by exact prefixLift 4605297
  have htrace : WordTrace (prefixWord ++ tailWord_4605297) baseStart_4605297 baseEnd_4605297 := by
    simpa [prefixWord, tailWord_4605297, baseEnd_4605297] using wordTrace_append hprefix tailTrace_4605297
  have hstable : (prefixWord ++ tailWord_4605297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605297).length < 2 ^ (prefixWord ++ tailWord_4605297).sum := by decide
  have hdescent : baseEnd_4605297 < baseStart_4605297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605373 : List Nat := [1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 3]
def baseStart_4605373 : Nat := 118140960795 + 4605373 * 2 ^ 59
def prefixEnd_4605373 : Nat := 4983230072969 + 3 ^ 40 * 4605373 * 2
def baseEnd_4605373 : Nat := 2364769942238715190657781

theorem tailTrace_4605373 : CollatzResearch.WordTrace tailWord_4605373 prefixEnd_4605373 2364769942238715190657781 := by
  unfold tailWord_4605373
  simp only [CollatzResearch.WordTrace]
  refine ⟨167971752744527630934252773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111981168496351753956168515 167971752744527630934252773)
  ·
    refine ⟨31494703639598930800172395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167971752744527630934252773 31494703639598930800172395)
    ·
      refine ⟨47242055459398396200258593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31494703639598930800172395 47242055459398396200258593)
      ·
        refine ⟨35431541594548797150193945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47242055459398396200258593 35431541594548797150193945)
        ·
          refine ⟨26573656195911597862645459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35431541594548797150193945 26573656195911597862645459)
          ·
            refine ⟨39860484293867396793968189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26573656195911597862645459 39860484293867396793968189)
            ·
              refine ⟨14947681610200273797738071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39860484293867396793968189 14947681610200273797738071)
              ·
                refine ⟨22421522415300410696607107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14947681610200273797738071 22421522415300410696607107)
                ·
                  refine ⟨33632283622950616044910661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22421522415300410696607107 33632283622950616044910661)
                  ·
                    refine ⟨6306053179303240508420749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33632283622950616044910661 6306053179303240508420749)
                    ·
                      refine ⟨2364769942238715190657781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306053179303240508420749 2364769942238715190657781)
                      ·
                        rfl

theorem cell23_4605373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 1, 1, 4, 3].length) (baseStart_4605373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605373 prefixEnd_4605373 := by exact prefixLift 4605373
  have htrace : WordTrace (prefixWord ++ tailWord_4605373) baseStart_4605373 baseEnd_4605373 := by
    simpa [prefixWord, tailWord_4605373, baseEnd_4605373] using wordTrace_append hprefix tailTrace_4605373
  have hstable : (prefixWord ++ tailWord_4605373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605373).length < 2 ^ (prefixWord ++ tailWord_4605373).sum := by decide
  have hdescent : baseEnd_4605373 < baseStart_4605373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605423 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 1, 5]
def baseStart_4605423 : Nat := 118140960795 + 4605423 * 2 ^ 59
def prefixEnd_4605423 : Nat := 4983230072969 + 3 ^ 40 * 4605423 * 2
def baseEnd_4605423 : Nat := 788265205423813331677517

theorem tailTrace_4605423 : CollatzResearch.WordTrace tailWord_4605423 prefixEnd_4605423 788265205423813331677517 := by
  unfold tailWord_4605423
  simp only [CollatzResearch.WordTrace]
  refine ⟨167973576394346489473572923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111982384262897659649048615 167973576394346489473572923)
  ·
    refine ⟨251960364591519734210359385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167973576394346489473572923 251960364591519734210359385)
    ·
      refine ⟨188970273443639800657769539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251960364591519734210359385 188970273443639800657769539)
      ·
        refine ⟨283455410165459700986654309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188970273443639800657769539 283455410165459700986654309)
        ·
          refine ⟨53147889406023693934997683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283455410165459700986654309 53147889406023693934997683)
          ·
            refine ⟨79721834109035540902496525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53147889406023693934997683 79721834109035540902496525)
            ·
              refine ⟨29895687790888327838436197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79721834109035540902496525 29895687790888327838436197)
              ·
                refine ⟨5605441460791561469706787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29895687790888327838436197 5605441460791561469706787)
                ·
                  refine ⟨8408162191187342204560181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605441460791561469706787 8408162191187342204560181)
                  ·
                    refine ⟨788265205423813331677517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8408162191187342204560181 788265205423813331677517)
                    ·
                      rfl

theorem cell23_4605423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_4605423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605423 prefixEnd_4605423 := by exact prefixLift 4605423
  have htrace : WordTrace (prefixWord ++ tailWord_4605423) baseStart_4605423 baseEnd_4605423 := by
    simpa [prefixWord, tailWord_4605423, baseEnd_4605423] using wordTrace_append hprefix tailTrace_4605423
  have hstable : (prefixWord ++ tailWord_4605423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605423).length < 2 ^ (prefixWord ++ tailWord_4605423).sum := by decide
  have hdescent : baseEnd_4605423 < baseStart_4605423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605447 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_4605447 : Nat := 118140960795 + 4605447 * 2 ^ 59
def prefixEnd_4605447 : Nat := 4983230072969 + 3 ^ 40 * 4605447 * 2
def baseEnd_4605447 : Nat := 2364807939807147901132441

theorem tailTrace_4605447 : CollatzResearch.WordTrace tailWord_4605447 prefixEnd_4605447 2364807939807147901132441 := by
  unfold tailWord_4605447
  simp only [CollatzResearch.WordTrace]
  refine ⟨167974451746259541572446595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111982967830839694381631063 167974451746259541572446595)
  ·
    refine ⟨251961677619389312358669893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167974451746259541572446595 251961677619389312358669893)
    ·
      refine ⟨47242814553635496067250605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251961677619389312358669893 47242814553635496067250605)
      ·
        refine ⟨17716055457613311025218977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47242814553635496067250605 17716055457613311025218977)
        ·
          refine ⟨13287041593209983268914233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17716055457613311025218977 13287041593209983268914233)
          ·
            refine ⟨9965281194907487451685675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13287041593209983268914233 9965281194907487451685675)
            ·
              refine ⟨14947921792361231177528513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9965281194907487451685675 14947921792361231177528513)
              ·
                refine ⟨11210941344270923383146385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14947921792361231177528513 11210941344270923383146385)
                ·
                  refine ⟨8408206008203192537359789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11210941344270923383146385 8408206008203192537359789)
                  ·
                    refine ⟨3153077253076197201509921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8408206008203192537359789 3153077253076197201509921)
                    ·
                      refine ⟨2364807939807147901132441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153077253076197201509921 2364807939807147901132441)
                      ·
                        rfl

theorem cell23_4605447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_4605447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605447 prefixEnd_4605447 := by exact prefixLift 4605447
  have htrace : WordTrace (prefixWord ++ tailWord_4605447) baseStart_4605447 baseEnd_4605447 := by
    simpa [prefixWord, tailWord_4605447, baseEnd_4605447] using wordTrace_append hprefix tailTrace_4605447
  have hstable : (prefixWord ++ tailWord_4605447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605447).length < 2 ^ (prefixWord ++ tailWord_4605447).sum := by decide
  have hdescent : baseEnd_4605447 < baseStart_4605447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605454 : List Nat := [4, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4605454 : Nat := 118140960795 + 4605454 * 2 ^ 59
def prefixEnd_4605454 : Nat := 4983230072969 + 3 ^ 40 * 4605454 * 2
def baseEnd_4605454 : Nat := 2364811534171729373744909

theorem tailTrace_4605454 : CollatzResearch.WordTrace tailWord_4605454 prefixEnd_4605454 2364811534171729373744909 := by
  unfold tailWord_4605454
  simp only [CollatzResearch.WordTrace]
  refine ⟨20996838382154272720993927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111983138038156121178634277 20996838382154272720993927)
  ·
    refine ⟨31495257573231409081490891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20996838382154272720993927 31495257573231409081490891)
    ·
      refine ⟨47242886359847113622236337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31495257573231409081490891 47242886359847113622236337)
      ·
        refine ⟨35432164769885335216677253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47242886359847113622236337 35432164769885335216677253)
        ·
          refine ⟨6643530894353500353126985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35432164769885335216677253 6643530894353500353126985)
          ·
            refine ⟨4982648170765125264845239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6643530894353500353126985 4982648170765125264845239)
            ·
              refine ⟨7473972256147687897267859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982648170765125264845239 7473972256147687897267859)
              ·
                refine ⟨11210958384221531845901789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7473972256147687897267859 11210958384221531845901789)
                ·
                  refine ⟨4204109394083074442213171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11210958384221531845901789 4204109394083074442213171)
                  ·
                    refine ⟨6306164091124611663319757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4204109394083074442213171 6306164091124611663319757)
                    ·
                      refine ⟨2364811534171729373744909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306164091124611663319757 2364811534171729373744909)
                      ·
                        rfl

theorem cell23_4605454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4605454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605454 prefixEnd_4605454 := by exact prefixLift 4605454
  have htrace : WordTrace (prefixWord ++ tailWord_4605454) baseStart_4605454 baseEnd_4605454 := by
    simpa [prefixWord, tailWord_4605454, baseEnd_4605454] using wordTrace_append hprefix tailTrace_4605454
  have hstable : (prefixWord ++ tailWord_4605454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605454).length < 2 ^ (prefixWord ++ tailWord_4605454).sum := by decide
  have hdescent : baseEnd_4605454 < baseStart_4605454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605473 : List Nat := [1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 6]
def baseStart_4605473 : Nat := 118140960795 + 4605473 * 2 ^ 59
def prefixEnd_4605473 : Nat := 4983230072969 + 3 ^ 40 * 4605473 * 2
def baseEnd_4605473 : Nat := 2364821290304164799407321

theorem tailTrace_4605473 : CollatzResearch.WordTrace tailWord_4605473 prefixEnd_4605473 2364821290304164799407321 := by
  unfold tailWord_4605473
  simp only [CollatzResearch.WordTrace]
  refine ⟨167975400044165348012893073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111983600029443565341928715 167975400044165348012893073)
  ·
    refine ⟨125981550033124011009669805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167975400044165348012893073 125981550033124011009669805)
    ·
      refine ⟨47243081262421504128626177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125981550033124011009669805 47243081262421504128626177)
      ·
        refine ⟨35432310946816128096469633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47243081262421504128626177 35432310946816128096469633)
        ·
          refine ⟨26574233210112096072352225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35432310946816128096469633 26574233210112096072352225)
          ·
            refine ⟨19930674907584072054264169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26574233210112096072352225 19930674907584072054264169)
            ·
              refine ⟨14948006180688054040698127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19930674907584072054264169 14948006180688054040698127)
              ·
                refine ⟨22422009271032081061047191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14948006180688054040698127 22422009271032081061047191)
                ·
                  refine ⟨33633013906548121591570787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22422009271032081061047191 33633013906548121591570787)
                  ·
                    refine ⟨50449520859822182387356181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33633013906548121591570787 50449520859822182387356181)
                    ·
                      refine ⟨2364821290304164799407321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50449520859822182387356181 2364821290304164799407321)
                      ·
                        rfl

theorem cell23_4605473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_4605473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605473 prefixEnd_4605473 := by exact prefixLift 4605473
  have htrace : WordTrace (prefixWord ++ tailWord_4605473) baseStart_4605473 baseEnd_4605473 := by
    simpa [prefixWord, tailWord_4605473, baseEnd_4605473] using wordTrace_append hprefix tailTrace_4605473
  have hstable : (prefixWord ++ tailWord_4605473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605473).length < 2 ^ (prefixWord ++ tailWord_4605473).sum := by decide
  have hdescent : baseEnd_4605473 < baseStart_4605473 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605511 : List Nat := [1, 1, 4, 1, 5, 1, 1, 4, 1, 2, 2]
def baseStart_4605511 : Nat := 118140960795 + 4605511 * 2 ^ 59
def prefixEnd_4605511 : Nat := 4983230072969 + 3 ^ 40 * 4605511 * 2
def baseEnd_4605511 : Nat := 2364840802569035650732147

theorem tailTrace_4605511 : CollatzResearch.WordTrace tailWord_4605511 prefixEnd_4605511 2364840802569035650732147 := by
  unfold tailWord_4605511
  simp only [CollatzResearch.WordTrace]
  refine ⟨167976786018027680502776387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111984524012018453668517591 167976786018027680502776387)
  ·
    refine ⟨251965179027041520754164581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167976786018027680502776387 251965179027041520754164581)
    ·
      refine ⟨47243471067570285141405859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251965179027041520754164581 47243471067570285141405859)
      ·
        refine ⟨70865206601355427712108789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47243471067570285141405859 70865206601355427712108789)
        ·
          refine ⟨6643613118877071348010199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70865206601355427712108789 6643613118877071348010199)
          ·
            refine ⟨9965419678315607022015299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6643613118877071348010199 9965419678315607022015299)
            ·
              refine ⟨14948129517473410533022949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9965419678315607022015299 14948129517473410533022949)
              ·
                refine ⟨2802774284526264474941803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14948129517473410533022949 2802774284526264474941803)
                ·
                  refine ⟨4204161426789396712412705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2802774284526264474941803 4204161426789396712412705)
                  ·
                    refine ⟨3153121070092047534309529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4204161426789396712412705 3153121070092047534309529)
                    ·
                      refine ⟨2364840802569035650732147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153121070092047534309529 2364840802569035650732147)
                      ·
                        rfl

theorem cell23_4605511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 4, 1, 2, 2].length) (baseStart_4605511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605511 prefixEnd_4605511 := by exact prefixLift 4605511
  have htrace : WordTrace (prefixWord ++ tailWord_4605511) baseStart_4605511 baseEnd_4605511 := by
    simpa [prefixWord, tailWord_4605511, baseEnd_4605511] using wordTrace_append hprefix tailTrace_4605511
  have hstable : (prefixWord ++ tailWord_4605511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605511).length < 2 ^ (prefixWord ++ tailWord_4605511).sum := by decide
  have hdescent : baseEnd_4605511 < baseStart_4605511 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605517 : List Nat := [1, 6, 1, 1, 3, 2, 1, 8]
def baseStart_4605517 : Nat := 118140960795 + 4605517 * 2 ^ 59
def prefixEnd_4605517 : Nat := 4983230072969 + 3 ^ 40 * 4605517 * 2
def baseEnd_4605517 : Nat := 87586810498257875083597

theorem tailTrace_4605517 : CollatzResearch.WordTrace tailWord_4605517 prefixEnd_4605517 87586810498257875083597 := by
  unfold tailWord_4605517
  simp only [CollatzResearch.WordTrace]
  refine ⟨167977004856005943527494805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111984669904003962351663203 167977004856005943527494805)
  ·
    refine ⟨7873922102625278602851319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 167977004856005943527494805 7873922102625278602851319)
    ·
      refine ⟨11810883153937917904276979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7873922102625278602851319 11810883153937917904276979)
      ·
        refine ⟨17716324730906876856415469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11810883153937917904276979 17716324730906876856415469)
        ·
          refine ⟨6643621774090078821155801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17716324730906876856415469 6643621774090078821155801)
          ·
            refine ⟨4982716330567559115866851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6643621774090078821155801 4982716330567559115866851)
            ·
              refine ⟨7474074495851338673800277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4982716330567559115866851 7474074495851338673800277)
              ·
                refine ⟨87586810498257875083597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7474074495851338673800277 87586810498257875083597)
                ·
                  rfl

theorem cell23_4605517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 2, 1, 8].length) (baseStart_4605517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605517 prefixEnd_4605517 := by exact prefixLift 4605517
  have htrace : WordTrace (prefixWord ++ tailWord_4605517) baseStart_4605517 baseEnd_4605517 := by
    simpa [prefixWord, tailWord_4605517, baseEnd_4605517] using wordTrace_append hprefix tailTrace_4605517
  have hstable : (prefixWord ++ tailWord_4605517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605517).length < 2 ^ (prefixWord ++ tailWord_4605517).sum := by decide
  have hdescent : baseEnd_4605517 < baseStart_4605517 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605520 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 5, 3, 2]
def baseStart_4605520 : Nat := 118140960795 + 4605520 * 2 ^ 59
def prefixEnd_4605520 : Nat := 4983230072969 + 3 ^ 40 * 4605520 * 2
def baseEnd_4605520 : Nat := 2364845423894926115519605

theorem tailTrace_4605520 : CollatzResearch.WordTrace tailWord_4605520 prefixEnd_4605520 2364845423894926115519605 := by
  unfold tailWord_4605520
  simp only [CollatzResearch.WordTrace]
  refine ⟨83988557137497537519927007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111984742849996716693236009 83988557137497537519927007)
  ·
    refine ⟨125982835706246306279890511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83988557137497537519927007 125982835706246306279890511)
    ·
      refine ⟨188974253559369459419835767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125982835706246306279890511 188974253559369459419835767)
      ·
        refine ⟨283461380339054189129753651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188974253559369459419835767 283461380339054189129753651)
        ·
          refine ⟨425192070508581283694630477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283461380339054189129753651 425192070508581283694630477)
          ·
            refine ⟨159447026440717981385486429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 425192070508581283694630477 159447026440717981385486429)
            ·
              refine ⟨59792634915269243019557411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159447026440717981385486429 59792634915269243019557411)
              ·
                refine ⟨89688952372903864529336117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59792634915269243019557411 89688952372903864529336117)
                ·
                  refine ⟨8408339284959737299625261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 89688952372903864529336117 8408339284959737299625261)
                  ·
                    refine ⟨3153127231859901487359473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8408339284959737299625261 3153127231859901487359473)
                    ·
                      refine ⟨2364845423894926115519605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153127231859901487359473 2364845423894926115519605)
                      ·
                        rfl

theorem cell23_4605520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 5, 3, 2].length) (baseStart_4605520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605520 prefixEnd_4605520 := by exact prefixLift 4605520
  have htrace : WordTrace (prefixWord ++ tailWord_4605520) baseStart_4605520 baseEnd_4605520 := by
    simpa [prefixWord, tailWord_4605520, baseEnd_4605520] using wordTrace_append hprefix tailTrace_4605520
  have hstable : (prefixWord ++ tailWord_4605520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605520).length < 2 ^ (prefixWord ++ tailWord_4605520).sum := by decide
  have hdescent : baseEnd_4605520 < baseStart_4605520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605527 : List Nat := [1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 3]
def baseStart_4605527 : Nat := 118140960795 + 4605527 * 2 ^ 59
def prefixEnd_4605527 : Nat := 4983230072969 + 3 ^ 40 * 4605527 * 2
def baseEnd_4605527 : Nat := 2364849018259507588132073

theorem tailTrace_4605527 : CollatzResearch.WordTrace tailWord_4605527 prefixEnd_4605527 2364849018259507588132073 := by
  unfold tailWord_4605527
  simp only [CollatzResearch.WordTrace]
  refine ⟨167977369585969715235358835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111984913057313143490239223 167977369585969715235358835)
  ·
    refine ⟨251966054378954572853038253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167977369585969715235358835 251966054378954572853038253)
    ·
      refine ⟨94487270392107964819889345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 251966054378954572853038253 94487270392107964819889345)
      ·
        refine ⟨70865452794080973614917009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94487270392107964819889345 70865452794080973614917009)
        ·
          refine ⟨53149089595560730211187757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70865452794080973614917009 53149089595560730211187757)
          ·
            refine ⟨19930908598335273829195409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 53149089595560730211187757 19930908598335273829195409)
            ·
              refine ⟨14948181448751455371896557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19930908598335273829195409 14948181448751455371896557)
              ·
                refine ⟨5605568043281795764461209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14948181448751455371896557 5605568043281795764461209)
                ·
                  refine ⟨4204176032461346823345907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605568043281795764461209 4204176032461346823345907)
                  ·
                    refine ⟨6306264048692020235018861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4204176032461346823345907 6306264048692020235018861)
                    ·
                      refine ⟨2364849018259507588132073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306264048692020235018861 2364849018259507588132073)
                      ·
                        rfl

theorem cell23_4605527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_4605527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605527 prefixEnd_4605527 := by exact prefixLift 4605527
  have htrace : WordTrace (prefixWord ++ tailWord_4605527) baseStart_4605527 baseEnd_4605527 := by
    simpa [prefixWord, tailWord_4605527, baseEnd_4605527] using wordTrace_append hprefix tailTrace_4605527
  have hstable : (prefixWord ++ tailWord_4605527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605527).length < 2 ^ (prefixWord ++ tailWord_4605527).sum := by decide
  have hdescent : baseEnd_4605527 < baseStart_4605527 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605537 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 1, 3, 2]
def baseStart_4605537 : Nat := 118140960795 + 4605537 * 2 ^ 59
def prefixEnd_4605537 : Nat := 4983230072969 + 3 ^ 40 * 4605537 * 2
def baseEnd_4605537 : Nat := 2364854153066052549007027

theorem tailTrace_4605537 : CollatzResearch.WordTrace tailWord_4605537 prefixEnd_4605537 2364854153066052549007027 := by
  unfold tailWord_4605537
  simp only [CollatzResearch.WordTrace]
  refine ⟨167977734315933486943222865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111985156210622324628815243 167977734315933486943222865)
  ·
    refine ⟨125983300736950115207417149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167977734315933486943222865 125983300736950115207417149)
    ·
      refine ⟨47243737776356293202781431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125983300736950115207417149 47243737776356293202781431)
      ·
        refine ⟨70865606664534439804172147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47243737776356293202781431 70865606664534439804172147)
        ·
          refine ⟨106298409996801659706258221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70865606664534439804172147 106298409996801659706258221)
          ·
            refine ⟨39861903748800622389846833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106298409996801659706258221 39861903748800622389846833)
            ·
              refine ⟨29896427811600466792385125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39861903748800622389846833 29896427811600466792385125)
              ·
                refine ⟨5605580214675087523572211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29896427811600466792385125 5605580214675087523572211)
                ·
                  refine ⟨8408370322012631285358317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605580214675087523572211 8408370322012631285358317)
                  ·
                    refine ⟨3153138870754736732009369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8408370322012631285358317 3153138870754736732009369)
                    ·
                      refine ⟨2364854153066052549007027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153138870754736732009369 2364854153066052549007027)
                      ·
                        rfl

theorem cell23_4605537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 1, 3, 2].length) (baseStart_4605537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605537 prefixEnd_4605537 := by exact prefixLift 4605537
  have htrace : WordTrace (prefixWord ++ tailWord_4605537) baseStart_4605537 baseEnd_4605537 := by
    simpa [prefixWord, tailWord_4605537, baseEnd_4605537] using wordTrace_append hprefix tailTrace_4605537
  have hstable : (prefixWord ++ tailWord_4605537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605537).length < 2 ^ (prefixWord ++ tailWord_4605537).sum := by decide
  have hdescent : baseEnd_4605537 < baseStart_4605537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605553 : List Nat := [1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 5]
def baseStart_4605553 : Nat := 118140960795 + 4605553 * 2 ^ 59
def prefixEnd_4605553 : Nat := 4983230072969 + 3 ^ 40 * 4605553 * 2
def baseEnd_4605553 : Nat := 2364862368756524486406953

theorem tailTrace_4605553 : CollatzResearch.WordTrace tailWord_4605553 prefixEnd_4605553 2364862368756524486406953 := by
  unfold tailWord_4605553
  simp only [CollatzResearch.WordTrace]
  refine ⟨167978317883875521675805313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111985545255917014450536875 167978317883875521675805313)
  ·
    refine ⟨125983738412906641256853985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167978317883875521675805313 125983738412906641256853985)
    ·
      refine ⟨94487803809679980942640489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125983738412906641256853985 94487803809679980942640489)
      ·
        refine ⟨70865852857259985706980367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94487803809679980942640489 70865852857259985706980367)
        ·
          refine ⟨106298779285889978560470551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70865852857259985706980367 106298779285889978560470551)
          ·
            refine ⟨159448168928834967840705827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106298779285889978560470551 159448168928834967840705827)
            ·
              refine ⟨239172253393252451761058741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159448168928834967840705827 239172253393252451761058741)
              ·
                refine ⟨22422398755617417352599257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239172253393252451761058741 22422398755617417352599257)
                ·
                  refine ⟨16816799066713063014449443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22422398755617417352599257 16816799066713063014449443)
                  ·
                    refine ⟨25225198600069594521674165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16816799066713063014449443 25225198600069594521674165)
                    ·
                      refine ⟨2364862368756524486406953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25225198600069594521674165 2364862368756524486406953)
                      ·
                        rfl

theorem cell23_4605553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_4605553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605553 prefixEnd_4605553 := by exact prefixLift 4605553
  have htrace : WordTrace (prefixWord ++ tailWord_4605553) baseStart_4605553 baseEnd_4605553 := by
    simpa [prefixWord, tailWord_4605553, baseEnd_4605553] using wordTrace_append hprefix tailTrace_4605553
  have hstable : (prefixWord ++ tailWord_4605553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605553).length < 2 ^ (prefixWord ++ tailWord_4605553).sum := by decide
  have hdescent : baseEnd_4605553 < baseStart_4605553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605554 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 1, 3, 2]
def baseStart_4605554 : Nat := 118140960795 + 4605554 * 2 ^ 59
def prefixEnd_4605554 : Nat := 4983230072969 + 3 ^ 40 * 4605554 * 2
def baseEnd_4605554 : Nat := 2364862882237178982494449

theorem tailTrace_4605554 : CollatzResearch.WordTrace tailWord_4605554 prefixEnd_4605554 2364862882237178982494449 := by
  unfold tailWord_4605554
  simp only [CollatzResearch.WordTrace]
  refine ⟨41994588589217974711647929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111985569571247932564394477 41994588589217974711647929)
  ·
    refine ⟨31495941441913481033735947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41994588589217974711647929 31495941441913481033735947)
    ·
      refine ⟨47243912162870221550603921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31495941441913481033735947 47243912162870221550603921)
      ·
        refine ⟨35432934122152666162952941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47243912162870221550603921 35432934122152666162952941)
        ·
          refine ⟨13287350295807249811107353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35432934122152666162952941 13287350295807249811107353)
          ·
            refine ⟨9965512721855437358330515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13287350295807249811107353 9965512721855437358330515)
            ·
              refine ⟨14948269082783156037495773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9965512721855437358330515 14948269082783156037495773)
              ·
                refine ⟨5605600906043683514060915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14948269082783156037495773 5605600906043683514060915)
                ·
                  refine ⟨8408401359065525271091373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605600906043683514060915 8408401359065525271091373)
                  ·
                    refine ⟨3153150509649571976659265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8408401359065525271091373 3153150509649571976659265)
                    ·
                      refine ⟨2364862882237178982494449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153150509649571976659265 2364862882237178982494449)
                      ·
                        rfl

theorem cell23_4605554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 1, 3, 2].length) (baseStart_4605554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605554 prefixEnd_4605554 := by exact prefixLift 4605554
  have htrace : WordTrace (prefixWord ++ tailWord_4605554) baseStart_4605554 baseEnd_4605554 := by
    simpa [prefixWord, tailWord_4605554, baseEnd_4605554] using wordTrace_append hprefix tailTrace_4605554
  have hstable : (prefixWord ++ tailWord_4605554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605554).length < 2 ^ (prefixWord ++ tailWord_4605554).sum := by decide
  have hdescent : baseEnd_4605554 < baseStart_4605554 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605563 : List Nat := [1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4]
def baseStart_4605563 : Nat := 118140960795 + 4605563 * 2 ^ 59
def prefixEnd_4605563 : Nat := 4983230072969 + 3 ^ 40 * 4605563 * 2
def baseEnd_4605563 : Nat := 2364867503563069447281907

theorem tailTrace_4605563 : CollatzResearch.WordTrace tailWord_4605563 prefixEnd_4605563 2364867503563069447281907 := by
  unfold tailWord_4605563
  simp only [CollatzResearch.WordTrace]
  refine ⟨167978682613839293383669343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111985788409226195589112895 167978682613839293383669343)
  ·
    refine ⟨251968023920758940075504015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167978682613839293383669343 251968023920758940075504015)
    ·
      refine ⟨377952035881138410113256023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251968023920758940075504015 377952035881138410113256023)
      ·
        refine ⟨566928053821707615169884035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377952035881138410113256023 566928053821707615169884035)
        ·
          refine ⟨850392080732561422754826053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 566928053821707615169884035 850392080732561422754826053)
          ·
            refine ⟨159448515137355266766529885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 850392080732561422754826053 159448515137355266766529885)
            ·
              refine ⟨59793193176508225037448707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159448515137355266766529885 59793193176508225037448707)
              ·
                refine ⟨89689789764762337556173061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59793193176508225037448707 89689789764762337556173061)
                ·
                  refine ⟨16816835580892938291782449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89689789764762337556173061 16816835580892938291782449)
                  ·
                    refine ⟨12612626685669703718836837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16816835580892938291782449 12612626685669703718836837)
                    ·
                      refine ⟨2364867503563069447281907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12612626685669703718836837 2364867503563069447281907)
                      ·
                        rfl

theorem cell23_4605563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 3, 1, 4, 2, 4].length) (baseStart_4605563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605563 prefixEnd_4605563 := by exact prefixLift 4605563
  have htrace : WordTrace (prefixWord ++ tailWord_4605563) baseStart_4605563 baseEnd_4605563 := by
    simpa [prefixWord, tailWord_4605563, baseEnd_4605563] using wordTrace_append hprefix tailTrace_4605563
  have hstable : (prefixWord ++ tailWord_4605563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605563).length < 2 ^ (prefixWord ++ tailWord_4605563).sum := by decide
  have hdescent : baseEnd_4605563 < baseStart_4605563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605603 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 1, 7]
def baseStart_4605603 : Nat := 118140960795 + 4605603 * 2 ^ 59
def prefixEnd_4605603 : Nat := 4983230072969 + 3 ^ 40 * 4605603 * 2
def baseEnd_4605603 : Nat := 788296014263083096927241

theorem tailTrace_4605603 : CollatzResearch.WordTrace tailWord_4605603 prefixEnd_4605603 788296014263083096927241 := by
  unfold tailWord_4605603
  simp only [CollatzResearch.WordTrace]
  refine ⟨167980141533694380215125463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111986761022462920143416975 167980141533694380215125463)
  ·
    refine ⟨251970212300541570322688195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167980141533694380215125463 251970212300541570322688195)
    ·
      refine ⟨377955318450812355484032293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251970212300541570322688195 377955318450812355484032293)
      ·
        refine ⟨70866622209527316653256055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 377955318450812355484032293 70866622209527316653256055)
        ·
          refine ⟨106299933314290974979884083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70866622209527316653256055 106299933314290974979884083)
          ·
            refine ⟨159449899971436462469826125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106299933314290974979884083 159449899971436462469826125)
            ·
              refine ⟨59793712489288673426184797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159449899971436462469826125 59793712489288673426184797)
              ·
                refine ⟨22422642183483252534819299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59793712489288673426184797 22422642183483252534819299)
                ·
                  refine ⟨33633963275224878802228949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22422642183483252534819299 33633963275224878802228949)
                  ·
                    refine ⟨788296014263083096927241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33633963275224878802228949 788296014263083096927241)
                    ·
                      rfl

theorem cell23_4605603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 7].length) (baseStart_4605603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605603 prefixEnd_4605603 := by exact prefixLift 4605603
  have htrace : WordTrace (prefixWord ++ tailWord_4605603) baseStart_4605603 baseEnd_4605603 := by
    simpa [prefixWord, tailWord_4605603, baseEnd_4605603] using wordTrace_append hprefix tailTrace_4605603
  have hstable : (prefixWord ++ tailWord_4605603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605603).length < 2 ^ (prefixWord ++ tailWord_4605603).sum := by decide
  have hdescent : baseEnd_4605603 < baseStart_4605603 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605630 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_4605630 : Nat := 118140960795 + 4605630 * 2 ^ 59
def prefixEnd_4605630 : Nat := 4983230072969 + 3 ^ 40 * 4605630 * 2
def baseEnd_4605630 : Nat := 2364901906766920685144099

theorem tailTrace_4605630 : CollatzResearch.WordTrace tailWord_4605630 prefixEnd_4605630 2364901906766920685144099 := by
  unfold tailWord_4605630
  simp only [CollatzResearch.WordTrace]
  refine ⟨20997640788074570478294793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111987417536397709217572229 20997640788074570478294793)
  ·
    refine ⟨15748230591055927858721095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20997640788074570478294793 15748230591055927858721095)
    ·
      refine ⟨23622345886583891788081643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15748230591055927858721095 23622345886583891788081643)
      ·
        refine ⟨35433518829875837682122465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23622345886583891788081643 35433518829875837682122465)
        ·
          refine ⟨26575139122406878261591849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35433518829875837682122465 26575139122406878261591849)
          ·
            refine ⟨19931354341805158696193887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26575139122406878261591849 19931354341805158696193887)
            ·
              refine ⟨29897031512707738044290831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19931354341805158696193887 29897031512707738044290831)
              ·
                refine ⟨44845547269061607066436247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29897031512707738044290831 44845547269061607066436247)
                ·
                  refine ⟨67268320903592410599654371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44845547269061607066436247 67268320903592410599654371)
                  ·
                    refine ⟨100902481355388615899481557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 67268320903592410599654371 100902481355388615899481557)
                    ·
                      refine ⟨2364901906766920685144099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 100902481355388615899481557 2364901906766920685144099)
                      ·
                        rfl

theorem cell23_4605630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_4605630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605630 prefixEnd_4605630 := by exact prefixLift 4605630
  have htrace : WordTrace (prefixWord ++ tailWord_4605630) baseStart_4605630 baseEnd_4605630 := by
    simpa [prefixWord, tailWord_4605630, baseEnd_4605630] using wordTrace_append hprefix tailTrace_4605630
  have hstable : (prefixWord ++ tailWord_4605630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605630).length < 2 ^ (prefixWord ++ tailWord_4605630).sum := by decide
  have hdescent : baseEnd_4605630 < baseStart_4605630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605640 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_4605640 : Nat := 118140960795 + 4605640 * 2 ^ 59
def prefixEnd_4605640 : Nat := 4983230072969 + 3 ^ 40 * 4605640 * 2
def baseEnd_4605640 : Nat := 2364907041573465646019053

theorem tailTrace_4605640 : CollatzResearch.WordTrace tailWord_4605640 prefixEnd_4605640 2364907041573465646019053 := by
  unfold tailWord_4605640
  simp only [CollatzResearch.WordTrace]
  refine ⟨83990745517280167767111187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111987660689706890356148249 83990745517280167767111187)
  ·
    refine ⟨125986118275920251650666781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83990745517280167767111187 125986118275920251650666781)
    ·
      refine ⟨47244794353470094369000043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125986118275920251650666781 47244794353470094369000043)
      ·
        refine ⟨70867191530205141553500065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47244794353470094369000043 70867191530205141553500065)
        ·
          refine ⟨53150393647653856165125049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70867191530205141553500065 53150393647653856165125049)
          ·
            refine ⟨39862795235740392123843787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53150393647653856165125049 39862795235740392123843787)
            ·
              refine ⟨59794192853610588185765681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39862795235740392123843787 59794192853610588185765681)
              ·
                refine ⟨44845644640207941139324261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59794192853610588185765681 44845644640207941139324261)
                ·
                  refine ⟨8408558370038988963623299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44845644640207941139324261 8408558370038988963623299)
                  ·
                    refine ⟨12612837555058483445434949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8408558370038988963623299 12612837555058483445434949)
                    ·
                      refine ⟨2364907041573465646019053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12612837555058483445434949 2364907041573465646019053)
                      ·
                        rfl

theorem cell23_4605640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_4605640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605640 prefixEnd_4605640 := by exact prefixLift 4605640
  have htrace : WordTrace (prefixWord ++ tailWord_4605640) baseStart_4605640 baseEnd_4605640 := by
    simpa [prefixWord, tailWord_4605640, baseEnd_4605640] using wordTrace_append hprefix tailTrace_4605640
  have hstable : (prefixWord ++ tailWord_4605640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605640).length < 2 ^ (prefixWord ++ tailWord_4605640).sum := by decide
  have hdescent : baseEnd_4605640 < baseStart_4605640 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605643 : List Nat := [1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5]
def baseStart_4605643 : Nat := 118140960795 + 4605643 * 2 ^ 59
def prefixEnd_4605643 : Nat := 4983230072969 + 3 ^ 40 * 4605643 * 2
def baseEnd_4605643 : Nat := 2364908582015429134281539

theorem tailTrace_4605643 : CollatzResearch.WordTrace tailWord_4605643 prefixEnd_4605643 2364908582015429134281539 := by
  unfold tailWord_4605643
  simp only [CollatzResearch.WordTrace]
  refine ⟨167981600453549467046581583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111987733635699644697721055 167981600453549467046581583)
  ·
    refine ⟨251972400680324200569872375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167981600453549467046581583 251972400680324200569872375)
    ·
      refine ⟨377958601020486300854808563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251972400680324200569872375 377958601020486300854808563)
      ·
        refine ⟨566937901530729451282212845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377958601020486300854808563 566937901530729451282212845)
        ·
          refine ⟨212601713074023544230829817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 566937901530729451282212845 212601713074023544230829817)
          ·
            refine ⟨159451284805517658173122363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212601713074023544230829817 159451284805517658173122363)
            ·
              refine ⟨239176927208276487259683545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159451284805517658173122363 239176927208276487259683545)
              ·
                refine ⟨179382695406207365444762659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 239176927208276487259683545 179382695406207365444762659)
                ·
                  refine ⟨269074043109311048167143989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179382695406207365444762659 269074043109311048167143989)
                  ·
                    refine ⟨25225691541497910765669749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 269074043109311048167143989 25225691541497910765669749)
                    ·
                      refine ⟨2364908582015429134281539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25225691541497910765669749 2364908582015429134281539)
                      ·
                        rfl

theorem cell23_4605643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 5, 5].length) (baseStart_4605643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605643 prefixEnd_4605643 := by exact prefixLift 4605643
  have htrace : WordTrace (prefixWord ++ tailWord_4605643) baseStart_4605643 baseEnd_4605643 := by
    simpa [prefixWord, tailWord_4605643, baseEnd_4605643] using wordTrace_append hprefix tailTrace_4605643
  have hstable : (prefixWord ++ tailWord_4605643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605643).length < 2 ^ (prefixWord ++ tailWord_4605643).sum := by decide
  have hdescent : baseEnd_4605643 < baseStart_4605643 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605657 : List Nat := [1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 4]
def baseStart_4605657 : Nat := 118140960795 + 4605657 * 2 ^ 59
def prefixEnd_4605657 : Nat := 4983230072969 + 3 ^ 40 * 4605657 * 2
def baseEnd_4605657 : Nat := 2364915770744592079506475

theorem tailTrace_4605657 : CollatzResearch.WordTrace tailWord_4605657 prefixEnd_4605657 2364915770744592079506475 := by
  unfold tailWord_4605657
  simp only [CollatzResearch.WordTrace]
  refine ⟨167982111075498747437591225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111988074050332498291727483 167982111075498747437591225)
  ·
    refine ⟨125986583306624060578193419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 167982111075498747437591225 125986583306624060578193419)
    ·
      refine ⟨188979874959936090867290129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125986583306624060578193419 188979874959936090867290129)
      ·
        refine ⟨141734906219952068150467597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188979874959936090867290129 141734906219952068150467597)
        ·
          refine ⟨53150589832482025556425349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141734906219952068150467597 53150589832482025556425349)
          ·
            refine ⟨9965735593590379791829753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53150589832482025556425349 9965735593590379791829753)
            ·
              refine ⟨7474301695192784843872315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9965735593590379791829753 7474301695192784843872315)
              ·
                refine ⟨11211452542789177265808473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474301695192784843872315 11211452542789177265808473)
                ·
                  refine ⟨8408589407091882949356355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11211452542789177265808473 8408589407091882949356355)
                  ·
                    refine ⟨12612884110637824424034533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8408589407091882949356355 12612884110637824424034533)
                    ·
                      refine ⟨2364915770744592079506475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12612884110637824424034533 2364915770744592079506475)
                      ·
                        rfl

theorem cell23_4605657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 2, 1, 2, 1, 4].length) (baseStart_4605657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605657 prefixEnd_4605657 := by exact prefixLift 4605657
  have htrace : WordTrace (prefixWord ++ tailWord_4605657) baseStart_4605657 baseEnd_4605657 := by
    simpa [prefixWord, tailWord_4605657, baseEnd_4605657] using wordTrace_append hprefix tailTrace_4605657
  have hstable : (prefixWord ++ tailWord_4605657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605657).length < 2 ^ (prefixWord ++ tailWord_4605657).sum := by decide
  have hdescent : baseEnd_4605657 < baseStart_4605657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605690 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3]
def baseStart_4605690 : Nat := 118140960795 + 4605690 * 2 ^ 59
def prefixEnd_4605690 : Nat := 4983230072969 + 3 ^ 40 * 4605690 * 2
def baseEnd_4605690 : Nat := 2364932715606190450393823

theorem tailTrace_4605690 : CollatzResearch.WordTrace tailWord_4605690 prefixEnd_4605690 2364932715606190450393823 := by
  unfold tailWord_4605690
  simp only [CollatzResearch.WordTrace]
  refine ⟨41995828671094798518385631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111988876456252796049028349 41995828671094798518385631)
  ·
    refine ⟨62993743006642197777578447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41995828671094798518385631 62993743006642197777578447)
    ·
      refine ⟨94490614509963296666367671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62993743006642197777578447 94490614509963296666367671)
      ·
        refine ⟨141735921764944944999551507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94490614509963296666367671 141735921764944944999551507)
        ·
          refine ⟨212603882647417417499327261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141735921764944944999551507 212603882647417417499327261)
          ·
            refine ⟨79726455992781531562247723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212603882647417417499327261 79726455992781531562247723)
            ·
              refine ⟨119589683989172297343371585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79726455992781531562247723 119589683989172297343371585)
              ·
                refine ⟨89692262991879223007528689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119589683989172297343371585 89692262991879223007528689)
                ·
                  refine ⟨67269197243909417255646517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89692262991879223007528689 67269197243909417255646517)
                  ·
                    refine ⟨6306487241616507867716861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67269197243909417255646517 6306487241616507867716861)
                    ·
                      refine ⟨2364932715606190450393823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306487241616507867716861 2364932715606190450393823)
                      ·
                        rfl

theorem cell23_4605690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 2, 5, 3].length) (baseStart_4605690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605690 prefixEnd_4605690 := by exact prefixLift 4605690
  have htrace : WordTrace (prefixWord ++ tailWord_4605690) baseStart_4605690 baseEnd_4605690 := by
    simpa [prefixWord, tailWord_4605690, baseEnd_4605690] using wordTrace_append hprefix tailTrace_4605690
  have hstable : (prefixWord ++ tailWord_4605690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605690).length < 2 ^ (prefixWord ++ tailWord_4605690).sum := by decide
  have hdescent : baseEnd_4605690 < baseStart_4605690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605707 : List Nat := [1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 3]
def baseStart_4605707 : Nat := 118140960795 + 4605707 * 2 ^ 59
def prefixEnd_4605707 : Nat := 4983230072969 + 3 ^ 40 * 4605707 * 2
def baseEnd_4605707 : Nat := 2364941444777316883881245

theorem tailTrace_4605707 : CollatzResearch.WordTrace tailWord_4605707 prefixEnd_4605707 2364941444777316883881245 := by
  unfold tailWord_4605707
  simp only [CollatzResearch.WordTrace]
  refine ⟨167983934725317605976911375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111989289816878403984607583 167983934725317605976911375)
  ·
    refine ⟨251975902087976408965367063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167983934725317605976911375 251975902087976408965367063)
    ·
      refine ⟨377963853131964613448050595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251975902087976408965367063 377963853131964613448050595)
      ·
        refine ⟨566945779697946920172075893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 377963853131964613448050595 566945779697946920172075893)
        ·
          refine ⟨53151166846682523766132115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 566945779697946920172075893 53151166846682523766132115)
          ·
            refine ⟨79726750270023785649198173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53151166846682523766132115 79726750270023785649198173)
            ·
              refine ⟨29897531351258919618449315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79726750270023785649198173 29897531351258919618449315)
              ·
                refine ⟨44846297026888379427673973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29897531351258919618449315 44846297026888379427673973)
                ·
                  refine ⟨4204340346270785571344435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44846297026888379427673973 4204340346270785571344435)
                  ·
                    refine ⟨6306510519406178357016653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4204340346270785571344435 6306510519406178357016653)
                    ·
                      refine ⟨2364941444777316883881245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306510519406178357016653 2364941444777316883881245)
                      ·
                        rfl

theorem cell23_4605707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 1, 5, 1, 3].length) (baseStart_4605707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605707 prefixEnd_4605707 := by exact prefixLift 4605707
  have htrace : WordTrace (prefixWord ++ tailWord_4605707) baseStart_4605707 baseEnd_4605707 := by
    simpa [prefixWord, tailWord_4605707, baseEnd_4605707] using wordTrace_append hprefix tailTrace_4605707
  have hstable : (prefixWord ++ tailWord_4605707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605707).length < 2 ^ (prefixWord ++ tailWord_4605707).sum := by decide
  have hdescent : baseEnd_4605707 < baseStart_4605707 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605727 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 1, 5]
def baseStart_4605727 : Nat := 118140960795 + 4605727 * 2 ^ 59
def prefixEnd_4605727 : Nat := 4983230072969 + 3 ^ 40 * 4605727 * 2
def baseEnd_4605727 : Nat := 788317238130135601877051

theorem tailTrace_4605727 : CollatzResearch.WordTrace tailWord_4605727 prefixEnd_4605727 788317238130135601877051 := by
  unfold tailWord_4605727
  simp only [CollatzResearch.WordTrace]
  refine ⟨167984664185245149392639435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111989776123496766261759623 167984664185245149392639435)
  ·
    refine ⟨251976996277867724088959153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167984664185245149392639435 251976996277867724088959153)
    ·
      refine ⟨188982747208400793066719365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251976996277867724088959153 188982747208400793066719365)
      ·
        refine ⟨35434265101575148700009881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 188982747208400793066719365 35434265101575148700009881)
        ·
          refine ⟨26575698826181361525007411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35434265101575148700009881 26575698826181361525007411)
          ·
            refine ⟨39863548239272042287511117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26575698826181361525007411 39863548239272042287511117)
            ·
              refine ⟨14948830589727015857816669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39863548239272042287511117 14948830589727015857816669)
              ·
                refine ⟨5605811471147630946681251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14948830589727015857816669 5605811471147630946681251)
                ·
                  refine ⟨8408717206721446420021877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5605811471147630946681251 8408717206721446420021877)
                  ·
                    refine ⟨788317238130135601877051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8408717206721446420021877 788317238130135601877051)
                    ·
                      rfl

theorem cell23_4605727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 5].length) (baseStart_4605727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605727 prefixEnd_4605727 := by exact prefixLift 4605727
  have htrace : WordTrace (prefixWord ++ tailWord_4605727) baseStart_4605727 baseEnd_4605727 := by
    simpa [prefixWord, tailWord_4605727, baseEnd_4605727] using wordTrace_append hprefix tailTrace_4605727
  have hstable : (prefixWord ++ tailWord_4605727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605727).length < 2 ^ (prefixWord ++ tailWord_4605727).sum := by decide
  have hdescent : baseEnd_4605727 < baseStart_4605727 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605767 : List Nat := [1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 3]
def baseStart_4605767 : Nat := 118140960795 + 4605767 * 2 ^ 59
def prefixEnd_4605767 : Nat := 4983230072969 + 3 ^ 40 * 4605767 * 2
def baseEnd_4605767 : Nat := 2364972253616586649130969

theorem tailTrace_4605767 : CollatzResearch.WordTrace tailWord_4605767 prefixEnd_4605767 2364972253616586649130969 := by
  unfold tailWord_4605767
  simp only [CollatzResearch.WordTrace]
  refine ⟨167986123105100236224095555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111990748736733490816063703 167986123105100236224095555)
  ·
    refine ⟨251979184657650354336143333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167986123105100236224095555 251979184657650354336143333)
    ·
      refine ⟨47246097123309441438026875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 251979184657650354336143333 47246097123309441438026875)
      ·
        refine ⟨70869145684964162157040313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47246097123309441438026875 70869145684964162157040313)
        ·
          refine ⟨53151859263723121617780235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70869145684964162157040313 53151859263723121617780235)
          ·
            refine ⟨79727788895584682426670353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53151859263723121617780235 79727788895584682426670353)
            ·
              refine ⟨59795841671688511820002765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79727788895584682426670353 59795841671688511820002765)
              ·
                refine ⟨22423440626883191932501037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59795841671688511820002765 22423440626883191932501037)
                ·
                  refine ⟨8408790235081196974687889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22423440626883191932501037 8408790235081196974687889)
                  ·
                    refine ⟨6306592676310897731015917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8408790235081196974687889 6306592676310897731015917)
                    ·
                      refine ⟨2364972253616586649130969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306592676310897731015917 2364972253616586649130969)
                      ·
                        rfl

theorem cell23_4605767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 3].length) (baseStart_4605767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605767 prefixEnd_4605767 := by exact prefixLift 4605767
  have htrace : WordTrace (prefixWord ++ tailWord_4605767) baseStart_4605767 baseEnd_4605767 := by
    simpa [prefixWord, tailWord_4605767, baseEnd_4605767] using wordTrace_append hprefix tailTrace_4605767
  have hstable : (prefixWord ++ tailWord_4605767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605767).length < 2 ^ (prefixWord ++ tailWord_4605767).sum := by decide
  have hdescent : baseEnd_4605767 < baseStart_4605767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605770 : List Nat := [3, 1, 2, 1, 1, 1, 5, 9]
def baseStart_4605770 : Nat := 118140960795 + 4605770 * 2 ^ 59
def prefixEnd_4605770 : Nat := 4983230072969 + 3 ^ 40 * 4605770 * 2
def baseEnd_4605770 : Nat := 87591622002168523607165

theorem tailTrace_4605770 : CollatzResearch.WordTrace tailWord_4605770 prefixEnd_4605770 87591622002168523607165 := by
  unfold tailWord_4605770
  simp only [CollatzResearch.WordTrace]
  refine ⟨41996558131022341934113691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111990821682726245157636509 41996558131022341934113691)
  ·
    refine ⟨62994837196533512901170537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41996558131022341934113691 62994837196533512901170537)
    ·
      refine ⟨47246127897400134675877903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62994837196533512901170537 47246127897400134675877903)
      ·
        refine ⟨70869191846100202013816855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47246127897400134675877903 70869191846100202013816855)
        ·
          refine ⟨106303787769150303020725283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70869191846100202013816855 106303787769150303020725283)
          ·
            refine ⟨159455681653725454531087925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106303787769150303020725283 159455681653725454531087925)
            ·
              refine ⟨14948970155036761362289493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159455681653725454531087925 14948970155036761362289493)
              ·
                refine ⟨87591622002168523607165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14948970155036761362289493 87591622002168523607165)
                ·
                  rfl

theorem cell23_4605770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 5, 9].length) (baseStart_4605770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605770 prefixEnd_4605770 := by exact prefixLift 4605770
  have htrace : WordTrace (prefixWord ++ tailWord_4605770) baseStart_4605770 baseEnd_4605770 := by
    simpa [prefixWord, tailWord_4605770, baseEnd_4605770] using wordTrace_append hprefix tailTrace_4605770
  have hstable : (prefixWord ++ tailWord_4605770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605770).length < 2 ^ (prefixWord ++ tailWord_4605770).sum := by decide
  have hdescent : baseEnd_4605770 < baseStart_4605770 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605807 : List Nat := [1, 1, 2, 1, 3, 1, 1, 1, 1, 9, 2]
def baseStart_4605807 : Nat := 118140960795 + 4605807 * 2 ^ 59
def prefixEnd_4605807 : Nat := 4983230072969 + 3 ^ 40 * 4605807 * 2
def baseEnd_4605807 : Nat := 2364992792842766492630785

theorem tailTrace_4605807 : CollatzResearch.WordTrace tailWord_4605807 prefixEnd_4605807 2364992792842766492630785 := by
  unfold tailWord_4605807
  simp only [CollatzResearch.WordTrace]
  refine ⟨167987582024955323055551675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111991721349970215370367783 167987582024955323055551675)
  ·
    refine ⟨251981373037432984583327513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167987582024955323055551675 251981373037432984583327513)
    ·
      refine ⟨188986029778074738437495635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251981373037432984583327513 188986029778074738437495635)
      ·
        refine ⟨283479044667112107656243453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188986029778074738437495635 283479044667112107656243453)
        ·
          refine ⟨106304641750167040371091295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283479044667112107656243453 106304641750167040371091295)
          ·
            refine ⟨159456962625250560556636943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106304641750167040371091295 159456962625250560556636943)
            ·
              refine ⟨239185443937875840834955415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159456962625250560556636943 239185443937875840834955415)
              ·
                refine ⟨358778165906813761252433123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239185443937875840834955415 358778165906813761252433123)
                ·
                  refine ⟨538167248860220641878649685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358778165906813761252433123 538167248860220641878649685)
                  ·
                    refine ⟨3153323723790355323507713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 538167248860220641878649685 3153323723790355323507713)
                    ·
                      refine ⟨2364992792842766492630785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153323723790355323507713 2364992792842766492630785)
                      ·
                        rfl

theorem cell23_4605807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 9, 2].length) (baseStart_4605807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605807 prefixEnd_4605807 := by exact prefixLift 4605807
  have htrace : WordTrace (prefixWord ++ tailWord_4605807) baseStart_4605807 baseEnd_4605807 := by
    simpa [prefixWord, tailWord_4605807, baseEnd_4605807] using wordTrace_append hprefix tailTrace_4605807
  have hstable : (prefixWord ++ tailWord_4605807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605807).length < 2 ^ (prefixWord ++ tailWord_4605807).sum := by decide
  have hdescent : baseEnd_4605807 < baseStart_4605807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605820 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 10]
def baseStart_4605820 : Nat := 118140960795 + 4605820 * 2 ^ 59
def prefixEnd_4605820 : Nat := 4983230072969 + 3 ^ 40 * 4605820 * 2
def baseEnd_4605820 : Nat := 2364999468091274941768225

theorem tailTrace_4605820 : CollatzResearch.WordTrace tailWord_4605820 prefixEnd_4605820 2364999468091274941768225 := by
  unfold tailWord_4605820
  simp only [CollatzResearch.WordTrace]
  refine ⟨83994028086954113137887457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111992037449272150850516609 83994028086954113137887457)
  ·
    refine ⟨62995521065215584853415593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83994028086954113137887457 62995521065215584853415593)
    ·
      refine ⟨47246640798911688640061695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62995521065215584853415593 47246640798911688640061695)
      ·
        refine ⟨70869961198367532960092543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47246640798911688640061695 70869961198367532960092543)
        ·
          refine ⟨106304941797551299440138815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70869961198367532960092543 106304941797551299440138815)
          ·
            refine ⟨159457412696326949160208223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106304941797551299440138815 159457412696326949160208223)
            ·
              refine ⟨239186119044490423740312335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159457412696326949160208223 239186119044490423740312335)
              ·
                refine ⟨358779178566735635610468503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 239186119044490423740312335 358779178566735635610468503)
                ·
                  refine ⟨538168767850103453415702755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 358779178566735635610468503 538168767850103453415702755)
                  ·
                    refine ⟨807253151775155180123554133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 538168767850103453415702755 807253151775155180123554133)
                    ·
                      refine ⟨2364999468091274941768225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 807253151775155180123554133 2364999468091274941768225)
                      ·
                        rfl

theorem cell23_4605820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 10].length) (baseStart_4605820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605820 prefixEnd_4605820 := by exact prefixLift 4605820
  have htrace : WordTrace (prefixWord ++ tailWord_4605820) baseStart_4605820 baseEnd_4605820 := by
    simpa [prefixWord, tailWord_4605820, baseEnd_4605820] using wordTrace_append hprefix tailTrace_4605820
  have hstable : (prefixWord ++ tailWord_4605820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605820).length < 2 ^ (prefixWord ++ tailWord_4605820).sum := by decide
  have hdescent : baseEnd_4605820 < baseStart_4605820 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605824 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 3, 3, 2]
def baseStart_4605824 : Nat := 118140960795 + 4605824 * 2 ^ 59
def prefixEnd_4605824 : Nat := 4983230072969 + 3 ^ 40 * 4605824 * 2
def baseEnd_4605824 : Nat := 2365001522013892926118207

theorem tailTrace_4605824 : CollatzResearch.WordTrace tailWord_4605824 prefixEnd_4605824 2365001522013892926118207 := by
  unfold tailWord_4605824
  simp only [CollatzResearch.WordTrace]
  refine ⟨83994101032946867479460263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111992134710595823305947017 83994101032946867479460263)
  ·
    refine ⟨125991151549420301219190395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83994101032946867479460263 125991151549420301219190395)
    ·
      refine ⟨188986727324130451828785593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125991151549420301219190395 188986727324130451828785593)
      ·
        refine ⟨141740045493097838871589195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188986727324130451828785593 141740045493097838871589195)
        ·
          refine ⟨212610068239646758307383793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141740045493097838871589195 212610068239646758307383793)
          ·
            refine ⟨159457551179735068730537845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212610068239646758307383793 159457551179735068730537845)
            ·
              refine ⟨14949145423100162693487923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159457551179735068730537845 14949145423100162693487923)
              ·
                refine ⟨22423718134650244040231885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14949145423100162693487923 22423718134650244040231885)
                ·
                  refine ⟨8408894300493841515086957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22423718134650244040231885 8408894300493841515086957)
                  ·
                    refine ⟨3153335362685190568157609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8408894300493841515086957 3153335362685190568157609)
                    ·
                      refine ⟨2365001522013892926118207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153335362685190568157609 2365001522013892926118207)
                      ·
                        rfl

theorem cell23_4605824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 3, 3, 2].length) (baseStart_4605824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605824 prefixEnd_4605824 := by exact prefixLift 4605824
  have htrace : WordTrace (prefixWord ++ tailWord_4605824) baseStart_4605824 baseEnd_4605824 := by
    simpa [prefixWord, tailWord_4605824, baseEnd_4605824] using wordTrace_append hprefix tailTrace_4605824
  have hstable : (prefixWord ++ tailWord_4605824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605824).length < 2 ^ (prefixWord ++ tailWord_4605824).sum := by decide
  have hdescent : baseEnd_4605824 < baseStart_4605824 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605871 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 2, 2, 2]
def baseStart_4605871 : Nat := 118140960795 + 4605871 * 2 ^ 59
def prefixEnd_4605871 : Nat := 4983230072969 + 3 ^ 40 * 4605871 * 2
def baseEnd_4605871 : Nat := 2365025655604654242230491

theorem tailTrace_4605871 : CollatzResearch.WordTrace tailWord_4605871 prefixEnd_4605871 2365025655604654242230491 := by
  unfold tailWord_4605871
  simp only [CollatzResearch.WordTrace]
  refine ⟨167989916296723461985881467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111993277531148974657254311 167989916296723461985881467)
  ·
    refine ⟨251984874445085192978822201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167989916296723461985881467 251984874445085192978822201)
    ·
      refine ⟨188988655833813894734116651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251984874445085192978822201 188988655833813894734116651)
      ·
        refine ⟨283482983750720842101174977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 188988655833813894734116651 283482983750720842101174977)
        ·
          refine ⟨212612237813040631575881233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283482983750720842101174977 212612237813040631575881233)
          ·
            refine ⟨159459178359780473681910925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212612237813040631575881233 159459178359780473681910925)
            ·
              refine ⟨59797191884917677630716597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159459178359780473681910925 59797191884917677630716597)
              ·
                refine ⟨5605986739211032277879681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59797191884917677630716597 5605986739211032277879681)
                ·
                  refine ⟨4204490054408274208409761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5605986739211032277879681 4204490054408274208409761)
                  ·
                    refine ⟨3153367540806205656307321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4204490054408274208409761 3153367540806205656307321)
                    ·
                      refine ⟨2365025655604654242230491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153367540806205656307321 2365025655604654242230491)
                      ·
                        rfl

theorem cell23_4605871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 2, 2, 2].length) (baseStart_4605871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605871 prefixEnd_4605871 := by exact prefixLift 4605871
  have htrace : WordTrace (prefixWord ++ tailWord_4605871) baseStart_4605871 baseEnd_4605871 := by
    simpa [prefixWord, tailWord_4605871, baseEnd_4605871] using wordTrace_append hprefix tailTrace_4605871
  have hstable : (prefixWord ++ tailWord_4605871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605871).length < 2 ^ (prefixWord ++ tailWord_4605871).sum := by decide
  have hdescent : baseEnd_4605871 < baseStart_4605871 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605877 : List Nat := [1, 3, 3, 2, 1, 2, 1, 1, 9]
def baseStart_4605877 : Nat := 118140960795 + 4605877 * 2 ^ 59
def prefixEnd_4605877 : Nat := 4983230072969 + 3 ^ 40 * 4605877 * 2
def baseEnd_4605877 : Nat := 262780970720953468750607

theorem tailTrace_4605877 : CollatzResearch.WordTrace tailWord_4605877 prefixEnd_4605877 262780970720953468750607 := by
  unfold tailWord_4605877
  simp only [CollatzResearch.WordTrace]
  refine ⟨167990135134701725010599885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111993423423134483340399923 167990135134701725010599885)
  ·
    refine ⟨62996300675513146878974957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167990135134701725010599885 62996300675513146878974957)
    ·
      refine ⟨23623612753317430079615609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62996300675513146878974957 23623612753317430079615609)
      ·
        refine ⟨17717709564988072559711707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23623612753317430079615609 17717709564988072559711707)
        ·
          refine ⟨26576564347482108839567561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17717709564988072559711707 26576564347482108839567561)
          ·
            refine ⟨19932423260611581629675671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26576564347482108839567561 19932423260611581629675671)
            ·
              refine ⟨29898634890917372444513507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19932423260611581629675671 29898634890917372444513507)
              ·
                refine ⟨44847952336376058666770261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29898634890917372444513507 44847952336376058666770261)
                ·
                  refine ⟨262780970720953468750607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44847952336376058666770261 262780970720953468750607)
                  ·
                    rfl

theorem cell23_4605877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 1, 9].length) (baseStart_4605877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605877 prefixEnd_4605877 := by exact prefixLift 4605877
  have htrace : WordTrace (prefixWord ++ tailWord_4605877) baseStart_4605877 baseEnd_4605877 := by
    simpa [prefixWord, tailWord_4605877, baseEnd_4605877] using wordTrace_append hprefix tailTrace_4605877
  have hstable : (prefixWord ++ tailWord_4605877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605877).length < 2 ^ (prefixWord ++ tailWord_4605877).sum := by decide
  have hdescent : baseEnd_4605877 < baseStart_4605877 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605887 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 3]
def baseStart_4605887 : Nat := 118140960795 + 4605887 * 2 ^ 59
def prefixEnd_4605887 : Nat := 4983230072969 + 3 ^ 40 * 4605887 * 2
def baseEnd_4605887 : Nat := 2365033871295126179630417

theorem tailTrace_4605887 : CollatzResearch.WordTrace tailWord_4605887 prefixEnd_4605887 2365033871295126179630417 := by
  unfold tailWord_4605887
  simp only [CollatzResearch.WordTrace]
  refine ⟨167990499864665496718463915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111993666576443664478975943 167990499864665496718463915)
  ·
    refine ⟨251985749796998245077695873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167990499864665496718463915 251985749796998245077695873)
    ·
      refine ⟨188989312347748683808271905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 251985749796998245077695873 188989312347748683808271905)
      ·
        refine ⟨141741984260811512856203929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 188989312347748683808271905 141741984260811512856203929)
        ·
          refine ⟨106306488195608634642152947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141741984260811512856203929 106306488195608634642152947)
          ·
            refine ⟨159459732293412951963229421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106306488195608634642152947 159459732293412951963229421)
            ·
              refine ⟨59797399610029856986211033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 159459732293412951963229421 59797399610029856986211033)
              ·
                refine ⟨44848049707522392739658275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59797399610029856986211033 44848049707522392739658275)
                ·
                  refine ⟨67272074561283589109487413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44848049707522392739658275 67272074561283589109487413)
                  ·
                    refine ⟨6306756990120336479014445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 67272074561283589109487413 6306756990120336479014445)
                    ·
                      refine ⟨2365033871295126179630417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306756990120336479014445 2365033871295126179630417)
                      ·
                        rfl

theorem cell23_4605887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 3].length) (baseStart_4605887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605887 prefixEnd_4605887 := by exact prefixLift 4605887
  have htrace : WordTrace (prefixWord ++ tailWord_4605887) baseStart_4605887 baseEnd_4605887 := by
    simpa [prefixWord, tailWord_4605887, baseEnd_4605887] using wordTrace_append hprefix tailTrace_4605887
  have hstable : (prefixWord ++ tailWord_4605887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605887).length < 2 ^ (prefixWord ++ tailWord_4605887).sum := by decide
  have hdescent : baseEnd_4605887 < baseStart_4605887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605922 : List Nat := [3, 3, 3, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4605922 : Nat := 118140960795 + 4605922 * 2 ^ 59
def prefixEnd_4605922 : Nat := 4983230072969 + 3 ^ 40 * 4605922 * 2
def baseEnd_4605922 : Nat := 2365051843118033542692757

theorem tailTrace_4605922 : CollatzResearch.WordTrace tailWord_4605922 prefixEnd_4605922 2365051843118033542692757 := by
  unfold tailWord_4605922
  simp only [CollatzResearch.WordTrace]
  refine ⟨41997944104884674423997005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 111994517613025798463992013 41997944104884674423997005)
  ·
    refine ⟨15749229039331752908998877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41997944104884674423997005 15749229039331752908998877)
    ·
      refine ⟨5905960889749407340874579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15749229039331752908998877 5905960889749407340874579)
      ·
        refine ⟨8858941334624111011311869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5905960889749407340874579 8858941334624111011311869)
        ·
          refine ⟨3322103000484041629241951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8858941334624111011311869 3322103000484041629241951)
          ·
            refine ⟨4983154500726062443862927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322103000484041629241951 4983154500726062443862927)
            ·
              refine ⟨7474731751089093665794391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983154500726062443862927 7474731751089093665794391)
              ·
                refine ⟨11212097626633640498691587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474731751089093665794391 11212097626633640498691587)
                ·
                  refine ⟨16818146439950460748037381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11212097626633640498691587 16818146439950460748037381)
                  ·
                    refine ⟨3153402457490711390257009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16818146439950460748037381 3153402457490711390257009)
                    ·
                      refine ⟨2365051843118033542692757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153402457490711390257009 2365051843118033542692757)
                      ·
                        rfl

theorem cell23_4605922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4605922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605922 prefixEnd_4605922 := by exact prefixLift 4605922
  have htrace : WordTrace (prefixWord ++ tailWord_4605922) baseStart_4605922 baseEnd_4605922 := by
    simpa [prefixWord, tailWord_4605922, baseEnd_4605922] using wordTrace_append hprefix tailTrace_4605922
  have hstable : (prefixWord ++ tailWord_4605922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605922).length < 2 ^ (prefixWord ++ tailWord_4605922).sum := by decide
  have hdescent : baseEnd_4605922 < baseStart_4605922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605944 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 1, 6, 2]
def baseStart_4605944 : Nat := 118140960795 + 4605944 * 2 ^ 59
def prefixEnd_4605944 : Nat := 4983230072969 + 3 ^ 40 * 4605944 * 2
def baseEnd_4605944 : Nat := 2365063139692432456617655

theorem tailTrace_4605944 : CollatzResearch.WordTrace tailWord_4605944 prefixEnd_4605944 2365063139692432456617655 := by
  unfold tailWord_4605944
  simp only [CollatzResearch.WordTrace]
  refine ⟨83996289412729497726644443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 111995052550305996968859257 83996289412729497726644443)
  ·
    refine ⟨125994434119094246589966665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83996289412729497726644443 125994434119094246589966665)
    ·
      refine ⟨94495825589320684942474999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125994434119094246589966665 94495825589320684942474999)
      ·
        refine ⟨141743738383981027413712499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94495825589320684942474999 141743738383981027413712499)
        ·
          refine ⟨212615607575971541120568749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141743738383981027413712499 212615607575971541120568749)
          ·
            refine ⟨79730852840989327920213281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212615607575971541120568749 79730852840989327920213281)
            ·
              refine ⟨59798139630741995940159961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79730852840989327920213281 59798139630741995940159961)
              ·
                refine ⟨44848604723056496955119971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59798139630741995940159961 44848604723056496955119971)
                ·
                  refine ⟨67272907084584745432679957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44848604723056496955119971 67272907084584745432679957)
                  ·
                    refine ⟨3153417519589909942156873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 67272907084584745432679957 3153417519589909942156873)
                    ·
                      refine ⟨2365063139692432456617655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153417519589909942156873 2365063139692432456617655)
                      ·
                        rfl

theorem cell23_4605944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 1, 6, 2].length) (baseStart_4605944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605944 prefixEnd_4605944 := by exact prefixLift 4605944
  have htrace : WordTrace (prefixWord ++ tailWord_4605944) baseStart_4605944 baseEnd_4605944 := by
    simpa [prefixWord, tailWord_4605944, baseEnd_4605944] using wordTrace_append hprefix tailTrace_4605944
  have hstable : (prefixWord ++ tailWord_4605944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605944).length < 2 ^ (prefixWord ++ tailWord_4605944).sum := by decide
  have hdescent : baseEnd_4605944 < baseStart_4605944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605971 : List Nat := [1, 1, 1, 2, 1, 4, 2, 6, 1, 4]
def baseStart_4605971 : Nat := 118140960795 + 4605971 * 2 ^ 59
def prefixEnd_4605971 : Nat := 4983230072969 + 3 ^ 40 * 4605971 * 2
def baseEnd_4605971 : Nat := 788359001223367950326677

theorem tailTrace_4605971 : CollatzResearch.WordTrace tailWord_4605971 prefixEnd_4605971 788359001223367950326677 := by
  unfold tailWord_4605971
  simp only [CollatzResearch.WordTrace]
  refine ⟨167993563596361179064521767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111995709064240786043014511 167993563596361179064521767)
  ·
    refine ⟨251990345394541768596782651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 167993563596361179064521767 251990345394541768596782651)
    ·
      refine ⟨377985518091812652895173977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 251990345394541768596782651 377985518091812652895173977)
      ·
        refine ⟨283489138568859489671380483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 377985518091812652895173977 283489138568859489671380483)
        ·
          refine ⟨425233707853289234507070725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283489138568859489671380483 425233707853289234507070725)
          ·
            refine ⟨79731320222491731470075761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 425233707853289234507070725 79731320222491731470075761)
            ·
              refine ⟨59798490166868798602556821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79731320222491731470075761 59798490166868798602556821)
              ·
                refine ⟨2803054226571974934494851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59798490166868798602556821 2803054226571974934494851)
                ·
                  refine ⟨4204581339857962401742277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803054226571974934494851 4204581339857962401742277)
                  ·
                    refine ⟨788359001223367950326677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4204581339857962401742277 788359001223367950326677)
                    ·
                      rfl

theorem cell23_4605971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 4].length) (baseStart_4605971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605971 prefixEnd_4605971 := by exact prefixLift 4605971
  have htrace : WordTrace (prefixWord ++ tailWord_4605971) baseStart_4605971 baseEnd_4605971 := by
    simpa [prefixWord, tailWord_4605971, baseEnd_4605971] using wordTrace_append hprefix tailTrace_4605971
  have hstable : (prefixWord ++ tailWord_4605971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605971).length < 2 ^ (prefixWord ++ tailWord_4605971).sum := by decide
  have hdescent : baseEnd_4605971 < baseStart_4605971 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4605998 : List Nat := [4, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_4605998 : Nat := 118140960795 + 4605998 * 2 ^ 59
def prefixEnd_4605998 : Nat := 4983230072969 + 3 ^ 40 * 4605998 * 2
def baseEnd_4605998 : Nat := 2365090867647775245342407

theorem tailTrace_4605998 : CollatzResearch.WordTrace tailWord_4605998 prefixEnd_4605998 2365090867647775245342407 := by
  unfold tailWord_4605998
  simp only [CollatzResearch.WordTrace]
  refine ⟨20999318545907920334469331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 111996365578175575117169765 20999318545907920334469331)
  ·
    refine ⟨31498977818861880501703997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20999318545907920334469331 31498977818861880501703997)
    ·
      refine ⟨11812116682073205188138999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31498977818861880501703997 11812116682073205188138999)
      ·
        refine ⟨17718175023109807782208499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11812116682073205188138999 17718175023109807782208499)
        ·
          refine ⟨26577262534664711673312749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17718175023109807782208499 26577262534664711673312749)
          ·
            refine ⟨9966473450499266877492281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26577262534664711673312749 9966473450499266877492281)
            ·
              refine ⟨7474855087874450158119211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9966473450499266877492281 7474855087874450158119211)
              ·
                refine ⟨11212282631811675237178817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474855087874450158119211 11212282631811675237178817)
                ·
                  refine ⟨8409211973858756427884113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11212282631811675237178817 8409211973858756427884113)
                  ·
                    refine ⟨6306908980394067320913085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8409211973858756427884113 6306908980394067320913085)
                    ·
                      refine ⟨2365090867647775245342407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306908980394067320913085 2365090867647775245342407)
                      ·
                        rfl

theorem cell23_4605998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_4605998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4605998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4605998 prefixEnd_4605998 := by exact prefixLift 4605998
  have htrace : WordTrace (prefixWord ++ tailWord_4605998) baseStart_4605998 baseEnd_4605998 := by
    simpa [prefixWord, tailWord_4605998, baseEnd_4605998] using wordTrace_append hprefix tailTrace_4605998
  have hstable : (prefixWord ++ tailWord_4605998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4605998).length < 2 ^ (prefixWord ++ tailWord_4605998).sum := by decide
  have hdescent : baseEnd_4605998 < baseStart_4605998 := by decide
  rcases family_descends (prefixWord ++ tailWord_4605998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606045 : List Nat := [1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 3]
def baseStart_4606045 : Nat := 118140960795 + 4606045 * 2 ^ 59
def prefixEnd_4606045 : Nat := 4983230072969 + 3 ^ 40 * 4606045 * 2
def baseEnd_4606045 : Nat := 2365115001238536561454691

theorem tailTrace_4606045 : CollatzResearch.WordTrace tailWord_4606045 prefixEnd_4606045 2365115001238536561454691 := by
  unfold tailWord_4606045
  simp only [CollatzResearch.WordTrace]
  refine ⟨167996262598093089702715589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111997508398728726468477059 167996262598093089702715589)
  ·
    refine ⟨31499299237142454319259173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 167996262598093089702715589 31499299237142454319259173)
    ·
      refine ⟨5906118606964210184861095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31499299237142454319259173 5906118606964210184861095)
      ·
        refine ⟨8859177910446315277291643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5906118606964210184861095 8859177910446315277291643)
        ·
          refine ⟨13288766865669472915937465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8859177910446315277291643 13288766865669472915937465)
          ·
            refine ⟨9966575149252104686953099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13288766865669472915937465 9966575149252104686953099)
            ·
              refine ⟨14949862723878157030429649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9966575149252104686953099 14949862723878157030429649)
              ·
                refine ⟨11212397042908617772822237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14949862723878157030429649 11212397042908617772822237)
                ·
                  refine ⟨4204648891090731664808339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11212397042908617772822237 4204648891090731664808339)
                  ·
                    refine ⟨6306973336636097497212509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4204648891090731664808339 6306973336636097497212509)
                    ·
                      refine ⟨2365115001238536561454691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6306973336636097497212509 2365115001238536561454691)
                      ·
                        rfl

theorem cell23_4606045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_4606045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606045 prefixEnd_4606045 := by exact prefixLift 4606045
  have htrace : WordTrace (prefixWord ++ tailWord_4606045) baseStart_4606045 baseEnd_4606045 := by
    simpa [prefixWord, tailWord_4606045, baseEnd_4606045] using wordTrace_append hprefix tailTrace_4606045
  have hstable : (prefixWord ++ tailWord_4606045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606045).length < 2 ^ (prefixWord ++ tailWord_4606045).sum := by decide
  have hdescent : baseEnd_4606045 < baseStart_4606045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606061 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_4606061 : Nat := 118140960795 + 4606061 * 2 ^ 59
def prefixEnd_4606061 : Nat := 4983230072969 + 3 ^ 40 * 4606061 * 2
def baseEnd_4606061 : Nat := 788374405643002832951539

theorem tailTrace_4606061 : CollatzResearch.WordTrace tailWord_4606061 prefixEnd_4606061 788374405643002832951539 := by
  unfold tailWord_4606061
  simp only [CollatzResearch.WordTrace]
  refine ⟨167996846166035124435298037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111997897444023416290198691 167996846166035124435298037)
  ·
    refine ⟨15749704328065792915809191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 167996846166035124435298037 15749704328065792915809191)
    ·
      refine ⟨23624556492098689373713787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15749704328065792915809191 23624556492098689373713787)
      ·
        refine ⟨35436834738148034060570681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23624556492098689373713787 35436834738148034060570681)
        ·
          refine ⟨26577626053611025545428011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35436834738148034060570681 26577626053611025545428011)
          ·
            refine ⟨39866439080416538318142017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26577626053611025545428011 39866439080416538318142017)
            ·
              refine ⟨29899829310312403738606513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39866439080416538318142017 29899829310312403738606513)
              ·
                refine ⟨22424871982734302803954885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29899829310312403738606513 22424871982734302803954885)
                ·
                  refine ⟨4204663496762681775741541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22424871982734302803954885 4204663496762681775741541)
                  ·
                    refine ⟨788374405643002832951539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4204663496762681775741541 788374405643002832951539)
                    ·
                      rfl

theorem cell23_4606061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_4606061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606061 prefixEnd_4606061 := by exact prefixLift 4606061
  have htrace : WordTrace (prefixWord ++ tailWord_4606061) baseStart_4606061 baseEnd_4606061 := by
    simpa [prefixWord, tailWord_4606061, baseEnd_4606061] using wordTrace_append hprefix tailTrace_4606061
  have hstable : (prefixWord ++ tailWord_4606061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606061).length < 2 ^ (prefixWord ++ tailWord_4606061).sum := by decide
  have hdescent : baseEnd_4606061 < baseStart_4606061 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606085 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 3, 2, 2]
def baseStart_4606085 : Nat := 118140960795 + 4606085 * 2 ^ 59
def prefixEnd_4606085 : Nat := 4983230072969 + 3 ^ 40 * 4606085 * 2
def baseEnd_4606085 : Nat := 2365135540464716404954507

theorem tailTrace_4606085 : CollatzResearch.WordTrace tailWord_4606085 prefixEnd_4606085 2365135540464716404954507 := by
  unfold tailWord_4606085
  simp only [CollatzResearch.WordTrace]
  refine ⟨167997721517948176534171709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 111998481011965451022781139 167997721517948176534171709)
  ·
    refine ⟨62999145569230566200314391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 167997721517948176534171709 62999145569230566200314391)
    ·
      refine ⟨94498718353845849300471587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62999145569230566200314391 94498718353845849300471587)
      ·
        refine ⟨141748077530768773950707381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94498718353845849300471587 141748077530768773950707381)
        ·
          refine ⟨13288882268509572557878817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 141748077530768773950707381 13288882268509572557878817)
          ·
            refine ⟨9966661701382179418409113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13288882268509572557878817 9966661701382179418409113)
            ·
              refine ⟨7474996276036634563806835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9966661701382179418409113 7474996276036634563806835)
              ·
                refine ⟨11212494414054951845710253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7474996276036634563806835 11212494414054951845710253)
                ·
                  refine ⟨4204685405270606942141345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11212494414054951845710253 4204685405270606942141345)
                  ·
                    refine ⟨3153514053952955206606009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4204685405270606942141345 3153514053952955206606009)
                    ·
                      refine ⟨2365135540464716404954507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153514053952955206606009 2365135540464716404954507)
                      ·
                        rfl

theorem cell23_4606085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 3, 2, 2].length) (baseStart_4606085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606085 prefixEnd_4606085 := by exact prefixLift 4606085
  have htrace : WordTrace (prefixWord ++ tailWord_4606085) baseStart_4606085 baseEnd_4606085 := by
    simpa [prefixWord, tailWord_4606085, baseEnd_4606085] using wordTrace_append hprefix tailTrace_4606085
  have hstable : (prefixWord ++ tailWord_4606085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606085).length < 2 ^ (prefixWord ++ tailWord_4606085).sum := by decide
  have hdescent : baseEnd_4606085 < baseStart_4606085 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606162 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 1, 3, 2]
def baseStart_4606162 : Nat := 118140960795 + 4606162 * 2 ^ 59
def prefixEnd_4606162 : Nat := 4983230072969 + 3 ^ 40 * 4606162 * 2
def baseEnd_4606162 : Nat := 2365175078475112603691653

theorem tailTrace_4606162 : CollatzResearch.WordTrace tailWord_4606162 prefixEnd_4606162 2365175078475112603691653 := by
  unfold tailWord_4606162
  simp only [CollatzResearch.WordTrace]
  refine ⟨42000132484667304671181185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112000353292446145789816493 42000132484667304671181185)
  ·
    refine ⟨31500099363500478503385889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42000132484667304671181185 31500099363500478503385889)
    ·
      refine ⟨23625074522625358877539417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31500099363500478503385889 23625074522625358877539417)
      ·
        refine ⟨17718805891969019158154563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23625074522625358877539417 17718805891969019158154563)
        ·
          refine ⟨26578208837953528737231845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17718805891969019158154563 26578208837953528737231845)
          ·
            refine ⟨4983414157116286638230971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26578208837953528737231845 4983414157116286638230971)
            ·
              refine ⟨7475121235674429957346457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983414157116286638230971 7475121235674429957346457)
              ·
                refine ⟨5606340926755822468009843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7475121235674429957346457 5606340926755822468009843)
                ·
                  refine ⟨8409511390133733702014765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5606340926755822468009843 8409511390133733702014765)
                  ·
                    refine ⟨3153566771300150138255537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8409511390133733702014765 3153566771300150138255537)
                    ·
                      refine ⟨2365175078475112603691653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153566771300150138255537 2365175078475112603691653)
                      ·
                        rfl

theorem cell23_4606162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_4606162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606162 prefixEnd_4606162 := by exact prefixLift 4606162
  have htrace : WordTrace (prefixWord ++ tailWord_4606162) baseStart_4606162 baseEnd_4606162 := by
    simpa [prefixWord, tailWord_4606162, baseEnd_4606162] using wordTrace_append hprefix tailTrace_4606162
  have hstable : (prefixWord ++ tailWord_4606162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606162).length < 2 ^ (prefixWord ++ tailWord_4606162).sum := by decide
  have hdescent : baseEnd_4606162 < baseStart_4606162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606179 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 1, 3, 2]
def baseStart_4606179 : Nat := 118140960795 + 4606179 * 2 ^ 59
def prefixEnd_4606179 : Nat := 4983230072969 + 3 ^ 40 * 4606179 * 2
def baseEnd_4606179 : Nat := 2365183807646239037179075

theorem tailTrace_4606179 : CollatzResearch.WordTrace tailWord_4606179 prefixEnd_4606179 2365183807646239037179075 := by
  unfold tailWord_4606179
  simp only [CollatzResearch.WordTrace]
  refine ⟨168001149979607630588093591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112000766653071753725395727 168001149979607630588093591)
  ·
    refine ⟨252001724969411445882140387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168001149979607630588093591 252001724969411445882140387)
    ·
      refine ⟨378002587454117168823210581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252001724969411445882140387 378002587454117168823210581)
      ·
        refine ⟨4429717821727935572146999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 378002587454117168823210581 4429717821727935572146999)
        ·
          refine ⟨6644576732591903358220499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4429717821727935572146999 6644576732591903358220499)
          ·
            refine ⟨9966865098887855037330749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6644576732591903358220499 9966865098887855037330749)
            ·
              refine ⟨3737574412082945638999031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9966865098887855037330749 3737574412082945638999031)
              ·
                refine ⟨5606361618124418458498547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737574412082945638999031 5606361618124418458498547)
                ·
                  refine ⟨8409542427186627687747821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5606361618124418458498547 8409542427186627687747821)
                  ·
                    refine ⟨3153578410194985382905433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8409542427186627687747821 3153578410194985382905433)
                    ·
                      refine ⟨2365183807646239037179075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153578410194985382905433 2365183807646239037179075)
                      ·
                        rfl

theorem cell23_4606179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_4606179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606179 prefixEnd_4606179 := by exact prefixLift 4606179
  have htrace : WordTrace (prefixWord ++ tailWord_4606179) baseStart_4606179 baseEnd_4606179 := by
    simpa [prefixWord, tailWord_4606179, baseEnd_4606179] using wordTrace_append hprefix tailTrace_4606179
  have hstable : (prefixWord ++ tailWord_4606179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606179).length < 2 ^ (prefixWord ++ tailWord_4606179).sum := by decide
  have hdescent : baseEnd_4606179 < baseStart_4606179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606261 : List Nat := [1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4606261 : Nat := 118140960795 + 4606261 * 2 ^ 59
def prefixEnd_4606261 : Nat := 4983230072969 + 3 ^ 40 * 4606261 * 2
def baseEnd_4606261 : Nat := 2365225913059907716353697

theorem tailTrace_4606261 : CollatzResearch.WordTrace tailWord_4606261 prefixEnd_4606261 2365225913059907716353697 := by
  unfold tailWord_4606261
  simp only [CollatzResearch.WordTrace]
  refine ⟨168004140765310558592578637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112002760510207039061719091 168004140765310558592578637)
  ·
    refine ⟨63001552786991459472216989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168004140765310558592578637 63001552786991459472216989)
    ·
      refine ⟨23625582295121797302081371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63001552786991459472216989 23625582295121797302081371)
      ·
        refine ⟨35438373442682695953122057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23625582295121797302081371 35438373442682695953122057)
        ·
          refine ⟨26578780082012021964841543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35438373442682695953122057 26578780082012021964841543)
          ·
            refine ⟨39868170123018032947262315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26578780082012021964841543 39868170123018032947262315)
            ·
              refine ⟨59802255184527049420893473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39868170123018032947262315 59802255184527049420893473)
              ·
                refine ⟨44851691388395287065670105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59802255184527049420893473 44851691388395287065670105)
                ·
                  refine ⟨33638768541296465299252579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44851691388395287065670105 33638768541296465299252579)
                  ·
                    refine ⟨50458152811944697948878869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33638768541296465299252579 50458152811944697948878869)
                    ·
                      refine ⟨2365225913059907716353697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50458152811944697948878869 2365225913059907716353697)
                      ·
                        rfl

theorem cell23_4606261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4606261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606261 prefixEnd_4606261 := by exact prefixLift 4606261
  have htrace : WordTrace (prefixWord ++ tailWord_4606261) baseStart_4606261 baseEnd_4606261 := by
    simpa [prefixWord, tailWord_4606261, baseEnd_4606261] using wordTrace_append hprefix tailTrace_4606261
  have hstable : (prefixWord ++ tailWord_4606261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606261).length < 2 ^ (prefixWord ++ tailWord_4606261).sum := by decide
  have hdescent : baseEnd_4606261 < baseStart_4606261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606265 : List Nat := [1, 2, 1, 6, 1, 1, 2, 1, 2, 4, 2]
def baseStart_4606265 : Nat := 118140960795 + 4606265 * 2 ^ 59
def prefixEnd_4606265 : Nat := 4983230072969 + 3 ^ 40 * 4606265 * 2
def baseEnd_4606265 : Nat := 2365227966982525700703679

theorem tailTrace_4606265 : CollatzResearch.WordTrace tailWord_4606265 prefixEnd_4606265 2365227966982525700703679 := by
  unfold tailWord_4606265
  simp only [CollatzResearch.WordTrace]
  refine ⟨168004286657296067275724249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112002857771530711517149499 168004286657296067275724249)
  ·
    refine ⟨126003214992972050456793187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168004286657296067275724249 126003214992972050456793187)
    ·
      refine ⟨189004822489458075685189781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126003214992972050456793187 189004822489458075685189781)
      ·
        refine ⟨8859601054193347297743271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 189004822489458075685189781 8859601054193347297743271)
        ·
          refine ⟨13289401581290020946614907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8859601054193347297743271 13289401581290020946614907)
          ·
            refine ⟨19934102371935031419922361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13289401581290020946614907 19934102371935031419922361)
            ·
              refine ⟨14950576778951273564941771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19934102371935031419922361 14950576778951273564941771)
              ·
                refine ⟨22425865168426910347412657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14950576778951273564941771 22425865168426910347412657)
                ·
                  refine ⟨16819398876320182760559493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22425865168426910347412657 16819398876320182760559493)
                  ·
                    refine ⟨3153637289310034267604905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16819398876320182760559493 3153637289310034267604905)
                    ·
                      refine ⟨2365227966982525700703679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153637289310034267604905 2365227966982525700703679)
                      ·
                        rfl

theorem cell23_4606265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_4606265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606265 prefixEnd_4606265 := by exact prefixLift 4606265
  have htrace : WordTrace (prefixWord ++ tailWord_4606265) baseStart_4606265 baseEnd_4606265 := by
    simpa [prefixWord, tailWord_4606265, baseEnd_4606265] using wordTrace_append hprefix tailTrace_4606265
  have hstable : (prefixWord ++ tailWord_4606265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606265).length < 2 ^ (prefixWord ++ tailWord_4606265).sum := by decide
  have hdescent : baseEnd_4606265 < baseStart_4606265 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606281 : List Nat := [1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 3]
def baseStart_4606281 : Nat := 118140960795 + 4606281 * 2 ^ 59
def prefixEnd_4606281 : Nat := 4983230072969 + 3 ^ 40 * 4606281 * 2
def baseEnd_4606281 : Nat := 2365236182672997638103605

theorem tailTrace_4606281 : CollatzResearch.WordTrace tailWord_4606281 prefixEnd_4606281 2365236182672997638103605 := by
  unfold tailWord_4606281
  simp only [CollatzResearch.WordTrace]
  refine ⟨168004870225238102008306697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112003246816825401338871131 168004870225238102008306697)
  ·
    refine ⟨126003652668928576506230023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168004870225238102008306697 126003652668928576506230023)
    ·
      refine ⟨189005479003392864759345035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126003652668928576506230023 189005479003392864759345035)
      ·
        refine ⟨283508218505089297139017553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189005479003392864759345035 283508218505089297139017553)
        ·
          refine ⟨212631163878816972854263165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 283508218505089297139017553 212631163878816972854263165)
          ·
            refine ⟨79736686454556364820348687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 212631163878816972854263165 79736686454556364820348687)
            ·
              refine ⟨119605029681834547230523031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79736686454556364820348687 119605029681834547230523031)
              ·
                refine ⟨179407544522751820845784547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119605029681834547230523031 179407544522751820845784547)
                ·
                  refine ⟨269111316784127731268676821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 179407544522751820845784547 269111316784127731268676821)
                  ·
                    refine ⟨6307296487127993701609613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 269111316784127731268676821 6307296487127993701609613)
                    ·
                      refine ⟨2365236182672997638103605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307296487127993701609613 2365236182672997638103605)
                      ·
                        rfl

theorem cell23_4606281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 1, 1, 7, 3].length) (baseStart_4606281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606281 prefixEnd_4606281 := by exact prefixLift 4606281
  have htrace : WordTrace (prefixWord ++ tailWord_4606281) baseStart_4606281 baseEnd_4606281 := by
    simpa [prefixWord, tailWord_4606281, baseEnd_4606281] using wordTrace_append hprefix tailTrace_4606281
  have hstable : (prefixWord ++ tailWord_4606281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606281).length < 2 ^ (prefixWord ++ tailWord_4606281).sum := by decide
  have hdescent : baseEnd_4606281 < baseStart_4606281 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606292 : List Nat := [2, 4, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_4606292 : Nat := 118140960795 + 4606292 * 2 ^ 59
def prefixEnd_4606292 : Nat := 4983230072969 + 3 ^ 40 * 4606292 * 2
def baseEnd_4606292 : Nat := 788413943653399031688685

theorem tailTrace_4606292 : CollatzResearch.WordTrace tailWord_4606292 prefixEnd_4606292 788413943653399031688685 := by
  unfold tailWord_4606292
  simp only [CollatzResearch.WordTrace]
  refine ⟨84002635714099125443478565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112003514285465500591304753 84002635714099125443478565)
  ·
    refine ⟨15750494196393586020652231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 84002635714099125443478565 15750494196393586020652231)
    ·
      refine ⟨23625741294590379030978347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15750494196393586020652231 23625741294590379030978347)
      ·
        refine ⟨35438611941885568546467521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23625741294590379030978347 35438611941885568546467521)
        ·
          refine ⟨26578958956414176409850641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35438611941885568546467521 26578958956414176409850641)
          ·
            refine ⟨19934219217310632307387981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26578958956414176409850641 19934219217310632307387981)
            ·
              refine ⟨7475332206491487115270493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19934219217310632307387981 7475332206491487115270493)
              ·
                refine ⟨2803249577434307668226435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7475332206491487115270493 2803249577434307668226435)
                ·
                  refine ⟨4204874366151461502339653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803249577434307668226435 4204874366151461502339653)
                  ·
                    refine ⟨788413943653399031688685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4204874366151461502339653 788413943653399031688685)
                    ·
                      rfl

theorem cell23_4606292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_4606292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606292 prefixEnd_4606292 := by exact prefixLift 4606292
  have htrace : WordTrace (prefixWord ++ tailWord_4606292) baseStart_4606292 baseEnd_4606292 := by
    simpa [prefixWord, tailWord_4606292, baseEnd_4606292] using wordTrace_append hprefix tailTrace_4606292
  have hstable : (prefixWord ++ tailWord_4606292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606292).length < 2 ^ (prefixWord ++ tailWord_4606292).sum := by decide
  have hdescent : baseEnd_4606292 < baseStart_4606292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606321 : List Nat := [1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 4]
def baseStart_4606321 : Nat := 118140960795 + 4606321 * 2 ^ 59
def prefixEnd_4606321 : Nat := 4983230072969 + 3 ^ 40 * 4606321 * 2
def baseEnd_4606321 : Nat := 2365256721899177481603421

theorem tailTrace_4606321 : CollatzResearch.WordTrace tailWord_4606321 prefixEnd_4606321 2365256721899177481603421 := by
  unfold tailWord_4606321
  simp only [CollatzResearch.WordTrace]
  refine ⟨168006329145093188839762817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112004219430062125893175211 168006329145093188839762817)
  ·
    refine ⟨126004746858819891629822113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168006329145093188839762817 126004746858819891629822113)
    ·
      refine ⟨94503560144114918722366585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126004746858819891629822113 94503560144114918722366585)
      ·
        refine ⟨70877670108086189041774939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94503560144114918722366585 70877670108086189041774939)
        ·
          refine ⟨106316505162129283562662409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70877670108086189041774939 106316505162129283562662409)
          ·
            refine ⟨79737378871596962671996807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106316505162129283562662409 79737378871596962671996807)
            ·
              refine ⟨119606068307395444007995211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79737378871596962671996807 119606068307395444007995211)
              ·
                refine ⟨179409102461093166011992817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119606068307395444007995211 179409102461093166011992817)
                ·
                  refine ⟨134556826845819874508994613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 179409102461093166011992817 134556826845819874508994613)
                  ·
                    refine ⟨12614702516795613235218245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 134556826845819874508994613 12614702516795613235218245)
                    ·
                      refine ⟨2365256721899177481603421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12614702516795613235218245 2365256721899177481603421)
                      ·
                        rfl

theorem cell23_4606321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_4606321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606321 prefixEnd_4606321 := by exact prefixLift 4606321
  have htrace : WordTrace (prefixWord ++ tailWord_4606321) baseStart_4606321 baseEnd_4606321 := by
    simpa [prefixWord, tailWord_4606321, baseEnd_4606321] using wordTrace_append hprefix tailTrace_4606321
  have hstable : (prefixWord ++ tailWord_4606321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606321).length < 2 ^ (prefixWord ++ tailWord_4606321).sum := by decide
  have hdescent : baseEnd_4606321 < baseStart_4606321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606348 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 1, 6]
def baseStart_4606348 : Nat := 118140960795 + 4606348 * 2 ^ 59
def prefixEnd_4606348 : Nat := 4983230072969 + 3 ^ 40 * 4606348 * 2
def baseEnd_4606348 : Nat := 788423528625616291988599

theorem tailTrace_4606348 : CollatzResearch.WordTrace tailWord_4606348 prefixEnd_4606348 788423528625616291988599 := by
  unfold tailWord_4606348
  simp only [CollatzResearch.WordTrace]
  refine ⟨84003656957997686225497849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112004875943996914967330465 84003656957997686225497849)
  ·
    refine ⟨63002742718498264669123387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84003656957997686225497849 63002742718498264669123387)
    ·
      refine ⟨94504114077747397003685081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63002742718498264669123387 94504114077747397003685081)
      ·
        refine ⟨70878085558310547752763811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94504114077747397003685081 70878085558310547752763811)
        ·
          refine ⟨106317128337465821629145717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70878085558310547752763811 106317128337465821629145717)
          ·
            refine ⟨9967230781637420777732411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 106317128337465821629145717 9967230781637420777732411)
            ·
              refine ⟨14950846172456131166598617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9967230781637420777732411 14950846172456131166598617)
              ·
                refine ⟨11213134629342098374948963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14950846172456131166598617 11213134629342098374948963)
                ·
                  refine ⟨16819701944013147562423445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11213134629342098374948963 16819701944013147562423445)
                  ·
                    refine ⟨788423528625616291988599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16819701944013147562423445 788423528625616291988599)
                    ·
                      rfl

theorem cell23_4606348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 6].length) (baseStart_4606348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606348 prefixEnd_4606348 := by exact prefixLift 4606348
  have htrace : WordTrace (prefixWord ++ tailWord_4606348) baseStart_4606348 baseEnd_4606348 := by
    simpa [prefixWord, tailWord_4606348, baseEnd_4606348] using wordTrace_append hprefix tailTrace_4606348
  have hstable : (prefixWord ++ tailWord_4606348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606348).length < 2 ^ (prefixWord ++ tailWord_4606348).sum := by decide
  have hdescent : baseEnd_4606348 < baseStart_4606348 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606366 : List Nat := [4, 3, 1, 2, 1, 2, 1, 4, 1, 1, 3]
def baseStart_4606366 : Nat := 118140960795 + 4606366 * 2 ^ 59
def prefixEnd_4606366 : Nat := 4983230072969 + 3 ^ 40 * 4606366 * 2
def baseEnd_4606366 : Nat := 2365279828528629805540715

theorem tailTrace_4606366 : CollatzResearch.WordTrace tailWord_4606366 prefixEnd_4606366 2365279828528629805540715 := by
  unfold tailWord_4606366
  simp only [CollatzResearch.WordTrace]
  refine ⟨21000996303741270190643869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112005313619953441016767301 21000996303741270190643869)
  ·
    refine ⟨7875373613902976321491451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 21000996303741270190643869 7875373613902976321491451)
    ·
      refine ⟨11813060420854464482237177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7875373613902976321491451 11813060420854464482237177)
      ·
        refine ⟨8859795315640848361677883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11813060420854464482237177 8859795315640848361677883)
        ·
          refine ⟨13289692973461272542516825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8859795315640848361677883 13289692973461272542516825)
          ·
            refine ⟨9967269730095954406887619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13289692973461272542516825 9967269730095954406887619)
            ·
              refine ⟨14950904595143931610331429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9967269730095954406887619 14950904595143931610331429)
              ·
                refine ⟨2803294611589487176937143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14950904595143931610331429 2803294611589487176937143)
                ·
                  refine ⟨4204941917384230765405715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803294611589487176937143 4204941917384230765405715)
                  ·
                    refine ⟨6307412876076346148108573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4204941917384230765405715 6307412876076346148108573)
                    ·
                      refine ⟨2365279828528629805540715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307412876076346148108573 2365279828528629805540715)
                      ·
                        rfl

theorem cell23_4606366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_4606366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606366 prefixEnd_4606366 := by exact prefixLift 4606366
  have htrace : WordTrace (prefixWord ++ tailWord_4606366) baseStart_4606366 baseEnd_4606366 := by
    simpa [prefixWord, tailWord_4606366, baseEnd_4606366] using wordTrace_append hprefix tailTrace_4606366
  have hstable : (prefixWord ++ tailWord_4606366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606366).length < 2 ^ (prefixWord ++ tailWord_4606366).sum := by decide
  have hdescent : baseEnd_4606366 < baseStart_4606366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606375 : List Nat := [1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 3]
def baseStart_4606375 : Nat := 118140960795 + 4606375 * 2 ^ 59
def prefixEnd_4606375 : Nat := 4983230072969 + 3 ^ 40 * 4606375 * 2
def baseEnd_4606375 : Nat := 2365284449854520270328173

theorem tailTrace_4606375 : CollatzResearch.WordTrace tailWord_4606375 prefixEnd_4606375 2365284449854520270328173 := by
  unfold tailWord_4606375
  simp only [CollatzResearch.WordTrace]
  refine ⟨168008298686897556062228579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112005532457931704041485719 168008298686897556062228579)
  ·
    refine ⟨252012448030346334093342869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168008298686897556062228579 252012448030346334093342869)
    ·
      refine ⟨11813083501422484410625447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 252012448030346334093342869 11813083501422484410625447)
      ·
        refine ⟨17719625252133726615938171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11813083501422484410625447 17719625252133726615938171)
        ·
          refine ⟨26579437878200589923907257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17719625252133726615938171 26579437878200589923907257)
          ·
            refine ⟨19934578408650442442930443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26579437878200589923907257 19934578408650442442930443)
            ·
              refine ⟨29901867612975663664395665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19934578408650442442930443 29901867612975663664395665)
              ·
                refine ⟨22426400709731747748296749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29901867612975663664395665 22426400709731747748296749)
                ·
                  refine ⟨8409900266149405405611281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22426400709731747748296749 8409900266149405405611281)
                  ·
                    refine ⟨6307425199612054054208461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8409900266149405405611281 6307425199612054054208461)
                    ·
                      refine ⟨2365284449854520270328173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307425199612054054208461 2365284449854520270328173)
                      ·
                        rfl

theorem cell23_4606375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 2, 1, 2, 3, 2, 3].length) (baseStart_4606375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606375 prefixEnd_4606375 := by exact prefixLift 4606375
  have htrace : WordTrace (prefixWord ++ tailWord_4606375) baseStart_4606375 baseEnd_4606375 := by
    simpa [prefixWord, tailWord_4606375, baseEnd_4606375] using wordTrace_append hprefix tailTrace_4606375
  have hstable : (prefixWord ++ tailWord_4606375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606375).length < 2 ^ (prefixWord ++ tailWord_4606375).sum := by decide
  have hdescent : baseEnd_4606375 < baseStart_4606375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606385 : List Nat := [1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 4]
def baseStart_4606385 : Nat := 118140960795 + 4606385 * 2 ^ 59
def prefixEnd_4606385 : Nat := 4983230072969 + 3 ^ 40 * 4606385 * 2
def baseEnd_4606385 : Nat := 2365289584661065231203127

theorem tailTrace_4606385 : CollatzResearch.WordTrace tailWord_4606385 prefixEnd_4606385 2365289584661065231203127 := by
  unfold tailWord_4606385
  simp only [CollatzResearch.WordTrace]
  refine ⟨168008663416861327770092609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112005775611240885180061739 168008663416861327770092609)
  ·
    refine ⟨126006497562645995827569457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168008663416861327770092609 126006497562645995827569457)
    ·
      refine ⟨94504873171984496870677093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 126006497562645995827569457 94504873171984496870677093)
      ·
        refine ⟨17719663719747093163251955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 94504873171984496870677093 17719663719747093163251955)
        ·
          refine ⟨26579495579620639744877933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17719663719747093163251955 26579495579620639744877933)
          ·
            refine ⟨9967310842357739904329225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26579495579620639744877933 9967310842357739904329225)
            ·
              refine ⟨7475483131768304928246919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9967310842357739904329225 7475483131768304928246919)
              ·
                refine ⟨11213224697652457392370379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7475483131768304928246919 11213224697652457392370379)
                ·
                  refine ⟨16819837046478686088555569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11213224697652457392370379 16819837046478686088555569)
                  ·
                    refine ⟨12614877784859014566416677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16819837046478686088555569 12614877784859014566416677)
                    ·
                      refine ⟨2365289584661065231203127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12614877784859014566416677 2365289584661065231203127)
                      ·
                        rfl

theorem cell23_4606385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_4606385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606385 prefixEnd_4606385 := by exact prefixLift 4606385
  have htrace : WordTrace (prefixWord ++ tailWord_4606385) baseStart_4606385 baseEnd_4606385 := by
    simpa [prefixWord, tailWord_4606385, baseEnd_4606385] using wordTrace_append hprefix tailTrace_4606385
  have hstable : (prefixWord ++ tailWord_4606385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606385).length < 2 ^ (prefixWord ++ tailWord_4606385).sum := by decide
  have hdescent : baseEnd_4606385 < baseStart_4606385 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606389 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 3, 2, 2]
def baseStart_4606389 : Nat := 118140960795 + 4606389 * 2 ^ 59
def prefixEnd_4606389 : Nat := 4983230072969 + 3 ^ 40 * 4606389 * 2
def baseEnd_4606389 : Nat := 2365291638583683215553109

theorem tailTrace_4606389 : CollatzResearch.WordTrace tailWord_4606389 prefixEnd_4606389 2365291638583683215553109 := by
  unfold tailWord_4606389
  simp only [CollatzResearch.WordTrace]
  refine ⟨168008809308846836453238221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112005872872564557635492147 168008809308846836453238221)
  ·
    refine ⟨63003303490817563669964333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168008809308846836453238221 63003303490817563669964333)
    ·
      refine ⟨23626238809056586376236625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63003303490817563669964333 23626238809056586376236625)
      ·
        refine ⟨17719679106792439782177469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23626238809056586376236625 17719679106792439782177469)
        ·
          refine ⟨6644879665047164918316551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17719679106792439782177469 6644879665047164918316551)
          ·
            refine ⟨9967319497570747377474827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6644879665047164918316551 9967319497570747377474827)
            ·
              refine ⟨14950979246356121066212241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9967319497570747377474827 14950979246356121066212241)
              ·
                refine ⟨11213234434767090799659181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14950979246356121066212241 11213234434767090799659181)
                ·
                  refine ⟨4204962913037659049872193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11213234434767090799659181 4204962913037659049872193)
                  ·
                    refine ⟨3153722184778244287404145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4204962913037659049872193 3153722184778244287404145)
                    ·
                      refine ⟨2365291638583683215553109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153722184778244287404145 2365291638583683215553109)
                      ·
                        rfl

theorem cell23_4606389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_4606389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606389 prefixEnd_4606389 := by exact prefixLift 4606389
  have htrace : WordTrace (prefixWord ++ tailWord_4606389) baseStart_4606389 baseEnd_4606389 := by
    simpa [prefixWord, tailWord_4606389, baseEnd_4606389] using wordTrace_append hprefix tailTrace_4606389
  have hstable : (prefixWord ++ tailWord_4606389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606389).length < 2 ^ (prefixWord ++ tailWord_4606389).sum := by decide
  have hdescent : baseEnd_4606389 < baseStart_4606389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606439 : List Nat := [1, 1, 5, 2, 1, 1, 5, 1, 2, 1, 3]
def baseStart_4606439 : Nat := 118140960795 + 4606439 * 2 ^ 59
def prefixEnd_4606439 : Nat := 4983230072969 + 3 ^ 40 * 4606439 * 2
def baseEnd_4606439 : Nat := 2365317312616408019927879

theorem tailTrace_4606439 : CollatzResearch.WordTrace tailWord_4606439 prefixEnd_4606439 2365317312616408019927879 := by
  unfold tailWord_4606439
  simp only [CollatzResearch.WordTrace]
  refine ⟨168010632958665694992558371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112007088639110463328372247 168010632958665694992558371)
  ·
    refine ⟨252015949437998542488837557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168010632958665694992558371 252015949437998542488837557)
    ·
      refine ⟨23626495259812363358328521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 252015949437998542488837557 23626495259812363358328521)
      ·
        refine ⟨17719871444859272518746391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23626495259812363358328521 17719871444859272518746391)
        ·
          refine ⟨26579807167288908778119587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17719871444859272518746391 26579807167288908778119587)
          ·
            refine ⟨39869710750933363167179381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26579807167288908778119587 39869710750933363167179381)
            ·
              refine ⟨3737785382900002796923067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39869710750933363167179381 3737785382900002796923067)
              ·
                refine ⟨5606678074350004195384601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3737785382900002796923067 5606678074350004195384601)
                ·
                  refine ⟨4205008555762503146538451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5606678074350004195384601 4205008555762503146538451)
                  ·
                    refine ⟨6307512833643754719807677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4205008555762503146538451 6307512833643754719807677)
                    ·
                      refine ⟨2365317312616408019927879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307512833643754719807677 2365317312616408019927879)
                      ·
                        rfl

theorem cell23_4606439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 5, 1, 2, 1, 3].length) (baseStart_4606439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606439 prefixEnd_4606439 := by exact prefixLift 4606439
  have htrace : WordTrace (prefixWord ++ tailWord_4606439) baseStart_4606439 baseEnd_4606439 := by
    simpa [prefixWord, tailWord_4606439, baseEnd_4606439] using wordTrace_append hprefix tailTrace_4606439
  have hstable : (prefixWord ++ tailWord_4606439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606439).length < 2 ^ (prefixWord ++ tailWord_4606439).sum := by decide
  have hdescent : baseEnd_4606439 < baseStart_4606439 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606448 : List Nat := [2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_4606448 : Nat := 118140960795 + 4606448 * 2 ^ 59
def prefixEnd_4606448 : Nat := 4983230072969 + 3 ^ 40 * 4606448 * 2
def baseEnd_4606448 : Nat := 2365321933942298484715337

theorem tailTrace_4606448 : CollatzResearch.WordTrace tailWord_4606448 prefixEnd_4606448 2365321933942298484715337 := by
  unfold tailWord_4606448
  simp only [CollatzResearch.WordTrace]
  refine ⟨84005480607816544764817999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112007307477088726353090665 84005480607816544764817999)
  ·
    refine ⟨126008220911724817147226999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84005480607816544764817999 126008220911724817147226999)
    ·
      refine ⟨189012331367587225720840499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126008220911724817147226999 189012331367587225720840499)
      ·
        refine ⟨283518497051380838581260749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189012331367587225720840499 283518497051380838581260749)
        ·
          refine ⟨106319436394267814467972781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 283518497051380838581260749 106319436394267814467972781)
          ·
            refine ⟨39869788647850430425489793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106319436394267814467972781 39869788647850430425489793)
            ·
              refine ⟨29902341485887822819117345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39869788647850430425489793 29902341485887822819117345)
              ·
                refine ⟨22426756114415867114338009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29902341485887822819117345 22426756114415867114338009)
                ·
                  refine ⟨16820067085811900335753507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22426756114415867114338009 16820067085811900335753507)
                  ·
                    refine ⟨25230100628717850503630261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16820067085811900335753507 25230100628717850503630261)
                    ·
                      refine ⟨2365321933942298484715337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25230100628717850503630261 2365321933942298484715337)
                      ·
                        rfl

theorem cell23_4606448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_4606448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606448 prefixEnd_4606448 := by exact prefixLift 4606448
  have htrace : WordTrace (prefixWord ++ tailWord_4606448) baseStart_4606448 baseEnd_4606448 := by
    simpa [prefixWord, tailWord_4606448, baseEnd_4606448] using wordTrace_append hprefix tailTrace_4606448
  have hstable : (prefixWord ++ tailWord_4606448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606448).length < 2 ^ (prefixWord ++ tailWord_4606448).sum := by decide
  have hdescent : baseEnd_4606448 < baseStart_4606448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606458 : List Nat := [3, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4]
def baseStart_4606458 : Nat := 118140960795 + 4606458 * 2 ^ 59
def prefixEnd_4606458 : Nat := 4983230072969 + 3 ^ 40 * 4606458 * 2
def baseEnd_4606458 : Nat := 2365327068748843445590291

theorem tailTrace_4606458 : CollatzResearch.WordTrace tailWord_4606458 prefixEnd_4606458 2365327068748843445590291 := by
  unfold tailWord_4606458
  simp only [CollatzResearch.WordTrace]
  refine ⟨42002831486399215309375007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112007550630397907491666685 42002831486399215309375007)
  ·
    refine ⟨63004247229598822964062511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42002831486399215309375007 63004247229598822964062511)
    ·
      refine ⟨94506370844398234446093767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63004247229598822964062511 94506370844398234446093767)
      ·
        refine ⟨141759556266597351669140651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94506370844398234446093767 141759556266597351669140651)
        ·
          refine ⟨212639334399896027503710977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141759556266597351669140651 212639334399896027503710977)
          ·
            refine ⟨159479500799922020627783233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212639334399896027503710977 159479500799922020627783233)
            ·
              refine ⟨119609625599941515470837425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 159479500799922020627783233 119609625599941515470837425)
              ·
                refine ⟨89707219199956136603128069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119609625599941515470837425 89707219199956136603128069)
                ·
                  refine ⟨16820103599991775613086513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89707219199956136603128069 16820103599991775613086513)
                  ·
                    refine ⟨12615077699993831709814885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16820103599991775613086513 12615077699993831709814885)
                    ·
                      refine ⟨2365327068748843445590291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12615077699993831709814885 2365327068748843445590291)
                      ·
                        rfl

theorem cell23_4606458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 2, 2, 4, 2, 4].length) (baseStart_4606458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606458 prefixEnd_4606458 := by exact prefixLift 4606458
  have htrace : WordTrace (prefixWord ++ tailWord_4606458) baseStart_4606458 baseEnd_4606458 := by
    simpa [prefixWord, tailWord_4606458, baseEnd_4606458] using wordTrace_append hprefix tailTrace_4606458
  have hstable : (prefixWord ++ tailWord_4606458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606458).length < 2 ^ (prefixWord ++ tailWord_4606458).sum := by decide
  have hdescent : baseEnd_4606458 < baseStart_4606458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606465 : List Nat := [1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 5]
def baseStart_4606465 : Nat := 118140960795 + 4606465 * 2 ^ 59
def prefixEnd_4606465 : Nat := 4983230072969 + 3 ^ 40 * 4606465 * 2
def baseEnd_4606465 : Nat := 2365330663113424918202759

theorem tailTrace_4606465 : CollatzResearch.WordTrace tailWord_4606465 prefixEnd_4606465 2365330663113424918202759 := by
  unfold tailWord_4606465
  simp only [CollatzResearch.WordTrace]
  refine ⟨168011581256571501433004849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112007720837714334288669899 168011581256571501433004849)
  ·
    refine ⟨126008685942428626074753637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168011581256571501433004849 126008685942428626074753637)
    ·
      refine ⟨23626628614205367389016307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126008685942428626074753637 23626628614205367389016307)
      ·
        refine ⟨35439942921308051083524461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23626628614205367389016307 35439942921308051083524461)
        ·
          refine ⟨13289978595490519156321673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35439942921308051083524461 13289978595490519156321673)
          ·
            refine ⟨9967483946617889367241255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13289978595490519156321673 9967483946617889367241255)
            ·
              refine ⟨14951225919926834050861883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9967483946617889367241255 14951225919926834050861883)
              ·
                refine ⟨22426838879890251076292825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14951225919926834050861883 22426838879890251076292825)
                ·
                  refine ⟨16820129159917688307219619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22426838879890251076292825 16820129159917688307219619)
                  ·
                    refine ⟨25230193739876532460829429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16820129159917688307219619 25230193739876532460829429)
                    ·
                      refine ⟨2365330663113424918202759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25230193739876532460829429 2365330663113424918202759)
                      ·
                        rfl

theorem cell23_4606465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_4606465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606465 prefixEnd_4606465 := by exact prefixLift 4606465
  have htrace : WordTrace (prefixWord ++ tailWord_4606465) baseStart_4606465 baseEnd_4606465 := by
    simpa [prefixWord, tailWord_4606465, baseEnd_4606465] using wordTrace_append hprefix tailTrace_4606465
  have hstable : (prefixWord ++ tailWord_4606465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606465).length < 2 ^ (prefixWord ++ tailWord_4606465).sum := by decide
  have hdescent : baseEnd_4606465 < baseStart_4606465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606496 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 2, 2, 2]
def baseStart_4606496 : Nat := 118140960795 + 4606496 * 2 ^ 59
def prefixEnd_4606496 : Nat := 4983230072969 + 3 ^ 40 * 4606496 * 2
def baseEnd_4606496 : Nat := 2365346581013714296915117

theorem tailTrace_4606496 : CollatzResearch.WordTrace tailWord_4606496 prefixEnd_4606496 2365346581013714296915117 := by
  unfold tailWord_4606496
  simp only [CollatzResearch.WordTrace]
  refine ⟨84006355959729596863691671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112008474612972795818255561 84006355959729596863691671)
  ·
    refine ⟨126009533939594395295537507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84006355959729596863691671 126009533939594395295537507)
    ·
      refine ⟨189014300909391592943306261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126009533939594395295537507 189014300909391592943306261)
      ·
        refine ⟨8860045355127730919217481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 189014300909391592943306261 8860045355127730919217481)
        ·
          refine ⟨6645034016345798189413111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8860045355127730919217481 6645034016345798189413111)
          ·
            refine ⟨9967551024518697284119667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6645034016345798189413111 9967551024518697284119667)
            ·
              refine ⟨14951326536778045926179501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9967551024518697284119667 14951326536778045926179501)
              ·
                refine ⟨5606747451291767222317313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14951326536778045926179501 5606747451291767222317313)
                ·
                  refine ⟨4205060588468825416737985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5606747451291767222317313 4205060588468825416737985)
                  ·
                    refine ⟨3153795441351619062553489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4205060588468825416737985 3153795441351619062553489)
                    ·
                      refine ⟨2365346581013714296915117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3153795441351619062553489 2365346581013714296915117)
                      ·
                        rfl

theorem cell23_4606496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_4606496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606496 prefixEnd_4606496 := by exact prefixLift 4606496
  have htrace : WordTrace (prefixWord ++ tailWord_4606496) baseStart_4606496 baseEnd_4606496 := by
    simpa [prefixWord, tailWord_4606496, baseEnd_4606496] using wordTrace_append hprefix tailTrace_4606496
  have hstable : (prefixWord ++ tailWord_4606496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606496).length < 2 ^ (prefixWord ++ tailWord_4606496).sum := by decide
  have hdescent : baseEnd_4606496 < baseStart_4606496 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606515 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 2, 5]
def baseStart_4606515 : Nat := 118140960795 + 4606515 * 2 ^ 59
def prefixEnd_4606515 : Nat := 4983230072969 + 3 ^ 40 * 4606515 * 2
def baseEnd_4606515 : Nat := 788452112382049907525843

theorem tailTrace_4606515 : CollatzResearch.WordTrace tailWord_4606515 prefixEnd_4606515 788452112382049907525843 := by
  unfold tailWord_4606515
  simp only [CollatzResearch.WordTrace]
  refine ⟨168013404906390359972324999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112008936604260239981549999 168013404906390359972324999)
  ·
    refine ⟨252020107359585539958487499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168013404906390359972324999 252020107359585539958487499)
    ·
      refine ⟨378030161039378309937731249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252020107359585539958487499 378030161039378309937731249)
      ·
        refine ⟨283522620779533732453298437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378030161039378309937731249 283522620779533732453298437)
        ·
          refine ⟨53160491396162574834993457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283522620779533732453298437 53160491396162574834993457)
          ·
            refine ⟨39870368547121931126245093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53160491396162574834993457 39870368547121931126245093)
            ·
              refine ⟨7475694102585362086170955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39870368547121931126245093 7475694102585362086170955)
              ·
                refine ⟨11213541153878043129256433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7475694102585362086170955 11213541153878043129256433)
                ·
                  refine ⟨8410155865408532346942325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11213541153878043129256433 8410155865408532346942325)
                  ·
                    refine ⟨788452112382049907525843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8410155865408532346942325 788452112382049907525843)
                    ·
                      rfl

theorem cell23_4606515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 5].length) (baseStart_4606515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606515 prefixEnd_4606515 := by exact prefixLift 4606515
  have htrace : WordTrace (prefixWord ++ tailWord_4606515) baseStart_4606515 baseEnd_4606515 := by
    simpa [prefixWord, tailWord_4606515, baseEnd_4606515] using wordTrace_append hprefix tailTrace_4606515
  have hstable : (prefixWord ++ tailWord_4606515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606515).length < 2 ^ (prefixWord ++ tailWord_4606515).sum := by decide
  have hdescent : baseEnd_4606515 < baseStart_4606515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606525 : List Nat := [1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4606525 : Nat := 118140960795 + 4606525 * 2 ^ 59
def prefixEnd_4606525 : Nat := 4983230072969 + 3 ^ 40 * 4606525 * 2
def baseEnd_4606525 : Nat := 2365361471952694683452483

theorem tailTrace_4606525 : CollatzResearch.WordTrace tailWord_4606525 prefixEnd_4606525 2365361471952694683452483 := by
  unfold tailWord_4606525
  simp only [CollatzResearch.WordTrace]
  refine ⟨168013769636354131680189029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112009179757569421120126019 168013769636354131680189029)
  ·
    refine ⟨31502581806816399690035443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168013769636354131680189029 31502581806816399690035443)
    ·
      refine ⟨47253872710224599535053165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31502581806816399690035443 47253872710224599535053165)
      ·
        refine ⟨17720202266334224825644937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47253872710224599535053165 17720202266334224825644937)
        ·
          refine ⟨13290151699750668619233703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17720202266334224825644937 13290151699750668619233703)
          ·
            refine ⟨19935227549626002928850555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13290151699750668619233703 19935227549626002928850555)
            ·
              refine ⟨29902841324439004393275833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19935227549626002928850555 29902841324439004393275833)
              ·
                refine ⟨22427130993329253294956875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29902841324439004393275833 22427130993329253294956875)
                ·
                  refine ⟨33640696489993879942435313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22427130993329253294956875 33640696489993879942435313)
                  ·
                    refine ⟨25230522367495409956826485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33640696489993879942435313 25230522367495409956826485)
                    ·
                      refine ⟨2365361471952694683452483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25230522367495409956826485 2365361471952694683452483)
                      ·
                        rfl

theorem cell23_4606525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4606525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606525 prefixEnd_4606525 := by exact prefixLift 4606525
  have htrace : WordTrace (prefixWord ++ tailWord_4606525) baseStart_4606525 baseEnd_4606525 := by
    simpa [prefixWord, tailWord_4606525, baseEnd_4606525] using wordTrace_append hprefix tailTrace_4606525
  have hstable : (prefixWord ++ tailWord_4606525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606525).length < 2 ^ (prefixWord ++ tailWord_4606525).sum := by decide
  have hdescent : baseEnd_4606525 < baseStart_4606525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606572 : List Nat := [2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 3]
def baseStart_4606572 : Nat := 118140960795 + 4606572 * 2 ^ 59
def prefixEnd_4606572 : Nat := 4983230072969 + 3 ^ 40 * 4606572 * 2
def baseEnd_4606572 : Nat := 2365385605543455999564767

theorem tailTrace_4606572 : CollatzResearch.WordTrace tailWord_4606572 prefixEnd_4606572 2365385605543455999564767 := by
  unfold tailWord_4606572
  simp only [CollatzResearch.WordTrace]
  refine ⟨84007741933591929353574985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112010322578122572471433313 84007741933591929353574985)
  ·
    refine ⟨63005806450193947015181239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84007741933591929353574985 63005806450193947015181239)
    ·
      refine ⟨94508709675290920522771859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63005806450193947015181239 94508709675290920522771859)
      ·
        refine ⟨141763064512936380784157789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94508709675290920522771859 141763064512936380784157789)
        ·
          refine ⟨53161149192351142794059171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141763064512936380784157789 53161149192351142794059171)
          ·
            refine ⟨79741723788526714191088757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53161149192351142794059171 79741723788526714191088757)
            ·
              refine ⟨7475786605174379455414571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79741723788526714191088757 7475786605174379455414571)
              ·
                refine ⟨11213679907761569183121857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7475786605174379455414571 11213679907761569183121857)
                ·
                  refine ⟨8410259930821176887341393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11213679907761569183121857 8410259930821176887341393)
                  ·
                    refine ⟨6307694948115882665506045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8410259930821176887341393 6307694948115882665506045)
                    ·
                      refine ⟨2365385605543455999564767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307694948115882665506045 2365385605543455999564767)
                      ·
                        rfl

theorem cell23_4606572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 2, 2, 3].length) (baseStart_4606572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606572 prefixEnd_4606572 := by exact prefixLift 4606572
  have htrace : WordTrace (prefixWord ++ tailWord_4606572) baseStart_4606572 baseEnd_4606572 := by
    simpa [prefixWord, tailWord_4606572, baseEnd_4606572] using wordTrace_append hprefix tailTrace_4606572
  have hstable : (prefixWord ++ tailWord_4606572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606572).length < 2 ^ (prefixWord ++ tailWord_4606572).sum := by decide
  have hdescent : baseEnd_4606572 < baseStart_4606572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606592 : List Nat := [2, 1, 1, 2, 1, 7, 1, 2, 6]
def baseStart_4606592 : Nat := 118140960795 + 4606592 * 2 ^ 59
def prefixEnd_4606592 : Nat := 4983230072969 + 3 ^ 40 * 4606592 * 2
def baseEnd_4606592 : Nat := 262821763906282880146075

theorem tailTrace_4606592 : CollatzResearch.WordTrace tailWord_4606592 prefixEnd_4606592 262821763906282880146075 := by
  unfold tailWord_4606592
  simp only [CollatzResearch.WordTrace]
  refine ⟨84008106663555701061439015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112010808884740934748585353 84008106663555701061439015)
  ·
    refine ⟨126012159995333551592158523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84008106663555701061439015 126012159995333551592158523)
    ·
      refine ⟨189018239993000327388237785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126012159995333551592158523 189018239993000327388237785)
      ·
        refine ⟨141763679994750245541178339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189018239993000327388237785 141763679994750245541178339)
        ·
          refine ⟨212645519992125368311767509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141763679994750245541178339 212645519992125368311767509)
          ·
            refine ⟨4983879374815438319807051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 212645519992125368311767509 4983879374815438319807051)
            ·
              refine ⟨7475819062223157479710577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983879374815438319807051 7475819062223157479710577)
              ·
                refine ⟨5606864296667368109782933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7475819062223157479710577 5606864296667368109782933)
                ·
                  refine ⟨262821763906282880146075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5606864296667368109782933 262821763906282880146075)
                  ·
                    rfl

theorem cell23_4606592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 7, 1, 2, 6].length) (baseStart_4606592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606592 prefixEnd_4606592 := by exact prefixLift 4606592
  have htrace : WordTrace (prefixWord ++ tailWord_4606592) baseStart_4606592 baseEnd_4606592 := by
    simpa [prefixWord, tailWord_4606592, baseEnd_4606592] using wordTrace_append hprefix tailTrace_4606592
  have hstable : (prefixWord ++ tailWord_4606592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606592).length < 2 ^ (prefixWord ++ tailWord_4606592).sum := by decide
  have hdescent : baseEnd_4606592 < baseStart_4606592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606652 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 4, 4]
def baseStart_4606652 : Nat := 118140960795 + 4606652 * 2 ^ 59
def prefixEnd_4606652 : Nat := 4983230072969 + 3 ^ 40 * 4606652 * 2
def baseEnd_4606652 : Nat := 788475561331938562188133

theorem tailTrace_4606652 : CollatzResearch.WordTrace tailWord_4606652 prefixEnd_4606652 788475561331938562188133 := by
  unfold tailWord_4606652
  simp only [CollatzResearch.WordTrace]
  refine ⟨84009200853447016185031105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112012267804596021580041473 84009200853447016185031105)
  ·
    refine ⟨63006900640085262138773329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 84009200853447016185031105 63006900640085262138773329)
    ·
      refine ⟨47255175480063946604079997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 63006900640085262138773329 47255175480063946604079997)
      ·
        refine ⟨17720690805023979976529999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47255175480063946604079997 17720690805023979976529999)
        ·
          refine ⟨26581036207535969964794999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17720690805023979976529999 26581036207535969964794999)
          ·
            refine ⟨39871554311303954947192499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26581036207535969964794999 39871554311303954947192499)
            ·
              refine ⟨59807331466955932420788749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39871554311303954947192499 59807331466955932420788749)
              ·
                refine ⟨22427749300108474657795781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59807331466955932420788749 22427749300108474657795781)
                ·
                  refine ⟨4205202993770338998336709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22427749300108474657795781 4205202993770338998336709)
                  ·
                    refine ⟨788475561331938562188133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205202993770338998336709 788475561331938562188133)
                    ·
                      rfl

theorem cell23_4606652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_4606652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606652 prefixEnd_4606652 := by exact prefixLift 4606652
  have htrace : WordTrace (prefixWord ++ tailWord_4606652) baseStart_4606652 baseEnd_4606652 := by
    simpa [prefixWord, tailWord_4606652, baseEnd_4606652] using wordTrace_append hprefix tailTrace_4606652
  have hstable : (prefixWord ++ tailWord_4606652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606652).length < 2 ^ (prefixWord ++ tailWord_4606652).sum := by decide
  have hdescent : baseEnd_4606652 < baseStart_4606652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606653 : List Nat := [1, 4, 1, 2, 1, 4, 3, 2, 1, 1, 3]
def baseStart_4606653 : Nat := 118140960795 + 4606653 * 2 ^ 59
def prefixEnd_4606653 : Nat := 4983230072969 + 3 ^ 40 * 4606653 * 2
def baseEnd_4606653 : Nat := 2365427197476470182651895

theorem tailTrace_4606653 : CollatzResearch.WordTrace tailWord_4606653 prefixEnd_4606653 2365427197476470182651895 := by
  unfold tailWord_4606653
  simp only [CollatzResearch.WordTrace]
  refine ⟨168018438179890409540848613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112012292119926939693899075 168018438179890409540848613)
  ·
    refine ⟨31503457158729451788909115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168018438179890409540848613 31503457158729451788909115)
    ·
      refine ⟨47255185738094177683363673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31503457158729451788909115 47255185738094177683363673)
      ·
        refine ⟨35441389303570633262522755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47255185738094177683363673 35441389303570633262522755)
        ·
          refine ⟨53162083955355949893784133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35441389303570633262522755 53162083955355949893784133)
          ·
            refine ⟨9967890741629240605084525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53162083955355949893784133 9967890741629240605084525)
            ·
              refine ⟨3737959028110965226906697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9967890741629240605084525 3737959028110965226906697)
              ·
                refine ⟨2803469271083223920180023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3737959028110965226906697 2803469271083223920180023)
                ·
                  refine ⟨4205203906624835880270035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803469271083223920180023 4205203906624835880270035)
                  ·
                    refine ⟨6307805859937253820405053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4205203906624835880270035 6307805859937253820405053)
                    ·
                      refine ⟨2365427197476470182651895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307805859937253820405053 2365427197476470182651895)
                      ·
                        rfl

theorem cell23_4606653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 3, 2, 1, 1, 3].length) (baseStart_4606653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606653 prefixEnd_4606653 := by exact prefixLift 4606653
  have htrace : WordTrace (prefixWord ++ tailWord_4606653) baseStart_4606653 baseEnd_4606653 := by
    simpa [prefixWord, tailWord_4606653, baseEnd_4606653] using wordTrace_append hprefix tailTrace_4606653
  have hstable : (prefixWord ++ tailWord_4606653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606653).length < 2 ^ (prefixWord ++ tailWord_4606653).sum := by decide
  have hdescent : baseEnd_4606653 < baseStart_4606653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606655 : List Nat := [1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 6]
def baseStart_4606655 : Nat := 118140960795 + 4606655 * 2 ^ 59
def prefixEnd_4606655 : Nat := 4983230072969 + 3 ^ 40 * 4606655 * 2
def baseEnd_4606655 : Nat := 2365428224437779174826885

theorem tailTrace_4606655 : CollatzResearch.WordTrace tailWord_4606655 prefixEnd_4606655 2365428224437779174826885 := by
  unfold tailWord_4606655
  simp only [CollatzResearch.WordTrace]
  refine ⟨168018511125883163882421419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112012340750588775921614279 168018511125883163882421419)
  ·
    refine ⟨252027766688824745823632129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168018511125883163882421419 252027766688824745823632129)
    ·
      refine ⟨189020825016618559367724097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252027766688824745823632129 189020825016618559367724097)
      ·
        refine ⟨141765618762463919525793073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189020825016618559367724097 141765618762463919525793073)
        ·
          refine ⟨106324214071847939644344805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141765618762463919525793073 106324214071847939644344805)
          ·
            refine ⟨19935790138471488683314651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106324214071847939644344805 19935790138471488683314651)
            ·
              refine ⟨29903685207707233024971977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19935790138471488683314651 29903685207707233024971977)
              ·
                refine ⟨22427763905780424768728983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29903685207707233024971977 22427763905780424768728983)
                ·
                  refine ⟨33641645858670637153093475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22427763905780424768728983 33641645858670637153093475)
                  ·
                    refine ⟨50462468788005955729640213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33641645858670637153093475 50462468788005955729640213)
                    ·
                      refine ⟨2365428224437779174826885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50462468788005955729640213 2365428224437779174826885)
                      ·
                        rfl

theorem cell23_4606655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 6].length) (baseStart_4606655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606655 prefixEnd_4606655 := by exact prefixLift 4606655
  have htrace : WordTrace (prefixWord ++ tailWord_4606655) baseStart_4606655 baseEnd_4606655 := by
    simpa [prefixWord, tailWord_4606655, baseEnd_4606655] using wordTrace_append hprefix tailTrace_4606655
  have hstable : (prefixWord ++ tailWord_4606655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606655).length < 2 ^ (prefixWord ++ tailWord_4606655).sum := by decide
  have hdescent : baseEnd_4606655 < baseStart_4606655 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606675 : List Nat := [1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 3]
def baseStart_4606675 : Nat := 118140960795 + 4606675 * 2 ^ 59
def prefixEnd_4606675 : Nat := 4983230072969 + 3 ^ 40 * 4606675 * 2
def baseEnd_4606675 : Nat := 2365438494050869096576793

theorem tailTrace_4606675 : CollatzResearch.WordTrace tailWord_4606675 prefixEnd_4606675 2365438494050869096576793 := by
  unfold tailWord_4606675
  simp only [CollatzResearch.WordTrace]
  refine ⟨168019240585810707298149479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112012827057207138198766319 168019240585810707298149479)
  ·
    refine ⟨252028860878716060947224219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168019240585810707298149479 252028860878716060947224219)
    ·
      refine ⟨378043291318074091420836329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252028860878716060947224219 378043291318074091420836329)
      ·
        refine ⟨283532468488555568565627247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 378043291318074091420836329 283532468488555568565627247)
        ·
          refine ⟨425298702732833352848440871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 283532468488555568565627247 425298702732833352848440871)
          ·
            refine ⟨637948054099250029272661307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 425298702732833352848440871 637948054099250029272661307)
            ·
              refine ⟨956922081148875043908991961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 637948054099250029272661307 956922081148875043908991961)
              ·
                refine ⟨717691560861656282931743971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 956922081148875043908991961 717691560861656282931743971)
                ·
                  refine ⟨1076537341292484424397615957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 717691560861656282931743971 1076537341292484424397615957)
                  ·
                    refine ⟨6307835984135650924204781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1076537341292484424397615957 6307835984135650924204781)
                    ·
                      refine ⟨2365438494050869096576793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307835984135650924204781 2365438494050869096576793)
                      ·
                        rfl

theorem cell23_4606675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 9, 3].length) (baseStart_4606675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606675 prefixEnd_4606675 := by exact prefixLift 4606675
  have htrace : WordTrace (prefixWord ++ tailWord_4606675) baseStart_4606675 baseEnd_4606675 := by
    simpa [prefixWord, tailWord_4606675, baseEnd_4606675] using wordTrace_append hprefix tailTrace_4606675
  have hstable : (prefixWord ++ tailWord_4606675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606675).length < 2 ^ (prefixWord ++ tailWord_4606675).sum := by decide
  have hdescent : baseEnd_4606675 < baseStart_4606675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606679 : List Nat := [1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 3]
def baseStart_4606679 : Nat := 118140960795 + 4606679 * 2 ^ 59
def prefixEnd_4606679 : Nat := 4983230072969 + 3 ^ 40 * 4606679 * 2
def baseEnd_4606679 : Nat := 2365440547973487080926775

theorem tailTrace_4606679 : CollatzResearch.WordTrace tailWord_4606679 prefixEnd_4606679 2365440547973487080926775 := by
  unfold tailWord_4606679
  simp only [CollatzResearch.WordTrace]
  refine ⟨168019386477796215981295091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112012924318530810654196727 168019386477796215981295091)
  ·
    refine ⟨252029079716694323971942637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168019386477796215981295091 252029079716694323971942637)
    ·
      refine ⟨94510904893760371489478489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252029079716694323971942637 94510904893760371489478489)
      ·
        refine ⟨70883178670320278617108867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94510904893760371489478489 70883178670320278617108867)
        ·
          refine ⟨106324768005480417925663301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70883178670320278617108867 106324768005480417925663301)
          ·
            refine ⟨19935894001027578361061869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106324768005480417925663301 19935894001027578361061869)
            ·
              refine ⟨7475960250385341885398201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19935894001027578361061869 7475960250385341885398201)
              ·
                refine ⟨5606970187789006414048651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7475960250385341885398201 5606970187789006414048651)
                ·
                  refine ⟨8410455281683509621072977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5606970187789006414048651 8410455281683509621072977)
                  ·
                    refine ⟨6307841461262632215804733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8410455281683509621072977 6307841461262632215804733)
                    ·
                      refine ⟨2365440547973487080926775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307841461262632215804733 2365440547973487080926775)
                      ·
                        rfl

theorem cell23_4606679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 3, 2, 1, 2, 3].length) (baseStart_4606679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606679 prefixEnd_4606679 := by exact prefixLift 4606679
  have htrace : WordTrace (prefixWord ++ tailWord_4606679) baseStart_4606679 baseEnd_4606679 := by
    simpa [prefixWord, tailWord_4606679, baseEnd_4606679] using wordTrace_append hprefix tailTrace_4606679
  have hstable : (prefixWord ++ tailWord_4606679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606679).length < 2 ^ (prefixWord ++ tailWord_4606679).sum := by decide
  have hdescent : baseEnd_4606679 < baseStart_4606679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606692 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 3, 3, 3]
def baseStart_4606692 : Nat := 118140960795 + 4606692 * 2 ^ 59
def prefixEnd_4606692 : Nat := 4983230072969 + 3 ^ 40 * 4606692 * 2
def baseEnd_4606692 : Nat := 2365447223221995530064215

theorem tailTrace_4606692 : CollatzResearch.WordTrace tailWord_4606692 prefixEnd_4606692 2365447223221995530064215 := by
  unfold tailWord_4606692
  simp only [CollatzResearch.WordTrace]
  refine ⟨84009930313374559600759165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112013240417832746134345553 84009930313374559600759165)
  ·
    refine ⟨31503723867515459850284687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84009930313374559600759165 31503723867515459850284687)
    ·
      refine ⟨47255585801273189775427031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31503723867515459850284687 47255585801273189775427031)
      ·
        refine ⟨70883378701909784663140547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47255585801273189775427031 70883378701909784663140547)
        ·
          refine ⟨106325068052864676994710821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70883378701909784663140547 106325068052864676994710821)
          ·
            refine ⟨19935950259912126936508279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 106325068052864676994710821 19935950259912126936508279)
            ·
              refine ⟨29903925389868190404762419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19935950259912126936508279 29903925389868190404762419)
              ·
                refine ⟨44855888084802285607143629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29903925389868190404762419 44855888084802285607143629)
                ·
                  refine ⟨16820958031800857102678861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44855888084802285607143629 16820958031800857102678861)
                  ·
                    refine ⟨6307859261925321413504573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16820958031800857102678861 6307859261925321413504573)
                    ·
                      refine ⟨2365447223221995530064215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6307859261925321413504573 2365447223221995530064215)
                      ·
                        rfl

theorem cell23_4606692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 3, 3, 3].length) (baseStart_4606692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606692 prefixEnd_4606692 := by exact prefixLift 4606692
  have htrace : WordTrace (prefixWord ++ tailWord_4606692) baseStart_4606692 baseEnd_4606692 := by
    simpa [prefixWord, tailWord_4606692, baseEnd_4606692] using wordTrace_append hprefix tailTrace_4606692
  have hstable : (prefixWord ++ tailWord_4606692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606692).length < 2 ^ (prefixWord ++ tailWord_4606692).sum := by decide
  have hdescent : baseEnd_4606692 < baseStart_4606692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606696 : List Nat := [2, 1, 4, 1, 5, 1, 1, 1, 1, 1, 5]
def baseStart_4606696 : Nat := 118140960795 + 4606696 * 2 ^ 59
def prefixEnd_4606696 : Nat := 4983230072969 + 3 ^ 40 * 4606696 * 2
def baseEnd_4606696 : Nat := 2365449277144613514414197

theorem tailTrace_4606696 : CollatzResearch.WordTrace tailWord_4606696 prefixEnd_4606696 2365449277144613514414197 := by
  unfold tailWord_4606696
  simp only [CollatzResearch.WordTrace]
  refine ⟨84010003259367313942331971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112013337679156418589775961 84010003259367313942331971)
  ·
    refine ⟨126015004889050970913497957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84010003259367313942331971 126015004889050970913497957)
    ·
      refine ⟨23627813416697057046280867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 126015004889050970913497957 23627813416697057046280867)
      ·
        refine ⟨35441720125045585569421301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23627813416697057046280867 35441720125045585569421301)
        ·
          refine ⟨3322661261723023647133247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35441720125045585569421301 3322661261723023647133247)
          ·
            refine ⟨4983991892584535470699871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3322661261723023647133247 4983991892584535470699871)
            ·
              refine ⟨7475987838876803206049807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4983991892584535470699871 7475987838876803206049807)
              ·
                refine ⟨11213981758315204809074711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7475987838876803206049807 11213981758315204809074711)
                ·
                  refine ⟨16820972637472807213612067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11213981758315204809074711 16820972637472807213612067)
                  ·
                    refine ⟨25231458956209210820418101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16820972637472807213612067 25231458956209210820418101)
                    ·
                      refine ⟨2365449277144613514414197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25231458956209210820418101 2365449277144613514414197)
                      ·
                        rfl

theorem cell23_4606696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 5, 1, 1, 1, 1, 1, 5].length) (baseStart_4606696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606696 prefixEnd_4606696 := by exact prefixLift 4606696
  have htrace : WordTrace (prefixWord ++ tailWord_4606696) baseStart_4606696 baseEnd_4606696 := by
    simpa [prefixWord, tailWord_4606696, baseEnd_4606696] using wordTrace_append hprefix tailTrace_4606696
  have hstable : (prefixWord ++ tailWord_4606696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606696).length < 2 ^ (prefixWord ++ tailWord_4606696).sum := by decide
  have hdescent : baseEnd_4606696 < baseStart_4606696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606755 : List Nat := [1, 1, 1, 4, 2, 1, 1, 1, 11]
def baseStart_4606755 : Nat := 118140960795 + 4606755 * 2 ^ 59
def prefixEnd_4606755 : Nat := 4983230072969 + 3 ^ 40 * 4606755 * 2
def baseEnd_4606755 : Nat := 262831063611469864841825

theorem tailTrace_4606755 : CollatzResearch.WordTrace tailWord_4606755 prefixEnd_4606755 262831063611469864841825 := by
  unfold tailWord_4606755
  simp only [CollatzResearch.WordTrace]
  refine ⟨168022158425520880961061719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112014772283680587307374479 168022158425520880961061719)
  ·
    refine ⟨252033237638281321441592579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168022158425520880961061719 252033237638281321441592579)
    ·
      refine ⟨378049856457421982162388869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252033237638281321441592579 378049856457421982162388869)
      ·
        refine ⟨70884348085766621655447913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 378049856457421982162388869 70884348085766621655447913)
        ·
          refine ⟨53163261064324966241585935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70884348085766621655447913 53163261064324966241585935)
          ·
            refine ⟨79744891596487449362378903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53163261064324966241585935 79744891596487449362378903)
            ·
              refine ⟨119617337394731174043568355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79744891596487449362378903 119617337394731174043568355)
              ·
                refine ⟨179426006092096761065352533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 119617337394731174043568355 179426006092096761065352533)
                ·
                  refine ⟨262831063611469864841825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 179426006092096761065352533 262831063611469864841825)
                  ·
                    rfl

theorem cell23_4606755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 1, 11].length) (baseStart_4606755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606755 prefixEnd_4606755 := by exact prefixLift 4606755
  have htrace : WordTrace (prefixWord ++ tailWord_4606755) baseStart_4606755 baseEnd_4606755 := by
    simpa [prefixWord, tailWord_4606755, baseEnd_4606755] using wordTrace_append hprefix tailTrace_4606755
  have hstable : (prefixWord ++ tailWord_4606755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606755).length < 2 ^ (prefixWord ++ tailWord_4606755).sum := by decide
  have hdescent : baseEnd_4606755 < baseStart_4606755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606802 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 1, 7]
def baseStart_4606802 : Nat := 118140960795 + 4606802 * 2 ^ 59
def prefixEnd_4606802 : Nat := 4983230072969 + 3 ^ 40 * 4606802 * 2
def baseEnd_4606802 : Nat := 788501235364663366562903

theorem tailTrace_4606802 : CollatzResearch.WordTrace tailWord_4606802 prefixEnd_4606802 788501235364663366562903 := by
  unfold tailWord_4606802
  simp only [CollatzResearch.WordTrace]
  refine ⟨42005968164087651997005665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112015915104233738658681773 42005968164087651997005665)
  ·
    refine ⟨31504476123065738997754249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 42005968164087651997005665 31504476123065738997754249)
    ·
      refine ⟨23628357092299304248315687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31504476123065738997754249 23628357092299304248315687)
      ·
        refine ⟨35442535638448956372473531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23628357092299304248315687 35442535638448956372473531)
        ·
          refine ⟨53163803457673434558710297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35442535638448956372473531 53163803457673434558710297)
          ·
            refine ⟨39872852593255075919032723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53163803457673434558710297 39872852593255075919032723)
            ·
              refine ⟨59809278889882613878549085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39872852593255075919032723 59809278889882613878549085)
              ·
                refine ⟨22428479583705980204455907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59809278889882613878549085 22428479583705980204455907)
                ·
                  refine ⟨33642719375558970306683861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22428479583705980204455907 33642719375558970306683861)
                  ·
                    refine ⟨788501235364663366562903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33642719375558970306683861 788501235364663366562903)
                    ·
                      rfl

theorem cell23_4606802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_4606802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606802 prefixEnd_4606802 := by exact prefixLift 4606802
  have htrace : WordTrace (prefixWord ++ tailWord_4606802) baseStart_4606802 baseEnd_4606802 := by
    simpa [prefixWord, tailWord_4606802, baseEnd_4606802] using wordTrace_append hprefix tailTrace_4606802
  have hstable : (prefixWord ++ tailWord_4606802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606802).length < 2 ^ (prefixWord ++ tailWord_4606802).sum := by decide
  have hdescent : baseEnd_4606802 < baseStart_4606802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606819 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 2, 5]
def baseStart_4606819 : Nat := 118140960795 + 4606819 * 2 ^ 59
def prefixEnd_4606819 : Nat := 4983230072969 + 3 ^ 40 * 4606819 * 2
def baseEnd_4606819 : Nat := 788504145088372177725377

theorem tailTrace_4606819 : CollatzResearch.WordTrace tailWord_4606819 prefixEnd_4606819 788504145088372177725377 := by
  unfold tailWord_4606819
  simp only [CollatzResearch.WordTrace]
  refine ⟨168024492697289019891391511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112016328464859346594261007 168024492697289019891391511)
  ·
    refine ⟨252036739045933529837087267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168024492697289019891391511 252036739045933529837087267)
    ·
      refine ⟨378055108568900294755630901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252036739045933529837087267 378055108568900294755630901)
      ·
        refine ⟨35442666428334402633340397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 378055108568900294755630901 35442666428334402633340397)
        ·
          refine ⟨13290999910625400987502649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35442666428334402633340397 13290999910625400987502649)
          ·
            refine ⟨9968249932969050740626987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13290999910625400987502649 9968249932969050740626987)
            ·
              refine ⟨14952374899453576110940481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9968249932969050740626987 14952374899453576110940481)
              ·
                refine ⟨11214281174590182083205361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14952374899453576110940481 11214281174590182083205361)
                ·
                  refine ⟨8410710880942636562404021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11214281174590182083205361 8410710880942636562404021)
                  ·
                    refine ⟨788504145088372177725377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8410710880942636562404021 788504145088372177725377)
                    ·
                      rfl

theorem cell23_4606819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 5].length) (baseStart_4606819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606819 prefixEnd_4606819 := by exact prefixLift 4606819
  have htrace : WordTrace (prefixWord ++ tailWord_4606819) baseStart_4606819 baseEnd_4606819 := by
    simpa [prefixWord, tailWord_4606819, baseEnd_4606819] using wordTrace_append hprefix tailTrace_4606819
  have hstable : (prefixWord ++ tailWord_4606819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606819).length < 2 ^ (prefixWord ++ tailWord_4606819).sum := by decide
  have hdescent : baseEnd_4606819 < baseStart_4606819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606839 : List Nat := [1, 1, 3, 1, 1, 2, 1, 5, 2, 4, 2]
def baseStart_4606839 : Nat := 118140960795 + 4606839 * 2 ^ 59
def prefixEnd_4606839 : Nat := 4983230072969 + 3 ^ 40 * 4606839 * 2
def baseEnd_4606839 : Nat := 2365522704878206454926039

theorem tailTrace_4606839 : CollatzResearch.WordTrace tailWord_4606839 prefixEnd_4606839 2365522704878206454926039 := by
  unfold tailWord_4606839
  simp only [CollatzResearch.WordTrace]
  refine ⟨168025222157216563307119571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112016814771477708871413047 168025222157216563307119571)
  ·
    refine ⟨252037833235824844960679357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168025222157216563307119571 252037833235824844960679357)
    ·
      refine ⟨94514187463434316860254759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 252037833235824844960679357 94514187463434316860254759)
      ·
        refine ⟨141771281195151475290382139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94514187463434316860254759 141771281195151475290382139)
        ·
          refine ⟨212656921792727212935573209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141771281195151475290382139 212656921792727212935573209)
          ·
            refine ⟨159492691344545409701679907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 212656921792727212935573209 159492691344545409701679907)
            ·
              refine ⟨239239037016818114552519861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159492691344545409701679907 239239037016818114552519861)
              ·
                refine ⟨22428659720326698239298737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 239239037016818114552519861 22428659720326698239298737)
                ·
                  refine ⟨16821494790245023679474053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22428659720326698239298737 16821494790245023679474053)
                  ·
                    refine ⟨3154030273170941939901385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16821494790245023679474053 3154030273170941939901385)
                    ·
                      refine ⟨2365522704878206454926039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154030273170941939901385 2365522704878206454926039)
                      ·
                        rfl

theorem cell23_4606839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 5, 2, 4, 2].length) (baseStart_4606839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606839 prefixEnd_4606839 := by exact prefixLift 4606839
  have htrace : WordTrace (prefixWord ++ tailWord_4606839) baseStart_4606839 baseEnd_4606839 := by
    simpa [prefixWord, tailWord_4606839, baseEnd_4606839] using wordTrace_append hprefix tailTrace_4606839
  have hstable : (prefixWord ++ tailWord_4606839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606839).length < 2 ^ (prefixWord ++ tailWord_4606839).sum := by decide
  have hdescent : baseEnd_4606839 < baseStart_4606839 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606852 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4606852 : Nat := 118140960795 + 4606852 * 2 ^ 59
def prefixEnd_4606852 : Nat := 4983230072969 + 3 ^ 40 * 4606852 * 2
def baseEnd_4606852 : Nat := 2365529380126714904063479

theorem tailTrace_4606852 : CollatzResearch.WordTrace tailWord_4606852 prefixEnd_4606852 2365529380126714904063479 := by
  unfold tailWord_4606852
  simp only [CollatzResearch.WordTrace]
  refine ⟨84012848153084733263671405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112017130870779644351561873 84012848153084733263671405)
  ·
    refine ⟨31504818057406774973876777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 84012848153084733263671405 31504818057406774973876777)
    ·
      refine ⟨23628613543055081230407583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31504818057406774973876777 23628613543055081230407583)
      ·
        refine ⟨35442920314582621845611375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23628613543055081230407583 35442920314582621845611375)
        ·
          refine ⟨53164380471873932768417063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35442920314582621845611375 53164380471873932768417063)
          ·
            refine ⟨79746570707810899152625595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53164380471873932768417063 79746570707810899152625595)
            ·
              refine ⟨119619856061716348728938393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79746570707810899152625595 119619856061716348728938393)
              ·
                refine ⟨89714892046287261546703795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119619856061716348728938393 89714892046287261546703795)
                ·
                  refine ⟨134572338069430892320055693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89714892046287261546703795 134572338069430892320055693)
                  ·
                    refine ⟨50464626776036584620020885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 134572338069430892320055693 50464626776036584620020885)
                    ·
                      refine ⟨2365529380126714904063479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50464626776036584620020885 2365529380126714904063479)
                      ·
                        rfl

theorem cell23_4606852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4606852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606852 prefixEnd_4606852 := by exact prefixLift 4606852
  have htrace : WordTrace (prefixWord ++ tailWord_4606852) baseStart_4606852 baseEnd_4606852 := by
    simpa [prefixWord, tailWord_4606852, baseEnd_4606852] using wordTrace_append hprefix tailTrace_4606852
  have hstable : (prefixWord ++ tailWord_4606852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606852).length < 2 ^ (prefixWord ++ tailWord_4606852).sum := by decide
  have hdescent : baseEnd_4606852 < baseStart_4606852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606856 : List Nat := [2, 1, 3, 3, 2, 2, 2, 1, 2, 1, 4]
def baseStart_4606856 : Nat := 118140960795 + 4606856 * 2 ^ 59
def prefixEnd_4606856 : Nat := 4983230072969 + 3 ^ 40 * 4606856 * 2
def baseEnd_4606856 : Nat := 2365531434049332888413461

theorem tailTrace_4606856 : CollatzResearch.WordTrace tailWord_4606856 prefixEnd_4606856 2365531434049332888413461 := by
  unfold tailWord_4606856
  simp only [CollatzResearch.WordTrace]
  refine ⟨84012921099077487605244211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112017228132103316806992281 84012921099077487605244211)
  ·
    refine ⟨126019381648616231407866317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84012921099077487605244211 126019381648616231407866317)
    ·
      refine ⟨47257268118231086777949869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 126019381648616231407866317 47257268118231086777949869)
      ·
        refine ⟨17721475544336657541731201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47257268118231086777949869 17721475544336657541731201)
        ·
          refine ⟨13291106658252493156298401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17721475544336657541731201 13291106658252493156298401)
          ·
            refine ⟨9968329993689369867223801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13291106658252493156298401 9968329993689369867223801)
            ·
              refine ⟨7476247495267027400417851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9968329993689369867223801 7476247495267027400417851)
              ·
                refine ⟨11214371242900541100626777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476247495267027400417851 11214371242900541100626777)
                ·
                  refine ⟨8410778432175405825470083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11214371242900541100626777 8410778432175405825470083)
                  ·
                    refine ⟨12616167648263108738205125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8410778432175405825470083 12616167648263108738205125)
                    ·
                      refine ⟨2365531434049332888413461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12616167648263108738205125 2365531434049332888413461)
                      ·
                        rfl

theorem cell23_4606856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 2, 1, 2, 1, 4].length) (baseStart_4606856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606856 prefixEnd_4606856 := by exact prefixLift 4606856
  have htrace : WordTrace (prefixWord ++ tailWord_4606856) baseStart_4606856 baseEnd_4606856 := by
    simpa [prefixWord, tailWord_4606856, baseEnd_4606856] using wordTrace_append hprefix tailTrace_4606856
  have hstable : (prefixWord ++ tailWord_4606856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606856).length < 2 ^ (prefixWord ++ tailWord_4606856).sum := by decide
  have hdescent : baseEnd_4606856 < baseStart_4606856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606859 : List Nat := [1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 3]
def baseStart_4606859 : Nat := 118140960795 + 4606859 * 2 ^ 59
def prefixEnd_4606859 : Nat := 4983230072969 + 3 ^ 40 * 4606859 * 2
def baseEnd_4606859 : Nat := 2365532974491296376675947

theorem tailTrace_4606859 : CollatzResearch.WordTrace tailWord_4606859 prefixEnd_4606859 2365532974491296376675947 := by
  unfold tailWord_4606859
  simp only [CollatzResearch.WordTrace]
  refine ⟨168025951617144106722847631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112017301078096071148565087 168025951617144106722847631)
  ·
    refine ⟨252038927425716160084271447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168025951617144106722847631 252038927425716160084271447)
    ·
      refine ⟨378058391138574240126407171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252038927425716160084271447 378058391138574240126407171)
      ·
        refine ⟨567087586707861360189610757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378058391138574240126407171 567087586707861360189610757)
        ·
          refine ⟨106328922507724005035552017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 567087586707861360189610757 106328922507724005035552017)
          ·
            refine ⟨79746691880793003776664013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106328922507724005035552017 79746691880793003776664013)
            ·
              refine ⟨29905009455297376416249005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79746691880793003776664013 29905009455297376416249005)
              ·
                refine ⟨11214378545736516156093377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29905009455297376416249005 11214378545736516156093377)
                ·
                  refine ⟨8410783909302387117070033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11214378545736516156093377 8410783909302387117070033)
                  ·
                    refine ⟨6308087931976790337802525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8410783909302387117070033 6308087931976790337802525)
                    ·
                      refine ⟨2365532974491296376675947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6308087931976790337802525 2365532974491296376675947)
                      ·
                        rfl

theorem cell23_4606859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 3, 2, 2, 3].length) (baseStart_4606859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606859 prefixEnd_4606859 := by exact prefixLift 4606859
  have htrace : WordTrace (prefixWord ++ tailWord_4606859) baseStart_4606859 baseEnd_4606859 := by
    simpa [prefixWord, tailWord_4606859, baseEnd_4606859] using wordTrace_append hprefix tailTrace_4606859
  have hstable : (prefixWord ++ tailWord_4606859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606859).length < 2 ^ (prefixWord ++ tailWord_4606859).sum := by decide
  have hdescent : baseEnd_4606859 < baseStart_4606859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606879 : List Nat := [1, 1, 2, 5, 2, 1, 1, 4, 6]
def baseStart_4606879 : Nat := 118140960795 + 4606879 * 2 ^ 59
def prefixEnd_4606879 : Nat := 4983230072969 + 3 ^ 40 * 4606879 * 2
def baseEnd_4606879 : Nat := 262838138233820699825095

theorem tailTrace_4606879 : CollatzResearch.WordTrace tailWord_4606879 prefixEnd_4606879 262838138233820699825095 := by
  unfold tailWord_4606879
  simp only [CollatzResearch.WordTrace]
  refine ⟨168026681077071650138575691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112017787384714433425717127 168026681077071650138575691)
  ·
    refine ⟨252040021615607475207863537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168026681077071650138575691 252040021615607475207863537)
    ·
      refine ⟨189030016211705606405897653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252040021615607475207863537 189030016211705606405897653)
      ·
        refine ⟨17721564019847400600552905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 189030016211705606405897653 17721564019847400600552905)
        ·
          refine ⟨13291173014885550450414679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17721564019847400600552905 13291173014885550450414679)
          ·
            refine ⟨19936759522328325675622019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13291173014885550450414679 19936759522328325675622019)
            ·
              refine ⟨29905139283492488513433029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19936759522328325675622019 29905139283492488513433029)
              ·
                refine ⟨5607213615654841596268693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29905139283492488513433029 5607213615654841596268693)
                ·
                  refine ⟨262838138233820699825095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5607213615654841596268693 262838138233820699825095)
                  ·
                    rfl

theorem cell23_4606879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 4, 6].length) (baseStart_4606879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606879 prefixEnd_4606879 := by exact prefixLift 4606879
  have htrace : WordTrace (prefixWord ++ tailWord_4606879) baseStart_4606879 baseEnd_4606879 := by
    simpa [prefixWord, tailWord_4606879, baseEnd_4606879] using wordTrace_append hprefix tailTrace_4606879
  have hstable : (prefixWord ++ tailWord_4606879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606879).length < 2 ^ (prefixWord ++ tailWord_4606879).sum := by decide
  have hdescent : baseEnd_4606879 < baseStart_4606879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606883 : List Nat := [1, 1, 1, 4, 1, 2, 6, 2, 1, 4]
def baseStart_4606883 : Nat := 118140960795 + 4606883 * 2 ^ 59
def prefixEnd_4606883 : Nat := 4983230072969 + 3 ^ 40 * 4606883 * 2
def baseEnd_4606883 : Nat := 788515099342334760925279

theorem tailTrace_4606883 : CollatzResearch.WordTrace tailWord_4606883 prefixEnd_4606883 788515099342334760925279 := by
  unfold tailWord_4606883
  simp only [CollatzResearch.WordTrace]
  refine ⟨168026826969057158821721303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112017884646038105881147535 168026826969057158821721303)
  ·
    refine ⟨252040240453585738232581955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168026826969057158821721303 252040240453585738232581955)
    ·
      refine ⟨378060360680378607348872933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252040240453585738232581955 378060360680378607348872933)
      ·
        refine ⟨70886317627570988877913675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 378060360680378607348872933 70886317627570988877913675)
        ·
          refine ⟨106329476441356483316870513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70886317627570988877913675 106329476441356483316870513)
          ·
            refine ⟨79747107331017362487652885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 106329476441356483316870513 79747107331017362487652885)
            ·
              refine ⟨3738145656141438866608729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 79747107331017362487652885 3738145656141438866608729)
              ·
                refine ⟨2803609242106079149956547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3738145656141438866608729 2803609242106079149956547)
                ·
                  refine ⟨4205413863159118724934821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803609242106079149956547 4205413863159118724934821)
                  ·
                    refine ⟨788515099342334760925279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4205413863159118724934821 788515099342334760925279)
                    ·
                      rfl

theorem cell23_4606883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 4].length) (baseStart_4606883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606883 prefixEnd_4606883 := by exact prefixLift 4606883
  have htrace : WordTrace (prefixWord ++ tailWord_4606883) baseStart_4606883 baseEnd_4606883 := by
    simpa [prefixWord, tailWord_4606883, baseEnd_4606883] using wordTrace_append hprefix tailTrace_4606883
  have hstable : (prefixWord ++ tailWord_4606883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606883).length < 2 ^ (prefixWord ++ tailWord_4606883).sum := by decide
  have hdescent : baseEnd_4606883 < baseStart_4606883 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606906 : List Nat := [3, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3]
def baseStart_4606906 : Nat := 118140960795 + 4606906 * 2 ^ 59
def prefixEnd_4606906 : Nat := 4983230072969 + 3 ^ 40 * 4606906 * 2
def baseEnd_4606906 : Nat := 2365557108082057692788231

theorem tailTrace_4606906 : CollatzResearch.WordTrace tailWord_4606906 prefixEnd_4606906 2365557108082057692788231 := by
  unfold tailWord_4606906
  simp only [CollatzResearch.WordTrace]
  refine ⟨42006916461993458437452143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112018443898649222499872381 42006916461993458437452143)
  ·
    refine ⟨63010374692990187656178215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42006916461993458437452143 63010374692990187656178215)
    ·
      refine ⟨94515562039485281484267323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63010374692990187656178215 94515562039485281484267323)
      ·
        refine ⟨141773343059227922226400985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94515562039485281484267323 141773343059227922226400985)
        ·
          refine ⟨106330007294420941669800739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141773343059227922226400985 106330007294420941669800739)
          ·
            refine ⟨159495010941631412504701109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 106330007294420941669800739 159495010941631412504701109)
            ·
              refine ⟨14952657275777944922315729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 159495010941631412504701109 14952657275777944922315729)
              ·
                refine ⟨11214492956833458691736797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14952657275777944922315729 11214492956833458691736797)
                ·
                  refine ⟨4205434858812547009401299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11214492956833458691736797 4205434858812547009401299)
                  ·
                    refine ⟨6308152288218820514101949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4205434858812547009401299 6308152288218820514101949)
                    ·
                      refine ⟨2365557108082057692788231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6308152288218820514101949 2365557108082057692788231)
                      ·
                        rfl

theorem cell23_4606906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 2, 3, 1, 3].length) (baseStart_4606906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606906 prefixEnd_4606906 := by exact prefixLift 4606906
  have htrace : WordTrace (prefixWord ++ tailWord_4606906) baseStart_4606906 baseEnd_4606906 := by
    simpa [prefixWord, tailWord_4606906, baseEnd_4606906] using wordTrace_append hprefix tailTrace_4606906
  have hstable : (prefixWord ++ tailWord_4606906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606906).length < 2 ^ (prefixWord ++ tailWord_4606906).sum := by decide
  have hdescent : baseEnd_4606906 < baseStart_4606906 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606923 : List Nat := [1, 1, 1, 1, 3, 5, 1, 5, 1, 1, 3]
def baseStart_4606923 : Nat := 118140960795 + 4606923 * 2 ^ 59
def prefixEnd_4606923 : Nat := 4983230072969 + 3 ^ 40 * 4606923 * 2
def baseEnd_4606923 : Nat := 2365565837253184126275653

theorem tailTrace_4606923 : CollatzResearch.WordTrace tailWord_4606923 prefixEnd_4606923 2365565837253184126275653 := by
  unfold tailWord_4606923
  simp only [CollatzResearch.WordTrace]
  refine ⟨168028285888912245653177423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112018857259274830435451615 168028285888912245653177423)
  ·
    refine ⟨252042428833368368479766135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168028285888912245653177423 252042428833368368479766135)
    ·
      refine ⟨378063643250052552719649203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252042428833368368479766135 378063643250052552719649203)
      ·
        refine ⟨567095464875078829079473805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378063643250052552719649203 567095464875078829079473805)
        ·
          refine ⟨212660799328154560904802677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 567095464875078829079473805 212660799328154560904802677)
          ·
            refine ⟨19936949937014490084825251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 212660799328154560904802677 19936949937014490084825251)
            ·
              refine ⟨29905424905521735127237877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19936949937014490084825251 29905424905521735127237877)
              ·
                refine ⟨2803633584892662668178551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29905424905521735127237877 2803633584892662668178551)
                ·
                  refine ⟨4205450377338994002267827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803633584892662668178551 4205450377338994002267827)
                  ·
                    refine ⟨6308175566008491003401741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4205450377338994002267827 6308175566008491003401741)
                    ·
                      refine ⟨2365565837253184126275653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6308175566008491003401741 2365565837253184126275653)
                      ·
                        rfl

theorem cell23_4606923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 1, 5, 1, 1, 3].length) (baseStart_4606923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606923 prefixEnd_4606923 := by exact prefixLift 4606923
  have htrace : WordTrace (prefixWord ++ tailWord_4606923) baseStart_4606923 baseEnd_4606923 := by
    simpa [prefixWord, tailWord_4606923, baseEnd_4606923] using wordTrace_append hprefix tailTrace_4606923
  have hstable : (prefixWord ++ tailWord_4606923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606923).length < 2 ^ (prefixWord ++ tailWord_4606923).sum := by decide
  have hdescent : baseEnd_4606923 < baseStart_4606923 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606926 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_4606926 : Nat := 118140960795 + 4606926 * 2 ^ 59
def prefixEnd_4606926 : Nat := 4983230072969 + 3 ^ 40 * 4606926 * 2
def baseEnd_4606926 : Nat := 788522459231715871512713

theorem tailTrace_4606926 : CollatzResearch.WordTrace tailWord_4606926 prefixEnd_4606926 788522459231715871512713 := by
  unfold tailWord_4606926
  simp only [CollatzResearch.WordTrace]
  refine ⟨21003549413487672145692079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112018930205267584777024421 21003549413487672145692079)
  ·
    refine ⟨31505324120231508218538119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 21003549413487672145692079 31505324120231508218538119)
    ·
      refine ⟨47257986180347262327807179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31505324120231508218538119 47257986180347262327807179)
      ·
        refine ⟨70886979270520893491710769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47257986180347262327807179 70886979270520893491710769)
        ·
          refine ⟨53165234452890670118783077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70886979270520893491710769 53165234452890670118783077)
          ·
            refine ⟨9968481459917000647271827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53165234452890670118783077 9968481459917000647271827)
            ·
              refine ⟨14952722189875500970907741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9968481459917000647271827 14952722189875500970907741)
              ·
                refine ⟨5607270821203312864090403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14952722189875500970907741 5607270821203312864090403)
                ·
                  refine ⟨8410906231804969296135605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607270821203312864090403 8410906231804969296135605)
                  ·
                    refine ⟨788522459231715871512713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8410906231804969296135605 788522459231715871512713)
                    ·
                      rfl

theorem cell23_4606926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_4606926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606926 prefixEnd_4606926 := by exact prefixLift 4606926
  have htrace : WordTrace (prefixWord ++ tailWord_4606926) baseStart_4606926 baseEnd_4606926 := by
    simpa [prefixWord, tailWord_4606926, baseEnd_4606926] using wordTrace_append hprefix tailTrace_4606926
  have hstable : (prefixWord ++ tailWord_4606926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606926).length < 2 ^ (prefixWord ++ tailWord_4606926).sum := by decide
  have hdescent : baseEnd_4606926 < baseStart_4606926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606959 : List Nat := [1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 6]
def baseStart_4606959 : Nat := 118140960795 + 4606959 * 2 ^ 59
def prefixEnd_4606959 : Nat := 4983230072969 + 3 ^ 40 * 4606959 * 2
def baseEnd_4606959 : Nat := 2365584322556745985425487

theorem tailTrace_4606959 : CollatzResearch.WordTrace tailWord_4606959 prefixEnd_4606959 2365584322556745985425487 := by
  unfold tailWord_4606959
  simp only [CollatzResearch.WordTrace]
  refine ⟨168029598916781823801487931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112019732611187882534325287 168029598916781823801487931)
  ·
    refine ⟨252044398375172735702231897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168029598916781823801487931 252044398375172735702231897)
    ·
      refine ⟨189033298781379551776673923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 252044398375172735702231897 189033298781379551776673923)
      ·
        refine ⟨283549948172069327665010885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 189033298781379551776673923 283549948172069327665010885)
        ·
          refine ⟨53165615282262998937189541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 283549948172069327665010885 53165615282262998937189541)
          ·
            refine ⟨9968552865424312300723039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 53165615282262998937189541 9968552865424312300723039)
            ·
              refine ⟨14952829298136468451084559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9968552865424312300723039 14952829298136468451084559)
              ·
                refine ⟨22429243947204702676626839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14952829298136468451084559 22429243947204702676626839)
                ·
                  refine ⟨33643865920807054014940259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22429243947204702676626839 33643865920807054014940259)
                  ·
                    refine ⟨50465798881210581022410389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33643865920807054014940259 50465798881210581022410389)
                    ·
                      refine ⟨2365584322556745985425487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 50465798881210581022410389 2365584322556745985425487)
                      ·
                        rfl

theorem cell23_4606959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 6].length) (baseStart_4606959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606959 prefixEnd_4606959 := by exact prefixLift 4606959
  have htrace : WordTrace (prefixWord ++ tailWord_4606959) baseStart_4606959 baseEnd_4606959 := by
    simpa [prefixWord, tailWord_4606959, baseEnd_4606959] using wordTrace_append hprefix tailTrace_4606959
  have hstable : (prefixWord ++ tailWord_4606959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606959).length < 2 ^ (prefixWord ++ tailWord_4606959).sum := by decide
  have hdescent : baseEnd_4606959 < baseStart_4606959 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4606974 : List Nat := [4, 2, 2, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_4606974 : Nat := 118140960795 + 4606974 * 2 ^ 59
def prefixEnd_4606974 : Nat := 4983230072969 + 3 ^ 40 * 4606974 * 2
def baseEnd_4606974 : Nat := 2365592024766563426737919

theorem tailTrace_4606974 : CollatzResearch.WordTrace tailWord_4606974 prefixEnd_4606974 2365592024766563426737919 := by
  unfold tailWord_4606974
  simp only [CollatzResearch.WordTrace]
  refine ⟨21003768251465935170410497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 112020097341151654242189317 21003768251465935170410497)
  ·
    refine ⟨15752826188599451377807873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 21003768251465935170410497 15752826188599451377807873)
    ·
      refine ⟨11814619641449588533355905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15752826188599451377807873 11814619641449588533355905)
      ·
        refine ⟨8860964731087191400016929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11814619641449588533355905 8860964731087191400016929)
        ·
          refine ⟨6645723548315393550012697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8860964731087191400016929 6645723548315393550012697)
          ·
            refine ⟨4984292661236545162509523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6645723548315393550012697 4984292661236545162509523)
            ·
              refine ⟨7476438991854817743764285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4984292661236545162509523 7476438991854817743764285)
              ·
                refine ⟨2803664621945556653911607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7476438991854817743764285 2803664621945556653911607)
                ·
                  refine ⟨4205496932918334980867411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2803664621945556653911607 4205496932918334980867411)
                  ·
                    refine ⟨6308245399377502471301117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4205496932918334980867411 6308245399377502471301117)
                    ·
                      refine ⟨2365592024766563426737919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6308245399377502471301117 2365592024766563426737919)
                      ·
                        rfl

theorem cell23_4606974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_4606974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4606974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4606974 prefixEnd_4606974 := by exact prefixLift 4606974
  have htrace : WordTrace (prefixWord ++ tailWord_4606974) baseStart_4606974 baseEnd_4606974 := by
    simpa [prefixWord, tailWord_4606974, baseEnd_4606974] using wordTrace_append hprefix tailTrace_4606974
  have hstable : (prefixWord ++ tailWord_4606974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4606974).length < 2 ^ (prefixWord ++ tailWord_4606974).sum := by decide
  have hdescent : baseEnd_4606974 < baseStart_4606974 := by decide
  rcases family_descends (prefixWord ++ tailWord_4606974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607013 : List Nat := [1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 3]
def baseStart_4607013 : Nat := 118140960795 + 4607013 * 2 ^ 59
def prefixEnd_4607013 : Nat := 4983230072969 + 3 ^ 40 * 4607013 * 2
def baseEnd_4607013 : Nat := 2365612050512088774150239

theorem tailTrace_4607013 : CollatzResearch.WordTrace tailWord_4607013 prefixEnd_4607013 2365612050512088774150239 := by
  unfold tailWord_4607013
  simp only [CollatzResearch.WordTrace]
  refine ⟨168031568458586191023953693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112021045639057460682635795 168031568458586191023953693)
  ·
    refine ⟨63011838171969821633982635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168031568458586191023953693 63011838171969821633982635)
    ·
      refine ⟨94517757257954732450973953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63011838171969821633982635 94517757257954732450973953)
      ·
        refine ⟨70888317943466049338230465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 94517757257954732450973953 70888317943466049338230465)
        ·
          refine ⟨53166238457599537003672849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70888317943466049338230465 53166238457599537003672849)
          ·
            refine ⟨39874678843199652752754637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 53166238457599537003672849 39874678843199652752754637)
            ·
              refine ⟨14953004566199869782282989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39874678843199652752754637 14953004566199869782282989)
              ·
                refine ⟨5607376712324951168356121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14953004566199869782282989 5607376712324951168356121)
                ·
                  refine ⟨4205532534243713376267091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5607376712324951168356121 4205532534243713376267091)
                  ·
                    refine ⟨6308298801365570064400637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4205532534243713376267091 6308298801365570064400637)
                    ·
                      refine ⟨2365612050512088774150239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6308298801365570064400637 2365612050512088774150239)
                      ·
                        rfl

theorem cell23_4607013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_4607013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607013 prefixEnd_4607013 := by exact prefixLift 4607013
  have htrace : WordTrace (prefixWord ++ tailWord_4607013) baseStart_4607013 baseEnd_4607013 := by
    simpa [prefixWord, tailWord_4607013, baseEnd_4607013] using wordTrace_append hprefix tailTrace_4607013
  have hstable : (prefixWord ++ tailWord_4607013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607013).length < 2 ^ (prefixWord ++ tailWord_4607013).sum := by decide
  have hdescent : baseEnd_4607013 < baseStart_4607013 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607029 : List Nat := [1, 3, 3, 1, 1, 1, 1, 2, 4, 6]
def baseStart_4607029 : Nat := 118140960795 + 4607029 * 2 ^ 59
def prefixEnd_4607029 : Nat := 4983230072969 + 3 ^ 40 * 4607029 * 2
def baseEnd_4607029 : Nat := 788540088734186903850055

theorem tailTrace_4607029 : CollatzResearch.WordTrace tailWord_4607029 prefixEnd_4607029 788540088734186903850055 := by
  unfold tailWord_4607029
  simp only [CollatzResearch.WordTrace]
  refine ⟨168032152026528225756536141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112021434684352150504357427 168032152026528225756536141)
  ·
    refine ⟨63012057009948084658701053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 168032152026528225756536141 63012057009948084658701053)
    ·
      refine ⟨23629521378730531747012895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 63012057009948084658701053 23629521378730531747012895)
      ·
        refine ⟨35444282068095797620519343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23629521378730531747012895 35444282068095797620519343)
        ·
          refine ⟨53166423102143696430779015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35444282068095797620519343 53166423102143696430779015)
          ·
            refine ⟨79749634653215544646168523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53166423102143696430779015 79749634653215544646168523)
            ·
              refine ⟨119624451979823316969252785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79749634653215544646168523 119624451979823316969252785)
              ·
                refine ⟨89718338984867487726939589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 119624451979823316969252785 89718338984867487726939589)
                ·
                  refine ⟨16822188559662653948801173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 89718338984867487726939589 16822188559662653948801173)
                  ·
                    refine ⟨788540088734186903850055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16822188559662653948801173 788540088734186903850055)
                    ·
                      rfl

theorem cell23_4607029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_4607029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607029 prefixEnd_4607029 := by exact prefixLift 4607029
  have htrace : WordTrace (prefixWord ++ tailWord_4607029) baseStart_4607029 baseEnd_4607029 := by
    simpa [prefixWord, tailWord_4607029, baseEnd_4607029] using wordTrace_append hprefix tailTrace_4607029
  have hstable : (prefixWord ++ tailWord_4607029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607029).length < 2 ^ (prefixWord ++ tailWord_4607029).sum := by decide
  have hdescent : baseEnd_4607029 < baseStart_4607029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607040 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 1, 3, 2]
def baseStart_4607040 : Nat := 118140960795 + 4607040 * 2 ^ 59
def prefixEnd_4607040 : Nat := 4983230072969 + 3 ^ 40 * 4607040 * 2
def baseEnd_4607040 : Nat := 2365625914489760168512615

theorem tailTrace_4607040 : CollatzResearch.WordTrace tailWord_4607040 prefixEnd_4607040 2365625914489760168512615 := by
  unfold tailWord_4607040
  simp only [CollatzResearch.WordTrace]
  refine ⟨84016276614744187317593287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 112021702152992249756791049 84016276614744187317593287)
  ·
    refine ⟨126024414922116280976389931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 84016276614744187317593287 126024414922116280976389931)
    ·
      refine ⟨189036622383174421464584897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126024414922116280976389931 189036622383174421464584897)
      ·
        refine ⟨141777466787380816098438673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189036622383174421464584897 141777466787380816098438673)
        ·
          refine ⟨106333100090535612073829005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 141777466787380816098438673 106333100090535612073829005)
          ·
            refine ⟨39874912533950854527685877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 106333100090535612073829005 39874912533950854527685877)
            ·
              refine ⟨3738273050057892611970551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39874912533950854527685877 3738273050057892611970551)
              ·
                refine ⟨5607409575086838917955827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3738273050057892611970551 5607409575086838917955827)
                ·
                  refine ⟨8411114362630258376933741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5607409575086838917955827 8411114362630258376933741)
                  ·
                    refine ⟨3154167885986346891350153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8411114362630258376933741 3154167885986346891350153)
                    ·
                      refine ⟨2365625914489760168512615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3154167885986346891350153 2365625914489760168512615)
                      ·
                        rfl

theorem cell23_4607040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 1, 3, 2].length) (baseStart_4607040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607040 prefixEnd_4607040 := by exact prefixLift 4607040
  have htrace : WordTrace (prefixWord ++ tailWord_4607040) baseStart_4607040 baseEnd_4607040 := by
    simpa [prefixWord, tailWord_4607040, baseEnd_4607040] using wordTrace_append hprefix tailTrace_4607040
  have hstable : (prefixWord ++ tailWord_4607040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607040).length < 2 ^ (prefixWord ++ tailWord_4607040).sum := by decide
  have hdescent : baseEnd_4607040 < baseStart_4607040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607099 : List Nat := [1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5]
def baseStart_4607099 : Nat := 118140960795 + 4607099 * 2 ^ 59
def prefixEnd_4607099 : Nat := 4983230072969 + 3 ^ 40 * 4607099 * 2
def baseEnd_4607099 : Nat := 2365656209848375437674843

theorem tailTrace_4607099 : CollatzResearch.WordTrace tailWord_4607099 prefixEnd_4607099 2365656209848375437674843 := by
  unfold tailWord_4607099
  simp only [CollatzResearch.WordTrace]
  refine ⟨168034705136274627711584351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112023136757516418474389567 168034705136274627711584351)
  ·
    refine ⟨252052057704411941567376527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168034705136274627711584351 252052057704411941567376527)
    ·
      refine ⟨378078086556617912351064791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 252052057704411941567376527 378078086556617912351064791)
      ·
        refine ⟨567117129834926868526597187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 378078086556617912351064791 567117129834926868526597187)
        ·
          refine ⟨850675694752390302789895781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 567117129834926868526597187 850675694752390302789895781)
          ·
            refine ⟨159501692766073181773105459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 850675694752390302789895781 159501692766073181773105459)
            ·
              refine ⟨239252539149109772659658189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 159501692766073181773105459 239252539149109772659658189)
              ·
                refine ⟨89719702180916164747371821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 239252539149109772659658189 89719702180916164747371821)
                ·
                  refine ⟨33644888317843561780264433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89719702180916164747371821 33644888317843561780264433)
                  ·
                    refine ⟨25233666238382671335198325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33644888317843561780264433 25233666238382671335198325)
                    ·
                      refine ⟨2365656209848375437674843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 25233666238382671335198325 2365656209848375437674843)
                      ·
                        rfl

theorem cell23_4607099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 3, 2, 5].length) (baseStart_4607099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607099 prefixEnd_4607099 := by exact prefixLift 4607099
  have htrace : WordTrace (prefixWord ++ tailWord_4607099) baseStart_4607099 baseEnd_4607099 := by
    simpa [prefixWord, tailWord_4607099, baseEnd_4607099] using wordTrace_append hprefix tailTrace_4607099
  have hstable : (prefixWord ++ tailWord_4607099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607099).length < 2 ^ (prefixWord ++ tailWord_4607099).sum := by decide
  have hdescent : baseEnd_4607099 < baseStart_4607099 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607143 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 4]
def baseStart_4607143 : Nat := 118140960795 + 4607143 * 2 ^ 59
def prefixEnd_4607143 : Nat := 4983230072969 + 3 ^ 40 * 4607143 * 2
def baseEnd_4607143 : Nat := 2365678802997173265524641

theorem tailTrace_4607143 : CollatzResearch.WordTrace tailWord_4607143 prefixEnd_4607143 2365678802997173265524641 := by
  unfold tailWord_4607143
  simp only [CollatzResearch.WordTrace]
  refine ⟨168036309948115223226186083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112024206632076815484124055 168036309948115223226186083)
  ·
    refine ⟨252054464922172834839279125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 168036309948115223226186083 252054464922172834839279125)
    ·
      refine ⟨11815053043226851633091209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 252054464922172834839279125 11815053043226851633091209)
      ·
        refine ⟨8861289782420138724818407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11815053043226851633091209 8861289782420138724818407)
        ·
          refine ⟨13291934673630208087227611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8861289782420138724818407 13291934673630208087227611)
          ·
            refine ⟨19937902010445312130841417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13291934673630208087227611 19937902010445312130841417)
            ·
              refine ⟨14953426507833984098131063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19937902010445312130841417 14953426507833984098131063)
              ·
                refine ⟨22430139761750976147196595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14953426507833984098131063 22430139761750976147196595)
                ·
                  refine ⟨33645209642626464220794893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22430139761750976147196595 33645209642626464220794893)
                  ·
                    refine ⟨12616953615984924082798085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33645209642626464220794893 12616953615984924082798085)
                    ·
                      refine ⟨2365678802997173265524641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12616953615984924082798085 2365678802997173265524641)
                      ·
                        rfl

theorem cell23_4607143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 1, 3, 4].length) (baseStart_4607143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607143 prefixEnd_4607143 := by exact prefixLift 4607143
  have htrace : WordTrace (prefixWord ++ tailWord_4607143) baseStart_4607143 baseEnd_4607143 := by
    simpa [prefixWord, tailWord_4607143, baseEnd_4607143] using wordTrace_append hprefix tailTrace_4607143
  have hstable : (prefixWord ++ tailWord_4607143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607143).length < 2 ^ (prefixWord ++ tailWord_4607143).sum := by decide
  have hdescent : baseEnd_4607143 < baseStart_4607143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607193 : List Nat := [1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 3]
def baseStart_4607193 : Nat := 118140960795 + 4607193 * 2 ^ 59
def prefixEnd_4607193 : Nat := 4983230072969 + 3 ^ 40 * 4607193 * 2
def baseEnd_4607193 : Nat := 2365704477029898069899411

theorem tailTrace_4607193 : CollatzResearch.WordTrace tailWord_4607193 prefixEnd_4607193 2365704477029898069899411 := by
  unfold tailWord_4607193
  simp only [CollatzResearch.WordTrace]
  refine ⟨168038133597934081765506233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112025422398622721177004155 168038133597934081765506233)
  ·
    refine ⟨126028600198450561324129675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 168038133597934081765506233 126028600198450561324129675)
    ·
      refine ⟨189042900297675841986194513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 126028600198450561324129675 189042900297675841986194513)
      ·
        refine ⟨141782175223256881489645885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 189042900297675841986194513 141782175223256881489645885)
        ·
          refine ⟨53168315708721330558617207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141782175223256881489645885 53168315708721330558617207)
          ·
            refine ⟨79752473563081995837925811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 53168315708721330558617207 79752473563081995837925811)
            ·
              refine ⟨119628710344622993756888717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79752473563081995837925811 119628710344622993756888717)
              ·
                refine ⟨44860766379233622658833269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 119628710344622993756888717 44860766379233622658833269)
                ·
                  refine ⟨4205696848053152124265619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44860766379233622658833269 4205696848053152124265619)
                  ·
                    refine ⟨6308545272079728186398429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4205696848053152124265619 6308545272079728186398429)
                    ·
                      refine ⟨2365704477029898069899411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6308545272079728186398429 2365704477029898069899411)
                      ·
                        rfl

theorem cell23_4607193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 3, 5, 1, 3].length) (baseStart_4607193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607193 prefixEnd_4607193 := by exact prefixLift 4607193
  have htrace : WordTrace (prefixWord ++ tailWord_4607193) baseStart_4607193 baseEnd_4607193 := by
    simpa [prefixWord, tailWord_4607193, baseEnd_4607193] using wordTrace_append hprefix tailTrace_4607193
  have hstable : (prefixWord ++ tailWord_4607193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607193).length < 2 ^ (prefixWord ++ tailWord_4607193).sum := by decide
  have hdescent : baseEnd_4607193 < baseStart_4607193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607197 : List Nat := [1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 3]
def baseStart_4607197 : Nat := 118140960795 + 4607197 * 2 ^ 59
def prefixEnd_4607197 : Nat := 4983230072969 + 3 ^ 40 * 4607197 * 2
def baseEnd_4607197 : Nat := 2365706530952516054249393

theorem tailTrace_4607197 : CollatzResearch.WordTrace tailWord_4607197 prefixEnd_4607197 2365706530952516054249393 := by
  unfold tailWord_4607197
  simp only [CollatzResearch.WordTrace]
  refine ⟨168038279489919590448651845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 112025519659946393632434563 168038279489919590448651845)
  ·
    refine ⟨31507177404359923209122221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 168038279489919590448651845 31507177404359923209122221)
    ·
      refine ⟨11815191526634971203420833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31507177404359923209122221 11815191526634971203420833)
      ·
        refine ⟨8861393644976228402565625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11815191526634971203420833 8861393644976228402565625)
        ·
          refine ⟨6646045233732171301924219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8861393644976228402565625 6646045233732171301924219)
          ·
            refine ⟨9969067850598256952886329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6646045233732171301924219 9969067850598256952886329)
            ·
              refine ⟨7476800887948692714664747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9969067850598256952886329 7476800887948692714664747)
              ·
                refine ⟨11215201331923039071997121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7476800887948692714664747 11215201331923039071997121)
                ·
                  refine ⟨8411400998942279303997841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11215201331923039071997121 8411400998942279303997841)
                  ·
                    refine ⟨6308550749206709477998381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8411400998942279303997841 6308550749206709477998381)
                    ·
                      refine ⟨2365706530952516054249393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6308550749206709477998381 2365706530952516054249393)
                      ·
                        rfl

theorem cell23_4607197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_4607197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607197 prefixEnd_4607197 := by exact prefixLift 4607197
  have htrace : WordTrace (prefixWord ++ tailWord_4607197) baseStart_4607197 baseEnd_4607197 := by
    simpa [prefixWord, tailWord_4607197, baseEnd_4607197] using wordTrace_append hprefix tailTrace_4607197
  have hstable : (prefixWord ++ tailWord_4607197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607197).length < 2 ^ (prefixWord ++ tailWord_4607197).sum := by decide
  have hdescent : baseEnd_4607197 < baseStart_4607197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4607226 : List Nat := [3, 1, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_4607226 : Nat := 118140960795 + 4607226 * 2 ^ 59
def prefixEnd_4607226 : Nat := 4983230072969 + 3 ^ 40 * 4607226 * 2
def baseEnd_4607226 : Nat := 788573807297165480262253

theorem tailTrace_4607226 : CollatzResearch.WordTrace tailWord_4607226 prefixEnd_4607226 788573807297165480262253 := by
  unfold tailWord_4607226
  simp only [CollatzResearch.WordTrace]
  refine ⟨42009834301703632100364383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 112026224804543018934305021 42009834301703632100364383)
  ·
    refine ⟨63014751452555448150546575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 42009834301703632100364383 63014751452555448150546575)
    ·
      refine ⟨94522127178833172225819863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 63014751452555448150546575 94522127178833172225819863)
      ·
        refine ⟨141783190768249758338729795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94522127178833172225819863 141783190768249758338729795)
        ·
          refine ⟨212674786152374637508094693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 141783190768249758338729795 212674786152374637508094693)
          ·
            refine ⟨39876522403570244532767755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 212674786152374637508094693 39876522403570244532767755)
            ·
              refine ⟨59814783605355366799151633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39876522403570244532767755 59814783605355366799151633)
              ·
                refine ⟨44861087704016525099363725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59814783605355366799151633 44861087704016525099363725)
                ·
                  refine ⟨16822907889006196912261397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44861087704016525099363725 16822907889006196912261397)
                  ·
                    refine ⟨788573807297165480262253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16822907889006196912261397 788573807297165480262253)
                    ·
                      rfl

theorem cell23_4607226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_4607226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4607226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4607226 prefixEnd_4607226 := by exact prefixLift 4607226
  have htrace : WordTrace (prefixWord ++ tailWord_4607226) baseStart_4607226 baseEnd_4607226 := by
    simpa [prefixWord, tailWord_4607226, baseEnd_4607226] using wordTrace_append hprefix tailTrace_4607226
  have hstable : (prefixWord ++ tailWord_4607226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4607226).length < 2 ^ (prefixWord ++ tailWord_4607226).sum := by decide
  have hdescent : baseEnd_4607226 < baseStart_4607226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4607226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
