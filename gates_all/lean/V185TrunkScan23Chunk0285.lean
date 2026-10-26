import V185TrunkScan23Chunk0284

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1685276 : List Nat := [2, 2, 3, 1, 1, 2, 4, 3, 1, 4]
def baseStart_1685276 : Nat := 118140960795 + 1685276 * 2 ^ 59
def prefixEnd_1685276 : Nat := 4983230072969 + 3 ^ 40 * 1685276 * 2
def baseEnd_1685276 : Nat := 288452207828884527866521

theorem tailTrace_1685276 : CollatzResearch.WordTrace tailWord_1685276 prefixEnd_1685276 288452207828884527866521 := by
  unfold tailWord_1685276
  simp only [CollatzResearch.WordTrace]
  refine ⟨30733532721270174535605841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40978043628360232714141121 30733532721270174535605841)
  ·
    refine ⟨23050149540952630901704381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30733532721270174535605841 23050149540952630901704381)
    ·
      refine ⟨8643806077857236588139143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23050149540952630901704381 8643806077857236588139143)
      ·
        refine ⟨12965709116785854882208715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8643806077857236588139143 12965709116785854882208715)
        ·
          refine ⟨19448563675178782323313073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12965709116785854882208715 19448563675178782323313073)
          ·
            refine ⟨14586422756384086742484805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19448563675178782323313073 14586422756384086742484805)
            ·
              refine ⟨2734954266822016264215901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14586422756384086742484805 2734954266822016264215901)
              ·
                refine ⟨1025607850058256099080963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2734954266822016264215901 1025607850058256099080963)
                ·
                  refine ⟨1538411775087384148621445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025607850058256099080963 1538411775087384148621445)
                  ·
                    refine ⟨288452207828884527866521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538411775087384148621445 288452207828884527866521)
                    ·
                      rfl

theorem cell23_1685276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_1685276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685276 prefixEnd_1685276 := by exact prefixLift 1685276
  have htrace : WordTrace (prefixWord ++ tailWord_1685276) baseStart_1685276 baseEnd_1685276 := by
    simpa [prefixWord, tailWord_1685276, baseEnd_1685276] using wordTrace_append hprefix tailTrace_1685276
  have hstable : (prefixWord ++ tailWord_1685276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685276).length < 2 ^ (prefixWord ++ tailWord_1685276).sum := by decide
  have hdescent : baseEnd_1685276 < baseStart_1685276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685295 : List Nat := [1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 5]
def baseStart_1685295 : Nat := 118140960795 + 1685295 * 2 ^ 59
def prefixEnd_1685295 : Nat := 4983230072969 + 3 ^ 40 * 1685295 * 2
def baseEnd_1685295 : Nat := 865366379619089009261975

theorem tailTrace_1685295 : CollatzResearch.WordTrace tailWord_1685295 prefixEnd_1685295 865366379619089009261975 := by
  unfold tailWord_1685295
  simp only [CollatzResearch.WordTrace]
  refine ⟨61467758429471515316153339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40978505619647676877435559 61467758429471515316153339)
  ·
    refine ⟨92201637644207272974230009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61467758429471515316153339 92201637644207272974230009)
    ·
      refine ⟨69151228233155454730672507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92201637644207272974230009 69151228233155454730672507)
      ·
        refine ⟨103726842349733182096008761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69151228233155454730672507 103726842349733182096008761)
        ·
          refine ⟨77795131762299886572006571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103726842349733182096008761 77795131762299886572006571)
          ·
            refine ⟨116692697643449829858009857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77795131762299886572006571 116692697643449829858009857)
            ·
              refine ⟨87519523232587372393507393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116692697643449829858009857 87519523232587372393507393)
              ·
                refine ⟨65639642424440529295130545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87519523232587372393507393 65639642424440529295130545)
                ·
                  refine ⟨49229731818330396971347909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65639642424440529295130545 49229731818330396971347909)
                  ·
                    refine ⟨9230574715936949432127733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49229731818330396971347909 9230574715936949432127733)
                    ·
                      refine ⟨865366379619089009261975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9230574715936949432127733 865366379619089009261975)
                      ·
                        rfl

theorem cell23_1685295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 2, 2, 4, 5].length) (baseStart_1685295 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685295 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685295 prefixEnd_1685295 := by exact prefixLift 1685295
  have htrace : WordTrace (prefixWord ++ tailWord_1685295) baseStart_1685295 baseEnd_1685295 := by
    simpa [prefixWord, tailWord_1685295, baseEnd_1685295] using wordTrace_append hprefix tailTrace_1685295
  have hstable : (prefixWord ++ tailWord_1685295).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685295).length < 2 ^ (prefixWord ++ tailWord_1685295).sum := by decide
  have hdescent : baseEnd_1685295 < baseStart_1685295 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685333 : List Nat := [1, 3, 2, 2, 2, 2, 3, 3, 1, 1, 3]
def baseStart_1685333 : Nat := 118140960795 + 1685333 * 2 ^ 59
def prefixEnd_1685333 : Nat := 4983230072969 + 3 ^ 40 * 1685333 * 2
def baseEnd_1685333 : Nat := 865385891883959860586801

theorem tailTrace_1685333 : CollatzResearch.WordTrace tailWord_1685333 prefixEnd_1685333 865385891883959860586801 := by
  unfold tailWord_1685333
  simp only [CollatzResearch.WordTrace]
  refine ⟨61469144403333847806036653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40979429602222565204024435 61469144403333847806036653)
  ·
    refine ⟨23050929151250192927263745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61469144403333847806036653 23050929151250192927263745)
    ·
      refine ⟨17288196863437644695447809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23050929151250192927263745 17288196863437644695447809)
      ·
        refine ⟨12966147647578233521585857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17288196863437644695447809 12966147647578233521585857)
        ·
          refine ⟨9724610735683675141189393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12966147647578233521585857 9724610735683675141189393)
          ·
            refine ⟨7293458051762756355892045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9724610735683675141189393 7293458051762756355892045)
            ·
              refine ⟨2735046769411033633459517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7293458051762756355892045 2735046769411033633459517)
              ·
                refine ⟨1025642538529137612547319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2735046769411033633459517 1025642538529137612547319)
                ·
                  refine ⟨1538463807793706418820979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025642538529137612547319 1538463807793706418820979)
                  ·
                    refine ⟨2307695711690559628231469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1538463807793706418820979 2307695711690559628231469)
                    ·
                      refine ⟨865385891883959860586801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2307695711690559628231469 865385891883959860586801)
                      ·
                        rfl

theorem cell23_1685333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 3, 3, 1, 1, 3].length) (baseStart_1685333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685333 prefixEnd_1685333 := by exact prefixLift 1685333
  have htrace : WordTrace (prefixWord ++ tailWord_1685333) baseStart_1685333 baseEnd_1685333 := by
    simpa [prefixWord, tailWord_1685333, baseEnd_1685333] using wordTrace_append hprefix tailTrace_1685333
  have hstable : (prefixWord ++ tailWord_1685333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685333).length < 2 ^ (prefixWord ++ tailWord_1685333).sum := by decide
  have hdescent : baseEnd_1685333 < baseStart_1685333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685349 : List Nat := [1, 3, 1, 3, 1, 1, 1, 6, 2, 4]
def baseStart_1685349 : Nat := 118140960795 + 1685349 * 2 ^ 59
def prefixEnd_1685349 : Nat := 4983230072969 + 3 ^ 40 * 1685349 * 2
def baseEnd_1685349 : Nat := 288464702524810599328909

theorem tailTrace_1685349 : CollatzResearch.WordTrace tailWord_1685349 prefixEnd_1685349 288464702524810599328909 := by
  unfold tailWord_1685349
  simp only [CollatzResearch.WordTrace]
  refine ⟨61469727971275882538619101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40979818647517255025746067 61469727971275882538619101)
  ·
    refine ⟨23051147989228455951982163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61469727971275882538619101 23051147989228455951982163)
    ·
      refine ⟨34576721983842683927973245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23051147989228455951982163 34576721983842683927973245)
      ·
        refine ⟨12966270743941006472989967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34576721983842683927973245 12966270743941006472989967)
        ·
          refine ⟨19449406115911509709484951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12966270743941006472989967 19449406115911509709484951)
          ·
            refine ⟨29174109173867264564227427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19449406115911509709484951 29174109173867264564227427)
            ·
              refine ⟨43761163760800896846341141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29174109173867264564227427 43761163760800896846341141)
              ·
                refine ⟨2051304551287542039672241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43761163760800896846341141 2051304551287542039672241)
                ·
                  refine ⟨1538478413465656529754181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2051304551287542039672241 1538478413465656529754181)
                  ·
                    refine ⟨288464702524810599328909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538478413465656529754181 288464702524810599328909)
                    ·
                      rfl

theorem cell23_1685349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 6, 2, 4].length) (baseStart_1685349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685349 prefixEnd_1685349 := by exact prefixLift 1685349
  have htrace : WordTrace (prefixWord ++ tailWord_1685349) baseStart_1685349 baseEnd_1685349 := by
    simpa [prefixWord, tailWord_1685349, baseEnd_1685349] using wordTrace_append hprefix tailTrace_1685349
  have hstable : (prefixWord ++ tailWord_1685349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685349).length < 2 ^ (prefixWord ++ tailWord_1685349).sum := by decide
  have hdescent : baseEnd_1685349 < baseStart_1685349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685352 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 3, 1, 6]
def baseStart_1685352 : Nat := 118140960795 + 1685352 * 2 ^ 59
def prefixEnd_1685352 : Nat := 4983230072969 + 3 ^ 40 * 1685352 * 2
def baseEnd_1685352 : Nat := 865395648016395286249213

theorem tailTrace_1685352 : CollatzResearch.WordTrace tailWord_1685352 prefixEnd_1685352 865395648016395286249213 := by
  unfold tailWord_1685352
  simp only [CollatzResearch.WordTrace]
  refine ⟨30734918695132507025489155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40979891593510009367318873 30734918695132507025489155)
  ·
    refine ⟨46102378042698760538233733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30734918695132507025489155 46102378042698760538233733)
    ·
      refine ⟨8644195883006017600918825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46102378042698760538233733 8644195883006017600918825)
      ·
        refine ⟨6483146912254513200689119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8644195883006017600918825 6483146912254513200689119)
        ·
          refine ⟨9724720368381769801033679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6483146912254513200689119 9724720368381769801033679)
          ·
            refine ⟨14587080552572654701550519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9724720368381769801033679 14587080552572654701550519)
            ·
              refine ⟨21880620828858982052325779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14587080552572654701550519 21880620828858982052325779)
              ·
                refine ⟨32820931243288473078488669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21880620828858982052325779 32820931243288473078488669)
                ·
                  refine ⟨12307849216233177404433251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32820931243288473078488669 12307849216233177404433251)
                  ·
                    refine ⟨18461773824349766106649877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12307849216233177404433251 18461773824349766106649877)
                    ·
                      refine ⟨865395648016395286249213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18461773824349766106649877 865395648016395286249213)
                      ·
                        rfl

theorem cell23_1685352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_1685352 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685352 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685352 prefixEnd_1685352 := by exact prefixLift 1685352
  have htrace : WordTrace (prefixWord ++ tailWord_1685352) baseStart_1685352 baseEnd_1685352 := by
    simpa [prefixWord, tailWord_1685352, baseEnd_1685352] using wordTrace_append hprefix tailTrace_1685352
  have hstable : (prefixWord ++ tailWord_1685352).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685352).length < 2 ^ (prefixWord ++ tailWord_1685352).sum := by decide
  have hdescent : baseEnd_1685352 < baseStart_1685352 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685386 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4]
def baseStart_1685386 : Nat := 118140960795 + 1685386 * 2 ^ 59
def prefixEnd_1685386 : Nat := 4983230072969 + 3 ^ 40 * 1685386 * 2
def baseEnd_1685386 : Nat := 865413106358648153224057

theorem tailTrace_1685386 : CollatzResearch.WordTrace tailWord_1685386 prefixEnd_1685386 865413106358648153224057 := by
  unfold tailWord_1685386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15367769368035459464429003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40980718314761225238477341 15367769368035459464429003)
  ·
    refine ⟨23051654052053189196643505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15367769368035459464429003 23051654052053189196643505)
    ·
      refine ⟨17288740539039891897482629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23051654052053189196643505 17288740539039891897482629)
      ·
        refine ⟨3241638851069979730777993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17288740539039891897482629 3241638851069979730777993)
        ·
          refine ⟨2431229138302484798083495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3241638851069979730777993 2431229138302484798083495)
          ·
            refine ⟨3646843707453727197125243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431229138302484798083495 3646843707453727197125243)
            ·
              refine ⟨5470265561180590795687865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3646843707453727197125243 5470265561180590795687865)
              ·
                refine ⟨4102699170885443096765899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5470265561180590795687865 4102699170885443096765899)
                ·
                  refine ⟨6154048756328164645148849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4102699170885443096765899 6154048756328164645148849)
                  ·
                    refine ⟨4615536567246123483861637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6154048756328164645148849 4615536567246123483861637)
                    ·
                      refine ⟨865413106358648153224057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4615536567246123483861637 865413106358648153224057)
                      ·
                        rfl

theorem cell23_1685386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 1, 2, 4].length) (baseStart_1685386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685386 prefixEnd_1685386 := by exact prefixLift 1685386
  have htrace : WordTrace (prefixWord ++ tailWord_1685386) baseStart_1685386 baseEnd_1685386 := by
    simpa [prefixWord, tailWord_1685386, baseEnd_1685386] using wordTrace_append hprefix tailTrace_1685386
  have hstable : (prefixWord ++ tailWord_1685386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685386).length < 2 ^ (prefixWord ++ tailWord_1685386).sum := by decide
  have hdescent : baseEnd_1685386 < baseStart_1685386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685390 : List Nat := [4, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4]
def baseStart_1685390 : Nat := 118140960795 + 1685390 * 2 ^ 59
def prefixEnd_1685390 : Nat := 4983230072969 + 3 ^ 40 * 1685390 * 2
def baseEnd_1685390 : Nat := 865415160281266137574039

theorem tailTrace_1685390 : CollatzResearch.WordTrace tailWord_1685390 prefixEnd_1685390 865415160281266137574039 := by
  unfold tailWord_1685390
  simp only [CollatzResearch.WordTrace]
  refine ⟨7683902920515918317607703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40980815576084897693907749 7683902920515918317607703)
  ·
    refine ⟨11525854380773877476411555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7683902920515918317607703 11525854380773877476411555)
    ·
      refine ⟨17288781571160816214617333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11525854380773877476411555 17288781571160816214617333)
      ·
        refine ⟨1620823272296326520120375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17288781571160816214617333 1620823272296326520120375)
        ·
          refine ⟨2431234908444489780180563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1620823272296326520120375 2431234908444489780180563)
          ·
            refine ⟨3646852362666734670270845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2431234908444489780180563 3646852362666734670270845)
            ·
              refine ⟨1367569636000025501351567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3646852362666734670270845 1367569636000025501351567)
              ·
                refine ⟨2051354454000038252027351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367569636000025501351567 2051354454000038252027351)
                ·
                  refine ⟨3077031681000057378041027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051354454000038252027351 3077031681000057378041027)
                  ·
                    refine ⟨4615547521500086067061541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3077031681000057378041027 4615547521500086067061541)
                    ·
                      refine ⟨865415160281266137574039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4615547521500086067061541 865415160281266137574039)
                      ·
                        rfl

theorem cell23_1685390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 1, 1, 1, 4].length) (baseStart_1685390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685390 prefixEnd_1685390 := by exact prefixLift 1685390
  have htrace : WordTrace (prefixWord ++ tailWord_1685390) baseStart_1685390 baseEnd_1685390 := by
    simpa [prefixWord, tailWord_1685390, baseEnd_1685390] using wordTrace_append hprefix tailTrace_1685390
  have hstable : (prefixWord ++ tailWord_1685390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685390).length < 2 ^ (prefixWord ++ tailWord_1685390).sum := by decide
  have hdescent : baseEnd_1685390 < baseStart_1685390 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685580 : List Nat := [2, 2, 1, 3, 1, 1, 6, 2, 1, 4]
def baseStart_1685580 : Nat := 118140960795 + 1685580 * 2 ^ 59
def prefixEnd_1685580 : Nat := 4983230072969 + 3 ^ 40 * 1685580 * 2
def baseEnd_1685580 : Nat := 288504240535206798066055

theorem tailTrace_1685580 : CollatzResearch.WordTrace tailWord_1685580 prefixEnd_1685580 288504240535206798066055 := by
  unfold tailWord_1685580
  simp only [CollatzResearch.WordTrace]
  refine ⟨30739076616719504495139097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40985435488959339326852129 30739076616719504495139097)
  ·
    refine ⟨23054307462539628371354323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30739076616719504495139097 23054307462539628371354323)
    ·
      refine ⟨34581461193809442557031485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23054307462539628371354323 34581461193809442557031485)
      ·
        refine ⟨12968047947678540958886807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34581461193809442557031485 12968047947678540958886807)
        ·
          refine ⟨19452071921517811438330211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12968047947678540958886807 19452071921517811438330211)
          ·
            refine ⟨29178107882276717157495317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19452071921517811438330211 29178107882276717157495317)
            ·
              refine ⟨1367723806981721116757593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29178107882276717157495317 1367723806981721116757593)
              ·
                refine ⟨1025792855236290837568195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367723806981721116757593 1025792855236290837568195)
                ·
                  refine ⟨1538689282854436256352293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025792855236290837568195 1538689282854436256352293)
                  ·
                    refine ⟨288504240535206798066055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538689282854436256352293 288504240535206798066055)
                    ·
                      rfl

theorem cell23_1685580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 6, 2, 1, 4].length) (baseStart_1685580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685580 prefixEnd_1685580 := by exact prefixLift 1685580
  have htrace : WordTrace (prefixWord ++ tailWord_1685580) baseStart_1685580 baseEnd_1685580 := by
    simpa [prefixWord, tailWord_1685580, baseEnd_1685580] using wordTrace_append hprefix tailTrace_1685580
  have hstable : (prefixWord ++ tailWord_1685580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685580).length < 2 ^ (prefixWord ++ tailWord_1685580).sum := by decide
  have hdescent : baseEnd_1685580 < baseStart_1685580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685613 : List Nat := [1, 5, 1, 1, 2, 1, 3, 1, 1, 5, 2]
def baseStart_1685613 : Nat := 118140960795 + 1685613 * 2 ^ 59
def prefixEnd_1685613 : Nat := 4983230072969 + 3 ^ 40 * 1685613 * 2
def baseEnd_1685613 : Nat := 865529666467218765085513

theorem tailTrace_1685613 : CollatzResearch.WordTrace tailWord_1685613 prefixEnd_1685613 865529666467218765085513 := by
  unfold tailWord_1685613
  simp only [CollatzResearch.WordTrace]
  refine ⟨61479356842319455626229493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40986237894879637084152995 61479356842319455626229493)
  ·
    refine ⟨5763689703967448964959015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61479356842319455626229493 5763689703967448964959015)
    ·
      refine ⟨8645534555951173447438523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5763689703967448964959015 8645534555951173447438523)
      ·
        refine ⟨12968301833926760171157785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645534555951173447438523 12968301833926760171157785)
        ·
          refine ⟨9726226375445070128368339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12968301833926760171157785 9726226375445070128368339)
          ·
            refine ⟨14589339563167605192552509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9726226375445070128368339 14589339563167605192552509)
            ·
              refine ⟨5471002336187851947207191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14589339563167605192552509 5471002336187851947207191)
              ·
                refine ⟨8206503504281777920810787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471002336187851947207191 8206503504281777920810787)
                ·
                  refine ⟨12309755256422666881216181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8206503504281777920810787 12309755256422666881216181)
                  ·
                    refine ⟨1154039555289625020114017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12309755256422666881216181 1154039555289625020114017)
                    ·
                      refine ⟨865529666467218765085513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154039555289625020114017 865529666467218765085513)
                      ·
                        rfl

theorem cell23_1685613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 3, 1, 1, 5, 2].length) (baseStart_1685613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685613 prefixEnd_1685613 := by exact prefixLift 1685613
  have htrace : WordTrace (prefixWord ++ tailWord_1685613) baseStart_1685613 baseEnd_1685613 := by
    simpa [prefixWord, tailWord_1685613, baseEnd_1685613] using wordTrace_append hprefix tailTrace_1685613
  have hstable : (prefixWord ++ tailWord_1685613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685613).length < 2 ^ (prefixWord ++ tailWord_1685613).sum := by decide
  have hdescent : baseEnd_1685613 < baseStart_1685613 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685623 : List Nat := [1, 1, 3, 1, 1, 5, 4, 1, 1, 5]
def baseStart_1685623 : Nat := 118140960795 + 1685623 * 2 ^ 59
def prefixEnd_1685623 : Nat := 4983230072969 + 3 ^ 40 * 1685623 * 2
def baseEnd_1685623 : Nat := 288511600424587908653489

theorem tailTrace_1685623 : CollatzResearch.WordTrace tailWord_1685623 prefixEnd_1685623 288511600424587908653489 := by
  unfold tailWord_1685623
  simp only [CollatzResearch.WordTrace]
  refine ⟨61479721572283227334093523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40986481048188818222729015 61479721572283227334093523)
  ·
    refine ⟨92219582358424841001140285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61479721572283227334093523 92219582358424841001140285)
    ·
      refine ⟨34582343384409315375427607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92219582358424841001140285 34582343384409315375427607)
      ·
        refine ⟨51873515076613973063141411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34582343384409315375427607 51873515076613973063141411)
        ·
          refine ⟨77810272614920959594712117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51873515076613973063141411 77810272614920959594712117)
          ·
            refine ⟨7294713057648839962004261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77810272614920959594712117 7294713057648839962004261)
            ·
              refine ⟨1367758698309157492875799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7294713057648839962004261 1367758698309157492875799)
              ·
                refine ⟨2051638047463736239313699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1367758698309157492875799 2051638047463736239313699)
                ·
                  refine ⟨3077457071195604358970549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2051638047463736239313699 3077457071195604358970549)
                  ·
                    refine ⟨288511600424587908653489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3077457071195604358970549 288511600424587908653489)
                    ·
                      rfl

theorem cell23_1685623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_1685623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685623 prefixEnd_1685623 := by exact prefixLift 1685623
  have htrace : WordTrace (prefixWord ++ tailWord_1685623) baseStart_1685623 baseEnd_1685623 := by
    simpa [prefixWord, tailWord_1685623, baseEnd_1685623] using wordTrace_append hprefix tailTrace_1685623
  have hstable : (prefixWord ++ tailWord_1685623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685623).length < 2 ^ (prefixWord ++ tailWord_1685623).sum := by decide
  have hdescent : baseEnd_1685623 < baseStart_1685623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685626 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2]
def baseStart_1685626 : Nat := 118140960795 + 1685626 * 2 ^ 59
def prefixEnd_1685626 : Nat := 4983230072969 + 3 ^ 40 * 1685626 * 2
def baseEnd_1685626 : Nat := 865536341715727214222953

theorem tailTrace_1685626 : CollatzResearch.WordTrace tailWord_1685626 prefixEnd_1685626 865536341715727214222953 := by
  unfold tailWord_1685626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15369957747818089711613183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40986553994181572564301821 15369957747818089711613183)
  ·
    refine ⟨23054936621727134567419775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15369957747818089711613183 23054936621727134567419775)
    ·
      refine ⟨34582404932590701851129663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23054936621727134567419775 34582404932590701851129663)
      ·
        refine ⟨51873607398886052776694495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34582404932590701851129663 51873607398886052776694495)
        ·
          refine ⟨77810411098329079165041743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51873607398886052776694495 77810411098329079165041743)
          ·
            refine ⟨116715616647493618747562615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77810411098329079165041743 116715616647493618747562615)
            ·
              refine ⟨175073424971240428121343923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116715616647493618747562615 175073424971240428121343923)
              ·
                refine ⟨262610137456860642182015885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175073424971240428121343923 262610137456860642182015885)
                ·
                  refine ⟨98478801546322740818255957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 262610137456860642182015885 98478801546322740818255957)
                  ·
                    refine ⟨1154048455620969618963937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 98478801546322740818255957 1154048455620969618963937)
                    ·
                      refine ⟨865536341715727214222953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154048455620969618963937 865536341715727214222953)
                      ·
                        rfl

theorem cell23_1685626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 8, 2].length) (baseStart_1685626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685626 prefixEnd_1685626 := by exact prefixLift 1685626
  have htrace : WordTrace (prefixWord ++ tailWord_1685626) baseStart_1685626 baseEnd_1685626 := by
    simpa [prefixWord, tailWord_1685626, baseEnd_1685626] using wordTrace_append hprefix tailTrace_1685626
  have hstable : (prefixWord ++ tailWord_1685626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685626).length < 2 ^ (prefixWord ++ tailWord_1685626).sum := by decide
  have hdescent : baseEnd_1685626 < baseStart_1685626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685660 : List Nat := [2, 2, 3, 2, 1, 1, 1, 4, 3, 2, 2]
def baseStart_1685660 : Nat := 118140960795 + 1685660 * 2 ^ 59
def prefixEnd_1685660 : Nat := 4983230072969 + 3 ^ 40 * 1685660 * 2
def baseEnd_1685660 : Nat := 865553800057980081197797

theorem tailTrace_1685660 : CollatzResearch.WordTrace tailWord_1685660 prefixEnd_1685660 865553800057980081197797 := by
  unfold tailWord_1685660
  simp only [CollatzResearch.WordTrace]
  refine ⟨30740535536574591326595217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40987380715432788435460289 30740535536574591326595217)
  ·
    refine ⟨23055401652430943494946413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30740535536574591326595217 23055401652430943494946413)
    ·
      refine ⟨8645775619661603810604905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23055401652430943494946413 8645775619661603810604905)
      ·
        refine ⟨6484331714746202857953679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8645775619661603810604905 6484331714746202857953679)
        ·
          refine ⟨9726497572119304286930519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6484331714746202857953679 9726497572119304286930519)
          ·
            refine ⟨14589746358178956430395779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9726497572119304286930519 14589746358178956430395779)
            ·
              refine ⟨21884619537268434645593669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14589746358178956430395779 21884619537268434645593669)
              ·
                refine ⟨4103366163237831496048813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21884619537268434645593669 4103366163237831496048813)
                ·
                  refine ⟨1538762311214186811018305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4103366163237831496048813 1538762311214186811018305)
                  ·
                    refine ⟨1154071733410640108263729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1538762311214186811018305 1154071733410640108263729)
                    ·
                      refine ⟨865553800057980081197797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154071733410640108263729 865553800057980081197797)
                      ·
                        rfl

theorem cell23_1685660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 3, 2, 2].length) (baseStart_1685660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685660 prefixEnd_1685660 := by exact prefixLift 1685660
  have htrace : WordTrace (prefixWord ++ tailWord_1685660) baseStart_1685660 baseEnd_1685660 := by
    simpa [prefixWord, tailWord_1685660, baseEnd_1685660] using wordTrace_append hprefix tailTrace_1685660
  have hstable : (prefixWord ++ tailWord_1685660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685660).length < 2 ^ (prefixWord ++ tailWord_1685660).sum := by decide
  have hdescent : baseEnd_1685660 < baseStart_1685660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685671 : List Nat := [1, 1, 6, 2, 3, 1, 1, 3, 1, 1, 3]
def baseStart_1685671 : Nat := 118140960795 + 1685671 * 2 ^ 59
def prefixEnd_1685671 : Nat := 4983230072969 + 3 ^ 40 * 1685671 * 2
def baseEnd_1685671 : Nat := 865559448345179538160247

theorem tailTrace_1685671 : CollatzResearch.WordTrace tailWord_1685671 prefixEnd_1685671 865559448345179538160247 := by
  unfold tailWord_1685671
  simp only [CollatzResearch.WordTrace]
  refine ⟨61481472276109331531840867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40987648184072887687893911 61481472276109331531840867)
  ·
    refine ⟨92222208414163997297761301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61481472276109331531840867 92222208414163997297761301)
    ·
      refine ⟨4322916019413937373332561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 92222208414163997297761301 4322916019413937373332561)
      ·
        refine ⟨3242187014560453029999421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4322916019413937373332561 3242187014560453029999421)
        ·
          refine ⟨1215820130460169886249783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3242187014560453029999421 1215820130460169886249783)
          ·
            refine ⟨1823730195690254829374675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1215820130460169886249783 1823730195690254829374675)
            ·
              refine ⟨2735595293535382244062013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823730195690254829374675 2735595293535382244062013)
              ·
                refine ⟨1025848235075768341523255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2735595293535382244062013 1025848235075768341523255)
                ·
                  refine ⟨1538772352613652512284883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025848235075768341523255 1538772352613652512284883)
                  ·
                    refine ⟨2308158528920478768427325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1538772352613652512284883 2308158528920478768427325)
                    ·
                      refine ⟨865559448345179538160247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2308158528920478768427325 865559448345179538160247)
                      ·
                        rfl

theorem cell23_1685671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 3, 1, 1, 3, 1, 1, 3].length) (baseStart_1685671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685671 prefixEnd_1685671 := by exact prefixLift 1685671
  have htrace : WordTrace (prefixWord ++ tailWord_1685671) baseStart_1685671 baseEnd_1685671 := by
    simpa [prefixWord, tailWord_1685671, baseEnd_1685671] using wordTrace_append hprefix tailTrace_1685671
  have hstable : (prefixWord ++ tailWord_1685671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685671).length < 2 ^ (prefixWord ++ tailWord_1685671).sum := by decide
  have hdescent : baseEnd_1685671 < baseStart_1685671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685679 : List Nat := [1, 1, 2, 1, 2, 3, 1, 2, 1, 9]
def baseStart_1685679 : Nat := 118140960795 + 1685679 * 2 ^ 59
def prefixEnd_1685679 : Nat := 4983230072969 + 3 ^ 40 * 1685679 * 2
def baseEnd_1685679 : Nat := 288521185396805168953403

theorem tailTrace_1685679 : CollatzResearch.WordTrace tailWord_1685679 prefixEnd_1685679 288521185396805168953403 := by
  unfold tailWord_1685679
  simp only [CollatzResearch.WordTrace]
  refine ⟨61481764060080348898132091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40987842706720232598754727 61481764060080348898132091)
  ·
    refine ⟨92222646090120523347198137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61481764060080348898132091 92222646090120523347198137)
    ·
      refine ⟨69166984567590392510398603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92222646090120523347198137 69166984567590392510398603)
      ·
        refine ⟨103750476851385588765597905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69166984567590392510398603 103750476851385588765597905)
        ·
          refine ⟨77812857638539191574198429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103750476851385588765597905 77812857638539191574198429)
          ·
            refine ⟨29179821614452196840324411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77812857638539191574198429 29179821614452196840324411)
            ·
              refine ⟨43769732421678295260486617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29179821614452196840324411 43769732421678295260486617)
              ·
                refine ⟨32827299316258721445364963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43769732421678295260486617 32827299316258721445364963)
                ·
                  refine ⟨49240948974388082168047445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32827299316258721445364963 49240948974388082168047445)
                  ·
                    refine ⟨288521185396805168953403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49240948974388082168047445 288521185396805168953403)
                    ·
                      rfl

theorem cell23_1685679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 9].length) (baseStart_1685679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685679 prefixEnd_1685679 := by exact prefixLift 1685679
  have htrace : WordTrace (prefixWord ++ tailWord_1685679) baseStart_1685679 baseEnd_1685679 := by
    simpa [prefixWord, tailWord_1685679, baseEnd_1685679] using wordTrace_append hprefix tailTrace_1685679
  have hstable : (prefixWord ++ tailWord_1685679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685679).length < 2 ^ (prefixWord ++ tailWord_1685679).sum := by decide
  have hdescent : baseEnd_1685679 < baseStart_1685679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685694 : List Nat := [4, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2]
def baseStart_1685694 : Nat := 118140960795 + 1685694 * 2 ^ 59
def prefixEnd_1685694 : Nat := 4983230072969 + 3 ^ 40 * 1685694 * 2
def baseEnd_1685694 : Nat := 865571258400232948172641

theorem tailTrace_1685694 : CollatzResearch.WordTrace tailWord_1685694 prefixEnd_1685694 865571258400232948172641 := by
  unfold tailWord_1685694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7685288894378250807491017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40988207436684004306618757 7685288894378250807491017)
  ·
    refine ⟨5763966670783688105618263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7685288894378250807491017 5763966670783688105618263)
    ·
      refine ⟨8645950006175532158427395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5763966670783688105618263 8645950006175532158427395)
      ·
        refine ⟨12968925009263298237641093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8645950006175532158427395 12968925009263298237641093)
        ·
          refine ⟨2431673439236868419557705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12968925009263298237641093 2431673439236868419557705)
          ·
            refine ⟨1823755079427651314668279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2431673439236868419557705 1823755079427651314668279)
            ·
              refine ⟨2735632619141476972002419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1823755079427651314668279 2735632619141476972002419)
              ·
                refine ⟨4103448928712215458003629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2735632619141476972002419 4103448928712215458003629)
                ·
                  refine ⟨1538793348267080796751361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4103448928712215458003629 1538793348267080796751361)
                  ·
                    refine ⟨1154095011200310597563521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1538793348267080796751361 1154095011200310597563521)
                    ·
                      refine ⟨865571258400232948172641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154095011200310597563521 865571258400232948172641)
                      ·
                        rfl

theorem cell23_1685694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 2, 1, 1, 3, 2, 2].length) (baseStart_1685694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685694 prefixEnd_1685694 := by exact prefixLift 1685694
  have htrace : WordTrace (prefixWord ++ tailWord_1685694) baseStart_1685694 baseEnd_1685694 := by
    simpa [prefixWord, tailWord_1685694, baseEnd_1685694] using wordTrace_append hprefix tailTrace_1685694
  have hstable : (prefixWord ++ tailWord_1685694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685694).length < 2 ^ (prefixWord ++ tailWord_1685694).sum := by decide
  have hdescent : baseEnd_1685694 < baseStart_1685694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685699 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10]
def baseStart_1685699 : Nat := 118140960795 + 1685699 * 2 ^ 59
def prefixEnd_1685699 : Nat := 4983230072969 + 3 ^ 40 * 1685699 * 2
def baseEnd_1685699 : Nat := 865573825803505428610117

theorem tailTrace_1685699 : CollatzResearch.WordTrace tailWord_1685699 prefixEnd_1685699 865573825803505428610117 := by
  unfold tailWord_1685699
  simp only [CollatzResearch.WordTrace]
  refine ⟨61482493520007892313860151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40988329013338594875906767 61482493520007892313860151)
  ·
    refine ⟨92223740280011838470790227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61482493520007892313860151 92223740280011838470790227)
    ·
      refine ⟨138335610420017757706185341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92223740280011838470790227 138335610420017757706185341)
      ·
        refine ⟨51875853907506659139819503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138335610420017757706185341 51875853907506659139819503)
        ·
          refine ⟨77813780861259988709729255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51875853907506659139819503 77813780861259988709729255)
          ·
            refine ⟨116720671291889983064593883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77813780861259988709729255 116720671291889983064593883)
            ·
              refine ⟨175081006937834974596890825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116720671291889983064593883 175081006937834974596890825)
              ·
                refine ⟨131310755203376230947668119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175081006937834974596890825 131310755203376230947668119)
                ·
                  refine ⟨196966132805064346421502179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 131310755203376230947668119 196966132805064346421502179)
                  ·
                    refine ⟨295449199207596519632253269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 196966132805064346421502179 295449199207596519632253269)
                    ·
                      refine ⟨865573825803505428610117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 295449199207596519632253269 865573825803505428610117)
                      ·
                        rfl

theorem cell23_1685699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_1685699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685699 prefixEnd_1685699 := by exact prefixLift 1685699
  have htrace : WordTrace (prefixWord ++ tailWord_1685699) baseStart_1685699 baseEnd_1685699 := by
    simpa [prefixWord, tailWord_1685699, baseEnd_1685699] using wordTrace_append hprefix tailTrace_1685699
  have hstable : (prefixWord ++ tailWord_1685699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685699).length < 2 ^ (prefixWord ++ tailWord_1685699).sum := by decide
  have hdescent : baseEnd_1685699 < baseStart_1685699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685720 : List Nat := [2, 1, 2, 2, 4, 2, 1, 1, 3, 3, 2]
def baseStart_1685720 : Nat := 118140960795 + 1685720 * 2 ^ 59
def prefixEnd_1685720 : Nat := 4983230072969 + 3 ^ 40 * 1685720 * 2
def baseEnd_1685720 : Nat := 865584608897249846447521

theorem tailTrace_1685720 : CollatzResearch.WordTrace tailWord_1685720 prefixEnd_1685720 865584608897249846447521 := by
  unfold tailWord_1685720
  simp only [CollatzResearch.WordTrace]
  refine ⟨30741629726465906450187307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40988839635287875266916409 30741629726465906450187307)
  ·
    refine ⟨46112444589698859675280961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30741629726465906450187307 46112444589698859675280961)
    ·
      refine ⟨34584333442274144756460721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46112444589698859675280961 34584333442274144756460721)
      ·
        refine ⟨25938250081705608567345541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34584333442274144756460721 25938250081705608567345541)
        ·
          refine ⟨4863421890319801606377289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25938250081705608567345541 4863421890319801606377289)
          ·
            refine ⟨3647566417739851204782967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4863421890319801606377289 3647566417739851204782967)
            ·
              refine ⟨5471349626609776807174451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3647566417739851204782967 5471349626609776807174451)
              ·
                refine ⟨8207024439914665210761677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471349626609776807174451 8207024439914665210761677)
                ·
                  refine ⟨3077634164967999454035629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8207024439914665210761677 3077634164967999454035629)
                  ·
                    refine ⟨1154112811862999795263361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3077634164967999454035629 1154112811862999795263361)
                    ·
                      refine ⟨865584608897249846447521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154112811862999795263361 865584608897249846447521)
                      ·
                        rfl

theorem cell23_1685720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 1, 1, 3, 3, 2].length) (baseStart_1685720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685720 prefixEnd_1685720 := by exact prefixLift 1685720
  have htrace : WordTrace (prefixWord ++ tailWord_1685720) baseStart_1685720 baseEnd_1685720 := by
    simpa [prefixWord, tailWord_1685720, baseEnd_1685720] using wordTrace_append hprefix tailTrace_1685720
  have hstable : (prefixWord ++ tailWord_1685720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685720).length < 2 ^ (prefixWord ++ tailWord_1685720).sum := by decide
  have hdescent : baseEnd_1685720 < baseStart_1685720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685860 : List Nat := [2, 3, 1, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_1685860 : Nat := 118140960795 + 1685860 * 2 ^ 59
def prefixEnd_1685860 : Nat := 4983230072969 + 3 ^ 40 * 1685860 * 2
def baseEnd_1685860 : Nat := 865656496188879298696877

theorem tailTrace_1685860 : CollatzResearch.WordTrace tailWord_1685860 prefixEnd_1685860 865656496188879298696877 := by
  unfold tailWord_1685860
  simp only [CollatzResearch.WordTrace]
  refine ⟨30744182836212308405235517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40992243781616411206980689 30744182836212308405235517)
  ·
    refine ⟨11529068563579615651963319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30744182836212308405235517 11529068563579615651963319)
    ·
      refine ⟨17293602845369423477944979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11529068563579615651963319 17293602845369423477944979)
      ·
        refine ⟨25940404268054135216917469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17293602845369423477944979 25940404268054135216917469)
        ·
          refine ⟨9727651600520300706344051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25940404268054135216917469 9727651600520300706344051)
          ·
            refine ⟨14591477400780451059516077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9727651600520300706344051 14591477400780451059516077)
            ·
              refine ⟨5471804025292669147318529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14591477400780451059516077 5471804025292669147318529)
              ·
                refine ⟨4103853018969501860488897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5471804025292669147318529 4103853018969501860488897)
                ·
                  refine ⟨3077889764227126395366673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4103853018969501860488897 3077889764227126395366673)
                  ·
                    refine ⟨2308417323170344796525005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3077889764227126395366673 2308417323170344796525005)
                    ·
                      refine ⟨865656496188879298696877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2308417323170344796525005 865656496188879298696877)
                      ·
                        rfl

theorem cell23_1685860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_1685860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685860 prefixEnd_1685860 := by exact prefixLift 1685860
  have htrace : WordTrace (prefixWord ++ tailWord_1685860) baseStart_1685860 baseEnd_1685860 := by
    simpa [prefixWord, tailWord_1685860, baseEnd_1685860] using wordTrace_append hprefix tailTrace_1685860
  have hstable : (prefixWord ++ tailWord_1685860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685860).length < 2 ^ (prefixWord ++ tailWord_1685860).sum := by decide
  have hdescent : baseEnd_1685860 < baseStart_1685860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685863 : List Nat := [1, 1, 5, 1, 3, 1, 2, 1, 8]
def baseStart_1685863 : Nat := 118140960795 + 1685863 * 2 ^ 59
def prefixEnd_1685863 : Nat := 4983230072969 + 3 ^ 40 * 1685863 * 2
def baseEnd_1685863 : Nat := 96184226292315865217707

theorem tailTrace_1685863 : CollatzResearch.WordTrace tailWord_1685863 prefixEnd_1685863 96184226292315865217707 := by
  unfold tailWord_1685863
  simp only [CollatzResearch.WordTrace]
  refine ⟨61488475091413748322830243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40992316727609165548553495 61488475091413748322830243)
  ·
    refine ⟨92232712637120622484245365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61488475091413748322830243 92232712637120622484245365)
    ·
      refine ⟨8646816809730058357898003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92232712637120622484245365 8646816809730058357898003)
      ·
        refine ⟨12970225214595087536847005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8646816809730058357898003 12970225214595087536847005)
        ·
          refine ⟨4863834455473157826317627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12970225214595087536847005 4863834455473157826317627)
          ·
            refine ⟨7295751683209736739476441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4863834455473157826317627 7295751683209736739476441)
            ·
              refine ⟨5471813762407302554607331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7295751683209736739476441 5471813762407302554607331)
              ·
                refine ⟨8207720643610953831910997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5471813762407302554607331 8207720643610953831910997)
                ·
                  refine ⟨96184226292315865217707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8207720643610953831910997 96184226292315865217707)
                  ·
                    rfl

theorem cell23_1685863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 8].length) (baseStart_1685863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685863 prefixEnd_1685863 := by exact prefixLift 1685863
  have htrace : WordTrace (prefixWord ++ tailWord_1685863) baseStart_1685863 baseEnd_1685863 := by
    simpa [prefixWord, tailWord_1685863, baseEnd_1685863] using wordTrace_append hprefix tailTrace_1685863
  have hstable : (prefixWord ++ tailWord_1685863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685863).length < 2 ^ (prefixWord ++ tailWord_1685863).sum := by decide
  have hdescent : baseEnd_1685863 < baseStart_1685863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685918 : List Nat := [4, 3, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1685918 : Nat := 118140960795 + 1685918 * 2 ^ 59
def prefixEnd_1685918 : Nat := 4983230072969 + 3 ^ 40 * 1685918 * 2
def baseEnd_1685918 : Nat := 288562092688946690590537

theorem tailTrace_1685918 : CollatzResearch.WordTrace tailWord_1685918 prefixEnd_1685918 288562092688946690590537 := by
  unfold tailWord_1685918
  simp only [CollatzResearch.WordTrace]
  refine ⟨7686310138276811589510301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40993654070809661810721605 7686310138276811589510301)
  ·
    refine ⟨2882366301853804346066363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7686310138276811589510301 2882366301853804346066363)
    ·
      refine ⟨4323549452780706519099545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882366301853804346066363 4323549452780706519099545)
      ·
        refine ⟨3242662089585529889324659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4323549452780706519099545 3242662089585529889324659)
        ·
          refine ⟨4863993134378294833986989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3242662089585529889324659 4863993134378294833986989)
          ·
            refine ⟨1823997425391860562745121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4863993134378294833986989 1823997425391860562745121)
            ·
              refine ⟨1367998069043895422058841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1823997425391860562745121 1367998069043895422058841)
              ·
                refine ⟨1025998551782921566544131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1367998069043895422058841 1025998551782921566544131)
                ·
                  refine ⟨1538997827674382349816197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1025998551782921566544131 1538997827674382349816197)
                  ·
                    refine ⟨288562092688946690590537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1538997827674382349816197 288562092688946690590537)
                    ·
                      rfl

theorem cell23_1685918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1685918 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685918 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685918 prefixEnd_1685918 := by exact prefixLift 1685918
  have htrace : WordTrace (prefixWord ++ tailWord_1685918) baseStart_1685918 baseEnd_1685918 := by
    simpa [prefixWord, tailWord_1685918, baseEnd_1685918] using wordTrace_append hprefix tailTrace_1685918
  have hstable : (prefixWord ++ tailWord_1685918).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685918).length < 2 ^ (prefixWord ++ tailWord_1685918).sum := by decide
  have hdescent : baseEnd_1685918 < baseStart_1685918 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685960 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1685960 : Nat := 118140960795 + 1685960 * 2 ^ 59
def prefixEnd_1685960 : Nat := 4983230072969 + 3 ^ 40 * 1685960 * 2
def baseEnd_1685960 : Nat := 865707844254328907446417

theorem tailTrace_1685960 : CollatzResearch.WordTrace tailWord_1685960 prefixEnd_1685960 865707844254328907446417 := by
  unfold tailWord_1685960
  simp only [CollatzResearch.WordTrace]
  refine ⟨30746006486031166944555667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40994675314708222592740889 30746006486031166944555667)
  ·
    refine ⟨46119009729046750416833501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30746006486031166944555667 46119009729046750416833501)
    ·
      refine ⟨17294628648392531406312563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46119009729046750416833501 17294628648392531406312563)
      ·
        refine ⟨25941942972588797109468845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17294628648392531406312563 25941942972588797109468845)
        ·
          refine ⟨9728228614720798916050817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25941942972588797109468845 9728228614720798916050817)
          ·
            refine ⟨7296171461040599187038113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9728228614720798916050817 7296171461040599187038113)
            ·
              refine ⟨5472128595780449390278585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7296171461040599187038113 5472128595780449390278585)
              ·
                refine ⟨4104096446835337042708939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5472128595780449390278585 4104096446835337042708939)
                ·
                  refine ⟨6156144670253005564063409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104096446835337042708939 6156144670253005564063409)
                  ·
                    refine ⟨4617108502689754173047557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6156144670253005564063409 4617108502689754173047557)
                    ·
                      refine ⟨865707844254328907446417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4617108502689754173047557 865707844254328907446417)
                      ·
                        rfl

theorem cell23_1685960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1685960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685960 prefixEnd_1685960 := by exact prefixLift 1685960
  have htrace : WordTrace (prefixWord ++ tailWord_1685960) baseStart_1685960 baseEnd_1685960 := by
    simpa [prefixWord, tailWord_1685960, baseEnd_1685960] using wordTrace_append hprefix tailTrace_1685960
  have hstable : (prefixWord ++ tailWord_1685960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685960).length < 2 ^ (prefixWord ++ tailWord_1685960).sum := by decide
  have hdescent : baseEnd_1685960 < baseStart_1685960 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1685981 : List Nat := [1, 4, 3, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_1685981 : Nat := 118140960795 + 1685981 * 2 ^ 59
def prefixEnd_1685981 : Nat := 4983230072969 + 3 ^ 40 * 1685981 * 2
def baseEnd_1685981 : Nat := 865718627348073325283821

theorem tailTrace_1685981 : CollatzResearch.WordTrace tailWord_1685981 prefixEnd_1685981 865718627348073325283821 := by
  unfold tailWord_1685981
  simp only [CollatzResearch.WordTrace]
  refine ⟨61492778904986254475625797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40995185936657502983750531 61492778904986254475625797)
  ·
    refine ⟨11529896044684922714179837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61492778904986254475625797 11529896044684922714179837)
    ·
      refine ⟨4323711016756846017817439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11529896044684922714179837 4323711016756846017817439)
      ·
        refine ⟨6485566525135269026726159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4323711016756846017817439 6485566525135269026726159)
        ·
          refine ⟨9728349787702903540089239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6485566525135269026726159 9728349787702903540089239)
          ·
            refine ⟨14592524681554355310133859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9728349787702903540089239 14592524681554355310133859)
            ·
              refine ⟨21888787022331532965200789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14592524681554355310133859 21888787022331532965200789)
              ·
                refine ⟨1026036891671790607743787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21888787022331532965200789 1026036891671790607743787)
                ·
                  refine ⟨1539055337507685911615681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026036891671790607743787 1539055337507685911615681)
                  ·
                    refine ⟨1154291503130764433711761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1539055337507685911615681 1154291503130764433711761)
                    ·
                      refine ⟨865718627348073325283821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154291503130764433711761 865718627348073325283821)
                      ·
                        rfl

theorem cell23_1685981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_1685981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1685981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1685981 prefixEnd_1685981 := by exact prefixLift 1685981
  have htrace : WordTrace (prefixWord ++ tailWord_1685981) baseStart_1685981 baseEnd_1685981 := by
    simpa [prefixWord, tailWord_1685981, baseEnd_1685981] using wordTrace_append hprefix tailTrace_1685981
  have hstable : (prefixWord ++ tailWord_1685981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1685981).length < 2 ^ (prefixWord ++ tailWord_1685981).sum := by decide
  have hdescent : baseEnd_1685981 < baseStart_1685981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1685981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686033 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 6]
def baseStart_1686033 : Nat := 118140960795 + 1686033 * 2 ^ 59
def prefixEnd_1686033 : Nat := 4983230072969 + 3 ^ 40 * 1686033 * 2
def baseEnd_1686033 : Nat := 865745328342107121833581

theorem tailTrace_1686033 : CollatzResearch.WordTrace tailWord_1686033 prefixEnd_1686033 865745328342107121833581 := by
  unfold tailWord_1686033
  simp only [CollatzResearch.WordTrace]
  refine ⟨61494675500797867356518753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40996450333865244904345835 61494675500797867356518753)
  ·
    refine ⟨46121006625598400517389065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61494675500797867356518753 46121006625598400517389065)
    ·
      refine ⟨34590754969198800388041799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46121006625598400517389065 34590754969198800388041799)
      ·
        refine ⟨51886132453798200582062699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34590754969198800388041799 51886132453798200582062699)
        ·
          refine ⟨77829198680697300873094049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51886132453798200582062699 77829198680697300873094049)
          ·
            refine ⟨58371899010522975654820537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77829198680697300873094049 58371899010522975654820537)
            ·
              refine ⟨43778924257892231741115403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58371899010522975654820537 43778924257892231741115403)
              ·
                refine ⟨65668386386838347611673105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43778924257892231741115403 65668386386838347611673105)
                ·
                  refine ⟨49251289790128760708754829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65668386386838347611673105 49251289790128760708754829)
                  ·
                    refine ⟨18469233671298285265783061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49251289790128760708754829 18469233671298285265783061)
                    ·
                      refine ⟨865745328342107121833581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18469233671298285265783061 865745328342107121833581)
                      ·
                        rfl

theorem cell23_1686033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 6].length) (baseStart_1686033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686033 prefixEnd_1686033 := by exact prefixLift 1686033
  have htrace : WordTrace (prefixWord ++ tailWord_1686033) baseStart_1686033 baseEnd_1686033 := by
    simpa [prefixWord, tailWord_1686033, baseEnd_1686033] using wordTrace_append hprefix tailTrace_1686033
  have hstable : (prefixWord ++ tailWord_1686033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686033).length < 2 ^ (prefixWord ++ tailWord_1686033).sum := by decide
  have hdescent : baseEnd_1686033 < baseStart_1686033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686048 : List Nat := [2, 1, 1, 6, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1686048 : Nat := 118140960795 + 1686048 * 2 ^ 59
def prefixEnd_1686048 : Nat := 4983230072969 + 3 ^ 40 * 1686048 * 2
def baseEnd_1686048 : Nat := 865753030551924563146013

theorem tailTrace_1686048 : CollatzResearch.WordTrace tailWord_1686048 prefixEnd_1686048 865753030551924563146013 := by
  unfold tailWord_1686048
  simp only [CollatzResearch.WordTrace]
  refine ⟨30747611297871762459157399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40996815063829016612209865 30747611297871762459157399)
  ·
    refine ⟨46121416946807643688736099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30747611297871762459157399 46121416946807643688736099)
    ·
      refine ⟨69182125420211465533104149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46121416946807643688736099 69182125420211465533104149)
      ·
        refine ⟨3242912129072412446864257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 69182125420211465533104149 3242912129072412446864257)
        ·
          refine ⟨2432184096804309335148193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3242912129072412446864257 2432184096804309335148193)
          ·
            refine ⟨1824138072603232001361145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2432184096804309335148193 1824138072603232001361145)
            ·
              refine ⟨1368103554452424001020859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824138072603232001361145 1368103554452424001020859)
              ·
                refine ⟨2052155331678636001531289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368103554452424001020859 2052155331678636001531289)
                ·
                  refine ⟨1539116498758977001148467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2052155331678636001531289 1539116498758977001148467)
                  ·
                    refine ⟨2308674748138465501722701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1539116498758977001148467 2308674748138465501722701)
                    ·
                      refine ⟨865753030551924563146013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2308674748138465501722701 865753030551924563146013)
                      ·
                        rfl

theorem cell23_1686048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1686048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686048 prefixEnd_1686048 := by exact prefixLift 1686048
  have htrace : WordTrace (prefixWord ++ tailWord_1686048) baseStart_1686048 baseEnd_1686048 := by
    simpa [prefixWord, tailWord_1686048, baseEnd_1686048] using wordTrace_append hprefix tailTrace_1686048
  have hstable : (prefixWord ++ tailWord_1686048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686048).length < 2 ^ (prefixWord ++ tailWord_1686048).sum := by decide
  have hdescent : baseEnd_1686048 < baseStart_1686048 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686050 : List Nat := [3, 3, 1, 1, 1, 1, 1, 3, 1, 4, 4]
def baseStart_1686050 : Nat := 118140960795 + 1686050 * 2 ^ 59
def prefixEnd_1686050 : Nat := 4983230072969 + 3 ^ 40 * 1686050 * 2
def baseEnd_1686050 : Nat := 865754057513233555321003

theorem tailTrace_1686050 : CollatzResearch.WordTrace tailWord_1686050 prefixEnd_1686050 865754057513233555321003 := by
  unfold tailWord_1686050
  simp only [CollatzResearch.WordTrace]
  refine ⟨15373823885434069814971901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 40996863694490852839925069 15373823885434069814971901)
  ·
    refine ⟨5765183957037776180614463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15373823885434069814971901 5765183957037776180614463)
    ·
      refine ⟨8647775935556664270921695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5765183957037776180614463 8647775935556664270921695)
      ·
        refine ⟨12971663903334996406382543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8647775935556664270921695 12971663903334996406382543)
        ·
          refine ⟨19457495855002494609573815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12971663903334996406382543 19457495855002494609573815)
          ·
            refine ⟨29186243782503741914360723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19457495855002494609573815 29186243782503741914360723)
            ·
              refine ⟨43779365673755612871541085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29186243782503741914360723 43779365673755612871541085)
              ·
                refine ⟨16417262127658354826827907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43779365673755612871541085 16417262127658354826827907)
                ·
                  refine ⟨24625893191487532240241861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16417262127658354826827907 24625893191487532240241861)
                  ·
                    refine ⟨4617354973403912295045349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24625893191487532240241861 4617354973403912295045349)
                    ·
                      refine ⟨865754057513233555321003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4617354973403912295045349 865754057513233555321003)
                      ·
                        rfl

theorem cell23_1686050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 3, 1, 4, 4].length) (baseStart_1686050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686050 prefixEnd_1686050 := by exact prefixLift 1686050
  have htrace : WordTrace (prefixWord ++ tailWord_1686050) baseStart_1686050 baseEnd_1686050 := by
    simpa [prefixWord, tailWord_1686050, baseEnd_1686050] using wordTrace_append hprefix tailTrace_1686050
  have hstable : (prefixWord ++ tailWord_1686050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686050).length < 2 ^ (prefixWord ++ tailWord_1686050).sum := by decide
  have hdescent : baseEnd_1686050 < baseStart_1686050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686063 : List Nat := [1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 8]
def baseStart_1686063 : Nat := 118140960795 + 1686063 * 2 ^ 59
def prefixEnd_1686063 : Nat := 4983230072969 + 3 ^ 40 * 1686063 * 2
def baseEnd_1686063 : Nat := 865760732761742004458443

theorem tailTrace_1686063 : CollatzResearch.WordTrace tailWord_1686063 prefixEnd_1686063 865760732761742004458443 := by
  unfold tailWord_1686063
  simp only [CollatzResearch.WordTrace]
  refine ⟨61495769690689182480110843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40997179793792788320073895 61495769690689182480110843)
  ·
    refine ⟨92243654536033773720166265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61495769690689182480110843 92243654536033773720166265)
    ·
      refine ⟨69182740902025330290124699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92243654536033773720166265 69182740902025330290124699)
      ·
        refine ⟨103774111353037995435187049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69182740902025330290124699 103774111353037995435187049)
        ·
          refine ⟨77830583514778496576390287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103774111353037995435187049 77830583514778496576390287)
          ·
            refine ⟨116745875272167744864585431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77830583514778496576390287 116745875272167744864585431)
            ·
              refine ⟨175118812908251617296878147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116745875272167744864585431 175118812908251617296878147)
              ·
                refine ⟨262678219362377425945317221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175118812908251617296878147 262678219362377425945317221)
                ·
                  refine ⟨49252166130445767364746979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 262678219362377425945317221 49252166130445767364746979)
                  ·
                    refine ⟨73878249195668651047120469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49252166130445767364746979 73878249195668651047120469)
                    ·
                      refine ⟨865760732761742004458443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 73878249195668651047120469 865760732761742004458443)
                      ·
                        rfl

theorem cell23_1686063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 4, 1, 8].length) (baseStart_1686063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686063 prefixEnd_1686063 := by exact prefixLift 1686063
  have htrace : WordTrace (prefixWord ++ tailWord_1686063) baseStart_1686063 baseEnd_1686063 := by
    simpa [prefixWord, tailWord_1686063, baseEnd_1686063] using wordTrace_append hprefix tailTrace_1686063
  have hstable : (prefixWord ++ tailWord_1686063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686063).length < 2 ^ (prefixWord ++ tailWord_1686063).sum := by decide
  have hdescent : baseEnd_1686063 < baseStart_1686063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686094 : List Nat := [4, 1, 1, 1, 1, 2, 6, 2, 5]
def baseStart_1686094 : Nat := 118140960795 + 1686094 * 2 ^ 59
def prefixEnd_1686094 : Nat := 4983230072969 + 3 ^ 40 * 1686094 * 2
def baseEnd_1686094 : Nat := 96197405629114598130089

theorem tailTrace_1686094 : CollatzResearch.WordTrace tailWord_1686094 prefixEnd_1686094 96197405629114598130089 := by
  unfold tailWord_1686094
  simp only [CollatzResearch.WordTrace]
  refine ⟨7687112544197109346811167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 40997933569051249849659557 7687112544197109346811167)
  ·
    refine ⟨11530668816295664020216751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7687112544197109346811167 11530668816295664020216751)
    ·
      refine ⟨17296003224443496030325127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11530668816295664020216751 17296003224443496030325127)
      ·
        refine ⟨25944004836665244045487691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17296003224443496030325127 25944004836665244045487691)
        ·
          refine ⟨38916007254997866068231537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25944004836665244045487691 38916007254997866068231537)
          ·
            refine ⟨29187005441248399551173653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38916007254997866068231537 29187005441248399551173653)
            ·
              refine ⟨1368140880058518728961265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 29187005441248399551173653 1368140880058518728961265)
              ·
                refine ⟨1026105660043889046720949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368140880058518728961265 1026105660043889046720949)
                ·
                  refine ⟨96197405629114598130089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1026105660043889046720949 96197405629114598130089)
                  ·
                    rfl

theorem cell23_1686094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 6, 2, 5].length) (baseStart_1686094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686094 prefixEnd_1686094 := by exact prefixLift 1686094
  have htrace : WordTrace (prefixWord ++ tailWord_1686094) baseStart_1686094 baseEnd_1686094 := by
    simpa [prefixWord, tailWord_1686094, baseEnd_1686094] using wordTrace_append hprefix tailTrace_1686094
  have hstable : (prefixWord ++ tailWord_1686094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686094).length < 2 ^ (prefixWord ++ tailWord_1686094).sum := by decide
  have hdescent : baseEnd_1686094 < baseStart_1686094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686097 : List Nat := [1, 2, 2, 1, 3, 3, 1, 1, 2, 5, 2]
def baseStart_1686097 : Nat := 118140960795 + 1686097 * 2 ^ 59
def prefixEnd_1686097 : Nat := 4983230072969 + 3 ^ 40 * 1686097 * 2
def baseEnd_1686097 : Nat := 865778191103994871433287

theorem tailTrace_1686097 : CollatzResearch.WordTrace tailWord_1686097 prefixEnd_1686097 865778191103994871433287 := by
  unfold tailWord_1686097
  simp only [CollatzResearch.WordTrace]
  refine ⟨61497009772566006286848545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40998006515044004191232363 61497009772566006286848545)
  ·
    refine ⟨46122757329424504715136409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61497009772566006286848545 46122757329424504715136409)
    ·
      refine ⟨34592067997068378536352307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46122757329424504715136409 34592067997068378536352307)
      ·
        refine ⟨51888101995602567804528461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34592067997068378536352307 51888101995602567804528461)
        ·
          refine ⟨19458038248350962926698173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51888101995602567804528461 19458038248350962926698173)
          ·
            refine ⟨7296764343131611097511815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19458038248350962926698173 7296764343131611097511815)
            ·
              refine ⟨10945146514697416646267723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7296764343131611097511815 10945146514697416646267723)
              ·
                refine ⟨16417719772046124969401585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945146514697416646267723 16417719772046124969401585)
                ·
                  refine ⟨12313289829034593727051189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16417719772046124969401585 12313289829034593727051189)
                  ·
                    refine ⟨1154370921471993161911049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12313289829034593727051189 1154370921471993161911049)
                    ·
                      refine ⟨865778191103994871433287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154370921471993161911049 865778191103994871433287)
                      ·
                        rfl

theorem cell23_1686097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 1, 1, 2, 5, 2].length) (baseStart_1686097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686097 prefixEnd_1686097 := by exact prefixLift 1686097
  have htrace : WordTrace (prefixWord ++ tailWord_1686097) baseStart_1686097 baseEnd_1686097 := by
    simpa [prefixWord, tailWord_1686097, baseEnd_1686097] using wordTrace_append hprefix tailTrace_1686097
  have hstable : (prefixWord ++ tailWord_1686097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686097).length < 2 ^ (prefixWord ++ tailWord_1686097).sum := by decide
  have hdescent : baseEnd_1686097 < baseStart_1686097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686127 : List Nat := [1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 4]
def baseStart_1686127 : Nat := 118140960795 + 1686127 * 2 ^ 59
def prefixEnd_1686127 : Nat := 4983230072969 + 3 ^ 40 * 1686127 * 2
def baseEnd_1686127 : Nat := 865793595523629754058149

theorem tailTrace_1686127 : CollatzResearch.WordTrace tailWord_1686127 prefixEnd_1686127 865793595523629754058149 := by
  unfold tailWord_1686127
  simp only [CollatzResearch.WordTrace]
  refine ⟨61498103962457321410440635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40998735974971547606960423 61498103962457321410440635)
  ·
    refine ⟨92247155943685982115660953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61498103962457321410440635 92247155943685982115660953)
    ·
      refine ⟨69185366957764486586745715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92247155943685982115660953 69185366957764486586745715)
      ·
        refine ⟨103778050436646729880118573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69185366957764486586745715 103778050436646729880118573)
        ·
          refine ⟨38916768913742523705044465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103778050436646729880118573 38916768913742523705044465)
          ·
            refine ⟨29187576685306892778783349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38916768913742523705044465 29187576685306892778783349)
            ·
              refine ⟨2736335314247521198010939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29187576685306892778783349 2736335314247521198010939)
              ·
                refine ⟨4104502971371281797016409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736335314247521198010939 4104502971371281797016409)
                ·
                  refine ⟨3078377228528461347762307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4104502971371281797016409 3078377228528461347762307)
                  ·
                    refine ⟨4617565842792692021643461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3078377228528461347762307 4617565842792692021643461)
                    ·
                      refine ⟨865793595523629754058149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4617565842792692021643461 865793595523629754058149)
                      ·
                        rfl

theorem cell23_1686127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 4].length) (baseStart_1686127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686127 prefixEnd_1686127 := by exact prefixLift 1686127
  have htrace : WordTrace (prefixWord ++ tailWord_1686127) baseStart_1686127 baseEnd_1686127 := by
    simpa [prefixWord, tailWord_1686127, baseEnd_1686127] using wordTrace_append hprefix tailTrace_1686127
  have hstable : (prefixWord ++ tailWord_1686127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686127).length < 2 ^ (prefixWord ++ tailWord_1686127).sum := by decide
  have hdescent : baseEnd_1686127 < baseStart_1686127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686140 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 2, 1, 6]
def baseStart_1686140 : Nat := 118140960795 + 1686140 * 2 ^ 59
def prefixEnd_1686140 : Nat := 4983230072969 + 3 ^ 40 * 1686140 * 2
def baseEnd_1686140 : Nat := 865800270772138203195589

theorem tailTrace_1686140 : CollatzResearch.WordTrace tailWord_1686140 prefixEnd_1686140 865800270772138203195589 := by
  unfold tailWord_1686140
  simp only [CollatzResearch.WordTrace]
  refine ⟨30749289055705112315331937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40999052074273483087109249 30749289055705112315331937)
  ·
    refine ⟨23061966791778834236498953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30749289055705112315331937 23061966791778834236498953)
    ·
      refine ⟨17296475093834125677374215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23061966791778834236498953 17296475093834125677374215)
      ·
        refine ⟨25944712640751188516061323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17296475093834125677374215 25944712640751188516061323)
        ·
          refine ⟨38917068961126782774091985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25944712640751188516061323 38917068961126782774091985)
          ·
            refine ⟨29187801720845087080568989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38917068961126782774091985 29187801720845087080568989)
            ·
              refine ⟨10945425645316907655213371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29187801720845087080568989 10945425645316907655213371)
              ·
                refine ⟨16418138467975361482820057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10945425645316907655213371 16418138467975361482820057)
                ·
                  refine ⟨12313603850981521112115043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16418138467975361482820057 12313603850981521112115043)
                  ·
                    refine ⟨18470405776472281668172565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12313603850981521112115043 18470405776472281668172565)
                    ·
                      refine ⟨865800270772138203195589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18470405776472281668172565 865800270772138203195589)
                      ·
                        rfl

theorem cell23_1686140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 2, 1, 6].length) (baseStart_1686140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686140 prefixEnd_1686140 := by exact prefixLift 1686140
  have htrace : WordTrace (prefixWord ++ tailWord_1686140) baseStart_1686140 baseEnd_1686140 := by
    simpa [prefixWord, tailWord_1686140, baseEnd_1686140] using wordTrace_append hprefix tailTrace_1686140
  have hstable : (prefixWord ++ tailWord_1686140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686140).length < 2 ^ (prefixWord ++ tailWord_1686140).sum := by decide
  have hdescent : baseEnd_1686140 < baseStart_1686140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686147 : List Nat := [1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 3]
def baseStart_1686147 : Nat := 118140960795 + 1686147 * 2 ^ 59
def prefixEnd_1686147 : Nat := 4983230072969 + 3 ^ 40 * 1686147 * 2
def baseEnd_1686147 : Nat := 865803865136719675808057

theorem tailTrace_1686147 : CollatzResearch.WordTrace tailWord_1686147 prefixEnd_1686147 865803865136719675808057 := by
  unfold tailWord_1686147
  simp only [CollatzResearch.WordTrace]
  refine ⟨61498833422384864826168695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 40999222281589909884112463 61498833422384864826168695)
  ·
    refine ⟨92248250133577297239253043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61498833422384864826168695 92248250133577297239253043)
    ·
      refine ⟨138372375200365945858879565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92248250133577297239253043 138372375200365945858879565)
      ·
        refine ⟨51889640700137229697079837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138372375200365945858879565 51889640700137229697079837)
        ·
          refine ⟨19458615262551461136404939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51889640700137229697079837 19458615262551461136404939)
          ·
            refine ⟨29187922893827191704607409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19458615262551461136404939 29187922893827191704607409)
            ·
              refine ⟨21890942170370393778455557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29187922893827191704607409 21890942170370393778455557)
              ·
                refine ⟨4104551656944448833460417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21890942170370393778455557 4104551656944448833460417)
                ·
                  refine ⟨3078413742708336625095313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4104551656944448833460417 3078413742708336625095313)
                  ·
                    refine ⟨2308810307031252468821485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3078413742708336625095313 2308810307031252468821485)
                    ·
                      refine ⟨865803865136719675808057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2308810307031252468821485 865803865136719675808057)
                      ·
                        rfl

theorem cell23_1686147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 4, 2, 2, 3].length) (baseStart_1686147 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686147 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686147 prefixEnd_1686147 := by exact prefixLift 1686147
  have htrace : WordTrace (prefixWord ++ tailWord_1686147) baseStart_1686147 baseEnd_1686147 := by
    simpa [prefixWord, tailWord_1686147, baseEnd_1686147] using wordTrace_append hprefix tailTrace_1686147
  have hstable : (prefixWord ++ tailWord_1686147).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686147).length < 2 ^ (prefixWord ++ tailWord_1686147).sum := by decide
  have hdescent : baseEnd_1686147 < baseStart_1686147 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686164 : List Nat := [2, 4, 2, 2, 1, 1, 1, 2, 1, 4, 3]
def baseStart_1686164 : Nat := 118140960795 + 1686164 * 2 ^ 59
def prefixEnd_1686164 : Nat := 4983230072969 + 3 ^ 40 * 1686164 * 2
def baseEnd_1686164 : Nat := 865812594307846109295479

theorem tailTrace_1686164 : CollatzResearch.WordTrace tailWord_1686164 prefixEnd_1686164 865812594307846109295479 := by
  unfold tailWord_1686164
  simp only [CollatzResearch.WordTrace]
  refine ⟨30749726731661638364768773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 40999635642215517819691697 30749726731661638364768773)
  ·
    refine ⟨5765573762186557193394145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30749726731661638364768773 5765573762186557193394145)
    ·
      refine ⟨4324180321639917895045609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5765573762186557193394145 4324180321639917895045609)
      ·
        refine ⟨3243135241229938421284207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324180321639917895045609 3243135241229938421284207)
        ·
          refine ⟨4864702861844907631926311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243135241229938421284207 4864702861844907631926311)
          ·
            refine ⟨7297054292767361447889467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4864702861844907631926311 7297054292767361447889467)
            ·
              refine ⟨10945581439151042171834201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7297054292767361447889467 10945581439151042171834201)
              ·
                refine ⟨8209186079363281628875651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10945581439151042171834201 8209186079363281628875651)
                ·
                  refine ⟨12313779119044922443313477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8209186079363281628875651 12313779119044922443313477)
                  ·
                    refine ⟨2308833584820922958121277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12313779119044922443313477 2308833584820922958121277)
                    ·
                      refine ⟨865812594307846109295479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2308833584820922958121277 865812594307846109295479)
                      ·
                        rfl

theorem cell23_1686164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_1686164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686164 prefixEnd_1686164 := by exact prefixLift 1686164
  have htrace : WordTrace (prefixWord ++ tailWord_1686164) baseStart_1686164 baseEnd_1686164 := by
    simpa [prefixWord, tailWord_1686164, baseEnd_1686164] using wordTrace_append hprefix tailTrace_1686164
  have hstable : (prefixWord ++ tailWord_1686164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686164).length < 2 ^ (prefixWord ++ tailWord_1686164).sum := by decide
  have hdescent : baseEnd_1686164 < baseStart_1686164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686198 : List Nat := [5, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1686198 : Nat := 118140960795 + 1686198 * 2 ^ 59
def prefixEnd_1686198 : Nat := 4983230072969 + 3 ^ 40 * 1686198 * 2
def baseEnd_1686198 : Nat := 865830052650098976270323

theorem tailTrace_1686198 : CollatzResearch.WordTrace tailWord_1686198 prefixEnd_1686198 865830052650098976270323 := by
  unfold tailWord_1686198
  simp only [CollatzResearch.WordTrace]
  refine ⟨3843793346575006283517203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41000462363466733690850165 3843793346575006283517203)
  ·
    refine ⟨5765690019862509425275805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3843793346575006283517203 5765690019862509425275805)
    ·
      refine ⟨2162133757448441034478427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5765690019862509425275805 2162133757448441034478427)
      ·
        refine ⟨3243200636172661551717641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162133757448441034478427 3243200636172661551717641)
        ·
          refine ⟨2432400477129496163788231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3243200636172661551717641 2432400477129496163788231)
          ·
            refine ⟨3648600715694244245682347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2432400477129496163788231 3648600715694244245682347)
            ·
              refine ⟨5472901073541366368523521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648600715694244245682347 5472901073541366368523521)
              ·
                refine ⟨4104675805156024776392641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5472901073541366368523521 4104675805156024776392641)
                ·
                  refine ⟨3078506853867018582294481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4104675805156024776392641 3078506853867018582294481)
                  ·
                    refine ⟨2308880140400263936720861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3078506853867018582294481 2308880140400263936720861)
                    ·
                      refine ⟨865830052650098976270323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2308880140400263936720861 865830052650098976270323)
                      ·
                        rfl

theorem cell23_1686198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1686198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686198 prefixEnd_1686198 := by exact prefixLift 1686198
  have htrace : WordTrace (prefixWord ++ tailWord_1686198) baseStart_1686198 baseEnd_1686198 := by
    simpa [prefixWord, tailWord_1686198, baseEnd_1686198] using wordTrace_append hprefix tailTrace_1686198
  have hstable : (prefixWord ++ tailWord_1686198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686198).length < 2 ^ (prefixWord ++ tailWord_1686198).sum := by decide
  have hdescent : baseEnd_1686198 < baseStart_1686198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686254 : List Nat := [4, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5]
def baseStart_1686254 : Nat := 118140960795 + 1686254 * 2 ^ 59
def prefixEnd_1686254 : Nat := 4983230072969 + 3 ^ 40 * 1686254 * 2
def baseEnd_1686254 : Nat := 865858807566750757170065

theorem tailTrace_1686254 : CollatzResearch.WordTrace tailWord_1686254 prefixEnd_1686254 865858807566750757170065 := by
  unfold tailWord_1686254
  simp only [CollatzResearch.WordTrace]
  refine ⟨7687842004124652762539227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41001824021998148066875877 7687842004124652762539227)
  ·
    refine ⟨11531763006186979143808841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7687842004124652762539227 11531763006186979143808841)
    ·
      refine ⟨8648822254640234357856631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11531763006186979143808841 8648822254640234357856631)
      ·
        refine ⟨12973233381960351536784947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8648822254640234357856631 12973233381960351536784947)
        ·
          refine ⟨19459850072940527305177421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12973233381960351536784947 19459850072940527305177421)
          ·
            refine ⟨7297443777352697739441533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19459850072940527305177421 7297443777352697739441533)
            ·
              refine ⟨2736541416507261652290575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7297443777352697739441533 2736541416507261652290575)
              ·
                refine ⟨4104812124760892478435863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2736541416507261652290575 4104812124760892478435863)
                ·
                  refine ⟨6157218187141338717653795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4104812124760892478435863 6157218187141338717653795)
                  ·
                    refine ⟨9235827280712008076480693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6157218187141338717653795 9235827280712008076480693)
                    ·
                      refine ⟨865858807566750757170065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9235827280712008076480693 865858807566750757170065)
                      ·
                        rfl

theorem cell23_1686254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_1686254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686254 prefixEnd_1686254 := by exact prefixLift 1686254
  have htrace : WordTrace (prefixWord ++ tailWord_1686254) baseStart_1686254 baseEnd_1686254 := by
    simpa [prefixWord, tailWord_1686254, baseEnd_1686254] using wordTrace_append hprefix tailTrace_1686254
  have hstable : (prefixWord ++ tailWord_1686254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686254).length < 2 ^ (prefixWord ++ tailWord_1686254).sum := by decide
  have hdescent : baseEnd_1686254 < baseStart_1686254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686274 : List Nat := [3, 4, 1, 1, 1, 2, 3, 8]
def baseStart_1686274 : Nat := 118140960795 + 1686274 * 2 ^ 59
def prefixEnd_1686274 : Nat := 4983230072969 + 3 ^ 40 * 1686274 * 2
def baseEnd_1686274 : Nat := 32069225080734839959999

theorem tailTrace_1686274 : CollatzResearch.WordTrace tailWord_1686274 prefixEnd_1686274 32069225080734839959999 := by
  unfold tailWord_1686274
  simp only [CollatzResearch.WordTrace]
  refine ⟨15375866373231191379010469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41002310328616510344027917 15375866373231191379010469)
  ·
    refine ⟨2882974944980848383564463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15375866373231191379010469 2882974944980848383564463)
    ·
      refine ⟨4324462417471272575346695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2882974944980848383564463 4324462417471272575346695)
      ·
        refine ⟨6486693626206908863020043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4324462417471272575346695 6486693626206908863020043)
        ·
          refine ⟨9730040439310363294530065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6486693626206908863020043 9730040439310363294530065)
          ·
            refine ⟨7297530329482772470897549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9730040439310363294530065 7297530329482772470897549)
            ·
              refine ⟨2736573873556039676586581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7297530329482772470897549 2736573873556039676586581)
              ·
                refine ⟨32069225080734839959999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2736573873556039676586581 32069225080734839959999)
                ·
                  rfl

theorem cell23_1686274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 8].length) (baseStart_1686274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686274 prefixEnd_1686274 := by exact prefixLift 1686274
  have htrace : WordTrace (prefixWord ++ tailWord_1686274) baseStart_1686274 baseEnd_1686274 := by
    simpa [prefixWord, tailWord_1686274, baseEnd_1686274] using wordTrace_append hprefix tailTrace_1686274
  have hstable : (prefixWord ++ tailWord_1686274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686274).length < 2 ^ (prefixWord ++ tailWord_1686274).sum := by decide
  have hdescent : baseEnd_1686274 < baseStart_1686274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686284 : List Nat := [2, 2, 1, 2, 2, 1, 1, 2, 6, 1, 3]
def baseStart_1686284 : Nat := 118140960795 + 1686284 * 2 ^ 59
def prefixEnd_1686284 : Nat := 4983230072969 + 3 ^ 40 * 1686284 * 2
def baseEnd_1686284 : Nat := 865874211986385639794927

theorem tailTrace_1686284 : CollatzResearch.WordTrace tailWord_1686284 prefixEnd_1686284 865874211986385639794927 := by
  unfold tailWord_1686284
  simp only [CollatzResearch.WordTrace]
  refine ⟨30751915111444268611952953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41002553481925691482603937 30751915111444268611952953)
  ·
    refine ⟨23063936333583201458964715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30751915111444268611952953 23063936333583201458964715)
    ·
      refine ⟨34595904500374802188447073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23063936333583201458964715 34595904500374802188447073)
      ·
        refine ⟨25946928375281101641335305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34595904500374802188447073 25946928375281101641335305)
        ·
          refine ⟨19460196281460826231001479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25946928375281101641335305 19460196281460826231001479)
          ·
            refine ⟨29190294422191239346502219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19460196281460826231001479 29190294422191239346502219)
            ·
              refine ⟨43785441633286859019753329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29190294422191239346502219 43785441633286859019753329)
              ·
                refine ⟨32839081224965144264814997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43785441633286859019753329 32839081224965144264814997)
                ·
                  refine ⟨1539331932420241137413203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32839081224965144264814997 1539331932420241137413203)
                  ·
                    refine ⟨2308997898630361706119805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1539331932420241137413203 2308997898630361706119805)
                    ·
                      refine ⟨865874211986385639794927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2308997898630361706119805 865874211986385639794927)
                      ·
                        rfl

theorem cell23_1686284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 1, 2, 6, 1, 3].length) (baseStart_1686284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686284 prefixEnd_1686284 := by exact prefixLift 1686284
  have htrace : WordTrace (prefixWord ++ tailWord_1686284) baseStart_1686284 baseEnd_1686284 := by
    simpa [prefixWord, tailWord_1686284, baseEnd_1686284] using wordTrace_append hprefix tailTrace_1686284
  have hstable : (prefixWord ++ tailWord_1686284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686284).length < 2 ^ (prefixWord ++ tailWord_1686284).sum := by decide
  have hdescent : baseEnd_1686284 < baseStart_1686284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686318 : List Nat := [4, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1686318 : Nat := 118140960795 + 1686318 * 2 ^ 59
def prefixEnd_1686318 : Nat := 4983230072969 + 3 ^ 40 * 1686318 * 2
def baseEnd_1686318 : Nat := 865891670328638506769771

theorem tailTrace_1686318 : CollatzResearch.WordTrace tailWord_1686318 prefixEnd_1686318 865891670328638506769771 := by
  unfold tailWord_1686318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7688133788095670128830451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41003380203176907353762405 7688133788095670128830451)
  ·
    refine ⟨11532200682143505193245677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7688133788095670128830451 11532200682143505193245677)
    ·
      refine ⟨4324575255803814447467129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11532200682143505193245677 4324575255803814447467129)
      ·
        refine ⟨3243431441852860835600347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4324575255803814447467129 3243431441852860835600347)
        ·
          refine ⟨4865147162779291253400521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243431441852860835600347 4865147162779291253400521)
          ·
            refine ⟨3648860372084468440050391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4865147162779291253400521 3648860372084468440050391)
            ·
              refine ⟨5473290558126702660075587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3648860372084468440050391 5473290558126702660075587)
              ·
                refine ⟨8209935837190053990113381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5473290558126702660075587 8209935837190053990113381)
                ·
                  refine ⟨1539362969473135123146259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8209935837190053990113381 1539362969473135123146259)
                  ·
                    refine ⟨2309044454209702684719389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1539362969473135123146259 2309044454209702684719389)
                    ·
                      refine ⟨865891670328638506769771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2309044454209702684719389 865891670328638506769771)
                      ·
                        rfl

theorem cell23_1686318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1686318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686318 prefixEnd_1686318 := by exact prefixLift 1686318
  have htrace : WordTrace (prefixWord ++ tailWord_1686318) baseStart_1686318 baseEnd_1686318 := by
    simpa [prefixWord, tailWord_1686318, baseEnd_1686318] using wordTrace_append hprefix tailTrace_1686318
  have hstable : (prefixWord ++ tailWord_1686318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686318).length < 2 ^ (prefixWord ++ tailWord_1686318).sum := by decide
  have hdescent : baseEnd_1686318 < baseStart_1686318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686387 : List Nat := [1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7]
def baseStart_1686387 : Nat := 118140960795 + 1686387 * 2 ^ 59
def prefixEnd_1686387 : Nat := 4983230072969 + 3 ^ 40 * 1686387 * 2
def baseEnd_1686387 : Nat := 865927100493798736806953

theorem tailTrace_1686387 : CollatzResearch.WordTrace tailWord_1686387 prefixEnd_1686387 865927100493798736806953 := by
  unfold tailWord_1686387
  simp only [CollatzResearch.WordTrace]
  refine ⟨61507586941515385814905415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41005057961010257209936943 61507586941515385814905415)
  ·
    refine ⟨92261380412273078722358123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61507586941515385814905415 92261380412273078722358123)
    ·
      refine ⟨138392070618409618083537185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92261380412273078722358123 138392070618409618083537185)
      ·
        refine ⟨103794052963807213562652889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138392070618409618083537185 103794052963807213562652889)
        ·
          refine ⟨77845539722855410171989667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103794052963807213562652889 77845539722855410171989667)
          ·
            refine ⟨116768309584283115257984501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77845539722855410171989667 116768309584283115257984501)
            ·
              refine ⟨10947029023526542055436047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 116768309584283115257984501 10947029023526542055436047)
              ·
                refine ⟨16420543535289813083154071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10947029023526542055436047 16420543535289813083154071)
                ·
                  refine ⟨24630815302934719624731107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16420543535289813083154071 24630815302934719624731107)
                  ·
                    refine ⟨36946222954402079437096661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24630815302934719624731107 36946222954402079437096661)
                    ·
                      refine ⟨865927100493798736806953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36946222954402079437096661 865927100493798736806953)
                      ·
                        rfl

theorem cell23_1686387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 7].length) (baseStart_1686387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686387 prefixEnd_1686387 := by exact prefixLift 1686387
  have htrace : WordTrace (prefixWord ++ tailWord_1686387) baseStart_1686387 baseEnd_1686387 := by
    simpa [prefixWord, tailWord_1686387, baseEnd_1686387] using wordTrace_append hprefix tailTrace_1686387
  have hstable : (prefixWord ++ tailWord_1686387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686387).length < 2 ^ (prefixWord ++ tailWord_1686387).sum := by decide
  have hdescent : baseEnd_1686387 < baseStart_1686387 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686431 : List Nat := [1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 4]
def baseStart_1686431 : Nat := 118140960795 + 1686431 * 2 ^ 59
def prefixEnd_1686431 : Nat := 4983230072969 + 3 ^ 40 * 1686431 * 2
def baseEnd_1686431 : Nat := 865949693642596564656751

theorem tailTrace_1686431 : CollatzResearch.WordTrace tailWord_1686431 prefixEnd_1686431 865949693642596564656751 := by
  unfold tailWord_1686431
  simp only [CollatzResearch.WordTrace]
  refine ⟨61509191753355981329507147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41006127835570654219671431 61509191753355981329507147)
  ·
    refine ⟨92263787630033971994260721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61509191753355981329507147 92263787630033971994260721)
    ·
      refine ⟨69197840722525478995695541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92263787630033971994260721 69197840722525478995695541)
      ·
        refine ⟨6487297567736763655846457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 69197840722525478995695541 6487297567736763655846457)
        ·
          refine ⟨4865473175802572741884843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6487297567736763655846457 4865473175802572741884843)
          ·
            refine ⟨7298209763703859112827265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865473175802572741884843 7298209763703859112827265)
            ·
              refine ⟨5473657322777894334620449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7298209763703859112827265 5473657322777894334620449)
              ·
                refine ⟨4105242992083420750965337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5473657322777894334620449 4105242992083420750965337)
                ·
                  refine ⟨3078932244062565563224003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4105242992083420750965337 3078932244062565563224003)
                  ·
                    refine ⟨4618398366093848344836005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3078932244062565563224003 4618398366093848344836005)
                    ·
                      refine ⟨865949693642596564656751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4618398366093848344836005 865949693642596564656751)
                      ·
                        rfl

theorem cell23_1686431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_1686431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686431 prefixEnd_1686431 := by exact prefixLift 1686431
  have htrace : WordTrace (prefixWord ++ tailWord_1686431) baseStart_1686431 baseEnd_1686431 := by
    simpa [prefixWord, tailWord_1686431, baseEnd_1686431] using wordTrace_append hprefix tailTrace_1686431
  have hstable : (prefixWord ++ tailWord_1686431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686431).length < 2 ^ (prefixWord ++ tailWord_1686431).sum := by decide
  have hdescent : baseEnd_1686431 < baseStart_1686431 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686481 : List Nat := [1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 3]
def baseStart_1686481 : Nat := 118140960795 + 1686481 * 2 ^ 59
def prefixEnd_1686481 : Nat := 4983230072969 + 3 ^ 40 * 1686481 * 2
def baseEnd_1686481 : Nat := 865975367675321369031521

theorem tailTrace_1686481 : CollatzResearch.WordTrace tailWord_1686481 prefixEnd_1686481 865975367675321369031521 := by
  unfold tailWord_1686481
  simp only [CollatzResearch.WordTrace]
  refine ⟨61511015403174839868827297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41007343602116559912551531 61511015403174839868827297)
  ·
    refine ⟨46133261552381129901620473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61511015403174839868827297 46133261552381129901620473)
    ·
      refine ⟨34599946164285847426215355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46133261552381129901620473 34599946164285847426215355)
      ·
        refine ⟨51899919246428771139323033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34599946164285847426215355 51899919246428771139323033)
        ·
          refine ⟨38924939434821578354492275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51899919246428771139323033 38924939434821578354492275)
          ·
            refine ⟨58387409152232367531738413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38924939434821578354492275 58387409152232367531738413)
            ·
              refine ⟨21895278432087137824401905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58387409152232367531738413 21895278432087137824401905)
              ·
                refine ⟨16421458824065353368301429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21895278432087137824401905 16421458824065353368301429)
                ·
                  refine ⟨1539511764756126878278259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16421458824065353368301429 1539511764756126878278259)
                  ·
                    refine ⟨2309267647134190317417389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1539511764756126878278259 2309267647134190317417389)
                    ·
                      refine ⟨865975367675321369031521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2309267647134190317417389 865975367675321369031521)
                      ·
                        rfl

theorem cell23_1686481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 3, 2, 5, 1, 3].length) (baseStart_1686481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686481 prefixEnd_1686481 := by exact prefixLift 1686481
  have htrace : WordTrace (prefixWord ++ tailWord_1686481) baseStart_1686481 baseEnd_1686481 := by
    simpa [prefixWord, tailWord_1686481, baseEnd_1686481] using wordTrace_append hprefix tailTrace_1686481
  have hstable : (prefixWord ++ tailWord_1686481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686481).length < 2 ^ (prefixWord ++ tailWord_1686481).sum := by decide
  have hdescent : baseEnd_1686481 < baseStart_1686481 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686518 : List Nat := [5, 1, 1, 1, 3, 1, 1, 4, 1, 5]
def baseStart_1686518 : Nat := 118140960795 + 1686518 * 2 ^ 59
def prefixEnd_1686518 : Nat := 4983230072969 + 3 ^ 40 * 1686518 * 2
def baseEnd_1686518 : Nat := 288664788819845908089617

theorem tailTrace_1686518 : CollatzResearch.WordTrace tailWord_1686518 prefixEnd_1686518 288664788819845908089617 := by
  unfold tailWord_1686518
  simp only [CollatzResearch.WordTrace]
  refine ⟨3844522806502549699245263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41008243269360530125282805 3844522806502549699245263)
  ·
    refine ⟨5766784209753824548867895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3844522806502549699245263 5766784209753824548867895)
    ·
      refine ⟨8650176314630736823301843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5766784209753824548867895 8650176314630736823301843)
      ·
        refine ⟨12975264471946105234952765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8650176314630736823301843 12975264471946105234952765)
        ·
          refine ⟨4865724176979789463107287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12975264471946105234952765 4865724176979789463107287)
          ·
            refine ⟨7298586265469684194660931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865724176979789463107287 7298586265469684194660931)
            ·
              refine ⟨10947879398204526291991397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298586265469684194660931 10947879398204526291991397)
              ·
                refine ⟨2052727387163348679748387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10947879398204526291991397 2052727387163348679748387)
                ·
                  refine ⟨3079091080745023019622581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052727387163348679748387 3079091080745023019622581)
                  ·
                    refine ⟨288664788819845908089617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3079091080745023019622581 288664788819845908089617)
                    ·
                      rfl

theorem cell23_1686518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 5].length) (baseStart_1686518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686518 prefixEnd_1686518 := by exact prefixLift 1686518
  have htrace : WordTrace (prefixWord ++ tailWord_1686518) baseStart_1686518 baseEnd_1686518 := by
    simpa [prefixWord, tailWord_1686518, baseEnd_1686518] using wordTrace_append hprefix tailTrace_1686518
  have hstable : (prefixWord ++ tailWord_1686518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686518).length < 2 ^ (prefixWord ++ tailWord_1686518).sum := by decide
  have hdescent : baseEnd_1686518 < baseStart_1686518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686521 : List Nat := [1, 2, 1, 3, 1, 3, 1, 1, 2, 6, 2]
def baseStart_1686521 : Nat := 118140960795 + 1686521 * 2 ^ 59
def prefixEnd_1686521 : Nat := 4983230072969 + 3 ^ 40 * 1686521 * 2
def baseEnd_1686521 : Nat := 865995906901501212531337

theorem tailTrace_1686521 : CollatzResearch.WordTrace tailWord_1686521 prefixEnd_1686521 865995906901501212531337 := by
  unfold tailWord_1686521
  simp only [CollatzResearch.WordTrace]
  refine ⟨61512474323029926700283417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41008316215353284466855611 61512474323029926700283417)
  ·
    refine ⟨46134355742272445025212563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61512474323029926700283417 46134355742272445025212563)
    ·
      refine ⟨69201533613408667537818845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46134355742272445025212563 69201533613408667537818845)
      ·
        refine ⟨25950575105028250326682067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69201533613408667537818845 25950575105028250326682067)
        ·
          refine ⟨38925862657542375490023101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25950575105028250326682067 38925862657542375490023101)
          ·
            refine ⟨14597198496578390808758663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38925862657542375490023101 14597198496578390808758663)
            ·
              refine ⟨21895797744867586213137995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14597198496578390808758663 21895797744867586213137995)
              ·
                refine ⟨32843696617301379319706993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21895797744867586213137995 32843696617301379319706993)
                ·
                  refine ⟨24632772462976034489780245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32843696617301379319706993 24632772462976034489780245)
                  ·
                    refine ⟨1154661209202001616708449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24632772462976034489780245 1154661209202001616708449)
                    ·
                      refine ⟨865995906901501212531337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154661209202001616708449 865995906901501212531337)
                      ·
                        rfl

theorem cell23_1686521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 1, 2, 6, 2].length) (baseStart_1686521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686521 prefixEnd_1686521 := by exact prefixLift 1686521
  have htrace : WordTrace (prefixWord ++ tailWord_1686521) baseStart_1686521 baseEnd_1686521 := by
    simpa [prefixWord, tailWord_1686521, baseEnd_1686521] using wordTrace_append hprefix tailTrace_1686521
  have hstable : (prefixWord ++ tailWord_1686521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686521).length < 2 ^ (prefixWord ++ tailWord_1686521).sum := by decide
  have hdescent : baseEnd_1686521 < baseStart_1686521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686538 : List Nat := [3, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4]
def baseStart_1686538 : Nat := 118140960795 + 1686538 * 2 ^ 59
def prefixEnd_1686538 : Nat := 4983230072969 + 3 ^ 40 * 1686538 * 2
def baseEnd_1686538 : Nat := 866004636072627646018759

theorem tailTrace_1686538 : CollatzResearch.WordTrace tailWord_1686538 prefixEnd_1686538 866004636072627646018759 := by
  unfold tailWord_1686538
  simp only [CollatzResearch.WordTrace]
  refine ⟨15378273590992084650913067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41008729575978892402434845 15378273590992084650913067)
  ·
    refine ⟨23067410386488126976369601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15378273590992084650913067 23067410386488126976369601)
    ·
      refine ⟨17300557789866095232277201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23067410386488126976369601 17300557789866095232277201)
      ·
        refine ⟨12975418342399571424207901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17300557789866095232277201 12975418342399571424207901)
        ·
          refine ⟨4865781878399839284077963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12975418342399571424207901 4865781878399839284077963)
          ·
            refine ⟨7298672817599758926116945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865781878399839284077963 7298672817599758926116945)
            ·
              refine ⟨5474004613199819194587709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7298672817599758926116945 5474004613199819194587709)
              ·
                refine ⟨2052751729949932197970391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5474004613199819194587709 2052751729949932197970391)
                ·
                  refine ⟨3079127594924898296955587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052751729949932197970391 3079127594924898296955587)
                  ·
                    refine ⟨4618691392387347445433381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3079127594924898296955587 4618691392387347445433381)
                    ·
                      refine ⟨866004636072627646018759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4618691392387347445433381 866004636072627646018759)
                      ·
                        rfl

theorem cell23_1686538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 2, 3, 1, 1, 4].length) (baseStart_1686538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686538 prefixEnd_1686538 := by exact prefixLift 1686538
  have htrace : WordTrace (prefixWord ++ tailWord_1686538) baseStart_1686538 baseEnd_1686538 := by
    simpa [prefixWord, tailWord_1686538, baseEnd_1686538] using wordTrace_append hprefix tailTrace_1686538
  have hstable : (prefixWord ++ tailWord_1686538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686538).length < 2 ^ (prefixWord ++ tailWord_1686538).sum := by decide
  have hdescent : baseEnd_1686538 < baseStart_1686538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686551 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 6]
def baseStart_1686551 : Nat := 118140960795 + 1686551 * 2 ^ 59
def prefixEnd_1686551 : Nat := 4983230072969 + 3 ^ 40 * 1686551 * 2
def baseEnd_1686551 : Nat := 866011311321136095156199

theorem tailTrace_1686551 : CollatzResearch.WordTrace tailWord_1686551 prefixEnd_1686551 866011311321136095156199 := by
  unfold tailWord_1686551
  simp only [CollatzResearch.WordTrace]
  refine ⟨61513568512921241823875507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41009045675280827882583671 61513568512921241823875507)
  ·
    refine ⟨92270352769381862735813261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61513568512921241823875507 92270352769381862735813261)
    ·
      refine ⟨34601382288518198525929973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92270352769381862735813261 34601382288518198525929973)
      ·
        refine ⟨3243879589548581111805935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34601382288518198525929973 3243879589548581111805935)
        ·
          refine ⟨4865819384322871667708903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3243879589548581111805935 4865819384322871667708903)
          ·
            refine ⟨7298729076484307501563355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4865819384322871667708903 7298729076484307501563355)
            ·
              refine ⟨10948093614726461252345033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7298729076484307501563355 10948093614726461252345033)
              ·
                refine ⟨8211070211044845939258775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10948093614726461252345033 8211070211044845939258775)
                ·
                  refine ⟨12316605316567268908888163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8211070211044845939258775 12316605316567268908888163)
                  ·
                    refine ⟨18474907974850903363332245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12316605316567268908888163 18474907974850903363332245)
                    ·
                      refine ⟨866011311321136095156199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18474907974850903363332245 866011311321136095156199)
                      ·
                        rfl

theorem cell23_1686551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_1686551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686551 prefixEnd_1686551 := by exact prefixLift 1686551
  have htrace : WordTrace (prefixWord ++ tailWord_1686551) baseStart_1686551 baseEnd_1686551 := by
    simpa [prefixWord, tailWord_1686551, baseEnd_1686551] using wordTrace_append hprefix tailTrace_1686551
  have hstable : (prefixWord ++ tailWord_1686551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686551).length < 2 ^ (prefixWord ++ tailWord_1686551).sum := by decide
  have hdescent : baseEnd_1686551 < baseStart_1686551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686561 : List Nat := [1, 2, 3, 2, 3, 2, 2, 8]
def baseStart_1686561 : Nat := 118140960795 + 1686561 * 2 ^ 59
def prefixEnd_1686561 : Nat := 4983230072969 + 3 ^ 40 * 1686561 * 2
def baseEnd_1686561 : Nat := 32074683189914113186339

theorem tailTrace_1686561 : CollatzResearch.WordTrace tailWord_1686561 prefixEnd_1686561 32074683189914113186339 := by
  unfold tailWord_1686561
  simp only [CollatzResearch.WordTrace]
  refine ⟨61513933242885013531739537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41009288828590009021159691 61513933242885013531739537)
  ·
    refine ⟨46135449932163760148804653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61513933242885013531739537 46135449932163760148804653)
    ·
      refine ⟨17300793724561410055801745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46135449932163760148804653 17300793724561410055801745)
      ·
        refine ⟨12975595293421057541851309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17300793724561410055801745 12975595293421057541851309)
        ·
          refine ⟨4865848235032896578194241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12975595293421057541851309 4865848235032896578194241)
          ·
            refine ⟨3649386176274672433645681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4865848235032896578194241 3649386176274672433645681)
            ·
              refine ⟨2737039632206004325234261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3649386176274672433645681 2737039632206004325234261)
              ·
                refine ⟨32074683189914113186339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2737039632206004325234261 32074683189914113186339)
                ·
                  rfl

theorem cell23_1686561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 8].length) (baseStart_1686561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686561 prefixEnd_1686561 := by exact prefixLift 1686561
  have htrace : WordTrace (prefixWord ++ tailWord_1686561) baseStart_1686561 baseEnd_1686561 := by
    simpa [prefixWord, tailWord_1686561, baseEnd_1686561] using wordTrace_append hprefix tailTrace_1686561
  have hstable : (prefixWord ++ tailWord_1686561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686561).length < 2 ^ (prefixWord ++ tailWord_1686561).sum := by decide
  have hdescent : baseEnd_1686561 < baseStart_1686561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686571 : List Nat := [1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 3]
def baseStart_1686571 : Nat := 118140960795 + 1686571 * 2 ^ 59
def prefixEnd_1686571 : Nat := 4983230072969 + 3 ^ 40 * 1686571 * 2
def baseEnd_1686571 : Nat := 866021580934226016906107

theorem tailTrace_1686571 : CollatzResearch.WordTrace tailWord_1686571 prefixEnd_1686571 866021580934226016906107 := by
  unfold tailWord_1686571
  simp only [CollatzResearch.WordTrace]
  refine ⟨61514297972848785239603567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41009531981899190159735711 61514297972848785239603567)
  ·
    refine ⟨92271446959273177859405351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61514297972848785239603567 92271446959273177859405351)
    ·
      refine ⟨138407170438909766789108027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92271446959273177859405351 138407170438909766789108027)
      ·
        refine ⟨207610755658364650183662041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138407170438909766789108027 207610755658364650183662041)
        ·
          refine ⟨155708066743773487637746531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207610755658364650183662041 155708066743773487637746531)
          ·
            refine ⟨233562100115660231456619797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155708066743773487637746531 233562100115660231456619797)
            ·
              refine ⟨10948223442921573349529053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 233562100115660231456619797 10948223442921573349529053)
              ·
                refine ⟨4105583791095590006073395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10948223442921573349529053 4105583791095590006073395)
                ·
                  refine ⟨6158375686643385009110093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105583791095590006073395 6158375686643385009110093)
                  ·
                    refine ⟨2309390882491269378416285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6158375686643385009110093 2309390882491269378416285)
                    ·
                      refine ⟨866021580934226016906107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2309390882491269378416285 866021580934226016906107)
                      ·
                        rfl

theorem cell23_1686571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 3, 1, 3, 3].length) (baseStart_1686571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686571 prefixEnd_1686571 := by exact prefixLift 1686571
  have htrace : WordTrace (prefixWord ++ tailWord_1686571) baseStart_1686571 baseEnd_1686571 := by
    simpa [prefixWord, tailWord_1686571, baseEnd_1686571] using wordTrace_append hprefix tailTrace_1686571
  have hstable : (prefixWord ++ tailWord_1686571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686571).length < 2 ^ (prefixWord ++ tailWord_1686571).sum := by decide
  have hdescent : baseEnd_1686571 < baseStart_1686571 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686588 : List Nat := [2, 2, 2, 2, 2, 3, 1, 2, 1, 3, 3]
def baseStart_1686588 : Nat := 118140960795 + 1686588 * 2 ^ 59
def prefixEnd_1686588 : Nat := 4983230072969 + 3 ^ 40 * 1686588 * 2
def baseEnd_1686588 : Nat := 866030310105352450393529

theorem tailTrace_1686588 : CollatzResearch.WordTrace tailWord_1686588 prefixEnd_1686588 866030310105352450393529 := by
  unfold tailWord_1686588
  simp only [CollatzResearch.WordTrace]
  refine ⟨30757459006893598571486209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41009945342524798095314945 30757459006893598571486209)
  ·
    refine ⟨23068094255170198928614657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30757459006893598571486209 23068094255170198928614657)
    ·
      refine ⟨17301070691377649196460993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23068094255170198928614657 17301070691377649196460993)
      ·
        refine ⟨12975803018533236897345745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17301070691377649196460993 12975803018533236897345745)
        ·
          refine ⟨9731852263899927673009309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12975803018533236897345745 9731852263899927673009309)
          ·
            refine ⟨3649444598962472877378491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9731852263899927673009309 3649444598962472877378491)
            ·
              refine ⟨5474166898443709316067737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649444598962472877378491 5474166898443709316067737)
              ·
                refine ⟨4105625173832781987050803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5474166898443709316067737 4105625173832781987050803)
                ·
                  refine ⟨6158437760749172980576205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105625173832781987050803 6158437760749172980576205)
                  ·
                    refine ⟨2309414160280939867716077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6158437760749172980576205 2309414160280939867716077)
                    ·
                      refine ⟨866030310105352450393529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2309414160280939867716077 866030310105352450393529)
                      ·
                        rfl

theorem cell23_1686588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 2, 1, 3, 3].length) (baseStart_1686588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686588 prefixEnd_1686588 := by exact prefixLift 1686588
  have htrace : WordTrace (prefixWord ++ tailWord_1686588) baseStart_1686588 baseEnd_1686588 := by
    simpa [prefixWord, tailWord_1686588, baseEnd_1686588] using wordTrace_append hprefix tailTrace_1686588
  have hstable : (prefixWord ++ tailWord_1686588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686588).length < 2 ^ (prefixWord ++ tailWord_1686588).sum := by decide
  have hdescent : baseEnd_1686588 < baseStart_1686588 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686622 : List Nat := [4, 4, 1, 1, 1, 1, 1, 3, 1, 3, 3]
def baseStart_1686622 : Nat := 118140960795 + 1686622 * 2 ^ 59
def prefixEnd_1686622 : Nat := 4983230072969 + 3 ^ 40 * 1686622 * 2
def baseEnd_1686622 : Nat := 866047768447605317368373

theorem tailTrace_1686622 : CollatzResearch.WordTrace tailWord_1686622 prefixEnd_1686622 866047768447605317368373 := by
  unfold tailWord_1686622
  simp only [CollatzResearch.WordTrace]
  refine ⟨7689519761958002618713765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41010772063776013966473413 7689519761958002618713765)
  ·
    refine ⟨1441784955367125491008831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7689519761958002618713765 1441784955367125491008831)
    ·
      refine ⟨2162677433050688236513247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1441784955367125491008831 2162677433050688236513247)
      ·
        refine ⟨3244016149576032354769871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162677433050688236513247 3244016149576032354769871)
        ·
          refine ⟨4866024224364048532154807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244016149576032354769871 4866024224364048532154807)
          ·
            refine ⟨7299036336546072798232211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866024224364048532154807 7299036336546072798232211)
            ·
              refine ⟨10948554504819109197348317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7299036336546072798232211 10948554504819109197348317)
              ·
                refine ⟨4105707939307165949005619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10948554504819109197348317 4105707939307165949005619)
                ·
                  refine ⟨6158561908960748923508429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4105707939307165949005619 6158561908960748923508429)
                  ·
                    refine ⟨2309460715860280846315661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6158561908960748923508429 2309460715860280846315661)
                    ·
                      refine ⟨866047768447605317368373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2309460715860280846315661 866047768447605317368373)
                      ·
                        rfl

theorem cell23_1686622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_1686622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686622 prefixEnd_1686622 := by exact prefixLift 1686622
  have htrace : WordTrace (prefixWord ++ tailWord_1686622) baseStart_1686622 baseEnd_1686622 := by
    simpa [prefixWord, tailWord_1686622, baseEnd_1686622] using wordTrace_append hprefix tailTrace_1686622
  have hstable : (prefixWord ++ tailWord_1686622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686622).length < 2 ^ (prefixWord ++ tailWord_1686622).sum := by decide
  have hdescent : baseEnd_1686622 < baseStart_1686622 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686649 : List Nat := [1, 2, 1, 3, 5, 2, 2, 1, 1, 3, 2]
def baseStart_1686649 : Nat := 118140960795 + 1686649 * 2 ^ 59
def prefixEnd_1686649 : Nat := 4983230072969 + 3 ^ 40 * 1686649 * 2
def baseEnd_1686649 : Nat := 866061632425276711730749

theorem tailTrace_1686649 : CollatzResearch.WordTrace tailWord_1686649 prefixEnd_1686649 866061632425276711730749 := by
  unfold tailWord_1686649
  simp only [CollatzResearch.WordTrace]
  refine ⟨61517142866566204560943001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41011428577710803040628667 61517142866566204560943001)
  ·
    refine ⟨46137857149924653420707251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61517142866566204560943001 46137857149924653420707251)
    ·
      refine ⟨69206785724886980131060877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46137857149924653420707251 69206785724886980131060877)
      ·
        refine ⟨25952544646832617549147829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69206785724886980131060877 25952544646832617549147829)
        ·
          refine ⟨2433051060640557895232609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25952544646832617549147829 2433051060640557895232609)
          ·
            refine ⟨1824788295480418421424457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433051060640557895232609 1824788295480418421424457)
            ·
              refine ⟨1368591221610313816068343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1824788295480418421424457 1368591221610313816068343)
              ·
                refine ⟨2052886832415470724102515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368591221610313816068343 2052886832415470724102515)
                ·
                  refine ⟨3079330248623206086153773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2052886832415470724102515 3079330248623206086153773)
                  ·
                    refine ⟨1154748843233702282307665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079330248623206086153773 1154748843233702282307665)
                    ·
                      refine ⟨866061632425276711730749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154748843233702282307665 866061632425276711730749)
                      ·
                        rfl

theorem cell23_1686649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 2, 2, 1, 1, 3, 2].length) (baseStart_1686649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686649 prefixEnd_1686649 := by exact prefixLift 1686649
  have htrace : WordTrace (prefixWord ++ tailWord_1686649) baseStart_1686649 baseEnd_1686649 := by
    simpa [prefixWord, tailWord_1686649, baseEnd_1686649] using wordTrace_append hprefix tailTrace_1686649
  have hstable : (prefixWord ++ tailWord_1686649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686649).length < 2 ^ (prefixWord ++ tailWord_1686649).sum := by decide
  have hdescent : baseEnd_1686649 < baseStart_1686649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686679 : List Nat := [1, 1, 3, 3, 3, 2, 3, 1, 2, 2, 2]
def baseStart_1686679 : Nat := 118140960795 + 1686679 * 2 ^ 59
def prefixEnd_1686679 : Nat := 4983230072969 + 3 ^ 40 * 1686679 * 2
def baseEnd_1686679 : Nat := 866077036844911594355611

theorem tailTrace_1686679 : CollatzResearch.WordTrace tailWord_1686679 prefixEnd_1686679 866077036844911594355611 := by
  unfold tailWord_1686679
  simp only [CollatzResearch.WordTrace]
  refine ⟨61518237056457519684535091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41012158037638346456356727 61518237056457519684535091)
  ·
    refine ⟨92277355584686279526802637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61518237056457519684535091 92277355584686279526802637)
    ·
      refine ⟨34604008344257354822550989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92277355584686279526802637 34604008344257354822550989)
      ·
        refine ⟨12976503129096508058456621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34604008344257354822550989 12976503129096508058456621)
        ·
          refine ⟨4866188673411190521921233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12976503129096508058456621 4866188673411190521921233)
          ·
            refine ⟨3649641505058392891440925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4866188673411190521921233 3649641505058392891440925)
            ·
              refine ⟨1368615564396897334290347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3649641505058392891440925 1368615564396897334290347)
              ·
                refine ⟨2052923346595346001435521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368615564396897334290347 2052923346595346001435521)
                ·
                  refine ⟨1539692509946509501076641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2052923346595346001435521 1539692509946509501076641)
                  ·
                    refine ⟨1154769382459882125807481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1539692509946509501076641 1154769382459882125807481)
                    ·
                      refine ⟨866077036844911594355611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154769382459882125807481 866077036844911594355611)
                      ·
                        rfl

theorem cell23_1686679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 3, 1, 2, 2, 2].length) (baseStart_1686679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686679 prefixEnd_1686679 := by exact prefixLift 1686679
  have htrace : WordTrace (prefixWord ++ tailWord_1686679) baseStart_1686679 baseEnd_1686679 := by
    simpa [prefixWord, tailWord_1686679, baseEnd_1686679] using wordTrace_append hprefix tailTrace_1686679
  have hstable : (prefixWord ++ tailWord_1686679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686679).length < 2 ^ (prefixWord ++ tailWord_1686679).sum := by decide
  have hdescent : baseEnd_1686679 < baseStart_1686679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686731 : List Nat := [1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4]
def baseStart_1686731 : Nat := 118140960795 + 1686731 * 2 ^ 59
def prefixEnd_1686731 : Nat := 4983230072969 + 3 ^ 40 * 1686731 * 2
def baseEnd_1686731 : Nat := 866103737838945390905371

theorem tailTrace_1686731 : CollatzResearch.WordTrace tailWord_1686731 prefixEnd_1686731 866103737838945390905371 := by
  unfold tailWord_1686731
  simp only [CollatzResearch.WordTrace]
  refine ⟨61520133652269132565428047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41013422434846088376952031 61520133652269132565428047)
  ·
    refine ⟨92280200478403698848142071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61520133652269132565428047 92280200478403698848142071)
    ·
      refine ⟨138420300717605548272213107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92280200478403698848142071 138420300717605548272213107)
      ·
        refine ⟨207630451076408322408319661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138420300717605548272213107 207630451076408322408319661)
        ·
          refine ⟨77861419153653120903119873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207630451076408322408319661 77861419153653120903119873)
          ·
            refine ⟨58396064365239840677339905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77861419153653120903119873 58396064365239840677339905)
            ·
              refine ⟨43797048273929880508004929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58396064365239840677339905 43797048273929880508004929)
              ·
                refine ⟨32847786205447410381003697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43797048273929880508004929 32847786205447410381003697)
                ·
                  refine ⟨24635839654085557785752773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32847786205447410381003697 24635839654085557785752773)
                  ·
                    refine ⟨4619219935141042084828645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24635839654085557785752773 4619219935141042084828645)
                    ·
                      refine ⟨866103737838945390905371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4619219935141042084828645 866103737838945390905371)
                      ·
                        rfl

theorem cell23_1686731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 2, 2, 4, 4].length) (baseStart_1686731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686731 prefixEnd_1686731 := by exact prefixLift 1686731
  have htrace : WordTrace (prefixWord ++ tailWord_1686731) baseStart_1686731 baseEnd_1686731 := by
    simpa [prefixWord, tailWord_1686731, baseEnd_1686731] using wordTrace_append hprefix tailTrace_1686731
  have hstable : (prefixWord ++ tailWord_1686731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686731).length < 2 ^ (prefixWord ++ tailWord_1686731).sum := by decide
  have hdescent : baseEnd_1686731 < baseStart_1686731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686812 : List Nat := [2, 2, 3, 1, 1, 1, 5, 1, 2, 3, 2]
def baseStart_1686812 : Nat := 118140960795 + 1686812 * 2 ^ 59
def prefixEnd_1686812 : Nat := 4983230072969 + 3 ^ 40 * 1686812 * 2
def baseEnd_1686812 : Nat := 866145329771959573992499

theorem tailTrace_1686812 : CollatzResearch.WordTrace tailWord_1686812 prefixEnd_1686812 866145329771959573992499 := by
  unfold tailWord_1686812
  simp only [CollatzResearch.WordTrace]
  refine ⟨30761543982487841699563345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41015391976650455599417793 30761543982487841699563345)
  ·
    refine ⟨23071157986865881274672509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30761543982487841699563345 23071157986865881274672509)
    ·
      refine ⟨8651684245074705478002191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23071157986865881274672509 8651684245074705478002191)
      ·
        refine ⟨12977526367612058217003287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8651684245074705478002191 12977526367612058217003287)
        ·
          refine ⟨19466289551418087325504931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12977526367612058217003287 19466289551418087325504931)
          ·
            refine ⟨29199434327127130988257397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19466289551418087325504931 29199434327127130988257397)
            ·
              refine ⟨2737446968168168530149131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29199434327127130988257397 2737446968168168530149131)
              ·
                refine ⟨4106170452252252795223697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737446968168168530149131 4106170452252252795223697)
                ·
                  refine ⟨3079627839189189596417773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4106170452252252795223697 3079627839189189596417773)
                  ·
                    refine ⟨1154860439695946098656665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079627839189189596417773 1154860439695946098656665)
                    ·
                      refine ⟨866145329771959573992499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154860439695946098656665 866145329771959573992499)
                      ·
                        rfl

theorem cell23_1686812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 5, 1, 2, 3, 2].length) (baseStart_1686812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686812 prefixEnd_1686812 := by exact prefixLift 1686812
  have htrace : WordTrace (prefixWord ++ tailWord_1686812) baseStart_1686812 baseEnd_1686812 := by
    simpa [prefixWord, tailWord_1686812, baseEnd_1686812] using wordTrace_append hprefix tailTrace_1686812
  have hstable : (prefixWord ++ tailWord_1686812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686812).length < 2 ^ (prefixWord ++ tailWord_1686812).sum := by decide
  have hdescent : baseEnd_1686812 < baseStart_1686812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686819 : List Nat := [1, 1, 1, 4, 2, 4, 2, 3, 1, 1, 3]
def baseStart_1686819 : Nat := 118140960795 + 1686819 * 2 ^ 59
def prefixEnd_1686819 : Nat := 4983230072969 + 3 ^ 40 * 1686819 * 2
def baseEnd_1686819 : Nat := 866148924136541046604967

theorem tailTrace_1686819 : CollatzResearch.WordTrace tailWord_1686819 prefixEnd_1686819 866148924136541046604967 := by
  unfold tailWord_1686819
  simp only [CollatzResearch.WordTrace]
  refine ⟨61523343275950323594631511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41015562183966882396421007 61523343275950323594631511)
  ·
    refine ⟨92285014913925485391947267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61523343275950323594631511 92285014913925485391947267)
    ·
      refine ⟨138427522370888228087920901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92285014913925485391947267 138427522370888228087920901)
      ·
        refine ⟨25955160444541542766485169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 138427522370888228087920901 25955160444541542766485169)
        ·
          refine ⟨19466370333406157074863877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25955160444541542766485169 19466370333406157074863877)
          ·
            refine ⟨3649944437513654451536977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19466370333406157074863877 3649944437513654451536977)
            ·
              refine ⟨2737458328135240838652733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3649944437513654451536977 2737458328135240838652733)
              ·
                refine ⟨1026546873050715314494775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2737458328135240838652733 1026546873050715314494775)
                ·
                  refine ⟨1539820309576072971742163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026546873050715314494775 1539820309576072971742163)
                  ·
                    refine ⟨2309730464364109457613245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1539820309576072971742163 2309730464364109457613245)
                    ·
                      refine ⟨866148924136541046604967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2309730464364109457613245 866148924136541046604967)
                      ·
                        rfl

theorem cell23_1686819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 2, 3, 1, 1, 3].length) (baseStart_1686819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686819 prefixEnd_1686819 := by exact prefixLift 1686819
  have htrace : WordTrace (prefixWord ++ tailWord_1686819) baseStart_1686819 baseEnd_1686819 := by
    simpa [prefixWord, tailWord_1686819, baseEnd_1686819] using wordTrace_append hprefix tailTrace_1686819
  have hstable : (prefixWord ++ tailWord_1686819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686819).length < 2 ^ (prefixWord ++ tailWord_1686819).sum := by decide
  have hdescent : baseEnd_1686819 < baseStart_1686819 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686828 : List Nat := [2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 5]
def baseStart_1686828 : Nat := 118140960795 + 1686828 * 2 ^ 59
def prefixEnd_1686828 : Nat := 4983230072969 + 3 ^ 40 * 1686828 * 2
def baseEnd_1686828 : Nat := 866153545462431511392425

theorem tailTrace_1686828 : CollatzResearch.WordTrace tailWord_1686828 prefixEnd_1686828 866153545462431511392425 := by
  unfold tailWord_1686828
  simp only [CollatzResearch.WordTrace]
  refine ⟨30761835766458859065854569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41015781021945145421139425 30761835766458859065854569)
  ·
    refine ⟨23071376824844144299390927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30761835766458859065854569 23071376824844144299390927)
    ·
      refine ⟨34607065237266216449086391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23071376824844144299390927 34607065237266216449086391)
      ·
        refine ⟨51910597855899324673629587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34607065237266216449086391 51910597855899324673629587)
        ·
          refine ⟨77865896783848987010444381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51910597855899324673629587 77865896783848987010444381)
          ·
            refine ⟨29199711293943370128916643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77865896783848987010444381 29199711293943370128916643)
            ·
              refine ⟨43799566940915055193374965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29199711293943370128916643 43799566940915055193374965)
              ·
                refine ⟨4106209400710786424378903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43799566940915055193374965 4106209400710786424378903)
                ·
                  refine ⟨6159314101066179636568355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106209400710786424378903 6159314101066179636568355)
                  ·
                    refine ⟨9238971151599269454852533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6159314101066179636568355 9238971151599269454852533)
                    ·
                      refine ⟨866153545462431511392425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9238971151599269454852533 866153545462431511392425)
                      ·
                        rfl

theorem cell23_1686828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 5].length) (baseStart_1686828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686828 prefixEnd_1686828 := by exact prefixLift 1686828
  have htrace : WordTrace (prefixWord ++ tailWord_1686828) baseStart_1686828 baseEnd_1686828 := by
    simpa [prefixWord, tailWord_1686828, baseEnd_1686828] using wordTrace_append hprefix tailTrace_1686828
  have hstable : (prefixWord ++ tailWord_1686828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686828).length < 2 ^ (prefixWord ++ tailWord_1686828).sum := by decide
  have hdescent : baseEnd_1686828 < baseStart_1686828 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686835 : List Nat := [1, 1, 1, 2, 5, 3, 1, 1, 4, 4]
def baseStart_1686835 : Nat := 118140960795 + 1686835 * 2 ^ 59
def prefixEnd_1686835 : Nat := 4983230072969 + 3 ^ 40 * 1686835 * 2
def baseEnd_1686835 : Nat := 288719046609004328001631

theorem tailTrace_1686835 : CollatzResearch.WordTrace tailWord_1686835 prefixEnd_1686835 288719046609004328001631 := by
  unfold tailWord_1686835
  simp only [CollatzResearch.WordTrace]
  refine ⟨61523926843892358327213959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41015951229261572218142639 61523926843892358327213959)
  ·
    refine ⟨92285890265838537490820939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61523926843892358327213959 92285890265838537490820939)
    ·
      refine ⟨138428835398757806236231409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92285890265838537490820939 138428835398757806236231409)
      ·
        refine ⟨103821626549068354677173557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138428835398757806236231409 103821626549068354677173557)
        ·
          refine ⟨9733277488975158250985021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103821626549068354677173557 9733277488975158250985021)
          ·
            refine ⟨3649979058365684344119383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9733277488975158250985021 3649979058365684344119383)
            ·
              refine ⟨5474968587548526516179075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3649979058365684344119383 5474968587548526516179075)
              ·
                refine ⟨8212452881322789774268613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5474968587548526516179075 8212452881322789774268613)
                ·
                  refine ⟨1539834915248023082675365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8212452881322789774268613 1539834915248023082675365)
                  ·
                    refine ⟨288719046609004328001631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1539834915248023082675365 288719046609004328001631)
                    ·
                      rfl

theorem cell23_1686835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 1, 4, 4].length) (baseStart_1686835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686835 prefixEnd_1686835 := by exact prefixLift 1686835
  have htrace : WordTrace (prefixWord ++ tailWord_1686835) baseStart_1686835 baseEnd_1686835 := by
    simpa [prefixWord, tailWord_1686835, baseEnd_1686835] using wordTrace_append hprefix tailTrace_1686835
  have hstable : (prefixWord ++ tailWord_1686835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686835).length < 2 ^ (prefixWord ++ tailWord_1686835).sum := by decide
  have hdescent : baseEnd_1686835 < baseStart_1686835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686852 : List Nat := [2, 3, 4, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1686852 : Nat := 118140960795 + 1686852 * 2 ^ 59
def prefixEnd_1686852 : Nat := 4983230072969 + 3 ^ 40 * 1686852 * 2
def baseEnd_1686852 : Nat := 288721956332713139164105

theorem tailTrace_1686852 : CollatzResearch.WordTrace tailWord_1686852 prefixEnd_1686852 288721956332713139164105 := by
  unfold tailWord_1686852
  simp only [CollatzResearch.WordTrace]
  refine ⟨30762273442415385115291405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41016364589887180153721873 30762273442415385115291405)
  ·
    refine ⟨11535852540905769418234277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30762273442415385115291405 11535852540905769418234277)
    ·
      refine ⟨2162972351419831765918927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11535852540905769418234277 2162972351419831765918927)
      ·
        refine ⟨3244458527129747648878391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2162972351419831765918927 3244458527129747648878391)
        ·
          refine ⟨4866687790694621473317587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3244458527129747648878391 4866687790694621473317587)
          ·
            refine ⟨7300031686041932209976381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866687790694621473317587 7300031686041932209976381)
            ·
              refine ⟨2737511882265724578741143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7300031686041932209976381 2737511882265724578741143)
              ·
                refine ⟨4106267823398586868111715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737511882265724578741143 4106267823398586868111715)
                ·
                  refine ⟨6159401735097880302167573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106267823398586868111715 6159401735097880302167573)
                  ·
                    refine ⟨288721956332713139164105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6159401735097880302167573 288721956332713139164105)
                    ·
                      rfl

theorem cell23_1686852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1686852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686852 prefixEnd_1686852 := by exact prefixLift 1686852
  have htrace : WordTrace (prefixWord ++ tailWord_1686852) baseStart_1686852 baseEnd_1686852 := by
    simpa [prefixWord, tailWord_1686852, baseEnd_1686852] using wordTrace_append hprefix tailTrace_1686852
  have hstable : (prefixWord ++ tailWord_1686852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686852).length < 2 ^ (prefixWord ++ tailWord_1686852).sum := by decide
  have hdescent : baseEnd_1686852 < baseStart_1686852 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686855 : List Nat := [1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 4]
def baseStart_1686855 : Nat := 118140960795 + 1686855 * 2 ^ 59
def prefixEnd_1686855 : Nat := 4983230072969 + 3 ^ 40 * 1686855 * 2
def baseEnd_1686855 : Nat := 866167409440102905754801

theorem tailTrace_1686855 : CollatzResearch.WordTrace tailWord_1686855 prefixEnd_1686855 866167409440102905754801 := by
  unfold tailWord_1686855
  simp only [CollatzResearch.WordTrace]
  refine ⟨61524656303819901742942019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41016437535879934495294679 61524656303819901742942019)
  ·
    refine ⟨92286984455729852614413029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61524656303819901742942019 92286984455729852614413029)
    ·
      refine ⟨17303809585449347365202443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92286984455729852614413029 17303809585449347365202443)
      ·
        refine ⟨25955714378174021047803665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17303809585449347365202443 25955714378174021047803665)
        ·
          refine ⟨19466785783630515785852749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25955714378174021047803665 19466785783630515785852749)
          ·
            refine ⟨7300044668861443419694781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19466785783630515785852749 7300044668861443419694781)
            ·
              refine ⟨2737516750823041282385543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7300044668861443419694781 2737516750823041282385543)
              ·
                refine ⟨4106275126234561923578315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737516750823041282385543 4106275126234561923578315)
                ·
                  refine ⟨6159412689351842885367473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4106275126234561923578315 6159412689351842885367473)
                  ·
                    refine ⟨4619559517013882164025605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6159412689351842885367473 4619559517013882164025605)
                    ·
                      refine ⟨866167409440102905754801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4619559517013882164025605 866167409440102905754801)
                      ·
                        rfl

theorem cell23_1686855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_1686855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686855 prefixEnd_1686855 := by exact prefixLift 1686855
  have htrace : WordTrace (prefixWord ++ tailWord_1686855) baseStart_1686855 baseEnd_1686855 := by
    simpa [prefixWord, tailWord_1686855, baseEnd_1686855] using wordTrace_append hprefix tailTrace_1686855
  have hstable : (prefixWord ++ tailWord_1686855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686855).length < 2 ^ (prefixWord ++ tailWord_1686855).sum := by decide
  have hdescent : baseEnd_1686855 < baseStart_1686855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686862 : List Nat := [4, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3]
def baseStart_1686862 : Nat := 118140960795 + 1686862 * 2 ^ 59
def prefixEnd_1686862 : Nat := 4983230072969 + 3 ^ 40 * 1686862 * 2
def baseEnd_1686862 : Nat := 866171003804684378367269

theorem tailTrace_1686862 : CollatzResearch.WordTrace tailWord_1686862 prefixEnd_1686862 866171003804684378367269 := by
  unfold tailWord_1686862
  simp only [CollatzResearch.WordTrace]
  refine ⟨7690613951849317742305855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41016607743196361292297893 7690613951849317742305855)
  ·
    refine ⟨11535920927773976613458783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7690613951849317742305855 11535920927773976613458783)
    ·
      refine ⟨17303881391660964920188175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11535920927773976613458783 17303881391660964920188175)
      ·
        refine ⟨25955822087491447380282263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17303881391660964920188175 25955822087491447380282263)
        ·
          refine ⟨38933733131237171070423395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25955822087491447380282263 38933733131237171070423395)
          ·
            refine ⟨58400599696855756605635093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38933733131237171070423395 58400599696855756605635093)
            ·
              refine ⟨2737528110790113590889145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58400599696855756605635093 2737528110790113590889145)
              ·
                refine ⟨2053146083092585193166859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2737528110790113590889145 2053146083092585193166859)
                ·
                  refine ⟨3079719124638877789750289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053146083092585193166859 3079719124638877789750289)
                  ·
                    refine ⟨2309789343479158342312717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3079719124638877789750289 2309789343479158342312717)
                    ·
                      refine ⟨866171003804684378367269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2309789343479158342312717 866171003804684378367269)
                      ·
                        rfl

theorem cell23_1686862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 2, 1, 2, 3].length) (baseStart_1686862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686862 prefixEnd_1686862 := by exact prefixLift 1686862
  have htrace : WordTrace (prefixWord ++ tailWord_1686862) baseStart_1686862 baseEnd_1686862 := by
    simpa [prefixWord, tailWord_1686862, baseEnd_1686862] using wordTrace_append hprefix tailTrace_1686862
  have hstable : (prefixWord ++ tailWord_1686862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686862).length < 2 ^ (prefixWord ++ tailWord_1686862).sum := by decide
  have hdescent : baseEnd_1686862 < baseStart_1686862 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686892 : List Nat := [2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 3]
def baseStart_1686892 : Nat := 118140960795 + 1686892 * 2 ^ 59
def prefixEnd_1686892 : Nat := 4983230072969 + 3 ^ 40 * 1686892 * 2
def baseEnd_1686892 : Nat := 866186408224319260992131

theorem tailTrace_1686892 : CollatzResearch.WordTrace tailWord_1686892 prefixEnd_1686892 866186408224319260992131 := by
  unfold tailWord_1686892
  simp only [CollatzResearch.WordTrace]
  refine ⟨30763002902342928531019465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41017337203123904708025953 30763002902342928531019465)
  ·
    refine ⟨23072252176757196398264599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30763002902342928531019465 23072252176757196398264599)
    ·
      refine ⟨34608378265135794597396899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23072252176757196398264599 34608378265135794597396899)
      ·
        refine ⟨51912567397703691896095349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34608378265135794597396899 51912567397703691896095349)
        ·
          refine ⟨4866803193534721115258939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51912567397703691896095349 4866803193534721115258939)
          ·
            refine ⟨7300204790302081672888409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4866803193534721115258939 7300204790302081672888409)
            ·
              refine ⟨5475153592726561254666307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300204790302081672888409 5475153592726561254666307)
              ·
                refine ⟨8212730389089841881999461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5475153592726561254666307 8212730389089841881999461)
                ·
                  refine ⟨1539886947954345352874899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8212730389089841881999461 1539886947954345352874899)
                  ·
                    refine ⟨2309830421931518029312349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1539886947954345352874899 2309830421931518029312349)
                    ·
                      refine ⟨866186408224319260992131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2309830421931518029312349 866186408224319260992131)
                      ·
                        rfl

theorem cell23_1686892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 3].length) (baseStart_1686892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686892 prefixEnd_1686892 := by exact prefixLift 1686892
  have htrace : WordTrace (prefixWord ++ tailWord_1686892) baseStart_1686892 baseEnd_1686892 := by
    simpa [prefixWord, tailWord_1686892, baseEnd_1686892] using wordTrace_append hprefix tailTrace_1686892
  have hstable : (prefixWord ++ tailWord_1686892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686892).length < 2 ^ (prefixWord ++ tailWord_1686892).sum := by decide
  have hdescent : baseEnd_1686892 < baseStart_1686892 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686893 : List Nat := [1, 5, 1, 1, 1, 4, 3, 2, 1, 2, 2]
def baseStart_1686893 : Nat := 118140960795 + 1686893 * 2 ^ 59
def prefixEnd_1686893 : Nat := 4983230072969 + 3 ^ 40 * 1686893 * 2
def baseEnd_1686893 : Nat := 866186921704973757079627

theorem tailTrace_1686893 : CollatzResearch.WordTrace tailWord_1686893 prefixEnd_1686893 866186921704973757079627 := by
  unfold tailWord_1686893
  simp only [CollatzResearch.WordTrace]
  refine ⟨61526042277682234232825333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41017361518454822821883555 61526042277682234232825333)
  ·
    refine ⟨5768066463532709459327375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61526042277682234232825333 5768066463532709459327375)
    ·
      refine ⟨8652099695299064188991063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5768066463532709459327375 8652099695299064188991063)
      ·
        refine ⟨12978149542948596283486595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8652099695299064188991063 12978149542948596283486595)
        ·
          refine ⟨19467224314422894425229893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12978149542948596283486595 19467224314422894425229893)
          ·
            refine ⟨3650104558954292704730605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19467224314422894425229893 3650104558954292704730605)
            ·
              refine ⟨1368789209607859764273977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3650104558954292704730605 1368789209607859764273977)
              ·
                refine ⟨1026591907205894823205483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368789209607859764273977 1026591907205894823205483)
                ·
                  refine ⟨1539887860808842234808225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026591907205894823205483 1539887860808842234808225)
                  ·
                    refine ⟨1154915895606631676106169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1539887860808842234808225 1154915895606631676106169)
                    ·
                      refine ⟨866186921704973757079627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154915895606631676106169 866186921704973757079627)
                      ·
                        rfl

theorem cell23_1686893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 1, 2, 2].length) (baseStart_1686893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686893 prefixEnd_1686893 := by exact prefixLift 1686893
  have htrace : WordTrace (prefixWord ++ tailWord_1686893) baseStart_1686893 baseEnd_1686893 := by
    simpa [prefixWord, tailWord_1686893, baseEnd_1686893] using wordTrace_append hprefix tailTrace_1686893
  have hstable : (prefixWord ++ tailWord_1686893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686893).length < 2 ^ (prefixWord ++ tailWord_1686893).sum := by decide
  have hdescent : baseEnd_1686893 < baseStart_1686893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686908 : List Nat := [2, 2, 2, 1, 1, 1, 4, 1, 1, 8]
def baseStart_1686908 : Nat := 118140960795 + 1686908 * 2 ^ 59
def prefixEnd_1686908 : Nat := 4983230072969 + 3 ^ 40 * 1686908 * 2
def baseEnd_1686908 : Nat := 288731541304930399464019

theorem tailTrace_1686908 : CollatzResearch.WordTrace tailWord_1686908 prefixEnd_1686908 288731541304930399464019 := by
  unfold tailWord_1686908
  simp only [CollatzResearch.WordTrace]
  refine ⟨30763294686313945897310689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41017726248418594529747585 30763294686313945897310689)
  ·
    refine ⟨23072471014735459422983017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30763294686313945897310689 23072471014735459422983017)
    ·
      refine ⟨17304353261051594567237263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23072471014735459422983017 17304353261051594567237263)
      ·
        refine ⟨25956529891577391850855895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17304353261051594567237263 25956529891577391850855895)
        ·
          refine ⟨38934794837366087776283843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25956529891577391850855895 38934794837366087776283843)
          ·
            refine ⟨58402192256049131664425765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38934794837366087776283843 58402192256049131664425765)
            ·
              refine ⟨10950411048009212187079831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58402192256049131664425765 10950411048009212187079831)
              ·
                refine ⟨16425616572013818280619747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10950411048009212187079831 16425616572013818280619747)
                ·
                  refine ⟨24638424858020727420929621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16425616572013818280619747 24638424858020727420929621)
                  ·
                    refine ⟨288731541304930399464019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24638424858020727420929621 288731541304930399464019)
                    ·
                      rfl

theorem cell23_1686908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 8].length) (baseStart_1686908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686908 prefixEnd_1686908 := by exact prefixLift 1686908
  have htrace : WordTrace (prefixWord ++ tailWord_1686908) baseStart_1686908 baseEnd_1686908 := by
    simpa [prefixWord, tailWord_1686908, baseEnd_1686908] using wordTrace_append hprefix tailTrace_1686908
  have hstable : (prefixWord ++ tailWord_1686908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686908).length < 2 ^ (prefixWord ++ tailWord_1686908).sum := by decide
  have hdescent : baseEnd_1686908 < baseStart_1686908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686919 : List Nat := [1, 1, 4, 2, 2, 2, 3, 2, 1, 3, 2]
def baseStart_1686919 : Nat := 118140960795 + 1686919 * 2 ^ 59
def prefixEnd_1686919 : Nat := 4983230072969 + 3 ^ 40 * 1686919 * 2
def baseEnd_1686919 : Nat := 866200272201990655354507

theorem tailTrace_1686919 : CollatzResearch.WordTrace tailWord_1686919 prefixEnd_1686919 866200272201990655354507 := by
  unfold tailWord_1686919
  simp only [CollatzResearch.WordTrace]
  refine ⟨61526990575588040673271811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41017993717058693782181207 61526990575588040673271811)
  ·
    refine ⟨92290485863382061009907717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61526990575588040673271811 92290485863382061009907717)
    ·
      refine ⟨17304466099384136439357697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92290485863382061009907717 17304466099384136439357697)
      ·
        refine ⟨12978349574538102329518273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17304466099384136439357697 12978349574538102329518273)
        ·
          refine ⟨9733762180903576747138705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12978349574538102329518273 9733762180903576747138705)
          ·
            refine ⟨7300321635677682560354029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9733762180903576747138705 7300321635677682560354029)
            ·
              refine ⟨2737620613379130960132761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7300321635677682560354029 2737620613379130960132761)
              ·
                refine ⟨2053215460034348220099571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2737620613379130960132761 2053215460034348220099571)
                ·
                  refine ⟨3079823190051522330149357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053215460034348220099571 3079823190051522330149357)
                  ·
                    refine ⟨1154933696269320873806009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3079823190051522330149357 1154933696269320873806009)
                    ·
                      refine ⟨866200272201990655354507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1154933696269320873806009 866200272201990655354507)
                      ·
                        rfl

theorem cell23_1686919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_1686919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686919 prefixEnd_1686919 := by exact prefixLift 1686919
  have htrace : WordTrace (prefixWord ++ tailWord_1686919) baseStart_1686919 baseEnd_1686919 := by
    simpa [prefixWord, tailWord_1686919, baseEnd_1686919] using wordTrace_append hprefix tailTrace_1686919
  have hstable : (prefixWord ++ tailWord_1686919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686919).length < 2 ^ (prefixWord ++ tailWord_1686919).sum := by decide
  have hdescent : baseEnd_1686919 < baseStart_1686919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1686972 : List Nat := [2, 2, 2, 4, 2, 1, 1, 2, 7]
def baseStart_1686972 : Nat := 118140960795 + 1686972 * 2 ^ 59
def prefixEnd_1686972 : Nat := 4983230072969 + 3 ^ 40 * 1686972 * 2
def baseEnd_1686972 : Nat := 96247498519630994221307

theorem tailTrace_1686972 : CollatzResearch.WordTrace tailWord_1686972 prefixEnd_1686972 96247498519630994221307 := by
  unfold tailWord_1686972
  simp only [CollatzResearch.WordTrace]
  refine ⟨30764461822198015362475585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41019282429597353816634113 30764461822198015362475585)
  ·
    refine ⟨23073346366648511521856689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30764461822198015362475585 23073346366648511521856689)
    ·
      refine ⟨17305009774986383641392517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23073346366648511521856689 17305009774986383641392517)
      ·
        refine ⟨3244689332809946932761097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17305009774986383641392517 3244689332809946932761097)
        ·
          refine ⟨2433516999607460199570823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3244689332809946932761097 2433516999607460199570823)
          ·
            refine ⟨3650275499411190299356235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2433516999607460199570823 3650275499411190299356235)
            ·
              refine ⟨5475413249116785449034353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3650275499411190299356235 5475413249116785449034353)
              ·
                refine ⟨4106559936837589086775765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5475413249116785449034353 4106559936837589086775765)
                ·
                  refine ⟨96247498519630994221307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4106559936837589086775765 96247498519630994221307)
                  ·
                    rfl

theorem cell23_1686972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 2, 7].length) (baseStart_1686972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1686972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1686972 prefixEnd_1686972 := by exact prefixLift 1686972
  have htrace : WordTrace (prefixWord ++ tailWord_1686972) baseStart_1686972 baseEnd_1686972 := by
    simpa [prefixWord, tailWord_1686972, baseEnd_1686972] using wordTrace_append hprefix tailTrace_1686972
  have hstable : (prefixWord ++ tailWord_1686972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1686972).length < 2 ^ (prefixWord ++ tailWord_1686972).sum := by decide
  have hdescent : baseEnd_1686972 < baseStart_1686972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1686972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687032 : List Nat := [2, 1, 2, 1, 1, 5, 2, 2, 3, 4]
def baseStart_1687032 : Nat := 118140960795 + 1687032 * 2 ^ 59
def prefixEnd_1687032 : Nat := 4983230072969 + 3 ^ 40 * 1687032 * 2
def baseEnd_1687032 : Nat := 288752765171982904413829

theorem tailTrace_1687032 : CollatzResearch.WordTrace tailWord_1687032 prefixEnd_1687032 288752765171982904413829 := by
  unfold tailWord_1687032
  simp only [CollatzResearch.WordTrace]
  refine ⟨30765556012089330486067675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41020741349452440648090233 30765556012089330486067675)
  ·
    refine ⟨46148334018133995729101513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30765556012089330486067675 46148334018133995729101513)
    ·
      refine ⟨34611250513600496796826135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46148334018133995729101513 34611250513600496796826135)
      ·
        refine ⟨51916875770400745195239203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34611250513600496796826135 51916875770400745195239203)
        ·
          refine ⟨77875313655601117792858805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51916875770400745195239203 77875313655601117792858805)
          ·
            refine ⟨7300810655212604793080513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77875313655601117792858805 7300810655212604793080513)
            ·
              refine ⟨5475607991409453594810385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7300810655212604793080513 5475607991409453594810385)
              ·
                refine ⟨4106705993557090196107789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5475607991409453594810385 4106705993557090196107789)
                ·
                  refine ⟨1540014747583908823540421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4106705993557090196107789 1540014747583908823540421)
                  ·
                    refine ⟨288752765171982904413829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1540014747583908823540421 288752765171982904413829)
                    ·
                      rfl

theorem cell23_1687032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 2, 2, 3, 4].length) (baseStart_1687032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687032 prefixEnd_1687032 := by exact prefixLift 1687032
  have htrace : WordTrace (prefixWord ++ tailWord_1687032) baseStart_1687032 baseEnd_1687032 := by
    simpa [prefixWord, tailWord_1687032, baseEnd_1687032] using wordTrace_append hprefix tailTrace_1687032
  have hstable : (prefixWord ++ tailWord_1687032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687032).length < 2 ^ (prefixWord ++ tailWord_1687032).sum := by decide
  have hdescent : baseEnd_1687032 < baseStart_1687032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687055 : List Nat := [1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 3]
def baseStart_1687055 : Nat := 118140960795 + 1687055 * 2 ^ 59
def prefixEnd_1687055 : Nat := 4983230072969 + 3 ^ 40 * 1687055 * 2
def baseEnd_1687055 : Nat := 866270105571002123253881

theorem tailTrace_1687055 : CollatzResearch.WordTrace tailWord_1687055 prefixEnd_1687055 866270105571002123253881 := by
  unfold tailWord_1687055
  simp only [CollatzResearch.WordTrace]
  refine ⟨61531950903095335900222619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41021300602063557266815079 61531950903095335900222619)
  ·
    refine ⟨92297926354643003850333929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61531950903095335900222619 92297926354643003850333929)
    ·
      refine ⟨69223444765982252887750447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92297926354643003850333929 69223444765982252887750447)
      ·
        refine ⟨103835167148973379331625671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69223444765982252887750447 103835167148973379331625671)
        ·
          refine ⟨155752750723460068997438507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103835167148973379331625671 155752750723460068997438507)
          ·
            refine ⟨233629126085190103496157761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155752750723460068997438507 233629126085190103496157761)
            ·
              refine ⟨175221844563892577622118321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 233629126085190103496157761 175221844563892577622118321)
              ·
                refine ⟨131416383422919433216588741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175221844563892577622118321 131416383422919433216588741)
                ·
                  refine ⟨24640571891797393728110389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131416383422919433216588741 24640571891797393728110389)
                  ·
                    refine ⟨2310053614856005662010349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24640571891797393728110389 2310053614856005662010349)
                    ·
                      refine ⟨866270105571002123253881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2310053614856005662010349 866270105571002123253881)
                      ·
                        rfl

theorem cell23_1687055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 2, 4, 5, 3].length) (baseStart_1687055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687055 prefixEnd_1687055 := by exact prefixLift 1687055
  have htrace : WordTrace (prefixWord ++ tailWord_1687055) baseStart_1687055 baseEnd_1687055 := by
    simpa [prefixWord, tailWord_1687055, baseEnd_1687055] using wordTrace_append hprefix tailTrace_1687055
  have hstable : (prefixWord ++ tailWord_1687055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687055).length < 2 ^ (prefixWord ++ tailWord_1687055).sum := by decide
  have hdescent : baseEnd_1687055 < baseStart_1687055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687109 : List Nat := [1, 3, 1, 1, 1, 4, 5, 1, 1, 5]
def baseStart_1687109 : Nat := 118140960795 + 1687109 * 2 ^ 59
def prefixEnd_1687109 : Nat := 4983230072969 + 3 ^ 40 * 1687109 * 2
def baseEnd_1687109 : Nat := 288765944508781637326211

theorem tailTrace_1687109 : CollatzResearch.WordTrace tailWord_1687109 prefixEnd_1687109 288765944508781637326211 := by
  unfold tailWord_1687109
  simp only [CollatzResearch.WordTrace]
  refine ⟨61533920444899703122688381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41022613629933135415125587 61533920444899703122688381)
  ·
    refine ⟨23075220166837388671008143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61533920444899703122688381 23075220166837388671008143)
    ·
      refine ⟨34612830250256083006512215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23075220166837388671008143 34612830250256083006512215)
      ·
        refine ⟨51919245375384124509768323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34612830250256083006512215 51919245375384124509768323)
        ·
          refine ⟨77878868063076186764652485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51919245375384124509768323 77878868063076186764652485)
          ·
            refine ⟨14602287761826785018372341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77878868063076186764652485 14602287761826785018372341)
            ·
              refine ⟨1368964477671261095472407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14602287761826785018372341 1368964477671261095472407)
              ·
                refine ⟨2053446716506891643208611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1368964477671261095472407 2053446716506891643208611)
                ·
                  refine ⟨3080170074760337464812917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053446716506891643208611 3080170074760337464812917)
                  ·
                    refine ⟨288765944508781637326211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3080170074760337464812917 288765944508781637326211)
                    ·
                      rfl

theorem cell23_1687109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 5].length) (baseStart_1687109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687109 prefixEnd_1687109 := by exact prefixLift 1687109
  have htrace : WordTrace (prefixWord ++ tailWord_1687109) baseStart_1687109 baseEnd_1687109 := by
    simpa [prefixWord, tailWord_1687109, baseEnd_1687109] using wordTrace_append hprefix tailTrace_1687109
  have hstable : (prefixWord ++ tailWord_1687109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687109).length < 2 ^ (prefixWord ++ tailWord_1687109).sum := by decide
  have hdescent : baseEnd_1687109 < baseStart_1687109 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687117 : List Nat := [1, 6, 1, 1, 4, 1, 2, 2, 1, 4]
def baseStart_1687117 : Nat := 118140960795 + 1687117 * 2 ^ 59
def prefixEnd_1687117 : Nat := 4983230072969 + 3 ^ 40 * 1687117 * 2
def baseEnd_1687117 : Nat := 288767313790526960226199

theorem tailTrace_1687117 : CollatzResearch.WordTrace tailWord_1687117 prefixEnd_1687117 288767313790526960226199 := by
  unfold tailWord_1687117
  simp only [CollatzResearch.WordTrace]
  refine ⟨61534212228870720488979605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41022808152580480325986403 61534212228870720488979605)
  ·
    refine ⟨2884416198228315022920919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 61534212228870720488979605 2884416198228315022920919)
    ·
      refine ⟨4326624297342472534381379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2884416198228315022920919 4326624297342472534381379)
      ·
        refine ⟨6489936446013708801572069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4326624297342472534381379 6489936446013708801572069)
        ·
          refine ⟨1216863083627570400294763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6489936446013708801572069 1216863083627570400294763)
          ·
            refine ⟨1825294625441355600442145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216863083627570400294763 1825294625441355600442145)
            ·
              refine ⟨1368970969081016700331609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1825294625441355600442145 1368970969081016700331609)
              ·
                refine ⟨1026728226810762525248707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1368970969081016700331609 1026728226810762525248707)
                ·
                  refine ⟨1540092340216143787873061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026728226810762525248707 1540092340216143787873061)
                  ·
                    refine ⟨288767313790526960226199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1540092340216143787873061 288767313790526960226199)
                    ·
                      rfl

theorem cell23_1687117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 2, 2, 1, 4].length) (baseStart_1687117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687117 prefixEnd_1687117 := by exact prefixLift 1687117
  have htrace : WordTrace (prefixWord ++ tailWord_1687117) baseStart_1687117 baseEnd_1687117 := by
    simpa [prefixWord, tailWord_1687117, baseEnd_1687117] using wordTrace_append hprefix tailTrace_1687117
  have hstable : (prefixWord ++ tailWord_1687117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687117).length < 2 ^ (prefixWord ++ tailWord_1687117).sum := by decide
  have hdescent : baseEnd_1687117 < baseStart_1687117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687129 : List Nat := [1, 2, 1, 2, 2, 1, 1, 2, 7, 2, 2]
def baseStart_1687129 : Nat := 118140960795 + 1687129 * 2 ^ 59
def prefixEnd_1687129 : Nat := 4983230072969 + 3 ^ 40 * 1687129 * 2
def baseEnd_1687129 : Nat := 866308103139434833728541

theorem tailTrace_1687129 : CollatzResearch.WordTrace tailWord_1687129 prefixEnd_1687129 866308103139434833728541 := by
  unfold tailWord_1687129
  simp only [CollatzResearch.WordTrace]
  refine ⟨61534649904827246538416441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41023099936551497692277627 61534649904827246538416441)
  ·
    refine ⟨46150987428620434903812331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61534649904827246538416441 46150987428620434903812331)
    ·
      refine ⟨69226481142930652355718497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46150987428620434903812331 69226481142930652355718497)
      ·
        refine ⟨51919860857197989266788873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69226481142930652355718497 51919860857197989266788873)
        ·
          refine ⟨38939895642898491950091655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51919860857197989266788873 38939895642898491950091655)
          ·
            refine ⟨58409843464347737925137483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38939895642898491950091655 58409843464347737925137483)
            ·
              refine ⟨87614765196521606887706225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58409843464347737925137483 87614765196521606887706225)
              ·
                refine ⟨65711073897391205165779669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87614765196521606887706225 65711073897391205165779669)
                ·
                  refine ⟨1540103294470106371072961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 65711073897391205165779669 1540103294470106371072961)
                  ·
                    refine ⟨1155077470852579778304721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1540103294470106371072961 1155077470852579778304721)
                    ·
                      refine ⟨866308103139434833728541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155077470852579778304721 866308103139434833728541)
                      ·
                        rfl

theorem cell23_1687129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 2, 7, 2, 2].length) (baseStart_1687129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687129 prefixEnd_1687129 := by exact prefixLift 1687129
  have htrace : WordTrace (prefixWord ++ tailWord_1687129) baseStart_1687129 baseEnd_1687129 := by
    simpa [prefixWord, tailWord_1687129, baseEnd_1687129] using wordTrace_append hprefix tailTrace_1687129
  have hstable : (prefixWord ++ tailWord_1687129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687129).length < 2 ^ (prefixWord ++ tailWord_1687129).sum := by decide
  have hdescent : baseEnd_1687129 < baseStart_1687129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687139 : List Nat := [1, 1, 1, 5, 1, 3, 2, 3, 2, 4]
def baseStart_1687139 : Nat := 118140960795 + 1687139 * 2 ^ 59
def prefixEnd_1687139 : Nat := 4983230072969 + 3 ^ 40 * 1687139 * 2
def baseEnd_1687139 : Nat := 288771079315326598201165

theorem tailTrace_1687139 : CollatzResearch.WordTrace tailWord_1687139 prefixEnd_1687139 288771079315326598201165 := by
  unfold tailWord_1687139
  simp only [CollatzResearch.WordTrace]
  refine ⟨61535014634791018246280471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41023343089860678830853647 61535014634791018246280471)
  ·
    refine ⟨92302521952186527369420707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61535014634791018246280471 92302521952186527369420707)
    ·
      refine ⟨138453782928279791054131061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92302521952186527369420707 138453782928279791054131061)
      ·
        refine ⟨12980042149526230411324787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 138453782928279791054131061 12980042149526230411324787)
        ·
          refine ⟨19470063224289345616987181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12980042149526230411324787 19470063224289345616987181)
          ·
            refine ⟨7301273709108504606370193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19470063224289345616987181 7301273709108504606370193)
            ·
              refine ⟨5475955281831378454777645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7301273709108504606370193 5475955281831378454777645)
              ·
                refine ⟨2053483230686766920541617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5475955281831378454777645 2053483230686766920541617)
                ·
                  refine ⟨1540112423015075190406213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2053483230686766920541617 1540112423015075190406213)
                  ·
                    refine ⟨288771079315326598201165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1540112423015075190406213 288771079315326598201165)
                    ·
                      rfl

theorem cell23_1687139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 4].length) (baseStart_1687139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687139 prefixEnd_1687139 := by exact prefixLift 1687139
  have htrace : WordTrace (prefixWord ++ tailWord_1687139) baseStart_1687139 baseEnd_1687139 := by
    simpa [prefixWord, tailWord_1687139, baseEnd_1687139] using wordTrace_append hprefix tailTrace_1687139
  have hstable : (prefixWord ++ tailWord_1687139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687139).length < 2 ^ (prefixWord ++ tailWord_1687139).sum := by decide
  have hdescent : baseEnd_1687139 < baseStart_1687139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687146 : List Nat := [3, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2]
def baseStart_1687146 : Nat := 118140960795 + 1687146 * 2 ^ 59
def prefixEnd_1687146 : Nat := 4983230072969 + 3 ^ 40 * 1687146 * 2
def baseEnd_1687146 : Nat := 866316832310561267215963

theorem tailTrace_1687146 : CollatzResearch.WordTrace tailWord_1687146 prefixEnd_1687146 866316832310561267215963 := by
  unfold tailWord_1687146
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383817486441414610446323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41023513297177105627856861 15383817486441414610446323)
  ·
    refine ⟨23075726229662121915669485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15383817486441414610446323 23075726229662121915669485)
    ·
      refine ⟨8653397336123295718376057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23075726229662121915669485 8653397336123295718376057)
      ·
        refine ⟨6490048002092471788782043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8653397336123295718376057 6490048002092471788782043)
        ·
          refine ⟨9735072003138707683173065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6490048002092471788782043 9735072003138707683173065)
          ·
            refine ⟨7301304002354030762379799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9735072003138707683173065 7301304002354030762379799)
            ·
              refine ⟨10951956003531046143569699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7301304002354030762379799 10951956003531046143569699)
              ·
                refine ⟨16427934005296569215354549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10951956003531046143569699 16427934005296569215354549)
                ·
                  refine ⟨1540118812996553363939489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16427934005296569215354549 1540118812996553363939489)
                  ·
                    refine ⟨1155089109747415022954617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1540118812996553363939489 1155089109747415022954617)
                    ·
                      refine ⟨866316832310561267215963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155089109747415022954617 866316832310561267215963)
                      ·
                        rfl

theorem cell23_1687146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 1, 5, 2, 2].length) (baseStart_1687146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687146 prefixEnd_1687146 := by exact prefixLift 1687146
  have htrace : WordTrace (prefixWord ++ tailWord_1687146) baseStart_1687146 baseEnd_1687146 := by
    simpa [prefixWord, tailWord_1687146, baseEnd_1687146] using wordTrace_append hprefix tailTrace_1687146
  have hstable : (prefixWord ++ tailWord_1687146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687146).length < 2 ^ (prefixWord ++ tailWord_1687146).sum := by decide
  have hdescent : baseEnd_1687146 < baseStart_1687146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687150 : List Nat := [4, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2]
def baseStart_1687150 : Nat := 118140960795 + 1687150 * 2 ^ 59
def prefixEnd_1687150 : Nat := 4983230072969 + 3 ^ 40 * 1687150 * 2
def baseEnd_1687150 : Nat := 866318886233179251565945

theorem tailTrace_1687150 : CollatzResearch.WordTrace tailWord_1687150 prefixEnd_1687150 866318886233179251565945 := by
  unfold tailWord_1687150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7691926979718895890616363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41023610558500778083287269 7691926979718895890616363)
  ·
    refine ⟨11537890469578343835924545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7691926979718895890616363 11537890469578343835924545)
    ·
      refine ⟨8653417852183757876943409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11537890469578343835924545 8653417852183757876943409)
      ·
        refine ⟨6490063389137818407707557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8653417852183757876943409 6490063389137818407707557)
        ·
          refine ⟨1216886885463340951445167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6490063389137818407707557 1216886885463340951445167)
          ·
            refine ⟨1825330328195011427167751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1216886885463340951445167 1825330328195011427167751)
            ·
              refine ⟨2737995492292517140751627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825330328195011427167751 2737995492292517140751627)
              ·
                refine ⟨4106993238438775711127441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2737995492292517140751627 4106993238438775711127441)
                ·
                  refine ⟨3080244928829081783345581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4106993238438775711127441 3080244928829081783345581)
                  ·
                    refine ⟨1155091848310905668754593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080244928829081783345581 1155091848310905668754593)
                    ·
                      refine ⟨866318886233179251565945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155091848310905668754593 866318886233179251565945)
                      ·
                        rfl

theorem cell23_1687150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 4, 1, 1, 1, 2, 3, 2].length) (baseStart_1687150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687150 prefixEnd_1687150 := by exact prefixLift 1687150
  have htrace : WordTrace (prefixWord ++ tailWord_1687150) baseStart_1687150 baseEnd_1687150 := by
    simpa [prefixWord, tailWord_1687150, baseEnd_1687150] using wordTrace_append hprefix tailTrace_1687150
  have hstable : (prefixWord ++ tailWord_1687150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687150).length < 2 ^ (prefixWord ++ tailWord_1687150).sum := by decide
  have hdescent : baseEnd_1687150 < baseStart_1687150 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687155 : List Nat := [1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6]
def baseStart_1687155 : Nat := 118140960795 + 1687155 * 2 ^ 59
def prefixEnd_1687155 : Nat := 4983230072969 + 3 ^ 40 * 1687155 * 2
def baseEnd_1687155 : Nat := 866321453636451732003421

theorem tailTrace_1687155 : CollatzResearch.WordTrace tailWord_1687155 prefixEnd_1687155 866321453636451732003421 := by
  unfold tailWord_1687155
  simp only [CollatzResearch.WordTrace]
  refine ⟨61535598202733052978862919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41023732135155368652575279 61535598202733052978862919)
  ·
    refine ⟨92303397304099579468294379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61535598202733052978862919 92303397304099579468294379)
    ·
      refine ⟨138455095956149369202441569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92303397304099579468294379 138455095956149369202441569)
      ·
        refine ⟨103841321967112026901831177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138455095956149369202441569 103841321967112026901831177)
        ·
          refine ⟨77880991475334020176373383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103841321967112026901831177 77880991475334020176373383)
          ·
            refine ⟨116821487213001030264560075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77880991475334020176373383 116821487213001030264560075)
            ·
              refine ⟨175232230819501545396840113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116821487213001030264560075 175232230819501545396840113)
              ·
                refine ⟨131424173114626159047630085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 175232230819501545396840113 131424173114626159047630085)
                ·
                  refine ⟨24642032458992404821430641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131424173114626159047630085 24642032458992404821430641)
                  ·
                    refine ⟨18481524344244303616072981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24642032458992404821430641 18481524344244303616072981)
                    ·
                      refine ⟨866321453636451732003421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18481524344244303616072981 866321453636451732003421)
                      ·
                        rfl

theorem cell23_1687155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 2, 6].length) (baseStart_1687155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687155 prefixEnd_1687155 := by exact prefixLift 1687155
  have htrace : WordTrace (prefixWord ++ tailWord_1687155) baseStart_1687155 baseEnd_1687155 := by
    simpa [prefixWord, tailWord_1687155, baseEnd_1687155] using wordTrace_append hprefix tailTrace_1687155
  have hstable : (prefixWord ++ tailWord_1687155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687155).length < 2 ^ (prefixWord ++ tailWord_1687155).sum := by decide
  have hdescent : baseEnd_1687155 < baseStart_1687155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687162 : List Nat := [3, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3]
def baseStart_1687162 : Nat := 118140960795 + 1687162 * 2 ^ 59
def prefixEnd_1687162 : Nat := 4983230072969 + 3 ^ 40 * 1687162 * 2
def baseEnd_1687162 : Nat := 866325048001033204615889

theorem tailTrace_1687162 : CollatzResearch.WordTrace tailWord_1687162 prefixEnd_1687162 866325048001033204615889 := by
  unfold tailWord_1687162
  simp only [CollatzResearch.WordTrace]
  refine ⟨15383963378426923293591935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41023902342471795449578493 15383963378426923293591935)
  ·
    refine ⟨23075945067640384940387903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15383963378426923293591935 23075945067640384940387903)
    ·
      refine ⟨34613917601460577410581855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23075945067640384940387903 34613917601460577410581855)
      ·
        refine ⟨51920876402190866115872783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34613917601460577410581855 51920876402190866115872783)
        ·
          refine ⟨77881314603286299173809175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51920876402190866115872783 77881314603286299173809175)
          ·
            refine ⟨116821971904929448760713763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77881314603286299173809175 116821971904929448760713763)
            ·
              refine ⟨175232957857394173141070645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116821971904929448760713763 175232957857394173141070645)
              ·
                refine ⟨16428089799130703731975373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 175232957857394173141070645 16428089799130703731975373)
                ·
                  refine ⟨6160533674674013899490765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16428089799130703731975373 6160533674674013899490765)
                  ·
                    refine ⟨2310200128002755212309037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6160533674674013899490765 2310200128002755212309037)
                    ·
                      refine ⟨866325048001033204615889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2310200128002755212309037 866325048001033204615889)
                      ·
                        rfl

theorem cell23_1687162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 5, 3, 3, 3].length) (baseStart_1687162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687162 prefixEnd_1687162 := by exact prefixLift 1687162
  have htrace : WordTrace (prefixWord ++ tailWord_1687162) baseStart_1687162 baseEnd_1687162 := by
    simpa [prefixWord, tailWord_1687162, baseEnd_1687162] using wordTrace_append hprefix tailTrace_1687162
  have hstable : (prefixWord ++ tailWord_1687162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687162).length < 2 ^ (prefixWord ++ tailWord_1687162).sum := by decide
  have hdescent : baseEnd_1687162 < baseStart_1687162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687163 : List Nat := [1, 1, 1, 1, 1, 4, 6, 3, 1, 2, 2]
def baseStart_1687163 : Nat := 118140960795 + 1687163 * 2 ^ 59
def prefixEnd_1687163 : Nat := 4983230072969 + 3 ^ 40 * 1687163 * 2
def baseEnd_1687163 : Nat := 866325561481687700703385

theorem tailTrace_1687163 : CollatzResearch.WordTrace tailWord_1687163 prefixEnd_1687163 866325561481687700703385 := by
  unfold tailWord_1687163
  simp only [CollatzResearch.WordTrace]
  refine ⟨61535889986704070345154143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41023926657802713563436095 61535889986704070345154143)
  ·
    refine ⟨92303834980056105517731215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61535889986704070345154143 92303834980056105517731215)
    ·
      refine ⟨138455752470084158276596823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92303834980056105517731215 138455752470084158276596823)
      ·
        refine ⟨207683628705126237414895235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138455752470084158276596823 207683628705126237414895235)
        ·
          refine ⟨311525443057689356122342853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207683628705126237414895235 311525443057689356122342853)
          ·
            refine ⟨58411020573316754272939285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 311525443057689356122342853 58411020573316754272939285)
            ·
              refine ⟨2738016589374222856544029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58411020573316754272939285 2738016589374222856544029)
              ·
                refine ⟨1026756221015333571204011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2738016589374222856544029 1026756221015333571204011)
                ·
                  refine ⟨1540134331523000356806017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026756221015333571204011 1540134331523000356806017)
                  ·
                    refine ⟨1155100748642250267604513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1540134331523000356806017 1155100748642250267604513)
                    ·
                      refine ⟨866325561481687700703385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155100748642250267604513 866325561481687700703385)
                      ·
                        rfl

theorem cell23_1687163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 1, 2, 2].length) (baseStart_1687163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687163 prefixEnd_1687163 := by exact prefixLift 1687163
  have htrace : WordTrace (prefixWord ++ tailWord_1687163) baseStart_1687163 baseEnd_1687163 := by
    simpa [prefixWord, tailWord_1687163, baseEnd_1687163] using wordTrace_append hprefix tailTrace_1687163
  have hstable : (prefixWord ++ tailWord_1687163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687163).length < 2 ^ (prefixWord ++ tailWord_1687163).sum := by decide
  have hdescent : baseEnd_1687163 < baseStart_1687163 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687179 : List Nat := [1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 3]
def baseStart_1687179 : Nat := 118140960795 + 1687179 * 2 ^ 59
def prefixEnd_1687179 : Nat := 4983230072969 + 3 ^ 40 * 1687179 * 2
def baseEnd_1687179 : Nat := 866333777172159638103311

theorem tailTrace_1687179 : CollatzResearch.WordTrace tailWord_1687179 prefixEnd_1687179 866333777172159638103311 := by
  unfold tailWord_1687179
  simp only [CollatzResearch.WordTrace]
  refine ⟨61536473554646105077736591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41024315703097403385157727 61536473554646105077736591)
  ·
    refine ⟨92304710331969157616604887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61536473554646105077736591 92304710331969157616604887)
    ·
      refine ⟨138457065497953736424907331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92304710331969157616604887 138457065497953736424907331)
      ·
        refine ⟨207685598246930604637360997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138457065497953736424907331 207685598246930604637360997)
        ·
          refine ⟨38941049671299488369505187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 207685598246930604637360997 38941049671299488369505187)
          ·
            refine ⟨58411574506949232554257781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38941049671299488369505187 58411574506949232554257781)
            ·
              refine ⟨5476085110026490551961667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58411574506949232554257781 5476085110026490551961667)
              ·
                refine ⟨8214127665039735827942501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5476085110026490551961667 8214127665039735827942501)
                ·
                  refine ⟨1540148937194950467739219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8214127665039735827942501 1540148937194950467739219)
                  ·
                    refine ⟨2310223405792425701608829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1540148937194950467739219 2310223405792425701608829)
                    ·
                      refine ⟨866333777172159638103311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2310223405792425701608829 866333777172159638103311)
                      ·
                        rfl

theorem cell23_1687179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 5, 1, 4, 1, 3].length) (baseStart_1687179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687179 prefixEnd_1687179 := by exact prefixLift 1687179
  have htrace : WordTrace (prefixWord ++ tailWord_1687179) baseStart_1687179 baseEnd_1687179 := by
    simpa [prefixWord, tailWord_1687179, baseEnd_1687179] using wordTrace_append hprefix tailTrace_1687179
  have hstable : (prefixWord ++ tailWord_1687179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687179).length < 2 ^ (prefixWord ++ tailWord_1687179).sum := by decide
  have hdescent : baseEnd_1687179 < baseStart_1687179 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687189 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 5, 3, 2]
def baseStart_1687189 : Nat := 118140960795 + 1687189 * 2 ^ 59
def prefixEnd_1687189 : Nat := 4983230072969 + 3 ^ 40 * 1687189 * 2
def baseEnd_1687189 : Nat := 866338911978704598978265

theorem tailTrace_1687189 : CollatzResearch.WordTrace tailWord_1687189 prefixEnd_1687189 866338911978704598978265 := by
  unfold tailWord_1687189
  simp only [CollatzResearch.WordTrace]
  refine ⟨61536838284609876785600621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41024558856406584523733747 61536838284609876785600621)
  ·
    refine ⟨23076314356728703794600233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61536838284609876785600621 23076314356728703794600233)
    ·
      refine ⟨17307235767546527845950175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23076314356728703794600233 17307235767546527845950175)
      ·
        refine ⟨25960853651319791768925263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17307235767546527845950175 25960853651319791768925263)
        ·
          refine ⟨38941280476979687653387895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25960853651319791768925263 38941280476979687653387895)
          ·
            refine ⟨58411920715469531480081843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38941280476979687653387895 58411920715469531480081843)
            ·
              refine ⟨87617881073204297220122765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58411920715469531480081843 87617881073204297220122765)
              ·
                refine ⟨32856705402451611457546037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87617881073204297220122765 32856705402451611457546037)
                ·
                  refine ⟨3080316131479838574144941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32856705402451611457546037 3080316131479838574144941)
                  ·
                    refine ⟨1155118549304939465304353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3080316131479838574144941 1155118549304939465304353)
                    ·
                      refine ⟨866338911978704598978265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155118549304939465304353 866338911978704598978265)
                      ·
                        rfl

theorem cell23_1687189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5, 3, 2].length) (baseStart_1687189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687189 prefixEnd_1687189 := by exact prefixLift 1687189
  have htrace : WordTrace (prefixWord ++ tailWord_1687189) baseStart_1687189 baseEnd_1687189 := by
    simpa [prefixWord, tailWord_1687189, baseEnd_1687189] using wordTrace_append hprefix tailTrace_1687189
  have hstable : (prefixWord ++ tailWord_1687189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687189).length < 2 ^ (prefixWord ++ tailWord_1687189).sum := by decide
  have hdescent : baseEnd_1687189 < baseStart_1687189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687214 : List Nat := [4, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2]
def baseStart_1687214 : Nat := 118140960795 + 1687214 * 2 ^ 59
def prefixEnd_1687214 : Nat := 4983230072969 + 3 ^ 40 * 1687214 * 2
def baseEnd_1687214 : Nat := 866351748995067001165651

theorem tailTrace_1687214 : CollatzResearch.WordTrace tailWord_1687214 prefixEnd_1687214 866351748995067001165651 := by
  unfold tailWord_1687214
  simp only [CollatzResearch.WordTrace]
  refine ⟨7692218763689913256907587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41025166739679537370173797 7692218763689913256907587)
  ·
    refine ⟨11538328145534869885361381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7692218763689913256907587 11538328145534869885361381)
    ·
      refine ⟨2163436527287788103505259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11538328145534869885361381 2163436527287788103505259)
      ·
        refine ⟨3245154790931682155257889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2163436527287788103505259 3245154790931682155257889)
        ·
          refine ⟨2433866093198761616443417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3245154790931682155257889 2433866093198761616443417)
          ·
            refine ⟨1825399569899071212332563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2433866093198761616443417 1825399569899071212332563)
            ·
              refine ⟨2738099354848606818498845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825399569899071212332563 2738099354848606818498845)
              ·
                refine ⟨1026787258068227556937067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2738099354848606818498845 1026787258068227556937067)
                ·
                  refine ⟨1540180887102341335405601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1026787258068227556937067 1540180887102341335405601)
                  ·
                    refine ⟨1155135665326756001554201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1540180887102341335405601 1155135665326756001554201)
                    ·
                      refine ⟨866351748995067001165651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155135665326756001554201 866351748995067001165651)
                      ·
                        rfl

theorem cell23_1687214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 1, 2, 2].length) (baseStart_1687214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687214 prefixEnd_1687214 := by exact prefixLift 1687214
  have htrace : WordTrace (prefixWord ++ tailWord_1687214) baseStart_1687214 baseEnd_1687214 := by
    simpa [prefixWord, tailWord_1687214, baseEnd_1687214] using wordTrace_append hprefix tailTrace_1687214
  have hstable : (prefixWord ++ tailWord_1687214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687214).length < 2 ^ (prefixWord ++ tailWord_1687214).sum := by decide
  have hdescent : baseEnd_1687214 < baseStart_1687214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687219 : List Nat := [1, 1, 1, 2, 3, 3, 2, 1, 3, 4, 2]
def baseStart_1687219 : Nat := 118140960795 + 1687219 * 2 ^ 59
def prefixEnd_1687219 : Nat := 4983230072969 + 3 ^ 40 * 1687219 * 2
def baseEnd_1687219 : Nat := 866354316398339481603127

theorem tailTrace_1687219 : CollatzResearch.WordTrace tailWord_1687219 prefixEnd_1687219 866354316398339481603127 := by
  unfold tailWord_1687219
  simp only [CollatzResearch.WordTrace]
  refine ⟨61537932474501191909192711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41025288316334127939461807 61537932474501191909192711)
  ·
    refine ⟨92306898711751787863789067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61537932474501191909192711 92306898711751787863789067)
    ·
      refine ⟨138460348067627681795683601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92306898711751787863789067 138460348067627681795683601)
      ·
        refine ⟨103845261050720761346762701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138460348067627681795683601 103845261050720761346762701)
        ·
          refine ⟨38941972894020285505036013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103845261050720761346762701 38941972894020285505036013)
          ·
            refine ⟨14603239835257607064388505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38941972894020285505036013 14603239835257607064388505)
            ·
              refine ⟨10952429876443205298291379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14603239835257607064388505 10952429876443205298291379)
              ·
                refine ⟨16428644814664807947437069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10952429876443205298291379 16428644814664807947437069)
                ·
                  refine ⟨6160741805499302980288901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16428644814664807947437069 6160741805499302980288901)
                  ·
                    refine ⟨1155139088531119308804169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6160741805499302980288901 1155139088531119308804169)
                    ·
                      refine ⟨866354316398339481603127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155139088531119308804169 866354316398339481603127)
                      ·
                        rfl

theorem cell23_1687219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 2, 1, 3, 4, 2].length) (baseStart_1687219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687219 prefixEnd_1687219 := by exact prefixLift 1687219
  have htrace : WordTrace (prefixWord ++ tailWord_1687219) baseStart_1687219 baseEnd_1687219 := by
    simpa [prefixWord, tailWord_1687219, baseEnd_1687219] using wordTrace_append hprefix tailTrace_1687219
  have hstable : (prefixWord ++ tailWord_1687219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687219).length < 2 ^ (prefixWord ++ tailWord_1687219).sum := by decide
  have hdescent : baseEnd_1687219 < baseStart_1687219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687386 : List Nat := [3, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2]
def baseStart_1687386 : Nat := 118140960795 + 1687386 * 2 ^ 59
def prefixEnd_1687386 : Nat := 4983230072969 + 3 ^ 40 * 1687386 * 2
def baseEnd_1687386 : Nat := 866440067667640328214859

theorem tailTrace_1687386 : CollatzResearch.WordTrace tailWord_1687386 prefixEnd_1687386 866440067667640328214859 := by
  unfold tailWord_1687386
  simp only [CollatzResearch.WordTrace]
  refine ⟨15386005866224044857630503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41029348976597452953681341 15386005866224044857630503)
  ·
    refine ⟨23079008799336067286445755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15386005866224044857630503 23079008799336067286445755)
    ·
      refine ⟨34618513199004100929668633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23079008799336067286445755 34618513199004100929668633)
      ·
        refine ⟨25963884899253075697251475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34618513199004100929668633 25963884899253075697251475)
        ·
          refine ⟨38945827348879613545877213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25963884899253075697251475 38945827348879613545877213)
          ·
            refine ⟨14604685255829855079703955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38945827348879613545877213 14604685255829855079703955)
            ·
              refine ⟨21907027883744782619555933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14604685255829855079703955 21907027883744782619555933)
              ·
                refine ⟨8215135456404293482333475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21907027883744782619555933 8215135456404293482333475)
                ·
                  refine ⟨12322703184606440223500213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215135456404293482333475 12322703184606440223500213)
                  ·
                    refine ⟨1155253423556853770953145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12322703184606440223500213 1155253423556853770953145)
                    ·
                      refine ⟨866440067667640328214859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155253423556853770953145 866440067667640328214859)
                      ·
                        rfl

theorem cell23_1687386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 3, 1, 5, 2].length) (baseStart_1687386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687386 prefixEnd_1687386 := by exact prefixLift 1687386
  have htrace : WordTrace (prefixWord ++ tailWord_1687386) baseStart_1687386 baseEnd_1687386 := by
    simpa [prefixWord, tailWord_1687386, baseEnd_1687386] using wordTrace_append hprefix tailTrace_1687386
  have hstable : (prefixWord ++ tailWord_1687386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687386).length < 2 ^ (prefixWord ++ tailWord_1687386).sum := by decide
  have hdescent : baseEnd_1687386 < baseStart_1687386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687419 : List Nat := [1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 3]
def baseStart_1687419 : Nat := 118140960795 + 1687419 * 2 ^ 59
def prefixEnd_1687419 : Nat := 4983230072969 + 3 ^ 40 * 1687419 * 2
def baseEnd_1687419 : Nat := 866457012529238699102207

theorem tailTrace_1687419 : CollatzResearch.WordTrace tailWord_1687419 prefixEnd_1687419 866457012529238699102207 := by
  unfold tailWord_1687419
  simp only [CollatzResearch.WordTrace]
  refine ⟨61545227073776626066473311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41030151382517750710982207 61545227073776626066473311)
  ·
    refine ⟨92317840610664939099709967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61545227073776626066473311 92317840610664939099709967)
    ·
      refine ⟨138476760915997408649564951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92317840610664939099709967 138476760915997408649564951)
      ·
        refine ⟨207715141373996112974347427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138476760915997408649564951 207715141373996112974347427)
        ·
          refine ⟨311572712060994169461521141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207715141373996112974347427 311572712060994169461521141)
          ·
            refine ⟨29209941755718203387017607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 311572712060994169461521141 29209941755718203387017607)
            ·
              refine ⟨43814912633577305080526411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29209941755718203387017607 43814912633577305080526411)
              ·
                refine ⟨65722368950365957620789617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43814912633577305080526411 65722368950365957620789617)
                ·
                  refine ⟨49291776712774468215592213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65722368950365957620789617 49291776712774468215592213)
                  ·
                    refine ⟨2310552033411303197605885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 49291776712774468215592213 2310552033411303197605885)
                    ·
                      refine ⟨866457012529238699102207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2310552033411303197605885 866457012529238699102207)
                      ·
                        rfl

theorem cell23_1687419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 1, 2, 6, 3].length) (baseStart_1687419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687419 prefixEnd_1687419 := by exact prefixLift 1687419
  have htrace : WordTrace (prefixWord ++ tailWord_1687419) baseStart_1687419 baseEnd_1687419 := by
    simpa [prefixWord, tailWord_1687419, baseEnd_1687419] using wordTrace_append hprefix tailTrace_1687419
  have hstable : (prefixWord ++ tailWord_1687419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687419).length < 2 ^ (prefixWord ++ tailWord_1687419).sum := by decide
  have hdescent : baseEnd_1687419 < baseStart_1687419 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687429 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 6]
def baseStart_1687429 : Nat := 118140960795 + 1687429 * 2 ^ 59
def prefixEnd_1687429 : Nat := 4983230072969 + 3 ^ 40 * 1687429 * 2
def baseEnd_1687429 : Nat := 866462147335783659977161

theorem tailTrace_1687429 : CollatzResearch.WordTrace tailWord_1687429 prefixEnd_1687429 866462147335783659977161 := by
  unfold tailWord_1687429
  simp only [CollatzResearch.WordTrace]
  refine ⟨61545591803740397774337341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41030394535826931849558227 61545591803740397774337341)
  ·
    refine ⟨23079596926402649165376503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61545591803740397774337341 23079596926402649165376503)
    ·
      refine ⟨34619395389603973748064755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23079596926402649165376503 34619395389603973748064755)
      ·
        refine ⟨51929093084405960622097133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34619395389603973748064755 51929093084405960622097133)
        ·
          refine ⟨19473409906652235233286425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51929093084405960622097133 19473409906652235233286425)
          ·
            refine ⟨14605057429989176424964819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19473409906652235233286425 14605057429989176424964819)
            ·
              refine ⟨21907586144983764637447229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14605057429989176424964819 21907586144983764637447229)
              ·
                refine ⟨8215344804368911739042711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21907586144983764637447229 8215344804368911739042711)
                ·
                  refine ⟨12323017206553367608564067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8215344804368911739042711 12323017206553367608564067)
                  ·
                    refine ⟨18484525809830051412846101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12323017206553367608564067 18484525809830051412846101)
                    ·
                      refine ⟨866462147335783659977161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18484525809830051412846101 866462147335783659977161)
                      ·
                        rfl

theorem cell23_1687429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 1, 1, 6].length) (baseStart_1687429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687429 prefixEnd_1687429 := by exact prefixLift 1687429
  have htrace : WordTrace (prefixWord ++ tailWord_1687429) baseStart_1687429 baseEnd_1687429 := by
    simpa [prefixWord, tailWord_1687429, baseEnd_1687429] using wordTrace_append hprefix tailTrace_1687429
  have hstable : (prefixWord ++ tailWord_1687429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687429).length < 2 ^ (prefixWord ++ tailWord_1687429).sum := by decide
  have hdescent : baseEnd_1687429 < baseStart_1687429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687433 : List Nat := [1, 2, 1, 1, 5, 1, 2, 1, 5, 2, 2]
def baseStart_1687433 : Nat := 118140960795 + 1687433 * 2 ^ 59
def prefixEnd_1687433 : Nat := 4983230072969 + 3 ^ 40 * 1687433 * 2
def baseEnd_1687433 : Nat := 866464201258401644327143

theorem tailTrace_1687433 : CollatzResearch.WordTrace tailWord_1687433 prefixEnd_1687433 866464201258401644327143 := by
  unfold tailWord_1687433
  simp only [CollatzResearch.WordTrace]
  refine ⟨61545737695725906457482953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41030491797150604304988635 61545737695725906457482953)
  ·
    refine ⟨46159303271794429843112215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61545737695725906457482953 46159303271794429843112215)
    ·
      refine ⟨69238954907691644764668323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46159303271794429843112215 69238954907691644764668323)
      ·
        refine ⟨103858432361537467147002485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69238954907691644764668323 103858432361537467147002485)
        ·
          refine ⟨9736728033894137545031483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103858432361537467147002485 9736728033894137545031483)
          ·
            refine ⟨14605092050841206317547225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9736728033894137545031483 14605092050841206317547225)
            ·
              refine ⟨10953819038130904738160419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14605092050841206317547225 10953819038130904738160419)
              ·
                refine ⟨16430728557196357107240629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10953819038130904738160419 16430728557196357107240629)
                ·
                  refine ⟨1540380802237158478803809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16430728557196357107240629 1540380802237158478803809)
                  ·
                    refine ⟨1155285601677868859102857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1540380802237158478803809 1155285601677868859102857)
                    ·
                      refine ⟨866464201258401644327143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155285601677868859102857 866464201258401644327143)
                      ·
                        rfl

theorem cell23_1687433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 5, 2, 2].length) (baseStart_1687433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687433 prefixEnd_1687433 := by exact prefixLift 1687433
  have htrace : WordTrace (prefixWord ++ tailWord_1687433) baseStart_1687433 baseEnd_1687433 := by
    simpa [prefixWord, tailWord_1687433, baseEnd_1687433] using wordTrace_append hprefix tailTrace_1687433
  have hstable : (prefixWord ++ tailWord_1687433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687433).length < 2 ^ (prefixWord ++ tailWord_1687433).sum := by decide
  have hdescent : baseEnd_1687433 < baseStart_1687433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687450 : List Nat := [3, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4]
def baseStart_1687450 : Nat := 118140960795 + 1687450 * 2 ^ 59
def prefixEnd_1687450 : Nat := 4983230072969 + 3 ^ 40 * 1687450 * 2
def baseEnd_1687450 : Nat := 866472930429528077814565

theorem tailTrace_1687450 : CollatzResearch.WordTrace tailWord_1687450 prefixEnd_1687450 866472930429528077814565 := by
  unfold tailWord_1687450
  simp only [CollatzResearch.WordTrace]
  refine ⟨15386589434166079590212951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41030905157776212240567869 15386589434166079590212951)
  ·
    refine ⟨23079884151249119385319427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15386589434166079590212951 23079884151249119385319427)
    ·
      refine ⟨34619826226873679077979141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23079884151249119385319427 34619826226873679077979141)
      ·
        refine ⟨6491217417538814827121089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34619826226873679077979141 6491217417538814827121089)
        ·
          refine ⟨4868413063154111120340817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6491217417538814827121089 4868413063154111120340817)
          ·
            refine ⟨3651309797365583340255613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4868413063154111120340817 3651309797365583340255613)
            ·
              refine ⟨1369241174012093752595855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3651309797365583340255613 1369241174012093752595855)
              ·
                refine ⟨2053861761018140628893783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369241174012093752595855 2053861761018140628893783)
                ·
                  refine ⟨3080792641527210943340675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2053861761018140628893783 3080792641527210943340675)
                  ·
                    refine ⟨4621188962290816415011013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3080792641527210943340675 4621188962290816415011013)
                    ·
                      refine ⟨866472930429528077814565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4621188962290816415011013 866472930429528077814565)
                      ·
                        rfl

theorem cell23_1687450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_1687450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687450 prefixEnd_1687450 := by exact prefixLift 1687450
  have htrace : WordTrace (prefixWord ++ tailWord_1687450) baseStart_1687450 baseEnd_1687450 := by
    simpa [prefixWord, tailWord_1687450, baseEnd_1687450] using wordTrace_append hprefix tailTrace_1687450
  have hstable : (prefixWord ++ tailWord_1687450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687450).length < 2 ^ (prefixWord ++ tailWord_1687450).sum := by decide
  have hdescent : baseEnd_1687450 < baseStart_1687450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687453 : List Nat := [1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_1687453 : Nat := 118140960795 + 1687453 * 2 ^ 59
def prefixEnd_1687453 : Nat := 4983230072969 + 3 ^ 40 * 1687453 * 2
def baseEnd_1687453 : Nat := 866474470871491566077051

theorem tailTrace_1687453 : CollatzResearch.WordTrace tailWord_1687453 prefixEnd_1687453 866474470871491566077051 := by
  unfold tailWord_1687453
  simp only [CollatzResearch.WordTrace]
  refine ⟨61546467155653449873211013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41030978103768966582140675 61546467155653449873211013)
  ·
    refine ⟨11539962591685021851227065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61546467155653449873211013 11539962591685021851227065)
    ·
      refine ⟨8654971943763766388420299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11539962591685021851227065 8654971943763766388420299)
      ·
        refine ⟨12982457915645649582630449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8654971943763766388420299 12982457915645649582630449)
        ·
          refine ⟨9736843436734237186972837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12982457915645649582630449 9736843436734237186972837)
          ·
            refine ⟨1825658144387669472557407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9736843436734237186972837 1825658144387669472557407)
            ·
              refine ⟨2738487216581504208836111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1825658144387669472557407 2738487216581504208836111)
              ·
                refine ⟨4107730824872256313254167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2738487216581504208836111 4107730824872256313254167)
                ·
                  refine ⟨6161596237308384469881251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4107730824872256313254167 6161596237308384469881251)
                  ·
                    refine ⟨9242394355962576704821877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6161596237308384469881251 9242394355962576704821877)
                    ·
                      refine ⟨866474470871491566077051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9242394355962576704821877 866474470871491566077051)
                      ·
                        rfl

theorem cell23_1687453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_1687453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687453 prefixEnd_1687453 := by exact prefixLift 1687453
  have htrace : WordTrace (prefixWord ++ tailWord_1687453) baseStart_1687453 baseEnd_1687453 := by
    simpa [prefixWord, tailWord_1687453, baseEnd_1687453] using wordTrace_append hprefix tailTrace_1687453
  have hstable : (prefixWord ++ tailWord_1687453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687453).length < 2 ^ (prefixWord ++ tailWord_1687453).sum := by decide
  have hdescent : baseEnd_1687453 < baseStart_1687453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687479 : List Nat := [1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 5]
def baseStart_1687479 : Nat := 118140960795 + 1687479 * 2 ^ 59
def prefixEnd_1687479 : Nat := 4983230072969 + 3 ^ 40 * 1687479 * 2
def baseEnd_1687479 : Nat := 866487821368508464351931

theorem tailTrace_1687479 : CollatzResearch.WordTrace tailWord_1687479 prefixEnd_1687479 866487821368508464351931 := by
  unfold tailWord_1687479
  simp only [CollatzResearch.WordTrace]
  refine ⟨61547415453559256313657491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41031610302372837542438327 61547415453559256313657491)
  ·
    refine ⟨92321123180338884470486237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61547415453559256313657491 92321123180338884470486237)
    ·
      refine ⟨34620421192627081676432339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92321123180338884470486237 34620421192627081676432339)
      ·
        refine ⟨51930631788940622514648509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34620421192627081676432339 51930631788940622514648509)
        ·
          refine ⟨19473986920852733442993191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51930631788940622514648509 19473986920852733442993191)
          ·
            refine ⟨29210980381279100164489787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19473986920852733442993191 29210980381279100164489787)
            ·
              refine ⟨43816470571918650246734681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29210980381279100164489787 43816470571918650246734681)
              ·
                refine ⟨32862352928938987685051011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43816470571918650246734681 32862352928938987685051011)
                ·
                  refine ⟨49293529393408481527576517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32862352928938987685051011 49293529393408481527576517)
                  ·
                    refine ⟨9242536761264090286420597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49293529393408481527576517 9242536761264090286420597)
                    ·
                      refine ⟨866487821368508464351931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9242536761264090286420597 866487821368508464351931)
                      ·
                        rfl

theorem cell23_1687479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 2, 1, 4, 5].length) (baseStart_1687479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687479 prefixEnd_1687479 := by exact prefixLift 1687479
  have htrace : WordTrace (prefixWord ++ tailWord_1687479) baseStart_1687479 baseEnd_1687479 := by
    simpa [prefixWord, tailWord_1687479, baseEnd_1687479] using wordTrace_append hprefix tailTrace_1687479
  have hstable : (prefixWord ++ tailWord_1687479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687479).length < 2 ^ (prefixWord ++ tailWord_1687479).sum := by decide
  have hdescent : baseEnd_1687479 < baseStart_1687479 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687499 : List Nat := [1, 1, 1, 1, 3, 4, 1, 2, 1, 8]
def baseStart_1687499 : Nat := 118140960795 + 1687499 * 2 ^ 59
def prefixEnd_1687499 : Nat := 4983230072969 + 3 ^ 40 * 1687499 * 2
def baseEnd_1687499 : Nat := 288832696993866128700613

theorem tailTrace_1687499 : CollatzResearch.WordTrace tailWord_1687499 prefixEnd_1687499 288832696993866128700613 := by
  unfold tailWord_1687499
  simp only [CollatzResearch.WordTrace]
  refine ⟨61548144913486799729385551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41032096608991199819590367 61548144913486799729385551)
  ·
    refine ⟨92322217370230199594078327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61548144913486799729385551 92322217370230199594078327)
    ·
      refine ⟨138483326055345299391117491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92322217370230199594078327 138483326055345299391117491)
      ·
        refine ⟨207724989083017949086676237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138483326055345299391117491 207724989083017949086676237)
        ·
          refine ⟨77896870906131730907503589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207724989083017949086676237 77896870906131730907503589)
          ·
            refine ⟨14605663294899699545156923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77896870906131730907503589 14605663294899699545156923)
            ·
              refine ⟨21908494942349549317735385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14605663294899699545156923 21908494942349549317735385)
              ·
                refine ⟨16431371206762161988301539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21908494942349549317735385 16431371206762161988301539)
                ·
                  refine ⟨24647056810143242982452309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16431371206762161988301539 24647056810143242982452309)
                  ·
                    refine ⟨288832696993866128700613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24647056810143242982452309 288832696993866128700613)
                    ·
                      rfl

theorem cell23_1687499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 8].length) (baseStart_1687499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687499 prefixEnd_1687499 := by exact prefixLift 1687499
  have htrace : WordTrace (prefixWord ++ tailWord_1687499) baseStart_1687499 baseEnd_1687499 := by
    simpa [prefixWord, tailWord_1687499, baseEnd_1687499] using wordTrace_append hprefix tailTrace_1687499
  have hstable : (prefixWord ++ tailWord_1687499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687499).length < 2 ^ (prefixWord ++ tailWord_1687499).sum := by decide
  have hdescent : baseEnd_1687499 < baseStart_1687499 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687536 : List Nat := [2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4]
def baseStart_1687536 : Nat := 118140960795 + 1687536 * 2 ^ 59
def prefixEnd_1687536 : Nat := 4983230072969 + 3 ^ 40 * 1687536 * 2
def baseEnd_1687536 : Nat := 866517089765814741339169

theorem tailTrace_1687536 : CollatzResearch.WordTrace tailWord_1687536 prefixEnd_1687536 866517089765814741339169 := by
  unfold tailWord_1687536
  simp only [CollatzResearch.WordTrace]
  refine ⟨30774747207176377524241231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41032996276235170032321641 30774747207176377524241231)
  ·
    refine ⟨46162120810764566286361847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30774747207176377524241231 46162120810764566286361847)
    ·
      refine ⟨69243181216146849429542771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46162120810764566286361847 69243181216146849429542771)
      ·
        refine ⟨103864771824220274144314157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69243181216146849429542771 103864771824220274144314157)
        ·
          refine ⟨38949289434082602804117809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103864771824220274144314157 38949289434082602804117809)
          ·
            refine ⟨29211967075561952103088357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38949289434082602804117809 29211967075561952103088357)
            ·
              refine ⟨5477243826667866019329067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29211967075561952103088357 5477243826667866019329067)
              ·
                refine ⟨8215865740001799028993601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5477243826667866019329067 8215865740001799028993601)
                ·
                  refine ⟨6161899305001349271745201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8215865740001799028993601 6161899305001349271745201)
                  ·
                    refine ⟨4621424478751011953808901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6161899305001349271745201 4621424478751011953808901)
                    ·
                      refine ⟨866517089765814741339169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4621424478751011953808901 866517089765814741339169)
                      ·
                        rfl

theorem cell23_1687536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 4, 1, 2, 2, 4].length) (baseStart_1687536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687536 prefixEnd_1687536 := by exact prefixLift 1687536
  have htrace : WordTrace (prefixWord ++ tailWord_1687536) baseStart_1687536 baseEnd_1687536 := by
    simpa [prefixWord, tailWord_1687536, baseEnd_1687536] using wordTrace_append hprefix tailTrace_1687536
  have hstable : (prefixWord ++ tailWord_1687536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687536).length < 2 ^ (prefixWord ++ tailWord_1687536).sum := by decide
  have hdescent : baseEnd_1687536 < baseStart_1687536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687539 : List Nat := [1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9]
def baseStart_1687539 : Nat := 118140960795 + 1687539 * 2 ^ 59
def prefixEnd_1687539 : Nat := 4983230072969 + 3 ^ 40 * 1687539 * 2
def baseEnd_1687539 : Nat := 866518630207778229601655

theorem tailTrace_1687539 : CollatzResearch.WordTrace tailWord_1687539 prefixEnd_1687539 866518630207778229601655 := by
  unfold tailWord_1687539
  simp only [CollatzResearch.WordTrace]
  refine ⟨61549603833341886560841671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41033069222227924373894447 61549603833341886560841671)
  ·
    refine ⟨92324405750012829841262507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61549603833341886560841671 92324405750012829841262507)
    ·
      refine ⟨138486608625019244761893761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92324405750012829841262507 138486608625019244761893761)
      ·
        refine ⟨103864956468764433571420321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138486608625019244761893761 103864956468764433571420321)
        ·
          refine ⟨77898717351573325178565241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103864956468764433571420321 77898717351573325178565241)
          ·
            refine ⟨58424038013679993883923931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77898717351573325178565241 58424038013679993883923931)
            ·
              refine ⟨87636057020519990825885897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58424038013679993883923931 87636057020519990825885897)
              ·
                refine ⟨65727042765389993119414423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87636057020519990825885897 65727042765389993119414423)
                ·
                  refine ⟨98590564148084989679121635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65727042765389993119414423 98590564148084989679121635)
                  ·
                    refine ⟨147885846222127484518682453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98590564148084989679121635 147885846222127484518682453)
                    ·
                      refine ⟨866518630207778229601655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 147885846222127484518682453 866518630207778229601655)
                      ·
                        rfl

theorem cell23_1687539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_1687539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687539 prefixEnd_1687539 := by exact prefixLift 1687539
  have htrace : WordTrace (prefixWord ++ tailWord_1687539) baseStart_1687539 baseEnd_1687539 := by
    simpa [prefixWord, tailWord_1687539, baseEnd_1687539] using wordTrace_append hprefix tailTrace_1687539
  have hstable : (prefixWord ++ tailWord_1687539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687539).length < 2 ^ (prefixWord ++ tailWord_1687539).sum := by decide
  have hdescent : baseEnd_1687539 < baseStart_1687539 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687583 : List Nat := [1, 1, 2, 4, 1, 2, 2, 1, 2, 5, 2]
def baseStart_1687583 : Nat := 118140960795 + 1687583 * 2 ^ 59
def prefixEnd_1687583 : Nat := 4983230072969 + 3 ^ 40 * 1687583 * 2
def baseEnd_1687583 : Nat := 866541223356576057451453

theorem tailTrace_1687583 : CollatzResearch.WordTrace tailWord_1687583 prefixEnd_1687583 866541223356576057451453 := by
  unfold tailWord_1687583
  simp only [CollatzResearch.WordTrace]
  refine ⟨61551208645182482075443403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41034139096788321383628935 61551208645182482075443403)
  ·
    refine ⟨92326812967773723113165105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61551208645182482075443403 92326812967773723113165105)
    ·
      refine ⟨69245109725830292334873829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92326812967773723113165105 69245109725830292334873829)
      ·
        refine ⟨12983458073593179812788843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69245109725830292334873829 12983458073593179812788843)
        ·
          refine ⟨19475187110389769719183265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12983458073593179812788843 19475187110389769719183265)
          ·
            refine ⟨14606390332792327289387449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19475187110389769719183265 14606390332792327289387449)
            ·
              refine ⟨10954792749594245467040587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14606390332792327289387449 10954792749594245467040587)
              ·
                refine ⟨16432189124391368200560881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10954792749594245467040587 16432189124391368200560881)
                ·
                  refine ⟨12324141843293526150420661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16432189124391368200560881 12324141843293526150420661)
                  ·
                    refine ⟨1155388297808768076601937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12324141843293526150420661 1155388297808768076601937)
                    ·
                      refine ⟨866541223356576057451453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155388297808768076601937 866541223356576057451453)
                      ·
                        rfl

theorem cell23_1687583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 2, 1, 2, 5, 2].length) (baseStart_1687583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687583 prefixEnd_1687583 := by exact prefixLift 1687583
  have htrace : WordTrace (prefixWord ++ tailWord_1687583) baseStart_1687583 baseEnd_1687583 := by
    simpa [prefixWord, tailWord_1687583, baseEnd_1687583] using wordTrace_append hprefix tailTrace_1687583
  have hstable : (prefixWord ++ tailWord_1687583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687583).length < 2 ^ (prefixWord ++ tailWord_1687583).sum := by decide
  have hdescent : baseEnd_1687583 < baseStart_1687583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687596 : List Nat := [2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 4]
def baseStart_1687596 : Nat := 118140960795 + 1687596 * 2 ^ 59
def prefixEnd_1687596 : Nat := 4983230072969 + 3 ^ 40 * 1687596 * 2
def baseEnd_1687596 : Nat := 866547898605084506588893

theorem tailTrace_1687596 : CollatzResearch.WordTrace tailWord_1687596 prefixEnd_1687596 866547898605084506588893 := by
  unfold tailWord_1687596
  simp only [CollatzResearch.WordTrace]
  refine ⟨30775841397067692647833321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41034455196090256863777761 30775841397067692647833321)
  ·
    refine ⟨23081881047800769485874991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30775841397067692647833321 23081881047800769485874991)
    ·
      refine ⟨34622821571701154228812487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23081881047800769485874991 34622821571701154228812487)
      ·
        refine ⟨51934232357551731343218731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34622821571701154228812487 51934232357551731343218731)
        ·
          refine ⟨77901348536327597014828097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51934232357551731343218731 77901348536327597014828097)
          ·
            refine ⟨58426011402245697761121073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77901348536327597014828097 58426011402245697761121073)
            ·
              refine ⟨43819508551684273320840805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58426011402245697761121073 43819508551684273320840805)
              ·
                refine ⟨8216157853440801247657651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43819508551684273320840805 8216157853440801247657651)
                ·
                  refine ⟨12324236780161201871486477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8216157853440801247657651 12324236780161201871486477)
                  ·
                    refine ⟨4621588792560450701807429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12324236780161201871486477 4621588792560450701807429)
                    ·
                      refine ⟨866547898605084506588893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4621588792560450701807429 866547898605084506588893)
                      ·
                        rfl

theorem cell23_1687596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 4].length) (baseStart_1687596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687596 prefixEnd_1687596 := by exact prefixLift 1687596
  have htrace : WordTrace (prefixWord ++ tailWord_1687596) baseStart_1687596 baseEnd_1687596 := by
    simpa [prefixWord, tailWord_1687596, baseEnd_1687596] using wordTrace_append hprefix tailTrace_1687596
  have hstable : (prefixWord ++ tailWord_1687596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687596).length < 2 ^ (prefixWord ++ tailWord_1687596).sum := by decide
  have hdescent : baseEnd_1687596 < baseStart_1687596 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687626 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1687626 : Nat := 118140960795 + 1687626 * 2 ^ 59
def prefixEnd_1687626 : Nat := 4983230072969 + 3 ^ 40 * 1687626 * 2
def baseEnd_1687626 : Nat := 866563303024719389213755

theorem tailTrace_1687626 : CollatzResearch.WordTrace tailWord_1687626 prefixEnd_1687626 866563303024719389213755 := by
  unfold tailWord_1687626
  simp only [CollatzResearch.WordTrace]
  refine ⟨15388194246006675104814683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41035184656017800279505821 15388194246006675104814683)
  ·
    refine ⟨23082291369010012657222025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15388194246006675104814683 23082291369010012657222025)
    ·
      refine ⟨17311718526757509492916519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23082291369010012657222025 17311718526757509492916519)
      ·
        refine ⟨25967577790136264239374779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17311718526757509492916519 25967577790136264239374779)
        ·
          refine ⟨38951366685204396359062169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25967577790136264239374779 38951366685204396359062169)
          ·
            refine ⟨29213525013903297269296627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38951366685204396359062169 29213525013903297269296627)
            ·
              refine ⟨43820287520854945903944941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29213525013903297269296627 43820287520854945903944941)
              ·
                refine ⟨16432607820320604713979353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43820287520854945903944941 16432607820320604713979353)
                ·
                  refine ⟨12324455865240453535484515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16432607820320604713979353 12324455865240453535484515)
                  ·
                    refine ⟨18486683797860680303226773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12324455865240453535484515 18486683797860680303226773)
                    ·
                      refine ⟨866563303024719389213755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18486683797860680303226773 866563303024719389213755)
                      ·
                        rfl

theorem cell23_1687626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1687626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687626 prefixEnd_1687626 := by exact prefixLift 1687626
  have htrace : WordTrace (prefixWord ++ tailWord_1687626) baseStart_1687626 baseEnd_1687626 := by
    simpa [prefixWord, tailWord_1687626, baseEnd_1687626] using wordTrace_append hprefix tailTrace_1687626
  have hstable : (prefixWord ++ tailWord_1687626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687626).length < 2 ^ (prefixWord ++ tailWord_1687626).sum := by decide
  have hdescent : baseEnd_1687626 < baseStart_1687626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687653 : List Nat := [1, 3, 1, 3, 2, 2, 2, 3, 6]
def baseStart_1687653 : Nat := 118140960795 + 1687653 * 2 ^ 59
def prefixEnd_1687653 : Nat := 4983230072969 + 3 ^ 40 * 1687653 * 2
def baseEnd_1687653 : Nat := 96286351889154531508459

theorem tailTrace_1687653 : CollatzResearch.WordTrace tailWord_1687653 prefixEnd_1687653 96286351889154531508459 := by
  unfold tailWord_1687653
  simp only [CollatzResearch.WordTrace]
  refine ⟨61553761754928884030491613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41035841169952589353661075 61553761754928884030491613)
  ·
    refine ⟨23082660658098331511434355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61553761754928884030491613 23082660658098331511434355)
    ·
      refine ⟨34623990987147497267151533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23082660658098331511434355 34623990987147497267151533)
      ·
        refine ⟨12983996620180311475181825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34623990987147497267151533 12983996620180311475181825)
        ·
          refine ⟨9737997465135233606386369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12983996620180311475181825 9737997465135233606386369)
          ·
            refine ⟨7303498098851425204789777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9737997465135233606386369 7303498098851425204789777)
            ·
              refine ⟨5477623574138568903592333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7303498098851425204789777 5477623574138568903592333)
              ·
                refine ⟨2054108840301963338847125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5477623574138568903592333 2054108840301963338847125)
                ·
                  refine ⟨96286351889154531508459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2054108840301963338847125 96286351889154531508459)
                  ·
                    rfl

theorem cell23_1687653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 2, 3, 6].length) (baseStart_1687653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687653 prefixEnd_1687653 := by exact prefixLift 1687653
  have htrace : WordTrace (prefixWord ++ tailWord_1687653) baseStart_1687653 baseEnd_1687653 := by
    simpa [prefixWord, tailWord_1687653, baseEnd_1687653] using wordTrace_append hprefix tailTrace_1687653
  have hstable : (prefixWord ++ tailWord_1687653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687653).length < 2 ^ (prefixWord ++ tailWord_1687653).sum := by decide
  have hdescent : baseEnd_1687653 < baseStart_1687653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687723 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 3]
def baseStart_1687723 : Nat := 118140960795 + 1687723 * 2 ^ 59
def prefixEnd_1687723 : Nat := 4983230072969 + 3 ^ 40 * 1687723 * 2
def baseEnd_1687723 : Nat := 866613110648205509700809

theorem tailTrace_1687723 : CollatzResearch.WordTrace tailWord_1687723 prefixEnd_1687723 866613110648205509700809 := by
  unfold tailWord_1687723
  simp only [CollatzResearch.WordTrace]
  refine ⟨61556314864675285985539823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41037543243116857323693215 61556314864675285985539823)
  ·
    refine ⟨92334472297012928978309735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61556314864675285985539823 92334472297012928978309735)
    ·
      refine ⟨138501708445519393467464603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92334472297012928978309735 138501708445519393467464603)
      ·
        refine ⟨207752562668279090201196905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138501708445519393467464603 207752562668279090201196905)
        ·
          refine ⟨155814422001209317650897679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 207752562668279090201196905 155814422001209317650897679)
          ·
            refine ⟨233721633001813976476346519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155814422001209317650897679 233721633001813976476346519)
            ·
              refine ⟨350582449502720964714519779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233721633001813976476346519 350582449502720964714519779)
              ·
                refine ⟨525873674254081447071779669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 350582449502720964714519779 525873674254081447071779669)
                ·
                  refine ⟨3081291060082508478936209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 525873674254081447071779669 3081291060082508478936209)
                  ·
                    refine ⟨2310968295061881359202157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3081291060082508478936209 2310968295061881359202157)
                    ·
                      refine ⟨866613110648205509700809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2310968295061881359202157 866613110648205509700809)
                      ·
                        rfl

theorem cell23_1687723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 9, 2, 3].length) (baseStart_1687723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687723 prefixEnd_1687723 := by exact prefixLift 1687723
  have htrace : WordTrace (prefixWord ++ tailWord_1687723) baseStart_1687723 baseEnd_1687723 := by
    simpa [prefixWord, tailWord_1687723, baseEnd_1687723] using wordTrace_append hprefix tailTrace_1687723
  have hstable : (prefixWord ++ tailWord_1687723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687723).length < 2 ^ (prefixWord ++ tailWord_1687723).sum := by decide
  have hdescent : baseEnd_1687723 < baseStart_1687723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687753 : List Nat := [1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 3]
def baseStart_1687753 : Nat := 118140960795 + 1687753 * 2 ^ 59
def prefixEnd_1687753 : Nat := 4983230072969 + 3 ^ 40 * 1687753 * 2
def baseEnd_1687753 : Nat := 866628515067840392325671

theorem tailTrace_1687753 : CollatzResearch.WordTrace tailWord_1687753 prefixEnd_1687753 866628515067840392325671 := by
  unfold tailWord_1687753
  simp only [CollatzResearch.WordTrace]
  refine ⟨61557409054566601109131913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41038272703044400739421275 61557409054566601109131913)
  ·
    refine ⟨46168056790924950831848935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61557409054566601109131913 46168056790924950831848935)
    ·
      refine ⟨69252085186387426247773403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46168056790924950831848935 69252085186387426247773403)
      ·
        refine ⟨103878127779581139371660105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69252085186387426247773403 103878127779581139371660105)
        ·
          refine ⟨77908595834685854528745079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103878127779581139371660105 77908595834685854528745079)
          ·
            refine ⟨116862893752028781793117619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77908595834685854528745079 116862893752028781793117619)
            ·
              refine ⟨175294340628043172689676429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116862893752028781793117619 175294340628043172689676429)
              ·
                refine ⟨65735377735516189758628661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175294340628043172689676429 65735377735516189758628661)
                ·
                  refine ⟨6162691662704642789871437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65735377735516189758628661 6162691662704642789871437)
                  ·
                    refine ⟨2311009373514241046201789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6162691662704642789871437 2311009373514241046201789)
                    ·
                      refine ⟨866628515067840392325671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2311009373514241046201789 866628515067840392325671)
                      ·
                        rfl

theorem cell23_1687753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 3, 5, 3, 3].length) (baseStart_1687753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687753 prefixEnd_1687753 := by exact prefixLift 1687753
  have htrace : WordTrace (prefixWord ++ tailWord_1687753) baseStart_1687753 baseEnd_1687753 := by
    simpa [prefixWord, tailWord_1687753, baseEnd_1687753] using wordTrace_append hprefix tailTrace_1687753
  have hstable : (prefixWord ++ tailWord_1687753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687753).length < 2 ^ (prefixWord ++ tailWord_1687753).sum := by decide
  have hdescent : baseEnd_1687753 < baseStart_1687753 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687804 : List Nat := [2, 2, 2, 1, 4, 2, 2, 2, 2, 1, 3]
def baseStart_1687804 : Nat := 118140960795 + 1687804 * 2 ^ 59
def prefixEnd_1687804 : Nat := 4983230072969 + 3 ^ 40 * 1687804 * 2
def baseEnd_1687804 : Nat := 866654702581219692787937

theorem tailTrace_1687804 : CollatzResearch.WordTrace tailWord_1687804 prefixEnd_1687804 866654702581219692787937 := by
  unfold tailWord_1687804
  simp only [CollatzResearch.WordTrace]
  refine ⟨30779634588690918409619233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41039512784921224546158977 30779634588690918409619233)
  ·
    refine ⟨23084725941518188807214425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30779634588690918409619233 23084725941518188807214425)
    ·
      refine ⟨17313544456138641605410819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23084725941518188807214425 17313544456138641605410819)
      ·
        refine ⟨25970316684207962408116229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17313544456138641605410819 25970316684207962408116229)
        ·
          refine ⟨4869434378288992951521793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25970316684207962408116229 4869434378288992951521793)
          ·
            refine ⟨3652075783716744713641345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4869434378288992951521793 3652075783716744713641345)
            ·
              refine ⟨2739056837787558535231009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3652075783716744713641345 2739056837787558535231009)
              ·
                refine ⟨2054292628340668901423257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739056837787558535231009 2054292628340668901423257)
                ·
                  refine ⟨1540719471255501676067443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054292628340668901423257 1540719471255501676067443)
                  ·
                    refine ⟨2311079206883252514101165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1540719471255501676067443 2311079206883252514101165)
                    ·
                      refine ⟨866654702581219692787937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2311079206883252514101165 866654702581219692787937)
                      ·
                        rfl

theorem cell23_1687804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 2, 1, 3].length) (baseStart_1687804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687804 prefixEnd_1687804 := by exact prefixLift 1687804
  have htrace : WordTrace (prefixWord ++ tailWord_1687804) baseStart_1687804 baseEnd_1687804 := by
    simpa [prefixWord, tailWord_1687804, baseEnd_1687804] using wordTrace_append hprefix tailTrace_1687804
  have hstable : (prefixWord ++ tailWord_1687804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687804).length < 2 ^ (prefixWord ++ tailWord_1687804).sum := by decide
  have hdescent : baseEnd_1687804 < baseStart_1687804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687813 : List Nat := [1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 5]
def baseStart_1687813 : Nat := 118140960795 + 1687813 * 2 ^ 59
def prefixEnd_1687813 : Nat := 4983230072969 + 3 ^ 40 * 1687813 * 2
def baseEnd_1687813 : Nat := 866659323907110157575395

theorem tailTrace_1687813 : CollatzResearch.WordTrace tailWord_1687813 prefixEnd_1687813 866659323907110157575395 := by
  unfold tailWord_1687813
  simp only [CollatzResearch.WordTrace]
  refine ⟨61559597434349231356316093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41039731622899487570877395 61559597434349231356316093)
  ·
    refine ⟨23084849037880961758618535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61559597434349231356316093 23084849037880961758618535)
    ·
      refine ⟨34627273556821442637927803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23084849037880961758618535 34627273556821442637927803)
      ·
        refine ⟨51940910335232163956891705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34627273556821442637927803 51940910335232163956891705)
        ·
          refine ⟨38955682751424122967668779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51940910335232163956891705 38955682751424122967668779)
          ·
            refine ⟨58433524127136184451503169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38955682751424122967668779 58433524127136184451503169)
            ·
              refine ⟨43825143095352138338627377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58433524127136184451503169 43825143095352138338627377)
              ·
                refine ⟨32868857321514103753970533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43825143095352138338627377 32868857321514103753970533)
                ·
                  refine ⟨6162910747783894453869475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32868857321514103753970533 6162910747783894453869475)
                  ·
                    refine ⟨9244366121675841680804213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6162910747783894453869475 9244366121675841680804213)
                    ·
                      refine ⟨866659323907110157575395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9244366121675841680804213 866659323907110157575395)
                      ·
                        rfl

theorem cell23_1687813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 2, 4, 1, 5].length) (baseStart_1687813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687813 prefixEnd_1687813 := by exact prefixLift 1687813
  have htrace : WordTrace (prefixWord ++ tailWord_1687813) baseStart_1687813 baseEnd_1687813 := by
    simpa [prefixWord, tailWord_1687813, baseEnd_1687813] using wordTrace_append hprefix tailTrace_1687813
  have hstable : (prefixWord ++ tailWord_1687813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687813).length < 2 ^ (prefixWord ++ tailWord_1687813).sum := by decide
  have hdescent : baseEnd_1687813 < baseStart_1687813 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687848 : List Nat := [2, 1, 5, 1, 3, 2, 2, 1, 1, 3, 2]
def baseStart_1687848 : Nat := 118140960795 + 1687848 * 2 ^ 59
def prefixEnd_1687848 : Nat := 4983230072969 + 3 ^ 40 * 1687848 * 2
def baseEnd_1687848 : Nat := 866677295730017520637735

theorem tailTrace_1687848 : CollatzResearch.WordTrace tailWord_1687848 prefixEnd_1687848 866677295730017520637735 := by
  unfold tailWord_1687848
  simp only [CollatzResearch.WordTrace]
  refine ⟨30780436994611216166920099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41040582659481621555893465 30780436994611216166920099)
  ·
    refine ⟨46170655491916824250380149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30780436994611216166920099 46170655491916824250380149)
    ·
      refine ⟨4328498952367202273473139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46170655491916824250380149 4328498952367202273473139)
      ·
        refine ⟨6492748428550803410209709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4328498952367202273473139 6492748428550803410209709)
        ·
          refine ⟨2434780660706551278828641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6492748428550803410209709 2434780660706551278828641)
          ·
            refine ⟨1826085495529913459121481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2434780660706551278828641 1826085495529913459121481)
            ·
              refine ⟨1369564121647435094341111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826085495529913459121481 1369564121647435094341111)
              ·
                refine ⟨2054346182471152641511667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369564121647435094341111 2054346182471152641511667)
                ·
                  refine ⟨3081519273706728962267501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054346182471152641511667 3081519273706728962267501)
                  ·
                    refine ⟨1155569727640023360850313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3081519273706728962267501 1155569727640023360850313)
                    ·
                      refine ⟨866677295730017520637735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155569727640023360850313 866677295730017520637735)
                      ·
                        rfl

theorem cell23_1687848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 2, 2, 1, 1, 3, 2].length) (baseStart_1687848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687848 prefixEnd_1687848 := by exact prefixLift 1687848
  have htrace : WordTrace (prefixWord ++ tailWord_1687848) baseStart_1687848 baseEnd_1687848 := by
    simpa [prefixWord, tailWord_1687848, baseEnd_1687848] using wordTrace_append hprefix tailTrace_1687848
  have hstable : (prefixWord ++ tailWord_1687848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687848).length < 2 ^ (prefixWord ++ tailWord_1687848).sum := by decide
  have hdescent : baseEnd_1687848 < baseStart_1687848 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1687917 : List Nat := [1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 4]
def baseStart_1687917 : Nat := 118140960795 + 1687917 * 2 ^ 59
def prefixEnd_1687917 : Nat := 4983230072969 + 3 ^ 40 * 1687917 * 2
def baseEnd_1687917 : Nat := 866712725895177750674917

theorem tailTrace_1687917 : CollatzResearch.WordTrace tailWord_1687917 prefixEnd_1687917 866712725895177750674917 := by
  unfold tailWord_1687917
  simp only [CollatzResearch.WordTrace]
  refine ⟨61563390625972457118102005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41042260417314971412068003 61563390625972457118102005)
  ·
    refine ⟨5771567871184917854822063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61563390625972457118102005 5771567871184917854822063)
    ·
      refine ⟨8657351806777376782233095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5771567871184917854822063 8657351806777376782233095)
      ·
        refine ⟨12986027710166065173349643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8657351806777376782233095 12986027710166065173349643)
        ·
          refine ⟨19479041565249097760024465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12986027710166065173349643 19479041565249097760024465)
          ·
            refine ⟨14609281173936823320018349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19479041565249097760024465 14609281173936823320018349)
            ·
              refine ⟨5478480440226308745006881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14609281173936823320018349 5478480440226308745006881)
              ·
                refine ⟨4108860330169731558755161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5478480440226308745006881 4108860330169731558755161)
                ·
                  refine ⟨3081645247627298669066371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4108860330169731558755161 3081645247627298669066371)
                  ·
                    refine ⟨4622467871440948003599557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3081645247627298669066371 4622467871440948003599557)
                    ·
                      refine ⟨866712725895177750674917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4622467871440948003599557 866712725895177750674917)
                      ·
                        rfl

theorem cell23_1687917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 3, 2, 2, 1, 4].length) (baseStart_1687917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1687917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1687917 prefixEnd_1687917 := by exact prefixLift 1687917
  have htrace : WordTrace (prefixWord ++ tailWord_1687917) baseStart_1687917 baseEnd_1687917 := by
    simpa [prefixWord, tailWord_1687917, baseEnd_1687917] using wordTrace_append hprefix tailTrace_1687917
  have hstable : (prefixWord ++ tailWord_1687917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1687917).length < 2 ^ (prefixWord ++ tailWord_1687917).sum := by decide
  have hdescent : baseEnd_1687917 < baseStart_1687917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1687917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688007 : List Nat := [1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1688007 : Nat := 118140960795 + 1688007 * 2 ^ 59
def prefixEnd_1688007 : Nat := 4983230072969 + 3 ^ 40 * 1688007 * 2
def baseEnd_1688007 : Nat := 866758939154082398549503

theorem tailTrace_1688007 : CollatzResearch.WordTrace tailWord_1688007 prefixEnd_1688007 866758939154082398549503 := by
  unfold tailWord_1688007
  simp only [CollatzResearch.WordTrace]
  refine ⟨61566673195646402488878275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41044448797097601659252183 61566673195646402488878275)
  ·
    refine ⟨92350009793469603733317413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61566673195646402488878275 92350009793469603733317413)
    ·
      refine ⟨17315626836275550699997015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92350009793469603733317413 17315626836275550699997015)
      ·
        refine ⟨25973440254413326049995523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17315626836275550699997015 25973440254413326049995523)
        ·
          refine ⟨38960160381619989074993285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25973440254413326049995523 38960160381619989074993285)
          ·
            refine ⟨7305030071553747951561241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38960160381619989074993285 7305030071553747951561241)
            ·
              refine ⟨5478772553665310963670931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7305030071553747951561241 5478772553665310963670931)
              ·
                refine ⟨8218158830497966445506397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5478772553665310963670931 8218158830497966445506397)
                ·
                  refine ⟨3081809561436737417064899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8218158830497966445506397 3081809561436737417064899)
                  ·
                    refine ⟨4622714342155106125597349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3081809561436737417064899 4622714342155106125597349)
                    ·
                      refine ⟨866758939154082398549503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4622714342155106125597349 866758939154082398549503)
                      ·
                        rfl

theorem cell23_1688007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1688007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688007 prefixEnd_1688007 := by exact prefixLift 1688007
  have htrace : WordTrace (prefixWord ++ tailWord_1688007) baseStart_1688007 baseEnd_1688007 := by
    simpa [prefixWord, tailWord_1688007, baseEnd_1688007] using wordTrace_append hprefix tailTrace_1688007
  have hstable : (prefixWord ++ tailWord_1688007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688007).length < 2 ^ (prefixWord ++ tailWord_1688007).sum := by decide
  have hdescent : baseEnd_1688007 < baseStart_1688007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688021 : List Nat := [1, 3, 2, 3, 1, 4, 2, 1, 1, 5]
def baseStart_1688021 : Nat := 118140960795 + 1688021 * 2 ^ 59
def prefixEnd_1688021 : Nat := 4983230072969 + 3 ^ 40 * 1688021 * 2
def baseEnd_1688021 : Nat := 288922042627748447924813

theorem tailTrace_1688021 : CollatzResearch.WordTrace tailWord_1688021 prefixEnd_1688021 288922042627748447924813 := by
  unfold tailWord_1688021
  simp only [CollatzResearch.WordTrace]
  refine ⟨61567183817595682879887917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41044789211730455253258611 61567183817595682879887917)
  ·
    refine ⟨23087693931598381079957969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61567183817595682879887917 23087693931598381079957969)
    ·
      refine ⟨17315770448698785809968477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23087693931598381079957969 17315770448698785809968477)
      ·
        refine ⟨6493413918262044678738179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17315770448698785809968477 6493413918262044678738179)
        ·
          refine ⟨9740120877393067018107269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6493413918262044678738179 9740120877393067018107269)
          ·
            refine ⟨1826272664511200065895113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9740120877393067018107269 1826272664511200065895113)
            ·
              refine ⟨1369704498383400049421335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826272664511200065895113 1369704498383400049421335)
              ·
                refine ⟨2054556747575100074132003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1369704498383400049421335 2054556747575100074132003)
                ·
                  refine ⟨3081835121362650111198005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2054556747575100074132003 3081835121362650111198005)
                  ·
                    refine ⟨288922042627748447924813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3081835121362650111198005 288922042627748447924813)
                    ·
                      rfl

theorem cell23_1688021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 5].length) (baseStart_1688021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688021 prefixEnd_1688021 := by exact prefixLift 1688021
  have htrace : WordTrace (prefixWord ++ tailWord_1688021) baseStart_1688021 baseEnd_1688021 := by
    simpa [prefixWord, tailWord_1688021, baseEnd_1688021] using wordTrace_append hprefix tailTrace_1688021
  have hstable : (prefixWord ++ tailWord_1688021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688021).length < 2 ^ (prefixWord ++ tailWord_1688021).sum := by decide
  have hdescent : baseEnd_1688021 < baseStart_1688021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688024 : List Nat := [2, 1, 2, 2, 2, 1, 1, 1, 7, 2, 2]
def baseStart_1688024 : Nat := 118140960795 + 1688024 * 2 ^ 59
def prefixEnd_1688024 : Nat := 4983230072969 + 3 ^ 40 * 1688024 * 2
def baseEnd_1688024 : Nat := 866767668325208832036925

theorem tailTrace_1688024 : CollatzResearch.WordTrace tailWord_1688024 prefixEnd_1688024 866767668325208832036925 := by
  unfold tailWord_1688024
  simp only [CollatzResearch.WordTrace]
  refine ⟨30783646618292407196123563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41044862157723209594831417 30783646618292407196123563)
  ·
    refine ⟨46175469927438610794185345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30783646618292407196123563 46175469927438610794185345)
    ·
      refine ⟨34631602445578958095639009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46175469927438610794185345 34631602445578958095639009)
      ·
        refine ⟨25973701834184218571729257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34631602445578958095639009 25973701834184218571729257)
        ·
          refine ⟨19480276375638163928796943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25973701834184218571729257 19480276375638163928796943)
          ·
            refine ⟨29220414563457245893195415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19480276375638163928796943 29220414563457245893195415)
            ·
              refine ⟨43830621845185868839793123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29220414563457245893195415 43830621845185868839793123)
              ·
                refine ⟨65745932767778803259689685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43830621845185868839793123 65745932767778803259689685)
                ·
                  refine ⟨1540920299244815701398977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 65745932767778803259689685 1540920299244815701398977)
                  ·
                    refine ⟨1155690224433611776049233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1540920299244815701398977 1155690224433611776049233)
                    ·
                      refine ⟨866767668325208832036925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155690224433611776049233 866767668325208832036925)
                      ·
                        rfl

theorem cell23_1688024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 7, 2, 2].length) (baseStart_1688024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688024 prefixEnd_1688024 := by exact prefixLift 1688024
  have htrace : WordTrace (prefixWord ++ tailWord_1688024) baseStart_1688024 baseEnd_1688024 := by
    simpa [prefixWord, tailWord_1688024, baseEnd_1688024] using wordTrace_append hprefix tailTrace_1688024
  have hstable : (prefixWord ++ tailWord_1688024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688024).length < 2 ^ (prefixWord ++ tailWord_1688024).sum := by decide
  have hdescent : baseEnd_1688024 < baseStart_1688024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688074 : List Nat := [3, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_1688074 : Nat := 118140960795 + 1688074 * 2 ^ 59
def prefixEnd_1688074 : Nat := 4983230072969 + 3 ^ 40 * 1688074 * 2
def baseEnd_1688074 : Nat := 866793342357933636411695

theorem tailTrace_1688074 : CollatzResearch.WordTrace tailWord_1688074 prefixEnd_1688074 866793342357933636411695 := by
  unfold tailWord_1688074
  simp only [CollatzResearch.WordTrace]
  refine ⟨15392279221600918232891819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41046077924269115287711517 15392279221600918232891819)
  ·
    refine ⟨23088418832401377349337729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15392279221600918232891819 23088418832401377349337729)
    ·
      refine ⟨17316314124301033012003297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23088418832401377349337729 17316314124301033012003297)
      ·
        refine ⟨12987235593225774759002473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17316314124301033012003297 12987235593225774759002473)
        ·
          refine ⟨9740426694919331069251855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12987235593225774759002473 9740426694919331069251855)
          ·
            refine ⟨14610640042378996603877783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740426694919331069251855 14610640042378996603877783)
            ·
              refine ⟨21915960063568494905816675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14610640042378996603877783 21915960063568494905816675)
              ·
                refine ⟨32873940095352742358725013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21915960063568494905816675 32873940095352742358725013)
                ·
                  refine ⟨1540965941969659798065235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32873940095352742358725013 1540965941969659798065235)
                  ·
                    refine ⟨2311448912954489697097853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1540965941969659798065235 2311448912954489697097853)
                    ·
                      refine ⟨866793342357933636411695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2311448912954489697097853 866793342357933636411695)
                      ·
                        rfl

theorem cell23_1688074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_1688074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688074 prefixEnd_1688074 := by exact prefixLift 1688074
  have htrace : WordTrace (prefixWord ++ tailWord_1688074) baseStart_1688074 baseEnd_1688074 := by
    simpa [prefixWord, tailWord_1688074, baseEnd_1688074] using wordTrace_append hprefix tailTrace_1688074
  have hstable : (prefixWord ++ tailWord_1688074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688074).length < 2 ^ (prefixWord ++ tailWord_1688074).sum := by decide
  have hdescent : baseEnd_1688074 < baseStart_1688074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688075 : List Nat := [1, 1, 1, 1, 7, 3, 1, 3, 1, 2, 2]
def baseStart_1688075 : Nat := 118140960795 + 1688075 * 2 ^ 59
def prefixEnd_1688075 : Nat := 4983230072969 + 3 ^ 40 * 1688075 * 2
def baseEnd_1688075 : Nat := 866793855838588132499191

theorem tailTrace_1688075 : CollatzResearch.WordTrace tailWord_1688075 prefixEnd_1688075 866793855838588132499191 := by
  unfold tailWord_1688075
  simp only [CollatzResearch.WordTrace]
  refine ⟨61569153359400050102353679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41046102239600033401569119 61569153359400050102353679)
  ·
    refine ⟨92353730039100075153530519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61569153359400050102353679 92353730039100075153530519)
    ·
      refine ⟨138530595058650112730295779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92353730039100075153530519 138530595058650112730295779)
      ·
        refine ⟨207795892587975169095443669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138530595058650112730295779 207795892587975169095443669)
        ·
          refine ⟨4870216232530668025674461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 207795892587975169095443669 4870216232530668025674461)
          ·
            refine ⟨1826331087199000509627923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4870216232530668025674461 1826331087199000509627923)
            ·
              refine ⟨2739496630798500764441885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826331087199000509627923 2739496630798500764441885)
              ·
                refine ⟨1027311236549437786665707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2739496630798500764441885 1027311236549437786665707)
                ·
                  refine ⟨1540966854824156679998561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027311236549437786665707 1540966854824156679998561)
                  ·
                    refine ⟨1155725141118117509998921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1540966854824156679998561 1155725141118117509998921)
                    ·
                      refine ⟨866793855838588132499191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155725141118117509998921 866793855838588132499191)
                      ·
                        rfl

theorem cell23_1688075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 1, 2, 2].length) (baseStart_1688075 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688075 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688075 prefixEnd_1688075 := by exact prefixLift 1688075
  have htrace : WordTrace (prefixWord ++ tailWord_1688075) baseStart_1688075 baseEnd_1688075 := by
    simpa [prefixWord, tailWord_1688075, baseEnd_1688075] using wordTrace_append hprefix tailTrace_1688075
  have hstable : (prefixWord ++ tailWord_1688075).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688075).length < 2 ^ (prefixWord ++ tailWord_1688075).sum := by decide
  have hdescent : baseEnd_1688075 < baseStart_1688075 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688097 : List Nat := [1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1688097 : Nat := 118140960795 + 1688097 * 2 ^ 59
def prefixEnd_1688097 : Nat := 4983230072969 + 3 ^ 40 * 1688097 * 2
def baseEnd_1688097 : Nat := 866805152412987046424089

theorem tailTrace_1688097 : CollatzResearch.WordTrace tailWord_1688097 prefixEnd_1688097 866805152412987046424089 := by
  unfold tailWord_1688097
  simp only [CollatzResearch.WordTrace]
  refine ⟨61569955765320347859654545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41046637176880231906436363 61569955765320347859654545)
  ·
    refine ⟨46177466823990260894740909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61569955765320347859654545 46177466823990260894740909)
    ·
      refine ⟨17316550058996347835527841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46177466823990260894740909 17316550058996347835527841)
      ·
        refine ⟨12987412544247260876645881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17316550058996347835527841 12987412544247260876645881)
        ·
          refine ⟨9740559408185445657484411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12987412544247260876645881 9740559408185445657484411)
          ·
            refine ⟨14610839112278168486226617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9740559408185445657484411 14610839112278168486226617)
            ·
              refine ⟨10958129334208626364669963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14610839112278168486226617 10958129334208626364669963)
              ·
                refine ⟨16437194001312939547004945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10958129334208626364669963 16437194001312939547004945)
                ·
                  refine ⟨12327895500984704660253709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16437194001312939547004945 12327895500984704660253709)
                  ·
                    refine ⟨4622960812869264247595141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12327895500984704660253709 4622960812869264247595141)
                    ·
                      refine ⟨866805152412987046424089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4622960812869264247595141 866805152412987046424089)
                      ·
                        rfl

theorem cell23_1688097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1688097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688097 prefixEnd_1688097 := by exact prefixLift 1688097
  have htrace : WordTrace (prefixWord ++ tailWord_1688097) baseStart_1688097 baseEnd_1688097 := by
    simpa [prefixWord, tailWord_1688097, baseEnd_1688097] using wordTrace_append hprefix tailTrace_1688097
  have hstable : (prefixWord ++ tailWord_1688097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688097).length < 2 ^ (prefixWord ++ tailWord_1688097).sum := by decide
  have hdescent : baseEnd_1688097 < baseStart_1688097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688117 : List Nat := [1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 5]
def baseStart_1688117 : Nat := 118140960795 + 1688117 * 2 ^ 59
def prefixEnd_1688117 : Nat := 4983230072969 + 3 ^ 40 * 1688117 * 2
def baseEnd_1688117 : Nat := 866815422026076968173997

theorem tailTrace_1688117 : CollatzResearch.WordTrace tailWord_1688117 prefixEnd_1688117 866815422026076968173997 := by
  unfold tailWord_1688117
  simp only [CollatzResearch.WordTrace]
  refine ⟨61570685225247891275382605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41047123483498594183588403 61570685225247891275382605)
  ·
    refine ⟨23089006959467959228268477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61570685225247891275382605 23089006959467959228268477)
    ·
      refine ⟨8658377609800484710600679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23089006959467959228268477 8658377609800484710600679)
      ·
        refine ⟨12987566414700727065901019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8658377609800484710600679 12987566414700727065901019)
        ·
          refine ⟨19481349622051090598851529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12987566414700727065901019 19481349622051090598851529)
          ·
            refine ⟨14611012216538317949138647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19481349622051090598851529 14611012216538317949138647)
            ·
              refine ⟨21916518324807476923707971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14611012216538317949138647 21916518324807476923707971)
              ·
                refine ⟨32874777487211215385561957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21916518324807476923707971 32874777487211215385561957)
                ·
                  refine ⟨6164020778852102884792867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32874777487211215385561957 6164020778852102884792867)
                  ·
                    refine ⟨9246031168278154327189301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6164020778852102884792867 9246031168278154327189301)
                    ·
                      refine ⟨866815422026076968173997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9246031168278154327189301 866815422026076968173997)
                      ·
                        rfl

theorem cell23_1688117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 1, 4, 1, 5].length) (baseStart_1688117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688117 prefixEnd_1688117 := by exact prefixLift 1688117
  have htrace : WordTrace (prefixWord ++ tailWord_1688117) baseStart_1688117 baseEnd_1688117 := by
    simpa [prefixWord, tailWord_1688117, baseEnd_1688117] using wordTrace_append hprefix tailTrace_1688117
  have hstable : (prefixWord ++ tailWord_1688117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688117).length < 2 ^ (prefixWord ++ tailWord_1688117).sum := by decide
  have hdescent : baseEnd_1688117 < baseStart_1688117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688118 : List Nat := [5, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2]
def baseStart_1688118 : Nat := 118140960795 + 1688118 * 2 ^ 59
def prefixEnd_1688118 : Nat := 4983230072969 + 3 ^ 40 * 1688118 * 2
def baseEnd_1688118 : Nat := 866815935506731464261493

theorem tailTrace_1688118 : CollatzResearch.WordTrace tailWord_1688118 prefixEnd_1688118 866815935506731464261493 := by
  unfold tailWord_1688118
  simp only [CollatzResearch.WordTrace]
  refine ⟨3848170106140266777885563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41047147798829512297446005 3848170106140266777885563)
  ·
    refine ⟨5772255159210400166828345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3848170106140266777885563 5772255159210400166828345)
    ·
      refine ⟨4329191369407800125121259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5772255159210400166828345 4329191369407800125121259)
      ·
        refine ⟨6493787054111700187681889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329191369407800125121259 6493787054111700187681889)
        ·
          refine ⟨4870340290583775140761417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6493787054111700187681889 4870340290583775140761417)
          ·
            refine ⟨3652755217937831355571063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4870340290583775140761417 3652755217937831355571063)
            ·
              refine ⟨5479132826906747033356595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3652755217937831355571063 5479132826906747033356595)
              ·
                refine ⟨8218699240360120550034893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479132826906747033356595 8218699240360120550034893)
                ·
                  refine ⟨3082012215135045206263085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8218699240360120550034893 3082012215135045206263085)
                  ·
                    refine ⟨1155754580675641952348657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082012215135045206263085 1155754580675641952348657)
                    ·
                      refine ⟨866815935506731464261493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155754580675641952348657 866815935506731464261493)
                      ·
                        rfl

theorem cell23_1688118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 2, 1, 1, 3, 3, 2].length) (baseStart_1688118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688118 prefixEnd_1688118 := by exact prefixLift 1688118
  have htrace : WordTrace (prefixWord ++ tailWord_1688118) baseStart_1688118 baseEnd_1688118 := by
    simpa [prefixWord, tailWord_1688118, baseEnd_1688118] using wordTrace_append hprefix tailTrace_1688118
  have hstable : (prefixWord ++ tailWord_1688118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688118).length < 2 ^ (prefixWord ++ tailWord_1688118).sum := by decide
  have hdescent : baseEnd_1688118 < baseStart_1688118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688148 : List Nat := [2, 4, 1, 1, 1, 3, 1, 4, 2, 2, 2]
def baseStart_1688148 : Nat := 118140960795 + 1688148 * 2 ^ 59
def prefixEnd_1688148 : Nat := 4983230072969 + 3 ^ 40 * 1688148 * 2
def baseEnd_1688148 : Nat := 866831339926366346886355

theorem tailTrace_1688148 : CollatzResearch.WordTrace tailWord_1688148 prefixEnd_1688148 866831339926366346886355 := by
  unfold tailWord_1688148
  simp only [CollatzResearch.WordTrace]
  refine ⟨30785907944067791784880549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41047877258757055713174065 30785907944067791784880549)
  ·
    refine ⟨5772357739512710959665103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30785907944067791784880549 5772357739512710959665103)
    ·
      refine ⟨8658536609269066439497655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5772357739512710959665103 8658536609269066439497655)
      ·
        refine ⟨12987804913903599659246483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8658536609269066439497655 12987804913903599659246483)
        ·
          refine ⟨19481707370855399488869725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12987804913903599659246483 19481707370855399488869725)
          ·
            refine ⟨7305640264070774808326147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19481707370855399488869725 7305640264070774808326147)
            ·
              refine ⟨10958460396106162212489221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7305640264070774808326147 10958460396106162212489221)
              ·
                refine ⟨2054711324269905414841729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10958460396106162212489221 2054711324269905414841729)
                ·
                  refine ⟨1541033493202429061131297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054711324269905414841729 1541033493202429061131297)
                  ·
                    refine ⟨1155775119901821795848473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1541033493202429061131297 1155775119901821795848473)
                    ·
                      refine ⟨866831339926366346886355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155775119901821795848473 866831339926366346886355)
                      ·
                        rfl

theorem cell23_1688148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 4, 2, 2, 2].length) (baseStart_1688148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688148 prefixEnd_1688148 := by exact prefixLift 1688148
  have htrace : WordTrace (prefixWord ++ tailWord_1688148) baseStart_1688148 baseEnd_1688148 := by
    simpa [prefixWord, tailWord_1688148, baseEnd_1688148] using wordTrace_append hprefix tailTrace_1688148
  have hstable : (prefixWord ++ tailWord_1688148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688148).length < 2 ^ (prefixWord ++ tailWord_1688148).sum := by decide
  have hdescent : baseEnd_1688148 < baseStart_1688148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688164 : List Nat := [2, 3, 1, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_1688164 : Nat := 118140960795 + 1688164 * 2 ^ 59
def prefixEnd_1688164 : Nat := 4983230072969 + 3 ^ 40 * 1688164 * 2
def baseEnd_1688164 : Nat := 866839555616838284286281

theorem tailTrace_1688164 : CollatzResearch.WordTrace tailWord_1688164 prefixEnd_1688164 866839555616838284286281 := by
  unfold tailWord_1688164
  simp only [CollatzResearch.WordTrace]
  refine ⟨30786199728038809151171773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41048266304051745534895697 30786199728038809151171773)
  ·
    refine ⟨11544824898014553431689415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30786199728038809151171773 11544824898014553431689415)
    ·
      refine ⟨17317237347021830147534123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11544824898014553431689415 17317237347021830147534123)
      ·
        refine ⟨25975856020532745221301185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17317237347021830147534123 25975856020532745221301185)
        ·
          refine ⟨19481892015399558915975889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25975856020532745221301185 19481892015399558915975889)
          ·
            refine ⟨14611419011549669186981917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19481892015399558915975889 14611419011549669186981917)
            ·
              refine ⟨5479282129331125945118219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14611419011549669186981917 5479282129331125945118219)
              ·
                refine ⟨8218923193996688917677329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479282129331125945118219 8218923193996688917677329)
                ·
                  refine ⟨6164192395497516688257997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8218923193996688917677329 6164192395497516688257997)
                  ·
                    refine ⟨2311572148311568758096749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6164192395497516688257997 2311572148311568758096749)
                    ·
                      refine ⟨866839555616838284286281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2311572148311568758096749 866839555616838284286281)
                      ·
                        rfl

theorem cell23_1688164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_1688164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688164 prefixEnd_1688164 := by exact prefixLift 1688164
  have htrace : WordTrace (prefixWord ++ tailWord_1688164) baseStart_1688164 baseEnd_1688164 := by
    simpa [prefixWord, tailWord_1688164, baseEnd_1688164] using wordTrace_append hprefix tailTrace_1688164
  have hstable : (prefixWord ++ tailWord_1688164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688164).length < 2 ^ (prefixWord ++ tailWord_1688164).sum := by decide
  have hdescent : baseEnd_1688164 < baseStart_1688164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688167 : List Nat := [1, 1, 5, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1688167 : Nat := 118140960795 + 1688167 * 2 ^ 59
def prefixEnd_1688167 : Nat := 4983230072969 + 3 ^ 40 * 1688167 * 2
def baseEnd_1688167 : Nat := 288947032019600590849589

theorem tailTrace_1688167 : CollatzResearch.WordTrace tailWord_1688167 prefixEnd_1688167 288947032019600590849589 := by
  unfold tailWord_1688167
  simp only [CollatzResearch.WordTrace]
  refine ⟨61572508875066749814702755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41048339250044499876468503 61572508875066749814702755)
  ·
    refine ⟨92358763312600124722054133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61572508875066749814702755 92358763312600124722054133)
    ·
      refine ⟨8658634060556261692692575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92358763312600124722054133 8658634060556261692692575)
      ·
        refine ⟨12987951090834392539038863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8658634060556261692692575 12987951090834392539038863)
        ·
          refine ⟨19481926636251588808558295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12987951090834392539038863 19481926636251588808558295)
          ·
            refine ⟨29222889954377383212837443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19481926636251588808558295 29222889954377383212837443)
            ·
              refine ⟨43834334931566074819256165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29222889954377383212837443 43834334931566074819256165)
              ·
                refine ⟨8218937799668639028610531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43834334931566074819256165 8218937799668639028610531)
                ·
                  refine ⟨12328406699502958542915797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8218937799668639028610531 12328406699502958542915797)
                  ·
                    refine ⟨288947032019600590849589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12328406699502958542915797 288947032019600590849589)
                    ·
                      rfl

theorem cell23_1688167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1688167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688167 prefixEnd_1688167 := by exact prefixLift 1688167
  have htrace : WordTrace (prefixWord ++ tailWord_1688167) baseStart_1688167 baseEnd_1688167 := by
    simpa [prefixWord, tailWord_1688167, baseEnd_1688167] using wordTrace_append hprefix tailTrace_1688167
  have hstable : (prefixWord ++ tailWord_1688167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688167).length < 2 ^ (prefixWord ++ tailWord_1688167).sum := by decide
  have hdescent : baseEnd_1688167 < baseStart_1688167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688217 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 6]
def baseStart_1688217 : Nat := 118140960795 + 1688217 * 2 ^ 59
def prefixEnd_1688217 : Nat := 4983230072969 + 3 ^ 40 * 1688217 * 2
def baseEnd_1688217 : Nat := 866866770091526576923537

theorem tailTrace_1688217 : CollatzResearch.WordTrace tailWord_1688217 prefixEnd_1688217 866866770091526576923537 := by
  unfold tailWord_1688217
  simp only [CollatzResearch.WordTrace]
  refine ⟨61574332524885608354022905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41049555016590405569348603 61574332524885608354022905)
  ·
    refine ⟨46180749393664206265517179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61574332524885608354022905 46180749393664206265517179)
    ·
      refine ⟨69271124090496309398275769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46180749393664206265517179 69271124090496309398275769)
      ·
        refine ⟨51953343067872232048706827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69271124090496309398275769 51953343067872232048706827)
        ·
          refine ⟨77930014601808348073060241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51953343067872232048706827 77930014601808348073060241)
          ·
            refine ⟨58447510951356261054795181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77930014601808348073060241 58447510951356261054795181)
            ·
              refine ⟨21917816606758597895548193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58447510951356261054795181 21917816606758597895548193)
              ·
                refine ⟨16438362455068948421661145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21917816606758597895548193 16438362455068948421661145)
                ·
                  refine ⟨12328771841301711316245859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16438362455068948421661145 12328771841301711316245859)
                  ·
                    refine ⟨18493157761952566974368789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12328771841301711316245859 18493157761952566974368789)
                    ·
                      refine ⟨866866770091526576923537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18493157761952566974368789 866866770091526576923537)
                      ·
                        rfl

theorem cell23_1688217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 2, 1, 6].length) (baseStart_1688217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688217 prefixEnd_1688217 := by exact prefixLift 1688217
  have htrace : WordTrace (prefixWord ++ tailWord_1688217) baseStart_1688217 baseEnd_1688217 := by
    simpa [prefixWord, tailWord_1688217, baseEnd_1688217] using wordTrace_append hprefix tailTrace_1688217
  have hstable : (prefixWord ++ tailWord_1688217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688217).length < 2 ^ (prefixWord ++ tailWord_1688217).sum := by decide
  have hdescent : baseEnd_1688217 < baseStart_1688217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688221 : List Nat := [1, 4, 2, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_1688221 : Nat := 118140960795 + 1688221 * 2 ^ 59
def prefixEnd_1688221 : Nat := 4983230072969 + 3 ^ 40 * 1688221 * 2
def baseEnd_1688221 : Nat := 866868824014144561273519

theorem tailTrace_1688221 : CollatzResearch.WordTrace tailWord_1688221 prefixEnd_1688221 866868824014144561273519 := by
  unfold tailWord_1688221
  simp only [CollatzResearch.WordTrace]
  refine ⟨61574478416871117037168517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41049652277914078024779011 61574478416871117037168517)
  ·
    refine ⟨11545214703163334444469097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61574478416871117037168517 11545214703163334444469097)
    ·
      refine ⟨8658911027372500833351823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11545214703163334444469097 8658911027372500833351823)
      ·
        refine ⟨12988366541058751250027735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8658911027372500833351823 12988366541058751250027735)
        ·
          refine ⟨19482549811588126875041603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12988366541058751250027735 19482549811588126875041603)
          ·
            refine ⟨29223824717382190312562405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19482549811588126875041603 29223824717382190312562405)
            ·
              refine ⟨5479467134509160683605451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29223824717382190312562405 5479467134509160683605451)
              ·
                refine ⟨8219200701763741025408177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479467134509160683605451 8219200701763741025408177)
                ·
                  refine ⟨6164400526322805769056133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8219200701763741025408177 6164400526322805769056133)
                  ·
                    refine ⟨1155825098685526081698025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6164400526322805769056133 1155825098685526081698025)
                    ·
                      refine ⟨866868824014144561273519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155825098685526081698025 866868824014144561273519)
                      ·
                        rfl

theorem cell23_1688221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_1688221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688221 prefixEnd_1688221 := by exact prefixLift 1688221
  have htrace : WordTrace (prefixWord ++ tailWord_1688221) baseStart_1688221 baseEnd_1688221 := by
    simpa [prefixWord, tailWord_1688221, baseEnd_1688221] using wordTrace_append hprefix tailTrace_1688221
  have hstable : (prefixWord ++ tailWord_1688221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688221).length < 2 ^ (prefixWord ++ tailWord_1688221).sum := by decide
  have hdescent : baseEnd_1688221 < baseStart_1688221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688267 : List Nat := [1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7]
def baseStart_1688267 : Nat := 118140960795 + 1688267 * 2 ^ 59
def prefixEnd_1688267 : Nat := 4983230072969 + 3 ^ 40 * 1688267 * 2
def baseEnd_1688267 : Nat := 866892444124251381298307

theorem tailTrace_1688267 : CollatzResearch.WordTrace tailWord_1688267 prefixEnd_1688267 866892444124251381298307 := by
  unfold tailWord_1688267
  simp only [CollatzResearch.WordTrace]
  refine ⟨61576156174704466893343055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41050770783136311262228703 61576156174704466893343055)
  ·
    refine ⟨92364234262056700340014583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61576156174704466893343055 92364234262056700340014583)
    ·
      refine ⟨138546351393085050510021875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92364234262056700340014583 138546351393085050510021875)
      ·
        refine ⟨207819527089627575765032813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138546351393085050510021875 207819527089627575765032813)
        ·
          refine ⟨77932322658610340911887305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207819527089627575765032813 77932322658610340911887305)
          ·
            refine ⟨58449241993957755683915479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77932322658610340911887305 58449241993957755683915479)
            ·
              refine ⟨87673862990936633525873219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58449241993957755683915479 87673862990936633525873219)
              ·
                refine ⟨131510794486404950288809829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87673862990936633525873219 131510794486404950288809829)
                ·
                  refine ⟨24658273966200928179151843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 131510794486404950288809829 24658273966200928179151843)
                  ·
                    refine ⟨36987410949301392268727765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24658273966200928179151843 36987410949301392268727765)
                    ·
                      refine ⟨866892444124251381298307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 36987410949301392268727765 866892444124251381298307)
                      ·
                        rfl

theorem cell23_1688267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 1, 7].length) (baseStart_1688267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688267 prefixEnd_1688267 := by exact prefixLift 1688267
  have htrace : WordTrace (prefixWord ++ tailWord_1688267) baseStart_1688267 baseEnd_1688267 := by
    simpa [prefixWord, tailWord_1688267, baseEnd_1688267] using wordTrace_append hprefix tailTrace_1688267
  have hstable : (prefixWord ++ tailWord_1688267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688267).length < 2 ^ (prefixWord ++ tailWord_1688267).sum := by decide
  have hdescent : baseEnd_1688267 < baseStart_1688267 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688281 : List Nat := [1, 2, 1, 2, 3, 2, 1, 2, 4, 3, 2]
def baseStart_1688281 : Nat := 118140960795 + 1688281 * 2 ^ 59
def prefixEnd_1688281 : Nat := 4983230072969 + 3 ^ 40 * 1688281 * 2
def baseEnd_1688281 : Nat := 866899632853414326523243

theorem tailTrace_1688281 : CollatzResearch.WordTrace tailWord_1688281 prefixEnd_1688281 866899632853414326523243 := by
  unfold tailWord_1688281
  simp only [CollatzResearch.WordTrace]
  refine ⟨61576666796653747284352697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41051111197769164856235131 61576666796653747284352697)
  ·
    refine ⟨46182500097490310463264523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61576666796653747284352697 46182500097490310463264523)
    ·
      refine ⟨69273750146235465694896785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46182500097490310463264523 69273750146235465694896785)
      ·
        refine ⟨51955312609676599271172589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69273750146235465694896785 51955312609676599271172589)
        ·
          refine ⟨19483242228628724726689721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51955312609676599271172589 19483242228628724726689721)
          ·
            refine ⟨14612431671471543545017291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19483242228628724726689721 14612431671471543545017291)
            ·
              refine ⟨21918647507207315317525937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14612431671471543545017291 21918647507207315317525937)
              ·
                refine ⟨16438985630405486488144453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21918647507207315317525937 16438985630405486488144453)
                ·
                  refine ⟨3082309805701028716527085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16438985630405486488144453 3082309805701028716527085)
                  ·
                    refine ⟨1155866177137885768697657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082309805701028716527085 1155866177137885768697657)
                    ·
                      refine ⟨866899632853414326523243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155866177137885768697657 866899632853414326523243)
                      ·
                        rfl

theorem cell23_1688281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 2, 1, 2, 4, 3, 2].length) (baseStart_1688281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688281 prefixEnd_1688281 := by exact prefixLift 1688281
  have htrace : WordTrace (prefixWord ++ tailWord_1688281) baseStart_1688281 baseEnd_1688281 := by
    simpa [prefixWord, tailWord_1688281, baseEnd_1688281] using wordTrace_append hprefix tailTrace_1688281
  have hstable : (prefixWord ++ tailWord_1688281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688281).length < 2 ^ (prefixWord ++ tailWord_1688281).sum := by decide
  have hdescent : baseEnd_1688281 < baseStart_1688281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688291 : List Nat := [1, 1, 1, 7, 1, 2, 1, 1, 3, 5]
def baseStart_1688291 : Nat := 118140960795 + 1688291 * 2 ^ 59
def prefixEnd_1688291 : Nat := 4983230072969 + 3 ^ 40 * 1688291 * 2
def baseEnd_1688291 : Nat := 288968255886653095799399

theorem tailTrace_1688291 : CollatzResearch.WordTrace tailWord_1688291 prefixEnd_1688291 288968255886653095799399 := by
  unfold tailWord_1688291
  simp only [CollatzResearch.WordTrace]
  refine ⟨61577031526617518992216727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41051354351078345994811151 61577031526617518992216727)
  ·
    refine ⟨92365547289926278488325091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61577031526617518992216727 92365547289926278488325091)
    ·
      refine ⟨138548320934889417732487637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92365547289926278488325091 138548320934889417732487637)
      ·
        refine ⟨3247226271911470728105179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 138548320934889417732487637 3247226271911470728105179)
        ·
          refine ⟨4870839407867206092157769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3247226271911470728105179 4870839407867206092157769)
          ·
            refine ⟨3653129555900404569118327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4870839407867206092157769 3653129555900404569118327)
            ·
              refine ⟨5479694333850606853677491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653129555900404569118327 5479694333850606853677491)
              ·
                refine ⟨8219541500775910280516237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5479694333850606853677491 8219541500775910280516237)
                ·
                  refine ⟨3082328062790966355193589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8219541500775910280516237 3082328062790966355193589)
                  ·
                    refine ⟨288968255886653095799399, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3082328062790966355193589 288968255886653095799399)
                    ·
                      rfl

theorem cell23_1688291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 5].length) (baseStart_1688291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688291 prefixEnd_1688291 := by exact prefixLift 1688291
  have htrace : WordTrace (prefixWord ++ tailWord_1688291) baseStart_1688291 baseEnd_1688291 := by
    simpa [prefixWord, tailWord_1688291, baseEnd_1688291] using wordTrace_append hprefix tailTrace_1688291
  have hstable : (prefixWord ++ tailWord_1688291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688291).length < 2 ^ (prefixWord ++ tailWord_1688291).sum := by decide
  have hdescent : baseEnd_1688291 < baseStart_1688291 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688304 : List Nat := [2, 1, 1, 1, 3, 1, 5, 2, 1, 6]
def baseStart_1688304 : Nat := 118140960795 + 1688304 * 2 ^ 59
def prefixEnd_1688304 : Nat := 4983230072969 + 3 ^ 40 * 1688304 * 2
def baseEnd_1688304 : Nat := 288970480969489245511879

theorem tailTrace_1688304 : CollatzResearch.WordTrace tailWord_1688304 prefixEnd_1688304 288970480969489245511879 := by
  unfold tailWord_1688304
  simp only [CollatzResearch.WordTrace]
  refine ⟨30788752837785211106219983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41051670450380281474959977 30788752837785211106219983)
  ·
    refine ⟨46183129256677816659329975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30788752837785211106219983 46183129256677816659329975)
    ·
      refine ⟨69274693885016724988994963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46183129256677816659329975 69274693885016724988994963)
      ·
        refine ⟨103912040827525087483492445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69274693885016724988994963 103912040827525087483492445)
        ·
          refine ⟨38967015310321907806309667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103912040827525087483492445 38967015310321907806309667)
          ·
            refine ⟨58450522965482861709464501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38967015310321907806309667 58450522965482861709464501)
            ·
              refine ⟨5479736528014018285262297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58450522965482861709464501 5479736528014018285262297)
              ·
                refine ⟨4109802396010513713946723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5479736528014018285262297 4109802396010513713946723)
                ·
                  refine ⟨6164703594015770570920085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109802396010513713946723 6164703594015770570920085)
                  ·
                    refine ⟨288970480969489245511879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6164703594015770570920085 288970480969489245511879)
                    ·
                      rfl

theorem cell23_1688304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 1, 6].length) (baseStart_1688304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688304 prefixEnd_1688304 := by exact prefixLift 1688304
  have htrace : WordTrace (prefixWord ++ tailWord_1688304) baseStart_1688304 baseEnd_1688304 := by
    simpa [prefixWord, tailWord_1688304, baseEnd_1688304] using wordTrace_append hprefix tailTrace_1688304
  have hstable : (prefixWord ++ tailWord_1688304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688304).length < 2 ^ (prefixWord ++ tailWord_1688304).sum := by decide
  have hdescent : baseEnd_1688304 < baseStart_1688304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688322 : List Nat := [3, 4, 1, 1, 1, 3, 1, 4, 1, 1, 3]
def baseStart_1688322 : Nat := 118140960795 + 1688322 * 2 ^ 59
def prefixEnd_1688322 : Nat := 4983230072969 + 3 ^ 40 * 1688322 * 2
def baseEnd_1688322 : Nat := 866920685560248666110555

theorem tailTrace_1688322 : CollatzResearch.WordTrace tailWord_1688322 prefixEnd_1688322 866920685560248666110555 := by
  unfold tailWord_1688322
  simp only [CollatzResearch.WordTrace]
  refine ⟨15394540547376302821648805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41052108126336807524396813 15394540547376302821648805)
  ·
    refine ⟨2886476352633056779059151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15394540547376302821648805 2886476352633056779059151)
    ·
      refine ⟨4329714528949585168588727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2886476352633056779059151 4329714528949585168588727)
      ·
        refine ⟨6494571793424377752883091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329714528949585168588727 6494571793424377752883091)
        ·
          refine ⟨9741857690136566629324637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6494571793424377752883091 9741857690136566629324637)
          ·
            refine ⟨3653196633801212485996739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9741857690136566629324637 3653196633801212485996739)
            ·
              refine ⟨5479794950701818728995109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3653196633801212485996739 5479794950701818728995109)
              ·
                refine ⟨1027461553256591011686583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5479794950701818728995109 1027461553256591011686583)
                ·
                  refine ⟨1541192329884886517529875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1027461553256591011686583 1541192329884886517529875)
                  ·
                    refine ⟨2311788494827329776294813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1541192329884886517529875 2311788494827329776294813)
                    ·
                      refine ⟨866920685560248666110555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2311788494827329776294813 866920685560248666110555)
                      ·
                        rfl

theorem cell23_1688322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 3, 1, 4, 1, 1, 3].length) (baseStart_1688322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688322 prefixEnd_1688322 := by exact prefixLift 1688322
  have htrace : WordTrace (prefixWord ++ tailWord_1688322) baseStart_1688322 baseEnd_1688322 := by
    simpa [prefixWord, tailWord_1688322, baseEnd_1688322] using wordTrace_append hprefix tailTrace_1688322
  have hstable : (prefixWord ++ tailWord_1688322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688322).length < 2 ^ (prefixWord ++ tailWord_1688322).sum := by decide
  have hdescent : baseEnd_1688322 < baseStart_1688322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688341 : List Nat := [1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 4]
def baseStart_1688341 : Nat := 118140960795 + 1688341 * 2 ^ 59
def prefixEnd_1688341 : Nat := 4983230072969 + 3 ^ 40 * 1688341 * 2
def baseEnd_1688341 : Nat := 866930441692684091772967

theorem tailTrace_1688341 : CollatzResearch.WordTrace tailWord_1688341 prefixEnd_1688341 866930441692684091772967 := by
  unfold tailWord_1688341
  simp only [CollatzResearch.WordTrace]
  refine ⟨61578855176436377531536877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41052570117624251687691251 61578855176436377531536877)
  ·
    refine ⟨23092070691163641574326329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61578855176436377531536877 23092070691163641574326329)
    ·
      refine ⟨17319053018372731180744747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23092070691163641574326329 17319053018372731180744747)
      ·
        refine ⟨25978579527559096771117121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17319053018372731180744747 25978579527559096771117121)
        ·
          refine ⟨19483934645669322578337841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25978579527559096771117121 19483934645669322578337841)
          ·
            refine ⟨14612950984251991933753381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19483934645669322578337841 14612950984251991933753381)
            ·
              refine ⟨2739928309547248487578759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14612950984251991933753381 2739928309547248487578759)
              ·
                refine ⟨4109892464320872731368139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739928309547248487578759 4109892464320872731368139)
                ·
                  refine ⟨6164838696481309097052209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4109892464320872731368139 6164838696481309097052209)
                  ·
                    refine ⟨4623629022360981822789157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6164838696481309097052209 4623629022360981822789157)
                    ·
                      refine ⟨866930441692684091772967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4623629022360981822789157 866930441692684091772967)
                      ·
                        rfl

theorem cell23_1688341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 1, 1, 2, 4].length) (baseStart_1688341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688341 prefixEnd_1688341 := by exact prefixLift 1688341
  have htrace : WordTrace (prefixWord ++ tailWord_1688341) baseStart_1688341 baseEnd_1688341 := by
    simpa [prefixWord, tailWord_1688341, baseEnd_1688341] using wordTrace_append hprefix tailTrace_1688341
  have hstable : (prefixWord ++ tailWord_1688341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688341).length < 2 ^ (prefixWord ++ tailWord_1688341).sum := by decide
  have hdescent : baseEnd_1688341 < baseStart_1688341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688349 : List Nat := [1, 4, 2, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1688349 : Nat := 118140960795 + 1688349 * 2 ^ 59
def prefixEnd_1688349 : Nat := 4983230072969 + 3 ^ 40 * 1688349 * 2
def baseEnd_1688349 : Nat := 866934549537920060472931

theorem tailTrace_1688349 : CollatzResearch.WordTrace tailWord_1688349 prefixEnd_1688349 866934549537920060472931 := by
  unfold tailWord_1688349
  simp only [CollatzResearch.WordTrace]
  refine ⟨61579146960407394897828101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41052764640271596598552067 61579146960407394897828101)
  ·
    refine ⟨11546090055076386543342769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61579146960407394897828101 11546090055076386543342769)
    ·
      refine ⟨8659567541307289907507077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11546090055076386543342769 8659567541307289907507077)
      ·
        refine ⟨1623668913995116857657577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8659567541307289907507077 1623668913995116857657577)
        ·
          refine ⟨1217751685496337643243183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1623668913995116857657577 1217751685496337643243183)
          ·
            refine ⟨1826627528244506464864775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1217751685496337643243183 1826627528244506464864775)
            ·
              refine ⟨2739941292366759697297163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826627528244506464864775 2739941292366759697297163)
              ·
                refine ⟨4109911938550139545945745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2739941292366759697297163 4109911938550139545945745)
                ·
                  refine ⟨3082433953912604659459309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4109911938550139545945745 3082433953912604659459309)
                  ·
                    refine ⟨1155912732717226747297241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082433953912604659459309 1155912732717226747297241)
                    ·
                      refine ⟨866934549537920060472931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155912732717226747297241 866934549537920060472931)
                      ·
                        rfl

theorem cell23_1688349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1688349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688349 prefixEnd_1688349 := by exact prefixLift 1688349
  have htrace : WordTrace (prefixWord ++ tailWord_1688349) baseStart_1688349 baseEnd_1688349 := by
    simpa [prefixWord, tailWord_1688349, baseEnd_1688349] using wordTrace_append hprefix tailTrace_1688349
  have hstable : (prefixWord ++ tailWord_1688349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688349).length < 2 ^ (prefixWord ++ tailWord_1688349).sum := by decide
  have hdescent : baseEnd_1688349 < baseStart_1688349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688351 : List Nat := [1, 1, 2, 4, 2, 3, 3, 7]
def baseStart_1688351 : Nat := 118140960795 + 1688351 * 2 ^ 59
def prefixEnd_1688351 : Nat := 4983230072969 + 3 ^ 40 * 1688351 * 2
def baseEnd_1688351 : Nat := 32108725055527001949923

theorem tailTrace_1688351 : CollatzResearch.WordTrace tailWord_1688351 prefixEnd_1688351 32108725055527001949923 := by
  unfold tailWord_1688351
  simp only [CollatzResearch.WordTrace]
  refine ⟨61579219906400149239400907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41052813270933432826267271 61579219906400149239400907)
  ·
    refine ⟨92368829859600223859101361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61579219906400149239400907 92368829859600223859101361)
    ·
      refine ⟨69276622394700167894326021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92368829859600223859101361 69276622394700167894326021)
      ·
        refine ⟨12989366699006281480186129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69276622394700167894326021 12989366699006281480186129)
        ·
          refine ⟨9742025024254711110139597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12989366699006281480186129 9742025024254711110139597)
          ·
            refine ⟨3653259384095516666302349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9742025024254711110139597 3653259384095516666302349)
            ·
              refine ⟨1369972269035818749863381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3653259384095516666302349 1369972269035818749863381)
              ·
                refine ⟨32108725055527001949923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1369972269035818749863381 32108725055527001949923)
                ·
                  rfl

theorem cell23_1688351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 3, 7].length) (baseStart_1688351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688351 prefixEnd_1688351 := by exact prefixLift 1688351
  have htrace : WordTrace (prefixWord ++ tailWord_1688351) baseStart_1688351 baseEnd_1688351 := by
    simpa [prefixWord, tailWord_1688351, baseEnd_1688351] using wordTrace_append hprefix tailTrace_1688351
  have hstable : (prefixWord ++ tailWord_1688351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688351).length < 2 ^ (prefixWord ++ tailWord_1688351).sum := by decide
  have hdescent : baseEnd_1688351 < baseStart_1688351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688361 : List Nat := [1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 3]
def baseStart_1688361 : Nat := 118140960795 + 1688361 * 2 ^ 59
def prefixEnd_1688361 : Nat := 4983230072969 + 3 ^ 40 * 1688361 * 2
def baseEnd_1688361 : Nat := 866940711305774013522875

theorem tailTrace_1688361 : CollatzResearch.WordTrace tailWord_1688361 prefixEnd_1688361 866940711305774013522875 := by
  unfold tailWord_1688361
  simp only [CollatzResearch.WordTrace]
  refine ⟨61579584636363920947264937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41053056424242613964843291 61579584636363920947264937)
  ·
    refine ⟨46184688477272940710448703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61579584636363920947264937 46184688477272940710448703)
    ·
      refine ⟨69277032715909411065673055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46184688477272940710448703 69277032715909411065673055)
      ·
        refine ⟨103915549073864116598509583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69277032715909411065673055 103915549073864116598509583)
        ·
          refine ⟨155873323610796174897764375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103915549073864116598509583 155873323610796174897764375)
          ·
            refine ⟨233809985416194262346646563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155873323610796174897764375 233809985416194262346646563)
            ·
              refine ⟨350714978124291393519969845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 233809985416194262346646563 350714978124291393519969845)
              ·
                refine ⟨32879529199152318142497173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 350714978124291393519969845 32879529199152318142497173)
                ·
                  refine ⟨1541227931210264912929555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32879529199152318142497173 1541227931210264912929555)
                  ·
                    refine ⟨2311841896815397369394333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1541227931210264912929555 2311841896815397369394333)
                    ·
                      refine ⟨866940711305774013522875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2311841896815397369394333 866940711305774013522875)
                      ·
                        rfl

theorem cell23_1688361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 5, 6, 1, 3].length) (baseStart_1688361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688361 prefixEnd_1688361 := by exact prefixLift 1688361
  have htrace : WordTrace (prefixWord ++ tailWord_1688361) baseStart_1688361 baseEnd_1688361 := by
    simpa [prefixWord, tailWord_1688361, baseEnd_1688361] using wordTrace_append hprefix tailTrace_1688361
  have hstable : (prefixWord ++ tailWord_1688361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688361).length < 2 ^ (prefixWord ++ tailWord_1688361).sum := by decide
  have hdescent : baseEnd_1688361 < baseStart_1688361 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688372 : List Nat := [2, 5, 1, 1, 3, 2, 1, 2, 2, 4]
def baseStart_1688372 : Nat := 118140960795 + 1688372 * 2 ^ 59
def prefixEnd_1688372 : Nat := 4983230072969 + 3 ^ 40 * 1688372 * 2
def baseEnd_1688372 : Nat := 288982119864324490161775

theorem tailTrace_1688372 : CollatzResearch.WordTrace tailWord_1688372 prefixEnd_1688372 288982119864324490161775 := by
  unfold tailWord_1688372
  simp only [CollatzResearch.WordTrace]
  refine ⟨30789992919662034912957685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41053323892882713217276913 30789992919662034912957685)
  ·
    refine ⟨2886561836218315773089783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30789992919662034912957685 2886561836218315773089783)
    ·
      refine ⟨4329842754327473659634675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2886561836218315773089783 4329842754327473659634675)
      ·
        refine ⟨6494764131491210489452013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4329842754327473659634675 6494764131491210489452013)
        ·
          refine ⟨2435536549309203933544505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6494764131491210489452013 2435536549309203933544505)
          ·
            refine ⟨1826652411981902950158379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435536549309203933544505 1826652411981902950158379)
            ·
              refine ⟨2739978617972854425237569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826652411981902950158379 2739978617972854425237569)
              ·
                refine ⟨2054983963479640818928177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2739978617972854425237569 2054983963479640818928177)
                ·
                  refine ⟨1541237972609730614196133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2054983963479640818928177 1541237972609730614196133)
                  ·
                    refine ⟨288982119864324490161775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1541237972609730614196133 288982119864324490161775)
                    ·
                      rfl

theorem cell23_1688372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 4].length) (baseStart_1688372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688372 prefixEnd_1688372 := by exact prefixLift 1688372
  have htrace : WordTrace (prefixWord ++ tailWord_1688372) baseStart_1688372 baseEnd_1688372 := by
    simpa [prefixWord, tailWord_1688372, baseEnd_1688372] using wordTrace_append hprefix tailTrace_1688372
  have hstable : (prefixWord ++ tailWord_1688372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688372).length < 2 ^ (prefixWord ++ tailWord_1688372).sum := by decide
  have hdescent : baseEnd_1688372 < baseStart_1688372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688384 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4]
def baseStart_1688384 : Nat := 118140960795 + 1688384 * 2 ^ 59
def prefixEnd_1688384 : Nat := 4983230072969 + 3 ^ 40 * 1688384 * 2
def baseEnd_1688384 : Nat := 866952521360827423535269

theorem tailTrace_1688384 : CollatzResearch.WordTrace tailWord_1688384 prefixEnd_1688384 866952521360827423535269 := by
  unfold tailWord_1688384
  simp only [CollatzResearch.WordTrace]
  refine ⟨30790211757640297937676103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41053615676853730583568137 30790211757640297937676103)
  ·
    refine ⟨46185317636460446906514155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30790211757640297937676103 46185317636460446906514155)
    ·
      refine ⟨69277976454690670359771233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46185317636460446906514155 69277976454690670359771233)
      ·
        refine ⟨51958482341018002769828425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69277976454690670359771233 51958482341018002769828425)
        ·
          refine ⟨38968861755763502077371319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51958482341018002769828425 38968861755763502077371319)
          ·
            refine ⟨58453292633645253116056979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38968861755763502077371319 58453292633645253116056979)
            ·
              refine ⟨87679938950467879674085469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58453292633645253116056979 87679938950467879674085469)
              ·
                refine ⟨32879977106425454877782051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 87679938950467879674085469 32879977106425454877782051)
                ·
                  refine ⟨49319965659638182316673077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32879977106425454877782051 49319965659638182316673077)
                  ·
                    refine ⟨4623746780591079592188101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49319965659638182316673077 4623746780591079592188101)
                    ·
                      refine ⟨866952521360827423535269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4623746780591079592188101 866952521360827423535269)
                      ·
                        rfl

theorem cell23_1688384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 1, 5, 4].length) (baseStart_1688384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688384 prefixEnd_1688384 := by exact prefixLift 1688384
  have htrace : WordTrace (prefixWord ++ tailWord_1688384) baseStart_1688384 baseEnd_1688384 := by
    simpa [prefixWord, tailWord_1688384, baseEnd_1688384] using wordTrace_append hprefix tailTrace_1688384
  have hstable : (prefixWord ++ tailWord_1688384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688384).length < 2 ^ (prefixWord ++ tailWord_1688384).sum := by decide
  have hdescent : baseEnd_1688384 < baseStart_1688384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688394 : List Nat := [3, 1, 2, 1, 1, 1, 2, 3, 1, 8]
def baseStart_1688394 : Nat := 118140960795 + 1688394 * 2 ^ 59
def prefixEnd_1688394 : Nat := 4983230072969 + 3 ^ 40 * 1688394 * 2
def baseEnd_1688394 : Nat := 288985885389124128136741

theorem tailTrace_1688394 : CollatzResearch.WordTrace tailWord_1688394 prefixEnd_1688394 288985885389124128136741 := by
  unfold tailWord_1688394
  simp only [CollatzResearch.WordTrace]
  refine ⟨15395197061311091895804059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41053858830162911722144157 15395197061311091895804059)
  ·
    refine ⟨23092795591966637843706089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15395197061311091895804059 23092795591966637843706089)
    ·
      refine ⟨17319596693974978382779567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23092795591966637843706089 17319596693974978382779567)
      ·
        refine ⟨25979395040962467574169351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17319596693974978382779567 25979395040962467574169351)
        ·
          refine ⟨38969092561443701361254027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25979395040962467574169351 38969092561443701361254027)
          ·
            refine ⟨58453638842165552041881041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38969092561443701361254027 58453638842165552041881041)
            ·
              refine ⟨43840229131624164031410781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58453638842165552041881041 43840229131624164031410781)
              ·
                refine ⟨16440085924359061511779043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43840229131624164031410781 16440085924359061511779043)
                ·
                  refine ⟨24660128886538592267668565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16440085924359061511779043 24660128886538592267668565)
                  ·
                    refine ⟨288985885389124128136741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24660128886538592267668565 288985885389124128136741)
                    ·
                      rfl

theorem cell23_1688394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_1688394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688394 prefixEnd_1688394 := by exact prefixLift 1688394
  have htrace : WordTrace (prefixWord ++ tailWord_1688394) baseStart_1688394 baseEnd_1688394 := by
    simpa [prefixWord, tailWord_1688394, baseEnd_1688394] using wordTrace_append hprefix tailTrace_1688394
  have hstable : (prefixWord ++ tailWord_1688394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688394).length < 2 ^ (prefixWord ++ tailWord_1688394).sum := by decide
  have hdescent : baseEnd_1688394 < baseStart_1688394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688405 : List Nat := [1, 3, 2, 2, 2, 1, 4, 2, 1, 3, 2]
def baseStart_1688405 : Nat := 118140960795 + 1688405 * 2 ^ 59
def prefixEnd_1688405 : Nat := 4983230072969 + 3 ^ 40 * 1688405 * 2
def baseEnd_1688405 : Nat := 866963304454571841372673

theorem tailTrace_1688405 : CollatzResearch.WordTrace tailWord_1688405 prefixEnd_1688405 866963304454571841372673 := by
  unfold tailWord_1688405
  simp only [CollatzResearch.WordTrace]
  refine ⟨61581189448204516461866669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41054126298803010974577779 61581189448204516461866669)
  ·
    refine ⟨23092946043076693673200001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61581189448204516461866669 23092946043076693673200001)
    ·
      refine ⟨17319709532307520254900001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23092946043076693673200001 17319709532307520254900001)
      ·
        refine ⟨12989782149230640191175001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17319709532307520254900001 12989782149230640191175001)
        ·
          refine ⟨9742336611922980143381251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12989782149230640191175001 9742336611922980143381251)
          ·
            refine ⟨14613504917884470215071877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9742336611922980143381251 14613504917884470215071877)
            ·
              refine ⟨2740032172103338165325977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14613504917884470215071877 2740032172103338165325977)
              ·
                refine ⟨2055024129077503623994483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740032172103338165325977 2055024129077503623994483)
                ·
                  refine ⟨3082536193616255435991725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055024129077503623994483 3082536193616255435991725)
                  ·
                    refine ⟨1155951072606095788496897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3082536193616255435991725 1155951072606095788496897)
                    ·
                      refine ⟨866963304454571841372673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1155951072606095788496897 866963304454571841372673)
                      ·
                        rfl

theorem cell23_1688405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 4, 2, 1, 3, 2].length) (baseStart_1688405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688405 prefixEnd_1688405 := by exact prefixLift 1688405
  have htrace : WordTrace (prefixWord ++ tailWord_1688405) baseStart_1688405 baseEnd_1688405 := by
    simpa [prefixWord, tailWord_1688405, baseEnd_1688405] using wordTrace_append hprefix tailTrace_1688405
  have hstable : (prefixWord ++ tailWord_1688405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688405).length < 2 ^ (prefixWord ++ tailWord_1688405).sum := by decide
  have hdescent : baseEnd_1688405 < baseStart_1688405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688441 : List Nat := [1, 2, 1, 3, 2, 3, 3, 1, 7]
def baseStart_1688441 : Nat := 118140960795 + 1688441 * 2 ^ 59
def prefixEnd_1688441 : Nat := 4983230072969 + 3 ^ 40 * 1688441 * 2
def baseEnd_1688441 : Nat := 96331309973125966724723

theorem tailTrace_1688441 : CollatzResearch.WordTrace tailWord_1688441 prefixEnd_1688441 96331309973125966724723 := by
  unfold tailWord_1688441
  simp only [CollatzResearch.WordTrace]
  refine ⟨61582502476074094610177177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41055001650716063073451451 61582502476074094610177177)
  ·
    refine ⟨46186876857055570957632883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61582502476074094610177177 46186876857055570957632883)
    ·
      refine ⟨69280315285583356436449325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46186876857055570957632883 69280315285583356436449325)
      ·
        refine ⟨25980118232093758663668497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69280315285583356436449325 25980118232093758663668497)
        ·
          refine ⟨19485088674070318997751373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25980118232093758663668497 19485088674070318997751373)
          ·
            refine ⟨7306908252776369624156765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19485088674070318997751373 7306908252776369624156765)
            ·
              refine ⟨2740090594791138609058787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7306908252776369624156765 2740090594791138609058787)
              ·
                refine ⟨4110135892186707913588181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740090594791138609058787 4110135892186707913588181)
                ·
                  refine ⟨96331309973125966724723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4110135892186707913588181 96331309973125966724723)
                  ·
                    rfl

theorem cell23_1688441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 7].length) (baseStart_1688441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688441 prefixEnd_1688441 := by exact prefixLift 1688441
  have htrace : WordTrace (prefixWord ++ tailWord_1688441) baseStart_1688441 baseEnd_1688441 := by
    simpa [prefixWord, tailWord_1688441, baseEnd_1688441] using wordTrace_append hprefix tailTrace_1688441
  have hstable : (prefixWord ++ tailWord_1688441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688441).length < 2 ^ (prefixWord ++ tailWord_1688441).sum := by decide
  have hdescent : baseEnd_1688441 < baseStart_1688441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688446 : List Nat := [4, 2, 3, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_1688446 : Nat := 118140960795 + 1688446 * 2 ^ 59
def prefixEnd_1688446 : Nat := 4983230072969 + 3 ^ 40 * 1688446 * 2
def baseEnd_1688446 : Nat := 866984357161406180959985

theorem tailTrace_1688446 : CollatzResearch.WordTrace tailWord_1688446 prefixEnd_1688446 866984357161406180959985 := by
  unfold tailWord_1688446
  simp only [CollatzResearch.WordTrace]
  refine ⟨7697835605131997558013649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41055123227370653642739461 7697835605131997558013649)
  ·
    refine ⟨5773376703848998168510237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7697835605131997558013649 5773376703848998168510237)
    ·
      refine ⟨2165016263943374313191339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5773376703848998168510237 2165016263943374313191339)
      ·
        refine ⟨3247524395915061469787009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165016263943374313191339 3247524395915061469787009)
        ·
          refine ⟨2435643296936296102340257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3247524395915061469787009 2435643296936296102340257)
          ·
            refine ⟨1826732472702222076755193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2435643296936296102340257 1826732472702222076755193)
            ·
              refine ⟨1370049354526666557566395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1826732472702222076755193 1370049354526666557566395)
              ·
                refine ⟨2055074031789999836349593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370049354526666557566395 2055074031789999836349593)
                ·
                  refine ⟨1541305523842499877262195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055074031789999836349593 1541305523842499877262195)
                  ·
                    refine ⟨2311958285763749815893293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1541305523842499877262195 2311958285763749815893293)
                    ·
                      refine ⟨866984357161406180959985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2311958285763749815893293 866984357161406180959985)
                      ·
                        rfl

theorem cell23_1688446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_1688446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688446 prefixEnd_1688446 := by exact prefixLift 1688446
  have htrace : WordTrace (prefixWord ++ tailWord_1688446) baseStart_1688446 baseEnd_1688446 := by
    simpa [prefixWord, tailWord_1688446, baseEnd_1688446] using wordTrace_append hprefix tailTrace_1688446
  have hstable : (prefixWord ++ tailWord_1688446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688446).length < 2 ^ (prefixWord ++ tailWord_1688446).sum := by decide
  have hdescent : baseEnd_1688446 < baseStart_1688446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688451 : List Nat := [1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 3]
def baseStart_1688451 : Nat := 118140960795 + 1688451 * 2 ^ 59
def prefixEnd_1688451 : Nat := 4983230072969 + 3 ^ 40 * 1688451 * 2
def baseEnd_1688451 : Nat := 866986924564678661397461

theorem tailTrace_1688451 : CollatzResearch.WordTrace tailWord_1688451 prefixEnd_1688451 866986924564678661397461 := by
  unfold tailWord_1688451
  simp only [CollatzResearch.WordTrace]
  refine ⟨61582867206037866318041207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41055244804025244212027471 61582867206037866318041207)
  ·
    refine ⟨92374300809056799477061811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61582867206037866318041207 92374300809056799477061811)
    ·
      refine ⟨138561451213585199215592717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92374300809056799477061811 138561451213585199215592717)
      ·
        refine ⟨51960544205094449705847269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138561451213585199215592717 51960544205094449705847269)
        ·
          refine ⟨9742602038455209319846363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51960544205094449705847269 9742602038455209319846363)
          ·
            refine ⟨14613903057682813979769545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9742602038455209319846363 14613903057682813979769545)
            ·
              refine ⟨10960427293262110484827159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14613903057682813979769545 10960427293262110484827159)
              ·
                refine ⟨16440640939893165727240739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10960427293262110484827159 16440640939893165727240739)
                ·
                  refine ⟨24660961409839748590861109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16440640939893165727240739 24660961409839748590861109)
                  ·
                    refine ⟨2311965132172476430393229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24660961409839748590861109 2311965132172476430393229)
                    ·
                      refine ⟨866986924564678661397461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2311965132172476430393229 866986924564678661397461)
                      ·
                        rfl

theorem cell23_1688451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 1, 5, 3].length) (baseStart_1688451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688451 prefixEnd_1688451 := by exact prefixLift 1688451
  have htrace : WordTrace (prefixWord ++ tailWord_1688451) baseStart_1688451 baseEnd_1688451 := by
    simpa [prefixWord, tailWord_1688451, baseEnd_1688451] using wordTrace_append hprefix tailTrace_1688451
  have hstable : (prefixWord ++ tailWord_1688451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688451).length < 2 ^ (prefixWord ++ tailWord_1688451).sum := by decide
  have hdescent : baseEnd_1688451 < baseStart_1688451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688625 : List Nat := [1, 2, 2, 3, 1, 2, 3, 3, 2, 4]
def baseStart_1688625 : Nat := 118140960795 + 1688625 * 2 ^ 59
def prefixEnd_1688625 : Nat := 4983230072969 + 3 ^ 40 * 1688625 * 2
def baseEnd_1688625 : Nat := 289025423399520326873887

theorem tailTrace_1688625 : CollatzResearch.WordTrace tailWord_1688625 prefixEnd_1688625 289025423399520326873887 := by
  unfold tailWord_1688625
  simp only [CollatzResearch.WordTrace]
  refine ⟨61589213507407494034875329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41059475671604996023250219 61589213507407494034875329)
  ·
    refine ⟨46191910130555620526156497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61589213507407494034875329 46191910130555620526156497)
    ·
      refine ⟨34643932597916715394617373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46191910130555620526156497 34643932597916715394617373)
      ·
        refine ⟨12991474724218768272981515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34643932597916715394617373 12991474724218768272981515)
        ·
          refine ⟨19487212086328152409472273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12991474724218768272981515 19487212086328152409472273)
          ·
            refine ⟨14615409064746114307104205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19487212086328152409472273 14615409064746114307104205)
            ·
              refine ⟨5480778399279792865164077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14615409064746114307104205 5480778399279792865164077)
              ·
                refine ⟨2055291899729922324436529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5480778399279792865164077 2055291899729922324436529)
                ·
                  refine ⟨1541468924797441743327397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055291899729922324436529 1541468924797441743327397)
                  ·
                    refine ⟨289025423399520326873887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1541468924797441743327397 289025423399520326873887)
                    ·
                      rfl

theorem cell23_1688625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_1688625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688625 prefixEnd_1688625 := by exact prefixLift 1688625
  have htrace : WordTrace (prefixWord ++ tailWord_1688625) baseStart_1688625 baseEnd_1688625 := by
    simpa [prefixWord, tailWord_1688625, baseEnd_1688625] using wordTrace_append hprefix tailTrace_1688625
  have hstable : (prefixWord ++ tailWord_1688625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688625).length < 2 ^ (prefixWord ++ tailWord_1688625).sum := by decide
  have hdescent : baseEnd_1688625 < baseStart_1688625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688632 : List Nat := [2, 1, 2, 1, 5, 3, 1, 2, 1, 1, 4]
def baseStart_1688632 : Nat := 118140960795 + 1688632 * 2 ^ 59
def prefixEnd_1688632 : Nat := 4983230072969 + 3 ^ 40 * 1688632 * 2
def baseEnd_1688632 : Nat := 867079864563142453234129

theorem tailTrace_1688632 : CollatzResearch.WordTrace tailWord_1688632 prefixEnd_1688632 867079864563142453234129 := by
  unfold tailWord_1688632
  simp only [CollatzResearch.WordTrace]
  refine ⟨30794734409191067115190075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41059645878921422820253433 30794734409191067115190075)
  ·
    refine ⟨46192101613786600672785113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30794734409191067115190075 46192101613786600672785113)
    ·
      refine ⟨34644076210339950504588835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46192101613786600672785113 34644076210339950504588835)
      ·
        refine ⟨51966114315509925756883253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34644076210339950504588835 51966114315509925756883253)
        ·
          refine ⟨4871823217079055539707805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51966114315509925756883253 4871823217079055539707805)
          ·
            refine ⟨1826933706404645827390427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4871823217079055539707805 1826933706404645827390427)
            ·
              refine ⟨2740400559606968741085641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1826933706404645827390427 2740400559606968741085641)
              ·
                refine ⟨2055300419705226555814231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740400559606968741085641 2055300419705226555814231)
                ·
                  refine ⟨3082950629557839833721347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055300419705226555814231 3082950629557839833721347)
                  ·
                    refine ⟨4624425944336759750582021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3082950629557839833721347 4624425944336759750582021)
                    ·
                      refine ⟨867079864563142453234129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4624425944336759750582021 867079864563142453234129)
                      ·
                        rfl

theorem cell23_1688632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 3, 1, 2, 1, 1, 4].length) (baseStart_1688632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688632 prefixEnd_1688632 := by exact prefixLift 1688632
  have htrace : WordTrace (prefixWord ++ tailWord_1688632) baseStart_1688632 baseEnd_1688632 := by
    simpa [prefixWord, tailWord_1688632, baseEnd_1688632] using wordTrace_append hprefix tailTrace_1688632
  have hstable : (prefixWord ++ tailWord_1688632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688632).length < 2 ^ (prefixWord ++ tailWord_1688632).sum := by decide
  have hdescent : baseEnd_1688632 < baseStart_1688632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688651 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 3, 9]
def baseStart_1688651 : Nat := 118140960795 + 1688651 * 2 ^ 59
def prefixEnd_1688651 : Nat := 4983230072969 + 3 ^ 40 * 1688651 * 2
def baseEnd_1688651 : Nat := 289029873565192626298847

theorem tailTrace_1688651 : CollatzResearch.WordTrace tailWord_1688651 prefixEnd_1688651 289029873565192626298847 := by
  unfold tailWord_1688651
  simp only [CollatzResearch.WordTrace]
  refine ⟨61590161805313300475321807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41060107870208866983547871 61590161805313300475321807)
  ·
    refine ⟨92385242707969950712982711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61590161805313300475321807 92385242707969950712982711)
    ·
      refine ⟨138577864061954926069474067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92385242707969950712982711 138577864061954926069474067)
      ·
        refine ⟨207866796092932389104211101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138577864061954926069474067 207866796092932389104211101)
        ·
          refine ⟨77950048534849645914079163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 207866796092932389104211101 77950048534849645914079163)
          ·
            refine ⟨116925072802274468871118745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77950048534849645914079163 116925072802274468871118745)
            ·
              refine ⟨87693804601705851653339059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116925072802274468871118745 87693804601705851653339059)
              ·
                refine ⟨131540706902558777480008589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87693804601705851653339059 131540706902558777480008589)
                ·
                  refine ⟨49327765088459541555003221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 131540706902558777480008589 49327765088459541555003221)
                  ·
                    refine ⟨289029873565192626298847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49327765088459541555003221 289029873565192626298847)
                    ·
                      rfl

theorem cell23_1688651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 9].length) (baseStart_1688651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688651 prefixEnd_1688651 := by exact prefixLift 1688651
  have htrace : WordTrace (prefixWord ++ tailWord_1688651) baseStart_1688651 baseEnd_1688651 := by
    simpa [prefixWord, tailWord_1688651, baseEnd_1688651] using wordTrace_append hprefix tailTrace_1688651
  have hstable : (prefixWord ++ tailWord_1688651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688651).length < 2 ^ (prefixWord ++ tailWord_1688651).sum := by decide
  have hdescent : baseEnd_1688651 < baseStart_1688651 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688668 : List Nat := [2, 2, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1688668 : Nat := 118140960795 + 1688668 * 2 ^ 59
def prefixEnd_1688668 : Nat := 4983230072969 + 3 ^ 40 * 1688668 * 2
def baseEnd_1688668 : Nat := 289032783288901437461321

theorem tailTrace_1688668 : CollatzResearch.WordTrace tailWord_1688668 prefixEnd_1688668 289032783288901437461321 := by
  unfold tailWord_1688668
  simp only [CollatzResearch.WordTrace]
  refine ⟨30795390923125856189345329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41060521230834474919127105 30795390923125856189345329)
  ·
    refine ⟨23096543192344392142008997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30795390923125856189345329 23096543192344392142008997)
    ·
      refine ⟨4330601848564573526626687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23096543192344392142008997 4330601848564573526626687)
      ·
        refine ⟨6495902772846860289940031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4330601848564573526626687 6495902772846860289940031)
        ·
          refine ⟨9743854159270290434910047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6495902772846860289940031 9743854159270290434910047)
          ·
            refine ⟨14615781238905435652365071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743854159270290434910047 14615781238905435652365071)
            ·
              refine ⟨21923671858358153478547607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14615781238905435652365071 21923671858358153478547607)
              ·
                refine ⟨32885507787537230217821411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21923671858358153478547607 32885507787537230217821411)
                ·
                  refine ⟨49328261681305845326732117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32885507787537230217821411 49328261681305845326732117)
                  ·
                    refine ⟨289032783288901437461321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 49328261681305845326732117 289032783288901437461321)
                    ·
                      rfl

theorem cell23_1688668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1688668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688668 prefixEnd_1688668 := by exact prefixLift 1688668
  have htrace : WordTrace (prefixWord ++ tailWord_1688668) baseStart_1688668 baseEnd_1688668 := by
    simpa [prefixWord, tailWord_1688668, baseEnd_1688668] using wordTrace_append hprefix tailTrace_1688668
  have hstable : (prefixWord ++ tailWord_1688668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688668).length < 2 ^ (prefixWord ++ tailWord_1688668).sum := by decide
  have hdescent : baseEnd_1688668 < baseStart_1688668 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688682 : List Nat := [3, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_1688682 : Nat := 118140960795 + 1688682 * 2 ^ 59
def prefixEnd_1688682 : Nat := 4983230072969 + 3 ^ 40 * 1688682 * 2
def baseEnd_1688682 : Nat := 867105538595867257608899

theorem tailTrace_1688682 : CollatzResearch.WordTrace tailWord_1688682 prefixEnd_1688682 867105538595867257608899 := by
  unfold tailWord_1688682
  simp only [CollatzResearch.WordTrace]
  refine ⟨15397823117050248192425075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41060861645467328513133533 15397823117050248192425075)
  ·
    refine ⟨23096734675575372288637613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15397823117050248192425075 23096734675575372288637613)
    ·
      refine ⟨8661275503340764608239105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23096734675575372288637613 8661275503340764608239105)
      ·
        refine ⟨6495956627505573456179329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8661275503340764608239105 6495956627505573456179329)
        ·
          refine ⟨4871967470629180092134497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6495956627505573456179329 4871967470629180092134497)
          ·
            refine ⟨3653975602971885069100873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4871967470629180092134497 3653975602971885069100873)
            ·
              refine ⟨2740481702228913801825655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3653975602971885069100873 2740481702228913801825655)
              ·
                refine ⟨4110722553343370702738483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740481702228913801825655 4110722553343370702738483)
                ·
                  refine ⟨6166083830015056054107725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4110722553343370702738483 6166083830015056054107725)
                  ·
                    refine ⟨2312281436255646020290397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6166083830015056054107725 2312281436255646020290397)
                    ·
                      refine ⟨867105538595867257608899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2312281436255646020290397 867105538595867257608899)
                      ·
                        rfl

theorem cell23_1688682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_1688682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688682 prefixEnd_1688682 := by exact prefixLift 1688682
  have htrace : WordTrace (prefixWord ++ tailWord_1688682) baseStart_1688682 baseEnd_1688682 := by
    simpa [prefixWord, tailWord_1688682, baseEnd_1688682] using wordTrace_append hprefix tailTrace_1688682
  have hstable : (prefixWord ++ tailWord_1688682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688682).length < 2 ^ (prefixWord ++ tailWord_1688682).sum := by decide
  have hdescent : baseEnd_1688682 < baseStart_1688682 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688688 : List Nat := [2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4]
def baseStart_1688688 : Nat := 118140960795 + 1688688 * 2 ^ 59
def prefixEnd_1688688 : Nat := 4983230072969 + 3 ^ 40 * 1688688 * 2
def baseEnd_1688688 : Nat := 867108619479794234133871

theorem tailTrace_1688688 : CollatzResearch.WordTrace tailWord_1688688 prefixEnd_1688688 867108619479794234133871 := by
  unfold tailWord_1688688
  simp only [CollatzResearch.WordTrace]
  refine ⟨30795755653089627897209359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41061007537452837196279145 30795755653089627897209359)
  ·
    refine ⟨46193633479634441845814039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30795755653089627897209359 46193633479634441845814039)
    ·
      refine ⟨69290450219451662768721059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46193633479634441845814039 69290450219451662768721059)
      ·
        refine ⟨103935675329177494153081589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69290450219451662768721059 103935675329177494153081589)
        ·
          refine ⟨9743969562110390076851399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103935675329177494153081589 9743969562110390076851399)
          ·
            refine ⟨14615954343165585115277099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9743969562110390076851399 14615954343165585115277099)
            ·
              refine ⟨21923931514748377672915649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14615954343165585115277099 21923931514748377672915649)
              ·
                refine ⟨16442948636061283254686737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21923931514748377672915649 16442948636061283254686737)
                ·
                  refine ⟨12332211477045962441015053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16442948636061283254686737 12332211477045962441015053)
                  ·
                    refine ⟨4624579303892235915380645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12332211477045962441015053 4624579303892235915380645)
                    ·
                      refine ⟨867108619479794234133871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4624579303892235915380645 867108619479794234133871)
                      ·
                        rfl

theorem cell23_1688688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 2, 2, 3, 4].length) (baseStart_1688688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688688 prefixEnd_1688688 := by exact prefixLift 1688688
  have htrace : WordTrace (prefixWord ++ tailWord_1688688) baseStart_1688688 baseEnd_1688688 := by
    simpa [prefixWord, tailWord_1688688, baseEnd_1688688] using wordTrace_append hprefix tailTrace_1688688
  have hstable : (prefixWord ++ tailWord_1688688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688688).length < 2 ^ (prefixWord ++ tailWord_1688688).sum := by decide
  have hdescent : baseEnd_1688688 < baseStart_1688688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688709 : List Nat := [1, 3, 1, 1, 6, 1, 1, 3, 1, 3, 2]
def baseStart_1688709 : Nat := 118140960795 + 1688709 * 2 ^ 59
def prefixEnd_1688709 : Nat := 4983230072969 + 3 ^ 40 * 1688709 * 2
def baseEnd_1688709 : Nat := 867119402573538651971275

theorem tailTrace_1688709 : CollatzResearch.WordTrace tailWord_1688709 prefixEnd_1688709 867119402573538651971275 := by
  unfold tailWord_1688709
  simp only [CollatzResearch.WordTrace]
  refine ⟨61592277239103176380933181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41061518159402117587288787 61592277239103176380933181)
  ·
    refine ⟨23097103964663691142849943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61592277239103176380933181 23097103964663691142849943)
    ·
      refine ⟨34645655946995536714274915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23097103964663691142849943 34645655946995536714274915)
      ·
        refine ⟨51968483920493305071412373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34645655946995536714274915 51968483920493305071412373)
        ·
          refine ⟨2436022683773123675222455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51968483920493305071412373 2436022683773123675222455)
          ·
            refine ⟨3654034025659685512833683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436022683773123675222455 3654034025659685512833683)
            ·
              refine ⟨5481051038489528269250525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3654034025659685512833683 5481051038489528269250525)
              ·
                refine ⟨2055394139433573100968947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5481051038489528269250525 2055394139433573100968947)
                ·
                  refine ⟨3083091209150359651453421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055394139433573100968947 3083091209150359651453421)
                  ·
                    refine ⟨1156159203431384869295033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3083091209150359651453421 1156159203431384869295033)
                    ·
                      refine ⟨867119402573538651971275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156159203431384869295033 867119402573538651971275)
                      ·
                        rfl

theorem cell23_1688709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 6, 1, 1, 3, 1, 3, 2].length) (baseStart_1688709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688709 prefixEnd_1688709 := by exact prefixLift 1688709
  have htrace : WordTrace (prefixWord ++ tailWord_1688709) baseStart_1688709 baseEnd_1688709 := by
    simpa [prefixWord, tailWord_1688709, baseEnd_1688709] using wordTrace_append hprefix tailTrace_1688709
  have hstable : (prefixWord ++ tailWord_1688709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688709).length < 2 ^ (prefixWord ++ tailWord_1688709).sum := by decide
  have hdescent : baseEnd_1688709 < baseStart_1688709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688812 : List Nat := [2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 4]
def baseStart_1688812 : Nat := 118140960795 + 1688812 * 2 ^ 59
def prefixEnd_1688812 : Nat := 4983230072969 + 3 ^ 40 * 1688812 * 2
def baseEnd_1688812 : Nat := 867172291080951748983301

theorem tailTrace_1688812 : CollatzResearch.WordTrace tailWord_1688812 prefixEnd_1688812 867172291080951748983301 := by
  unfold tailWord_1688812
  simp only [CollatzResearch.WordTrace]
  refine ⟨30798016978865012485966345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41064022638486683314621793 30798016978865012485966345)
  ·
    refine ⟨23098512734148759364474759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30798016978865012485966345 23098512734148759364474759)
    ·
      refine ⟨34647769101223139046712139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23098512734148759364474759 34647769101223139046712139)
      ·
        refine ⟨51971653651834708570068209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34647769101223139046712139 51971653651834708570068209)
        ·
          refine ⟨38978740238876031427551157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51971653651834708570068209 38978740238876031427551157)
          ·
            refine ⟨3654256897394627946332921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38978740238876031427551157 3654256897394627946332921)
            ·
              refine ⟨2740692673045970959749691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3654256897394627946332921 2740692673045970959749691)
              ·
                refine ⟨4111039009568956439624537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740692673045970959749691 4111039009568956439624537)
                ·
                  refine ⟨3083279257176717329718403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4111039009568956439624537 3083279257176717329718403)
                  ·
                    refine ⟨4624918885765075994577605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3083279257176717329718403 4624918885765075994577605)
                    ·
                      refine ⟨867172291080951748983301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4624918885765075994577605 867172291080951748983301)
                      ·
                        rfl

theorem cell23_1688812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 1, 4].length) (baseStart_1688812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688812 prefixEnd_1688812 := by exact prefixLift 1688812
  have htrace : WordTrace (prefixWord ++ tailWord_1688812) baseStart_1688812 baseEnd_1688812 := by
    simpa [prefixWord, tailWord_1688812, baseEnd_1688812] using wordTrace_append hprefix tailTrace_1688812
  have hstable : (prefixWord ++ tailWord_1688812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688812).length < 2 ^ (prefixWord ++ tailWord_1688812).sum := by decide
  have hdescent : baseEnd_1688812 < baseStart_1688812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688835 : List Nat := [1, 1, 1, 3, 2, 4, 1, 4, 6]
def baseStart_1688835 : Nat := 118140960795 + 1688835 * 2 ^ 59
def prefixEnd_1688835 : Nat := 4983230072969 + 3 ^ 40 * 1688835 * 2
def baseEnd_1688835 : Nat := 96353789015111684332855

theorem tailTrace_1688835 : CollatzResearch.WordTrace tailWord_1688835 prefixEnd_1688835 96353789015111684332855 := by
  unfold tailWord_1688835
  simp only [CollatzResearch.WordTrace]
  refine ⟨61596872836646699900019959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41064581891097799933346639 61596872836646699900019959)
  ·
    refine ⟨92395309254970049850029939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61596872836646699900019959 92395309254970049850029939)
    ·
      refine ⟨138592963882455074775044909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92395309254970049850029939 138592963882455074775044909)
      ·
        refine ⟨51972361455920653040641841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138592963882455074775044909 51972361455920653040641841)
        ·
          refine ⟨38979271091940489780481381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51972361455920653040641841 38979271091940489780481381)
          ·
            refine ⟨7308613329738841833840259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38979271091940489780481381 7308613329738841833840259)
            ·
              refine ⟨10962919994608262750760389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7308613329738841833840259 10962919994608262750760389)
              ·
                refine ⟨2055547498989049265767573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10962919994608262750760389 2055547498989049265767573)
                ·
                  refine ⟨96353789015111684332855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2055547498989049265767573 96353789015111684332855)
                  ·
                    rfl

theorem cell23_1688835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 4, 1, 4, 6].length) (baseStart_1688835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688835 prefixEnd_1688835 := by exact prefixLift 1688835
  have htrace : WordTrace (prefixWord ++ tailWord_1688835) baseStart_1688835 baseEnd_1688835 := by
    simpa [prefixWord, tailWord_1688835, baseEnd_1688835] using wordTrace_append hprefix tailTrace_1688835
  have hstable : (prefixWord ++ tailWord_1688835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688835).length < 2 ^ (prefixWord ++ tailWord_1688835).sum := by decide
  have hdescent : baseEnd_1688835 < baseStart_1688835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688866 : List Nat := [3, 3, 1, 1, 4, 2, 1, 1, 2, 2, 3]
def baseStart_1688866 : Nat := 118140960795 + 1688866 * 2 ^ 59
def prefixEnd_1688866 : Nat := 4983230072969 + 3 ^ 40 * 1688866 * 2
def baseEnd_1688866 : Nat := 867200019036294537708053

theorem tailTrace_1688866 : CollatzResearch.WordTrace tailWord_1688866 prefixEnd_1688866 867200019036294537708053 := by
  unfold tailWord_1688866
  simp only [CollatzResearch.WordTrace]
  refine ⟨15399500874883598048599613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41065335666356261462932301 15399500874883598048599613)
  ·
    refine ⟨5774812828081349268224855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15399500874883598048599613 5774812828081349268224855)
    ·
      refine ⟨8662219242122023902337283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5774812828081349268224855 8662219242122023902337283)
      ·
        refine ⟨12993328863183035853505925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8662219242122023902337283 12993328863183035853505925)
        ·
          refine ⟨2436249161846819222532361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12993328863183035853505925 2436249161846819222532361)
          ·
            refine ⟨1827186871385114416899271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436249161846819222532361 1827186871385114416899271)
            ·
              refine ⟨2740780307077671625348907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827186871385114416899271 2740780307077671625348907)
              ·
                refine ⟨4111170460616507438023361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2740780307077671625348907 4111170460616507438023361)
                ·
                  refine ⟨3083377845462380578517521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4111170460616507438023361 3083377845462380578517521)
                  ·
                    refine ⟨2312533384096785433888141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083377845462380578517521 2312533384096785433888141)
                    ·
                      refine ⟨867200019036294537708053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2312533384096785433888141 867200019036294537708053)
                      ·
                        rfl

theorem cell23_1688866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 1, 2, 2, 3].length) (baseStart_1688866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688866 prefixEnd_1688866 := by exact prefixLift 1688866
  have htrace : WordTrace (prefixWord ++ tailWord_1688866) baseStart_1688866 baseEnd_1688866 := by
    simpa [prefixWord, tailWord_1688866, baseEnd_1688866] using wordTrace_append hprefix tailTrace_1688866
  have hstable : (prefixWord ++ tailWord_1688866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688866).length < 2 ^ (prefixWord ++ tailWord_1688866).sum := by decide
  have hdescent : baseEnd_1688866 < baseStart_1688866 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688905 : List Nat := [1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 5]
def baseStart_1688905 : Nat := 118140960795 + 1688905 * 2 ^ 59
def prefixEnd_1688905 : Nat := 4983230072969 + 3 ^ 40 * 1688905 * 2
def baseEnd_1688905 : Nat := 867220044781819885120373

theorem tailTrace_1688905 : CollatzResearch.WordTrace tailWord_1688905 prefixEnd_1688905 867220044781819885120373 := by
  unfold tailWord_1688905
  simp only [CollatzResearch.WordTrace]
  refine ⟨61599425946393101855068169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41066283964262067903378779 61599425946393101855068169)
  ·
    refine ⟨46199569459794826391301127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61599425946393101855068169 46199569459794826391301127)
    ·
      refine ⟨69299354189692239586951691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46199569459794826391301127 69299354189692239586951691)
      ·
        refine ⟨103949031284538359380427537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69299354189692239586951691 103949031284538359380427537)
        ·
          refine ⟨77961773463403769535320653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103949031284538359380427537 77961773463403769535320653)
          ·
            refine ⟨29235665048776413575745245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77961773463403769535320653 29235665048776413575745245)
            ·
              refine ⟨10963374393291155090904467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29235665048776413575745245 10963374393291155090904467)
              ·
                refine ⟨16445061589936732636356701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10963374393291155090904467 16445061589936732636356701)
                ·
                  refine ⟨6166898096226274738633763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16445061589936732636356701 6166898096226274738633763)
                  ·
                    refine ⟨9250347144339412107950645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6166898096226274738633763 9250347144339412107950645)
                    ·
                      refine ⟨867220044781819885120373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9250347144339412107950645 867220044781819885120373)
                      ·
                        rfl

theorem cell23_1688905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 3, 1, 3, 1, 5].length) (baseStart_1688905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688905 prefixEnd_1688905 := by exact prefixLift 1688905
  have htrace : WordTrace (prefixWord ++ tailWord_1688905) baseStart_1688905 baseEnd_1688905 := by
    simpa [prefixWord, tailWord_1688905, baseEnd_1688905] using wordTrace_append hprefix tailTrace_1688905
  have hstable : (prefixWord ++ tailWord_1688905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688905).length < 2 ^ (prefixWord ++ tailWord_1688905).sum := by decide
  have hdescent : baseEnd_1688905 < baseStart_1688905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688915 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6]
def baseStart_1688915 : Nat := 118140960795 + 1688915 * 2 ^ 59
def prefixEnd_1688915 : Nat := 4983230072969 + 3 ^ 40 * 1688915 * 2
def baseEnd_1688915 : Nat := 867225179588364845995327

theorem tailTrace_1688915 : CollatzResearch.WordTrace tailWord_1688915 prefixEnd_1688915 867225179588364845995327 := by
  unfold tailWord_1688915
  simp only [CollatzResearch.WordTrace]
  refine ⟨61599790676356873562932199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41066527117571249041954799 61599790676356873562932199)
  ·
    refine ⟨92399686014535310344398299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61599790676356873562932199 92399686014535310344398299)
    ·
      refine ⟨138599529021802965516597449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92399686014535310344398299 138599529021802965516597449)
      ·
        refine ⟨103949646766352224137448087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138599529021802965516597449 103949646766352224137448087)
        ·
          refine ⟨155924470149528336206172131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103949646766352224137448087 155924470149528336206172131)
          ·
            refine ⟨233886705224292504309258197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155924470149528336206172131 233886705224292504309258197)
            ·
              refine ⟨5481719653694355569748239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 233886705224292504309258197 5481719653694355569748239)
              ·
                refine ⟨8222579480541533354622359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5481719653694355569748239 8222579480541533354622359)
                ·
                  refine ⟨12333869220812300031933539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8222579480541533354622359 12333869220812300031933539)
                  ·
                    refine ⟨18500803831218450047900309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12333869220812300031933539 18500803831218450047900309)
                    ·
                      refine ⟨867225179588364845995327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18500803831218450047900309 867225179588364845995327)
                      ·
                        rfl

theorem cell23_1688915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_1688915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688915 prefixEnd_1688915 := by exact prefixLift 1688915
  have htrace : WordTrace (prefixWord ++ tailWord_1688915) baseStart_1688915 baseEnd_1688915 := by
    simpa [prefixWord, tailWord_1688915, baseEnd_1688915] using wordTrace_append hprefix tailTrace_1688915
  have hstable : (prefixWord ++ tailWord_1688915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688915).length < 2 ^ (prefixWord ++ tailWord_1688915).sum := by decide
  have hdescent : baseEnd_1688915 < baseStart_1688915 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688919 : List Nat := [1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 4]
def baseStart_1688919 : Nat := 118140960795 + 1688919 * 2 ^ 59
def prefixEnd_1688919 : Nat := 4983230072969 + 3 ^ 40 * 1688919 * 2
def baseEnd_1688919 : Nat := 867227233510982830345309

theorem tailTrace_1688919 : CollatzResearch.WordTrace tailWord_1688919 prefixEnd_1688919 867227233510982830345309 := by
  unfold tailWord_1688919
  simp only [CollatzResearch.WordTrace]
  refine ⟨61599936568342382246077811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41066624378894921497385207 61599936568342382246077811)
  ·
    refine ⟨92399904852513573369116717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61599936568342382246077811 92399904852513573369116717)
    ·
      refine ⟨34649964319692590013418769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92399904852513573369116717 34649964319692590013418769)
      ·
        refine ⟨25987473239769442510064077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34649964319692590013418769 25987473239769442510064077)
        ·
          refine ⟨9745302464913540941274029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25987473239769442510064077 9745302464913540941274029)
          ·
            refine ⟨3654488424342577852977761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9745302464913540941274029 3654488424342577852977761)
            ·
              refine ⟨2740866318256933389733321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3654488424342577852977761 2740866318256933389733321)
              ·
                refine ⟨2055649738692700042299991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2740866318256933389733321 2055649738692700042299991)
                ·
                  refine ⟨3083474608039050063449987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055649738692700042299991 3083474608039050063449987)
                  ·
                    refine ⟨4625211912058575095174981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3083474608039050063449987 4625211912058575095174981)
                    ·
                      refine ⟨867227233510982830345309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4625211912058575095174981 867227233510982830345309)
                      ·
                        rfl

theorem cell23_1688919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 3, 2, 2, 1, 1, 4].length) (baseStart_1688919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688919 prefixEnd_1688919 := by exact prefixLift 1688919
  have htrace : WordTrace (prefixWord ++ tailWord_1688919) baseStart_1688919 baseEnd_1688919 := by
    simpa [prefixWord, tailWord_1688919, baseEnd_1688919] using wordTrace_append hprefix tailTrace_1688919
  have hstable : (prefixWord ++ tailWord_1688919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688919).length < 2 ^ (prefixWord ++ tailWord_1688919).sum := by decide
  have hdescent : baseEnd_1688919 < baseStart_1688919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688922 : List Nat := [3, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3]
def baseStart_1688922 : Nat := 118140960795 + 1688922 * 2 ^ 59
def prefixEnd_1688922 : Nat := 4983230072969 + 3 ^ 40 * 1688922 * 2
def baseEnd_1688922 : Nat := 867228773952946318607795

theorem tailTrace_1688922 : CollatzResearch.WordTrace tailWord_1688922 prefixEnd_1688922 867228773952946318607795 := by
  unfold tailWord_1688922
  simp only [CollatzResearch.WordTrace]
  refine ⟨15400011496832878439609255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41066697324887675838958013 15400011496832878439609255)
  ·
    refine ⟨23100017245249317659413883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15400011496832878439609255 23100017245249317659413883)
    ·
      refine ⟨34650025867873976489120825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23100017245249317659413883 34650025867873976489120825)
      ·
        refine ⟨25987519400905482366840619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34650025867873976489120825 25987519400905482366840619)
        ·
          refine ⟨38981279101358223550260929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25987519400905482366840619 38981279101358223550260929)
          ·
            refine ⟨29235959326018667662695697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38981279101358223550260929 29235959326018667662695697)
            ·
              refine ⟨21926969494514000747021773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29235959326018667662695697 21926969494514000747021773)
              ·
                refine ⟨8222613560442750280133165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21926969494514000747021773 8222613560442750280133165)
                ·
                  refine ⟨3083480085166031355049937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8222613560442750280133165 3083480085166031355049937)
                  ·
                    refine ⟨2312610063874523516287453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083480085166031355049937 2312610063874523516287453)
                    ·
                      refine ⟨867228773952946318607795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2312610063874523516287453 867228773952946318607795)
                      ·
                        rfl

theorem cell23_1688922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_1688922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688922 prefixEnd_1688922 := by exact prefixLift 1688922
  have htrace : WordTrace (prefixWord ++ tailWord_1688922) baseStart_1688922 baseEnd_1688922 := by
    simpa [prefixWord, tailWord_1688922, baseEnd_1688922] using wordTrace_append hprefix tailTrace_1688922
  have hstable : (prefixWord ++ tailWord_1688922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688922).length < 2 ^ (prefixWord ++ tailWord_1688922).sum := by decide
  have hdescent : baseEnd_1688922 < baseStart_1688922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688955 : List Nat := [1, 1, 1, 1, 1, 6, 2, 1, 2, 7]
def baseStart_1688955 : Nat := 118140960795 + 1688955 * 2 ^ 59
def prefixEnd_1688955 : Nat := 4983230072969 + 3 ^ 40 * 1688955 * 2
def baseEnd_1688955 : Nat := 289081906271514896498381

theorem tailTrace_1688955 : CollatzResearch.WordTrace tailWord_1688955 prefixEnd_1688955 289081906271514896498381 := by
  unfold tailWord_1688955
  simp only [CollatzResearch.WordTrace]
  refine ⟨61601249596211960394388319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41067499730807973596258879 61601249596211960394388319)
  ·
    refine ⟨92401874394317940591582479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61601249596211960394388319 92401874394317940591582479)
    ·
      refine ⟨138602811591476910887373719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92401874394317940591582479 138602811591476910887373719)
      ·
        refine ⟨207904217387215366331060579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138602811591476910887373719 207904217387215366331060579)
        ·
          refine ⟨311856326080823049496590869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 207904217387215366331060579 311856326080823049496590869)
          ·
            refine ⟨14618265285038580445152697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 311856326080823049496590869 14618265285038580445152697)
            ·
              refine ⟨10963698963778935333864523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14618265285038580445152697 10963698963778935333864523)
              ·
                refine ⟨16445548445668403000796785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10963698963778935333864523 16445548445668403000796785)
                ·
                  refine ⟨12334161334251302250597589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16445548445668403000796785 12334161334251302250597589)
                  ·
                    refine ⟨289081906271514896498381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12334161334251302250597589 289081906271514896498381)
                    ·
                      rfl

theorem cell23_1688955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 1, 2, 7].length) (baseStart_1688955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688955 prefixEnd_1688955 := by exact prefixLift 1688955
  have htrace : WordTrace (prefixWord ++ tailWord_1688955) baseStart_1688955 baseEnd_1688955 := by
    simpa [prefixWord, tailWord_1688955, baseEnd_1688955] using wordTrace_append hprefix tailTrace_1688955
  have hstable : (prefixWord ++ tailWord_1688955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688955).length < 2 ^ (prefixWord ++ tailWord_1688955).sum := by decide
  have hdescent : baseEnd_1688955 < baseStart_1688955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1688990 : List Nat := [4, 3, 1, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_1688990 : Nat := 118140960795 + 1688990 * 2 ^ 59
def prefixEnd_1688990 : Nat := 4983230072969 + 3 ^ 40 * 1688990 * 2
def baseEnd_1688990 : Nat := 867263690637452052557483

theorem tailTrace_1688990 : CollatzResearch.WordTrace tailWord_1688990 prefixEnd_1688990 867263690637452052557483 := by
  unfold tailWord_1688990
  simp only [CollatzResearch.WordTrace]
  refine ⟨7700315768885645171489053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41068350767390107581274949 7700315768885645171489053)
  ·
    refine ⟨2887618413332116939308395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7700315768885645171489053 2887618413332116939308395)
    ·
      refine ⟨4331427619998175408962593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2887618413332116939308395 4331427619998175408962593)
      ·
        refine ⟨3248570714998631556721945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4331427619998175408962593 3248570714998631556721945)
        ·
          refine ⟨2436428036248973667541459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3248570714998631556721945 2436428036248973667541459)
          ·
            refine ⟨3654642054373460501312189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2436428036248973667541459 3654642054373460501312189)
            ·
              refine ⟨1370490770390047687992071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3654642054373460501312189 1370490770390047687992071)
              ·
                refine ⟨2055736155585071531988107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370490770390047687992071 2055736155585071531988107)
                ·
                  refine ⟨3083604233377607297982161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2055736155585071531988107 3083604233377607297982161)
                  ·
                    refine ⟨2312703175033205473486621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083604233377607297982161 2312703175033205473486621)
                    ·
                      refine ⟨867263690637452052557483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2312703175033205473486621 867263690637452052557483)
                      ·
                        rfl

theorem cell23_1688990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_1688990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1688990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1688990 prefixEnd_1688990 := by exact prefixLift 1688990
  have htrace : WordTrace (prefixWord ++ tailWord_1688990) baseStart_1688990 baseEnd_1688990 := by
    simpa [prefixWord, tailWord_1688990, baseEnd_1688990] using wordTrace_append hprefix tailTrace_1688990
  have hstable : (prefixWord ++ tailWord_1688990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1688990).length < 2 ^ (prefixWord ++ tailWord_1688990).sum := by decide
  have hdescent : baseEnd_1688990 < baseStart_1688990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1688990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689009 : List Nat := [1, 2, 2, 4, 1, 1, 1, 2, 3, 4, 2]
def baseStart_1689009 : Nat := 118140960795 + 1689009 * 2 ^ 59
def prefixEnd_1689009 : Nat := 4983230072969 + 3 ^ 40 * 1689009 * 2
def baseEnd_1689009 : Nat := 867273446769887478219895

theorem tailTrace_1689009 : CollatzResearch.WordTrace tailWord_1689009 prefixEnd_1689009 867273446769887478219895 := by
  unfold tailWord_1689009
  simp only [CollatzResearch.WordTrace]
  refine ⟨61603219138016327616854081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41068812758677551744569387 61603219138016327616854081)
  ·
    refine ⟨46202414353512245712640561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61603219138016327616854081 46202414353512245712640561)
    ·
      refine ⟨34651810765134184284480421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46202414353512245712640561 34651810765134184284480421)
      ·
        refine ⟨6497214518462659553340079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34651810765134184284480421 6497214518462659553340079)
        ·
          refine ⟨9745821777693989330010119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6497214518462659553340079 9745821777693989330010119)
          ·
            refine ⟨14618732666540983995015179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9745821777693989330010119 14618732666540983995015179)
            ·
              refine ⟨21928098999811475992522769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14618732666540983995015179 21928098999811475992522769)
              ·
                refine ⟨16446074249858606994392077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21928098999811475992522769 16446074249858606994392077)
                ·
                  refine ⟨6167277843696977622897029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16446074249858606994392077 6167277843696977622897029)
                  ·
                    refine ⟨1156364595693183304293193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6167277843696977622897029 1156364595693183304293193)
                    ·
                      refine ⟨867273446769887478219895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156364595693183304293193 867273446769887478219895)
                      ·
                        rfl

theorem cell23_1689009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_1689009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689009 prefixEnd_1689009 := by exact prefixLift 1689009
  have htrace : WordTrace (prefixWord ++ tailWord_1689009) baseStart_1689009 baseEnd_1689009 := by
    simpa [prefixWord, tailWord_1689009, baseEnd_1689009] using wordTrace_append hprefix tailTrace_1689009
  have hstable : (prefixWord ++ tailWord_1689009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689009).length < 2 ^ (prefixWord ++ tailWord_1689009).sum := by decide
  have hdescent : baseEnd_1689009 < baseStart_1689009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689032 : List Nat := [2, 1, 3, 1, 3, 1, 3, 2, 7]
def baseStart_1689032 : Nat := 118140960795 + 1689032 * 2 ^ 59
def prefixEnd_1689032 : Nat := 4983230072969 + 3 ^ 40 * 1689032 * 2
def baseEnd_1689032 : Nat := 96365028536104543136921

theorem tailTrace_1689032 : CollatzResearch.WordTrace tailWord_1689032 prefixEnd_1689032 96365028536104543136921 := by
  unfold tailWord_1689032
  simp only [CollatzResearch.WordTrace]
  refine ⟨30802029008466501272470675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41069372011288668363294233 30802029008466501272470675)
  ·
    refine ⟨46203043512699751908706013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30802029008466501272470675 46203043512699751908706013)
    ·
      refine ⟨17326141317262406965764755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46203043512699751908706013 17326141317262406965764755)
      ·
        refine ⟨25989211975893610448647133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17326141317262406965764755 25989211975893610448647133)
        ·
          refine ⟨9745954490960103918242675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25989211975893610448647133 9745954490960103918242675)
          ·
            refine ⟨14618931736440155877364013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9745954490960103918242675 14618931736440155877364013)
            ·
              refine ⟨5482099401165058454011505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14618931736440155877364013 5482099401165058454011505)
              ·
                refine ⟨4111574550873793840508629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5482099401165058454011505 4111574550873793840508629)
                ·
                  refine ⟨96365028536104543136921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4111574550873793840508629 96365028536104543136921)
                  ·
                    rfl

theorem cell23_1689032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 7].length) (baseStart_1689032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689032 prefixEnd_1689032 := by exact prefixLift 1689032
  have htrace : WordTrace (prefixWord ++ tailWord_1689032) baseStart_1689032 baseEnd_1689032 := by
    simpa [prefixWord, tailWord_1689032, baseEnd_1689032] using wordTrace_append hprefix tailTrace_1689032
  have hstable : (prefixWord ++ tailWord_1689032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689032).length < 2 ^ (prefixWord ++ tailWord_1689032).sum := by decide
  have hdescent : baseEnd_1689032 < baseStart_1689032 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689049 : List Nat := [1, 2, 1, 2, 4, 2, 1, 5, 5]
def baseStart_1689049 : Nat := 118140960795 + 1689049 * 2 ^ 59
def prefixEnd_1689049 : Nat := 4983230072969 + 3 ^ 40 * 1689049 * 2
def baseEnd_1689049 : Nat := 96365998444007480191079

theorem tailTrace_1689049 : CollatzResearch.WordTrace tailWord_1689049 prefixEnd_1689049 96365998444007480191079 := by
  unfold tailWord_1689049
  simp only [CollatzResearch.WordTrace]
  refine ⟨61604678057871414448310201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41069785371914276298873467 61604678057871414448310201)
  ·
    refine ⟨46203508543403560836232651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61604678057871414448310201 46203508543403560836232651)
    ·
      refine ⟨69305262815105341254348977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46203508543403560836232651 69305262815105341254348977)
      ·
        refine ⟨51978947111329005940761733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69305262815105341254348977 51978947111329005940761733)
        ·
          refine ⟨9746052583374188613892825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51978947111329005940761733 9746052583374188613892825)
          ·
            refine ⟨7309539437530641460419619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9746052583374188613892825 7309539437530641460419619)
            ·
              refine ⟨10964309156295962190629429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309539437530641460419619 10964309156295962190629429)
              ·
                refine ⟨1027903983402746455371509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10964309156295962190629429 1027903983402746455371509)
                ·
                  refine ⟨96365998444007480191079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1027903983402746455371509 96365998444007480191079)
                  ·
                    rfl

theorem cell23_1689049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 1, 5, 5].length) (baseStart_1689049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689049 prefixEnd_1689049 := by exact prefixLift 1689049
  have htrace : WordTrace (prefixWord ++ tailWord_1689049) baseStart_1689049 baseEnd_1689049 := by
    simpa [prefixWord, tailWord_1689049, baseEnd_1689049] using wordTrace_append hprefix tailTrace_1689049
  have hstable : (prefixWord ++ tailWord_1689049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689049).length < 2 ^ (prefixWord ++ tailWord_1689049).sum := by decide
  have hdescent : baseEnd_1689049 < baseStart_1689049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689059 : List Nat := [1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1689059 : Nat := 118140960795 + 1689059 * 2 ^ 59
def prefixEnd_1689059 : Nat := 4983230072969 + 3 ^ 40 * 1689059 * 2
def baseEnd_1689059 : Nat := 867299120802612282594665

theorem tailTrace_1689059 : CollatzResearch.WordTrace tailWord_1689059 prefixEnd_1689059 867299120802612282594665 := by
  unfold tailWord_1689059
  simp only [CollatzResearch.WordTrace]
  refine ⟨61605042787835186156174231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41070028525223457437449487 61605042787835186156174231)
  ·
    refine ⟨92407564181752779234261347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61605042787835186156174231 92407564181752779234261347)
    ·
      refine ⟨138611346272629168851392021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92407564181752779234261347 138611346272629168851392021)
      ·
        refine ⟨6497406856529492289909001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138611346272629168851392021 6497406856529492289909001)
        ·
          refine ⟨4873055142397119217431751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6497406856529492289909001 4873055142397119217431751)
          ·
            refine ⟨7309582713595678826147627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4873055142397119217431751 7309582713595678826147627)
            ·
              refine ⟨10964374070393518239221441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7309582713595678826147627 10964374070393518239221441)
              ·
                refine ⟨8223280552795138679416081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10964374070393518239221441 8223280552795138679416081)
                ·
                  refine ⟨6167460414596354009562061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8223280552795138679416081 6167460414596354009562061)
                  ·
                    refine ⟨2312797655473632753585773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6167460414596354009562061 2312797655473632753585773)
                    ·
                      refine ⟨867299120802612282594665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2312797655473632753585773 867299120802612282594665)
                      ·
                        rfl

theorem cell23_1689059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1689059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689059 prefixEnd_1689059 := by exact prefixLift 1689059
  have htrace : WordTrace (prefixWord ++ tailWord_1689059) baseStart_1689059 baseEnd_1689059 := by
    simpa [prefixWord, tailWord_1689059, baseEnd_1689059] using wordTrace_append hprefix tailTrace_1689059
  have hstable : (prefixWord ++ tailWord_1689059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689059).length < 2 ^ (prefixWord ++ tailWord_1689059).sum := by decide
  have hdescent : baseEnd_1689059 < baseStart_1689059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689077 : List Nat := [1, 3, 5, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_1689077 : Nat := 118140960795 + 1689077 * 2 ^ 59
def prefixEnd_1689077 : Nat := 4983230072969 + 3 ^ 40 * 1689077 * 2
def baseEnd_1689077 : Nat := 867308363454393212169583

theorem tailTrace_1689077 : CollatzResearch.WordTrace tailWord_1689077 prefixEnd_1689077 867308363454393212169583 := by
  unfold tailWord_1689077
  simp only [CollatzResearch.WordTrace]
  refine ⟨61605699301769975230329485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41070466201179983486886323 61605699301769975230329485)
  ·
    refine ⟨23102137238163740711373557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61605699301769975230329485 23102137238163740711373557)
    ·
      refine ⟨2165825366077850691691271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 23102137238163740711373557 2165825366077850691691271)
      ·
        refine ⟨3248738049116776037536907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2165825366077850691691271 3248738049116776037536907)
        ·
          refine ⟨4873107073675164056305361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3248738049116776037536907 4873107073675164056305361)
          ·
            refine ⟨3654830305256373042229021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4873107073675164056305361 3654830305256373042229021)
            ·
              refine ⟨1370561364471139890835883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3654830305256373042229021 1370561364471139890835883)
              ·
                refine ⟨2055842046706709836253825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370561364471139890835883 2055842046706709836253825)
                ·
                  refine ⟨1541881535030032377190369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2055842046706709836253825 1541881535030032377190369)
                  ·
                    refine ⟨1156411151272524282892777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1541881535030032377190369 1156411151272524282892777)
                    ·
                      refine ⟨867308363454393212169583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156411151272524282892777 867308363454393212169583)
                      ·
                        rfl

theorem cell23_1689077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_1689077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689077 prefixEnd_1689077 := by exact prefixLift 1689077
  have htrace : WordTrace (prefixWord ++ tailWord_1689077) baseStart_1689077 baseEnd_1689077 := by
    simpa [prefixWord, tailWord_1689077, baseEnd_1689077] using wordTrace_append hprefix tailTrace_1689077
  have hstable : (prefixWord ++ tailWord_1689077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689077).length < 2 ^ (prefixWord ++ tailWord_1689077).sum := by decide
  have hdescent : baseEnd_1689077 < baseStart_1689077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689082 : List Nat := [3, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4]
def baseStart_1689082 : Nat := 118140960795 + 1689082 * 2 ^ 59
def prefixEnd_1689082 : Nat := 4983230072969 + 3 ^ 40 * 1689082 * 2
def baseEnd_1689082 : Nat := 867310930857665692607059

theorem tailTrace_1689082 : CollatzResearch.WordTrace tailWord_1689082 prefixEnd_1689082 867310930857665692607059 := by
  unfold tailWord_1689082
  simp only [CollatzResearch.WordTrace]
  refine ⟨15401470416687965271065375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41070587777834574056174333 15401470416687965271065375)
  ·
    refine ⟨23102205625031947906598063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15401470416687965271065375 23102205625031947906598063)
    ·
      refine ⟨34653308437547921859897095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23102205625031947906598063 34653308437547921859897095)
      ·
        refine ⟨51979962656321882789845643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34653308437547921859897095 51979962656321882789845643)
        ·
          refine ⟨77969943984482824184768465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51979962656321882789845643 77969943984482824184768465)
          ·
            refine ⟨58477457988362118138576349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77969943984482824184768465 58477457988362118138576349)
            ·
              refine ⟨21929046745635794301966131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58477457988362118138576349 21929046745635794301966131)
              ·
                refine ⟨32893570118453691452949197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21929046745635794301966131 32893570118453691452949197)
                ·
                  refine ⟨12335088794420134294855949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32893570118453691452949197 12335088794420134294855949)
                  ·
                    refine ⟨4625658297907550360570981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12335088794420134294855949 4625658297907550360570981)
                    ·
                      refine ⟨867310930857665692607059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4625658297907550360570981 867310930857665692607059)
                      ·
                        rfl

theorem cell23_1689082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 1, 3, 3, 4].length) (baseStart_1689082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689082 prefixEnd_1689082 := by exact prefixLift 1689082
  have htrace : WordTrace (prefixWord ++ tailWord_1689082) baseStart_1689082 baseEnd_1689082 := by
    simpa [prefixWord, tailWord_1689082, baseEnd_1689082] using wordTrace_append hprefix tailTrace_1689082
  have hstable : (prefixWord ++ tailWord_1689082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689082).length < 2 ^ (prefixWord ++ tailWord_1689082).sum := by decide
  have hdescent : baseEnd_1689082 < baseStart_1689082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689119 : List Nat := [1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 3]
def baseStart_1689119 : Nat := 118140960795 + 1689119 * 2 ^ 59
def prefixEnd_1689119 : Nat := 4983230072969 + 3 ^ 40 * 1689119 * 2
def baseEnd_1689119 : Nat := 867329929641882047844389

theorem tailTrace_1689119 : CollatzResearch.WordTrace tailWord_1689119 prefixEnd_1689119 867329929641882047844389 := by
  unfold tailWord_1689119
  simp only [CollatzResearch.WordTrace]
  refine ⟨61607231167617816403358411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41071487445078544268905607 61607231167617816403358411)
  ·
    refine ⟨92410846751426724605037617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61607231167617816403358411 92410846751426724605037617)
    ·
      refine ⟨69308135063570043453778213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92410846751426724605037617 69308135063570043453778213)
      ·
        refine ⟨12995275324419383147583415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 69308135063570043453778213 12995275324419383147583415)
        ·
          refine ⟨19492912986629074721375123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12995275324419383147583415 19492912986629074721375123)
          ·
            refine ⟨29239369479943612082062685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19492912986629074721375123 29239369479943612082062685)
            ·
              refine ⟨10964763554978854530773507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29239369479943612082062685 10964763554978854530773507)
              ·
                refine ⟨16447145332468281796160261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10964763554978854530773507 16447145332468281796160261)
                ·
                  refine ⟨3083839749837802836780049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16447145332468281796160261 3083839749837802836780049)
                  ·
                    refine ⟨2312879812378352127585037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3083839749837802836780049 2312879812378352127585037)
                    ·
                      refine ⟨867329929641882047844389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2312879812378352127585037 867329929641882047844389)
                      ·
                        rfl

theorem cell23_1689119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 3, 1, 4, 2, 3].length) (baseStart_1689119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689119 prefixEnd_1689119 := by exact prefixLift 1689119
  have htrace : WordTrace (prefixWord ++ tailWord_1689119) baseStart_1689119 baseEnd_1689119 := by
    simpa [prefixWord, tailWord_1689119, baseEnd_1689119] using wordTrace_append hprefix tailTrace_1689119
  have hstable : (prefixWord ++ tailWord_1689119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689119).length < 2 ^ (prefixWord ++ tailWord_1689119).sum := by decide
  have hdescent : baseEnd_1689119 < baseStart_1689119 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689139 : List Nat := [1, 1, 1, 2, 4, 4, 1, 3, 6]
def baseStart_1689139 : Nat := 118140960795 + 1689139 * 2 ^ 59
def prefixEnd_1689139 : Nat := 4983230072969 + 3 ^ 40 * 1689139 * 2
def baseEnd_1689139 : Nat := 96371133250552441066033

theorem tailTrace_1689139 : CollatzResearch.WordTrace tailWord_1689139 prefixEnd_1689139 96371133250552441066033 := by
  unfold tailWord_1689139
  simp only [CollatzResearch.WordTrace]
  refine ⟨61607960627545359819086471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41071973751696906546057647 61607960627545359819086471)
  ·
    refine ⟨92411940941318039728629707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61607960627545359819086471 92411940941318039728629707)
    ·
      refine ⟨138617911411977059592944561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92411940941318039728629707 138617911411977059592944561)
      ·
        refine ⟨103963433558982794694708421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138617911411977059592944561 103963433558982794694708421)
        ·
          refine ⟨19493143792309274005257829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103963433558982794694708421 19493143792309274005257829)
          ·
            refine ⟨3654964461057988875985843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19493143792309274005257829 3654964461057988875985843)
            ·
              refine ⟨5482446691586983313978765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3654964461057988875985843 5482446691586983313978765)
              ·
                refine ⟨2055917509345118742742037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5482446691586983313978765 2055917509345118742742037)
                ·
                  refine ⟨96371133250552441066033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2055917509345118742742037 96371133250552441066033)
                  ·
                    rfl

theorem cell23_1689139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 1, 3, 6].length) (baseStart_1689139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689139 prefixEnd_1689139 := by exact prefixLift 1689139
  have htrace : WordTrace (prefixWord ++ tailWord_1689139) baseStart_1689139 baseEnd_1689139 := by
    simpa [prefixWord, tailWord_1689139, baseEnd_1689139] using wordTrace_append hprefix tailTrace_1689139
  have hstable : (prefixWord ++ tailWord_1689139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689139).length < 2 ^ (prefixWord ++ tailWord_1689139).sum := by decide
  have hdescent : baseEnd_1689139 < baseStart_1689139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689199 : List Nat := [1, 1, 2, 1, 3, 2, 1, 2, 6, 4]
def baseStart_1689199 : Nat := 118140960795 + 1689199 * 2 ^ 59
def prefixEnd_1689199 : Nat := 4983230072969 + 3 ^ 40 * 1689199 * 2
def baseEnd_1689199 : Nat := 289123669364747244948007

theorem tailTrace_1689199 : CollatzResearch.WordTrace tailWord_1689199 prefixEnd_1689199 289123669364747244948007 := by
  unfold tailWord_1689199
  simp only [CollatzResearch.WordTrace]
  refine ⟨61610149007327990066270651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41073432671551993377513767 61610149007327990066270651)
  ·
    refine ⟨92415223510991985099405977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61610149007327990066270651 92415223510991985099405977)
    ·
      refine ⟨69311417633243988824554483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92415223510991985099405977 69311417633243988824554483)
      ·
        refine ⟨103967126449865983236831725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69311417633243988824554483 103967126449865983236831725)
        ·
          refine ⟨38987672418699743713811897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103967126449865983236831725 38987672418699743713811897)
          ·
            refine ⟨29240754314024807785358923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38987672418699743713811897 29240754314024807785358923)
            ·
              refine ⟨43861131471037211678038385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29240754314024807785358923 43861131471037211678038385)
              ·
                refine ⟨32895848603277908758528789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43861131471037211678038385 32895848603277908758528789)
                ·
                  refine ⟨1541992903278651973056037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32895848603277908758528789 1541992903278651973056037)
                  ·
                    refine ⟨289123669364747244948007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1541992903278651973056037 289123669364747244948007)
                    ·
                      rfl

theorem cell23_1689199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 2, 6, 4].length) (baseStart_1689199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689199 prefixEnd_1689199 := by exact prefixLift 1689199
  have htrace : WordTrace (prefixWord ++ tailWord_1689199) baseStart_1689199 baseEnd_1689199 := by
    simpa [prefixWord, tailWord_1689199, baseEnd_1689199] using wordTrace_append hprefix tailTrace_1689199
  have hstable : (prefixWord ++ tailWord_1689199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689199).length < 2 ^ (prefixWord ++ tailWord_1689199).sum := by decide
  have hdescent : baseEnd_1689199 < baseStart_1689199 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689220 : List Nat := [2, 3, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1689220 : Nat := 118140960795 + 1689220 * 2 ^ 59
def prefixEnd_1689220 : Nat := 4983230072969 + 3 ^ 40 * 1689220 * 2
def baseEnd_1689220 : Nat := 289127263729328717560475

theorem tailTrace_1689220 : CollatzResearch.WordTrace tailWord_1689220 prefixEnd_1689220 289127263729328717560475 := by
  unfold tailWord_1689220
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805457470125955326392557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41073943293501273768523409 30805457470125955326392557)
  ·
    refine ⟨11552046551297233247397209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30805457470125955326392557 11552046551297233247397209)
    ·
      refine ⟨8664034913472924935547907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11552046551297233247397209 8664034913472924935547907)
      ·
        refine ⟨12996052370209387403321861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8664034913472924935547907 12996052370209387403321861)
        ·
          refine ⟨2436759819414260138122849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12996052370209387403321861 2436759819414260138122849)
          ·
            refine ⟨1827569864560695103592137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436759819414260138122849 1827569864560695103592137)
            ·
              refine ⟨1370677398420521327694103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827569864560695103592137 1370677398420521327694103)
              ·
                refine ⟨2056016097630781991541155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370677398420521327694103 2056016097630781991541155)
                ·
                  refine ⟨3084024146446172987311733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056016097630781991541155 3084024146446172987311733)
                  ·
                    refine ⟨289127263729328717560475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3084024146446172987311733 289127263729328717560475)
                    ·
                      rfl

theorem cell23_1689220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1689220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689220 prefixEnd_1689220 := by exact prefixLift 1689220
  have htrace : WordTrace (prefixWord ++ tailWord_1689220) baseStart_1689220 baseEnd_1689220 := by
    simpa [prefixWord, tailWord_1689220, baseEnd_1689220] using wordTrace_append hprefix tailTrace_1689220
  have hstable : (prefixWord ++ tailWord_1689220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689220).length < 2 ^ (prefixWord ++ tailWord_1689220).sum := by decide
  have hdescent : baseEnd_1689220 < baseStart_1689220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689223 : List Nat := [1, 1, 4, 2, 1, 3, 4, 1, 1, 1, 4]
def baseStart_1689223 : Nat := 118140960795 + 1689223 * 2 ^ 59
def prefixEnd_1689223 : Nat := 4983230072969 + 3 ^ 40 * 1689223 * 2
def baseEnd_1689223 : Nat := 867383331629949640943911

theorem tailTrace_1689223 : CollatzResearch.WordTrace tailWord_1689223 prefixEnd_1689223 867383331629949640943911 := by
  unfold tailWord_1689223
  simp only [CollatzResearch.WordTrace]
  refine ⟨61611024359241042165144323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41074016239494028110096215 61611024359241042165144323)
  ·
    refine ⟨92416536538861563247716485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61611024359241042165144323 92416536538861563247716485)
    ·
      refine ⟨17328100601036543108946841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92416536538861563247716485 17328100601036543108946841)
      ·
        refine ⟨12996075450777407331710131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17328100601036543108946841 12996075450777407331710131)
        ·
          refine ⟨19494113176166110997565197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12996075450777407331710131 19494113176166110997565197)
          ·
            refine ⟨7310292441062291624086949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19494113176166110997565197 7310292441062291624086949)
            ·
              refine ⟨1370679832699179679516303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7310292441062291624086949 1370679832699179679516303)
              ·
                refine ⟨2056019749048769519274455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1370679832699179679516303 2056019749048769519274455)
                ·
                  refine ⟨3084029623573154278911683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056019749048769519274455 3084029623573154278911683)
                  ·
                    refine ⟨4626044435359731418367525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3084029623573154278911683 4626044435359731418367525)
                    ·
                      refine ⟨867383331629949640943911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4626044435359731418367525 867383331629949640943911)
                      ·
                        rfl

theorem cell23_1689223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 4, 1, 1, 1, 4].length) (baseStart_1689223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689223 prefixEnd_1689223 := by exact prefixLift 1689223
  have htrace : WordTrace (prefixWord ++ tailWord_1689223) baseStart_1689223 baseEnd_1689223 := by
    simpa [prefixWord, tailWord_1689223, baseEnd_1689223] using wordTrace_append hprefix tailTrace_1689223
  have hstable : (prefixWord ++ tailWord_1689223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689223).length < 2 ^ (prefixWord ++ tailWord_1689223).sum := by decide
  have hdescent : baseEnd_1689223 < baseStart_1689223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689240 : List Nat := [2, 1, 2, 4, 1, 3, 2, 1, 3, 2, 2]
def baseStart_1689240 : Nat := 118140960795 + 1689240 * 2 ^ 59
def prefixEnd_1689240 : Nat := 4983230072969 + 3 ^ 40 * 1689240 * 2
def baseEnd_1689240 : Nat := 867392060801076074431333

theorem tailTrace_1689240 : CollatzResearch.WordTrace tailWord_1689240 prefixEnd_1689240 867392060801076074431333 := by
  unfold tailWord_1689240
  simp only [CollatzResearch.WordTrace]
  refine ⟨30805822200089727034256587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41074429600119636045675449 30805822200089727034256587)
  ·
    refine ⟨46208733300134590551384881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30805822200089727034256587 46208733300134590551384881)
    ·
      refine ⟨34656549975100942913538661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46208733300134590551384881 34656549975100942913538661)
      ·
        refine ⟨6498103120331426796288499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34656549975100942913538661 6498103120331426796288499)
        ·
          refine ⟨9747154680497140194432749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6498103120331426796288499 9747154680497140194432749)
          ·
            refine ⟨3655183005186427572912281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9747154680497140194432749 3655183005186427572912281)
            ·
              refine ⟨2741387253889820679684211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3655183005186427572912281 2741387253889820679684211)
              ·
                refine ⟨4112080880834731019526317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741387253889820679684211 4112080880834731019526317)
                ·
                  refine ⟨1542030330313024132322369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4112080880834731019526317 1542030330313024132322369)
                  ·
                    refine ⟨1156522747734768099241777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1542030330313024132322369 1156522747734768099241777)
                    ·
                      refine ⟨867392060801076074431333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156522747734768099241777 867392060801076074431333)
                      ·
                        rfl

theorem cell23_1689240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_1689240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689240 prefixEnd_1689240 := by exact prefixLift 1689240
  have htrace : WordTrace (prefixWord ++ tailWord_1689240) baseStart_1689240 baseEnd_1689240 := by
    simpa [prefixWord, tailWord_1689240, baseEnd_1689240] using wordTrace_append hprefix tailTrace_1689240
  have hstable : (prefixWord ++ tailWord_1689240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689240).length < 2 ^ (prefixWord ++ tailWord_1689240).sum := by decide
  have hdescent : baseEnd_1689240 < baseStart_1689240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689250 : List Nat := [3, 3, 1, 4, 1, 2, 1, 1, 1, 6]
def baseStart_1689250 : Nat := 118140960795 + 1689250 * 2 ^ 59
def prefixEnd_1689250 : Nat := 4983230072969 + 3 ^ 40 * 1689250 * 2
def baseEnd_1689250 : Nat := 289132398535873678435429

theorem tailTrace_1689250 : CollatzResearch.WordTrace tailWord_1689250 prefixEnd_1689250 289132398535873678435429 := by
  unfold tailWord_1689250
  simp only [CollatzResearch.WordTrace]
  refine ⟨15403002282535806444094301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41074672753428817184251469 15403002282535806444094301)
  ·
    refine ⟨5776125855950927416535363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15403002282535806444094301 5776125855950927416535363)
    ·
      refine ⟨8664188783926391124803045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5776125855950927416535363 8664188783926391124803045)
      ·
        refine ⟨1624535396986198335900571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8664188783926391124803045 1624535396986198335900571)
        ·
          refine ⟨2436803095479297503850857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1624535396986198335900571 2436803095479297503850857)
          ·
            refine ⟨1827602321609473127888143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2436803095479297503850857 1827602321609473127888143)
            ·
              refine ⟨2741403482414209691832215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1827602321609473127888143 2741403482414209691832215)
              ·
                refine ⟨4112105223621314537748323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741403482414209691832215 4112105223621314537748323)
                ·
                  refine ⟨6168157835431971806622485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112105223621314537748323 6168157835431971806622485)
                  ·
                    refine ⟨289132398535873678435429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6168157835431971806622485 289132398535873678435429)
                    ·
                      rfl

theorem cell23_1689250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_1689250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689250 prefixEnd_1689250 := by exact prefixLift 1689250
  have htrace : WordTrace (prefixWord ++ tailWord_1689250) baseStart_1689250 baseEnd_1689250 := by
    simpa [prefixWord, tailWord_1689250, baseEnd_1689250] using wordTrace_append hprefix tailTrace_1689250
  have hstable : (prefixWord ++ tailWord_1689250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689250).length < 2 ^ (prefixWord ++ tailWord_1689250).sum := by decide
  have hdescent : baseEnd_1689250 < baseStart_1689250 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689296 : List Nat := [2, 1, 1, 1, 1, 2, 1, 3, 5, 4, 2]
def baseStart_1689296 : Nat := 118140960795 + 1689296 * 2 ^ 59
def prefixEnd_1689296 : Nat := 4983230072969 + 3 ^ 40 * 1689296 * 2
def baseEnd_1689296 : Nat := 867420815717727855331075

theorem tailTrace_1689296 : CollatzResearch.WordTrace tailWord_1689296 prefixEnd_1689296 867420815717727855331075 := by
  unfold tailWord_1689296
  simp only [CollatzResearch.WordTrace]
  refine ⟨30806843443988287816275871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41075791258651050421701161 30806843443988287816275871)
  ·
    refine ⟨46210265165982431724413807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30806843443988287816275871 46210265165982431724413807)
    ·
      refine ⟨69315397748973647586620711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46210265165982431724413807 69315397748973647586620711)
      ·
        refine ⟨103973096623460471379931067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69315397748973647586620711 103973096623460471379931067)
        ·
          refine ⟨155959644935190707069896601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103973096623460471379931067 155959644935190707069896601)
          ·
            refine ⟨116969733701393030302422451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 155959644935190707069896601 116969733701393030302422451)
            ·
              refine ⟨175454600552089545453633677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116969733701393030302422451 175454600552089545453633677)
              ·
                refine ⟨65795475207033579545112629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 175454600552089545453633677 65795475207033579545112629)
                ·
                  refine ⟨6168325800659398082354309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65795475207033579545112629 6168325800659398082354309)
                  ·
                    refine ⟨1156561087623637140441433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6168325800659398082354309 1156561087623637140441433)
                    ·
                      refine ⟨867420815717727855331075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156561087623637140441433 867420815717727855331075)
                      ·
                        rfl

theorem cell23_1689296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 3, 5, 4, 2].length) (baseStart_1689296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689296 prefixEnd_1689296 := by exact prefixLift 1689296
  have htrace : WordTrace (prefixWord ++ tailWord_1689296) baseStart_1689296 baseEnd_1689296 := by
    simpa [prefixWord, tailWord_1689296, baseEnd_1689296] using wordTrace_append hprefix tailTrace_1689296
  have hstable : (prefixWord ++ tailWord_1689296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689296).length < 2 ^ (prefixWord ++ tailWord_1689296).sum := by decide
  have hdescent : baseEnd_1689296 < baseStart_1689296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689349 : List Nat := [1, 3, 1, 1, 2, 1, 1, 1, 5, 7]
def baseStart_1689349 : Nat := 118140960795 + 1689349 * 2 ^ 59
def prefixEnd_1689349 : Nat := 4983230072969 + 3 ^ 40 * 1689349 * 2
def baseEnd_1689349 : Nat := 289149343397472049322777

theorem tailTrace_1689349 : CollatzResearch.WordTrace tailWord_1689349 prefixEnd_1689349 289149343397472049322777 := by
  unfold tailWord_1689349
  simp only [CollatzResearch.WordTrace]
  refine ⟨61615619956784565684231101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41077079971189710456154067 61615619956784565684231101)
  ·
    refine ⟨23105857483794212131586663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61615619956784565684231101 23105857483794212131586663)
    ·
      refine ⟨34658786225691318197379995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23105857483794212131586663 34658786225691318197379995)
      ·
        refine ⟨51988179338536977296069993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34658786225691318197379995 51988179338536977296069993)
        ·
          refine ⟨38991134503902732972052495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51988179338536977296069993 38991134503902732972052495)
          ·
            refine ⟨58486701755854099458078743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38991134503902732972052495 58486701755854099458078743)
            ·
              refine ⟨87730052633781149187118115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58486701755854099458078743 87730052633781149187118115)
              ·
                refine ⟨131595078950671723780677173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87730052633781149187118115 131595078950671723780677173)
                ·
                  refine ⟨12337038651625474104438485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 131595078950671723780677173 12337038651625474104438485)
                  ·
                    refine ⟨289149343397472049322777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12337038651625474104438485 289149343397472049322777)
                    ·
                      rfl

theorem cell23_1689349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 5, 7].length) (baseStart_1689349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689349 prefixEnd_1689349 := by exact prefixLift 1689349
  have htrace : WordTrace (prefixWord ++ tailWord_1689349) baseStart_1689349 baseEnd_1689349 := by
    simpa [prefixWord, tailWord_1689349, baseEnd_1689349] using wordTrace_append hprefix tailTrace_1689349
  have hstable : (prefixWord ++ tailWord_1689349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689349).length < 2 ^ (prefixWord ++ tailWord_1689349).sum := by decide
  have hdescent : baseEnd_1689349 < baseStart_1689349 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689359 : List Nat := [1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 7]
def baseStart_1689359 : Nat := 118140960795 + 1689359 * 2 ^ 59
def prefixEnd_1689359 : Nat := 4983230072969 + 3 ^ 40 * 1689359 * 2
def baseEnd_1689359 : Nat := 867453164998961108843285

theorem tailTrace_1689359 : CollatzResearch.WordTrace tailWord_1689359 prefixEnd_1689359 867453164998961108843285 := by
  unfold tailWord_1689359
  simp only [CollatzResearch.WordTrace]
  refine ⟨61615984686748337392095131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41077323124498891594730087 61615984686748337392095131)
  ·
    refine ⟨92423977030122506088142697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61615984686748337392095131 92423977030122506088142697)
    ·
      refine ⟨69317982772591879566107023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92423977030122506088142697 69317982772591879566107023)
      ·
        refine ⟨103976974158887819349160535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69317982772591879566107023 103976974158887819349160535)
        ·
          refine ⟨155965461238331729023740803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103976974158887819349160535 155965461238331729023740803)
          ·
            refine ⟨233948191857497593535611205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 155965461238331729023740803 233948191857497593535611205)
            ·
              refine ⟨43865285973280798787927101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 233948191857497593535611205 43865285973280798787927101)
              ·
                refine ⟨16449482239980299545472663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43865285973280798787927101 16449482239980299545472663)
                ·
                  refine ⟨24674223359970449318208995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16449482239980299545472663 24674223359970449318208995)
                  ·
                    refine ⟨37011335039955673977313493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24674223359970449318208995 37011335039955673977313493)
                    ·
                      refine ⟨867453164998961108843285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 37011335039955673977313493 867453164998961108843285)
                      ·
                        rfl

theorem cell23_1689359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 3, 1, 1, 7].length) (baseStart_1689359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689359 prefixEnd_1689359 := by exact prefixLift 1689359
  have htrace : WordTrace (prefixWord ++ tailWord_1689359) baseStart_1689359 baseEnd_1689359 := by
    simpa [prefixWord, tailWord_1689359, baseEnd_1689359] using wordTrace_append hprefix tailTrace_1689359
  have hstable : (prefixWord ++ tailWord_1689359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689359).length < 2 ^ (prefixWord ++ tailWord_1689359).sum := by decide
  have hdescent : baseEnd_1689359 < baseStart_1689359 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689413 : List Nat := [1, 3, 1, 1, 1, 2, 6, 1, 3, 4]
def baseStart_1689413 : Nat := 118140960795 + 1689413 * 2 ^ 59
def prefixEnd_1689413 : Nat := 4983230072969 + 3 ^ 40 * 1689413 * 2
def baseEnd_1689413 : Nat := 289160297651434632522679

theorem tailTrace_1689413 : CollatzResearch.WordTrace tailWord_1689413 prefixEnd_1689413 289160297651434632522679 := by
  unfold tailWord_1689413
  simp only [CollatzResearch.WordTrace]
  refine ⟨61617954228552704614560893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41078636152368469743040595 61617954228552704614560893)
  ·
    refine ⟨23106732835707264230460335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61617954228552704614560893 23106732835707264230460335)
    ·
      refine ⟨34660099253560896345690503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23106732835707264230460335 34660099253560896345690503)
      ·
        refine ⟨51990148880341344518535755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34660099253560896345690503 51990148880341344518535755)
        ·
          refine ⟨77985223320512016777803633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51990148880341344518535755 77985223320512016777803633)
          ·
            refine ⟨58488917490384012583352725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77985223320512016777803633 58488917490384012583352725)
            ·
              refine ⟨2741668007361750589844659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58488917490384012583352725 2741668007361750589844659)
              ·
                refine ⟨4112502011042625884766989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2741668007361750589844659 4112502011042625884766989)
                ·
                  refine ⟨1542188254140984706787621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4112502011042625884766989 1542188254140984706787621)
                  ·
                    refine ⟨289160297651434632522679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542188254140984706787621 289160297651434632522679)
                    ·
                      rfl

theorem cell23_1689413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 4].length) (baseStart_1689413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689413 prefixEnd_1689413 := by exact prefixLift 1689413
  have htrace : WordTrace (prefixWord ++ tailWord_1689413) baseStart_1689413 baseEnd_1689413 := by
    simpa [prefixWord, tailWord_1689413, baseEnd_1689413] using wordTrace_append hprefix tailTrace_1689413
  have hstable : (prefixWord ++ tailWord_1689413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689413).length < 2 ^ (prefixWord ++ tailWord_1689413).sum := by decide
  have hdescent : baseEnd_1689413 < baseStart_1689413 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689456 : List Nat := [2, 1, 1, 1, 4, 1, 1, 2, 5, 5]
def baseStart_1689456 : Nat := 118140960795 + 1689456 * 2 ^ 59
def prefixEnd_1689456 : Nat := 4983230072969 + 3 ^ 40 * 1689456 * 2
def baseEnd_1689456 : Nat := 289167657540815743110113

theorem tailTrace_1689456 : CollatzResearch.WordTrace tailWord_1689456 prefixEnd_1689456 289167657540815743110113 := by
  unfold tailWord_1689456
  simp only [CollatzResearch.WordTrace]
  refine ⟨30809761283698461479188111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41079681711597948638917481 30809761283698461479188111)
  ·
    refine ⟨46214641925547692218782167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30809761283698461479188111 46214641925547692218782167)
    ·
      refine ⟨69321962888321538328173251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46214641925547692218782167 69321962888321538328173251)
      ·
        refine ⟨103982944332482307492259877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69321962888321538328173251 103982944332482307492259877)
        ·
          refine ⟨19496802062340432654798727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103982944332482307492259877 19496802062340432654798727)
          ·
            refine ⟨29245203093510648982198091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19496802062340432654798727 29245203093510648982198091)
            ·
              refine ⟨43867804640265973473297137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29245203093510648982198091 43867804640265973473297137)
              ·
                refine ⟨32900853480199480104972853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43867804640265973473297137 32900853480199480104972853)
                ·
                  refine ⟨3084455013768701259841205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32900853480199480104972853 3084455013768701259841205)
                  ·
                    refine ⟨289167657540815743110113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3084455013768701259841205 289167657540815743110113)
                    ·
                      rfl

theorem cell23_1689456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 2, 5, 5].length) (baseStart_1689456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689456 prefixEnd_1689456 := by exact prefixLift 1689456
  have htrace : WordTrace (prefixWord ++ tailWord_1689456) baseStart_1689456 baseEnd_1689456 := by
    simpa [prefixWord, tailWord_1689456, baseEnd_1689456] using wordTrace_append hprefix tailTrace_1689456
  have hstable : (prefixWord ++ tailWord_1689456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689456).length < 2 ^ (prefixWord ++ tailWord_1689456).sum := by decide
  have hdescent : baseEnd_1689456 < baseStart_1689456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689490 : List Nat := [3, 2, 3, 2, 1, 2, 1, 1, 3, 5]
def baseStart_1689490 : Nat := 118140960795 + 1689490 * 2 ^ 59
def prefixEnd_1689490 : Nat := 4983230072969 + 3 ^ 40 * 1689490 * 2
def baseEnd_1689490 : Nat := 289173476988233365435061

theorem tailTrace_1689490 : CollatzResearch.WordTrace tailWord_1689490 prefixEnd_1689490 289173476988233365435061 := by
  unfold tailWord_1689490
  simp only [CollatzResearch.WordTrace]
  refine ⟨15405190662318436691278481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41080508432849164510075949 15405190662318436691278481)
  ·
    refine ⟨11553892996738827518458861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15405190662318436691278481 11553892996738827518458861)
    ·
      refine ⟨4332709873777060319422073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11553892996738827518458861 4332709873777060319422073)
      ·
        refine ⟨3249532405332795239566555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4332709873777060319422073 3249532405332795239566555)
        ·
          refine ⟨4874298607999192859349833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3249532405332795239566555 4874298607999192859349833)
          ·
            refine ⟨3655723955999394644512375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4874298607999192859349833 3655723955999394644512375)
            ·
              refine ⟨5483585933999091966768563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3655723955999394644512375 5483585933999091966768563)
              ·
                refine ⟨8225378900998637950152845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483585933999091966768563 8225378900998637950152845)
                ·
                  refine ⟨3084517087874489231307317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8225378900998637950152845 3084517087874489231307317)
                  ·
                    refine ⟨289173476988233365435061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3084517087874489231307317 289173476988233365435061)
                    ·
                      rfl

theorem cell23_1689490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_1689490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689490 prefixEnd_1689490 := by exact prefixLift 1689490
  have htrace : WordTrace (prefixWord ++ tailWord_1689490) baseStart_1689490 baseEnd_1689490 := by
    simpa [prefixWord, tailWord_1689490, baseEnd_1689490] using wordTrace_append hprefix tailTrace_1689490
  have hstable : (prefixWord ++ tailWord_1689490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689490).length < 2 ^ (prefixWord ++ tailWord_1689490).sum := by decide
  have hdescent : baseEnd_1689490 < baseStart_1689490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689493 : List Nat := [1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 4]
def baseStart_1689493 : Nat := 118140960795 + 1689493 * 2 ^ 59
def prefixEnd_1689493 : Nat := 4983230072969 + 3 ^ 40 * 1689493 * 2
def baseEnd_1689493 : Nat := 867521971406663584567669

theorem tailTrace_1689493 : CollatzResearch.WordTrace tailWord_1689493 prefixEnd_1689493 867521971406663584567669 := by
  unfold tailWord_1689493
  simp only [CollatzResearch.WordTrace]
  refine ⟨61620872068262878277473133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41080581378841918851648755 61620872068262878277473133)
  ·
    refine ⟨23107827025598579354052425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61620872068262878277473133 23107827025598579354052425)
    ·
      refine ⟨17330870269198934515539319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23107827025598579354052425 17330870269198934515539319)
      ·
        refine ⟨25996305403798401773308979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17330870269198934515539319 25996305403798401773308979)
        ·
          refine ⟨38994458105697602659963469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25996305403798401773308979 38994458105697602659963469)
          ·
            refine ⟨14622921789636600997486301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38994458105697602659963469 14622921789636600997486301)
            ·
              refine ⟨5483595671113725374057363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14622921789636600997486301 5483595671113725374057363)
              ·
                refine ⟨8225393506670588061086045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483595671113725374057363 8225393506670588061086045)
                ·
                  refine ⟨3084522565001470522907267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8225393506670588061086045 3084522565001470522907267)
                  ·
                    refine ⟨4626783847502205784360901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3084522565001470522907267 4626783847502205784360901)
                    ·
                      refine ⟨867521971406663584567669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4626783847502205784360901 867521971406663584567669)
                      ·
                        rfl

theorem cell23_1689493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 3, 1, 3, 1, 4].length) (baseStart_1689493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689493 prefixEnd_1689493 := by exact prefixLift 1689493
  have htrace : WordTrace (prefixWord ++ tailWord_1689493) baseStart_1689493 baseEnd_1689493 := by
    simpa [prefixWord, tailWord_1689493, baseEnd_1689493] using wordTrace_append hprefix tailTrace_1689493
  have hstable : (prefixWord ++ tailWord_1689493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689493).length < 2 ^ (prefixWord ++ tailWord_1689493).sum := by decide
  have hdescent : baseEnd_1689493 < baseStart_1689493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689521 : List Nat := [1, 2, 2, 4, 2, 3, 2, 2, 1, 1, 3]
def baseStart_1689521 : Nat := 118140960795 + 1689521 * 2 ^ 59
def prefixEnd_1689521 : Nat := 4983230072969 + 3 ^ 40 * 1689521 * 2
def baseEnd_1689521 : Nat := 867536348864989475017541

theorem tailTrace_1689521 : CollatzResearch.WordTrace tailWord_1689521 prefixEnd_1689521 867536348864989475017541 := by
  unfold tailWord_1689521
  simp only [CollatzResearch.WordTrace]
  refine ⟨61621893312161439059492417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41081262208107626039661611 61621893312161439059492417)
  ·
    refine ⟨46216419984121079294619313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61621893312161439059492417 46216419984121079294619313)
    ·
      refine ⟨34662314988090809470964485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46216419984121079294619313 34662314988090809470964485)
      ·
        refine ⟨6499184060267026775805841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34662314988090809470964485 6499184060267026775805841)
        ·
          refine ⟨4874388045200270081854381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6499184060267026775805841 4874388045200270081854381)
          ·
            refine ⟨1827895516950101280695393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4874388045200270081854381 1827895516950101280695393)
            ·
              refine ⟨1370921637712575960521545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1827895516950101280695393 1370921637712575960521545)
              ·
                refine ⟨1028191228284431970391159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1370921637712575960521545 1028191228284431970391159)
                ·
                  refine ⟨1542286842426647955586739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028191228284431970391159 1542286842426647955586739)
                  ·
                    refine ⟨2313430263639971933380109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1542286842426647955586739 2313430263639971933380109)
                    ·
                      refine ⟨867536348864989475017541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2313430263639971933380109 867536348864989475017541)
                      ·
                        rfl

theorem cell23_1689521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_1689521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689521 prefixEnd_1689521 := by exact prefixLift 1689521
  have htrace : WordTrace (prefixWord ++ tailWord_1689521) baseStart_1689521 baseEnd_1689521 := by
    simpa [prefixWord, tailWord_1689521, baseEnd_1689521] using wordTrace_append hprefix tailTrace_1689521
  have hstable : (prefixWord ++ tailWord_1689521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689521).length < 2 ^ (prefixWord ++ tailWord_1689521).sum := by decide
  have hdescent : baseEnd_1689521 < baseStart_1689521 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689533 : List Nat := [1, 4, 1, 2, 3, 1, 3, 8]
def baseStart_1689533 : Nat := 118140960795 + 1689533 * 2 ^ 59
def prefixEnd_1689533 : Nat := 4983230072969 + 3 ^ 40 * 1689533 * 2
def baseEnd_1689533 : Nat := 32131204097512719558055

theorem tailTrace_1689533 : CollatzResearch.WordTrace tailWord_1689533 prefixEnd_1689533 32131204097512719558055 := by
  unfold tailWord_1689533
  simp only [CollatzResearch.WordTrace]
  refine ⟨61622330988117965108929253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41081553992078643405952835 61622330988117965108929253)
  ·
    refine ⟨11554187060272118457924235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61622330988117965108929253 11554187060272118457924235)
    ·
      refine ⟨17331280590408177686886353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11554187060272118457924235 17331280590408177686886353)
      ·
        refine ⟨12998460442806133265164765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17331280590408177686886353 12998460442806133265164765)
        ·
          refine ⟨4874422666052299974436787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12998460442806133265164765 4874422666052299974436787)
          ·
            refine ⟨7311633999078449961655181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4874422666052299974436787 7311633999078449961655181)
            ·
              refine ⟨2741862749654418735620693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7311633999078449961655181 2741862749654418735620693)
              ·
                refine ⟨32131204097512719558055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2741862749654418735620693 32131204097512719558055)
                ·
                  rfl

theorem cell23_1689533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 8].length) (baseStart_1689533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689533 prefixEnd_1689533 := by exact prefixLift 1689533
  have htrace : WordTrace (prefixWord ++ tailWord_1689533) baseStart_1689533 baseEnd_1689533 := by
    simpa [prefixWord, tailWord_1689533, baseEnd_1689533] using wordTrace_append hprefix tailTrace_1689533
  have hstable : (prefixWord ++ tailWord_1689533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689533).length < 2 ^ (prefixWord ++ tailWord_1689533).sum := by decide
  have hdescent : baseEnd_1689533 < baseStart_1689533 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689560 : List Nat := [2, 1, 2, 2, 2, 2, 2, 2, 4, 1, 3]
def baseStart_1689560 : Nat := 118140960795 + 1689560 * 2 ^ 59
def prefixEnd_1689560 : Nat := 4983230072969 + 3 ^ 40 * 1689560 * 2
def baseEnd_1689560 : Nat := 867556374610514822429861

theorem tailTrace_1689560 : CollatzResearch.WordTrace tailWord_1689560 prefixEnd_1689560 867556374610514822429861 := by
  unfold tailWord_1689560
  simp only [CollatzResearch.WordTrace]
  refine ⟨30811657879510074360081067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41082210506013432480108089 30811657879510074360081067)
  ·
    refine ⟨46217486819265111540121601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30811657879510074360081067 46217486819265111540121601)
    ·
      refine ⟨34663115114448833655091201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46217486819265111540121601 34663115114448833655091201)
      ·
        refine ⟨25997336335836625241318401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34663115114448833655091201 25997336335836625241318401)
        ·
          refine ⟨19498002251877468930988801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25997336335836625241318401 19498002251877468930988801)
          ·
            refine ⟨14623501688908101698241601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19498002251877468930988801 14623501688908101698241601)
            ·
              refine ⟨10967626266681076273681201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14623501688908101698241601 10967626266681076273681201)
              ·
                refine ⟨8225719700010807205260901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10967626266681076273681201 8225719700010807205260901)
                ·
                  refine ⟨1542322443752026350986419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8225719700010807205260901 1542322443752026350986419)
                  ·
                    refine ⟨2313483665628039526479629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1542322443752026350986419 2313483665628039526479629)
                    ·
                      refine ⟨867556374610514822429861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2313483665628039526479629 867556374610514822429861)
                      ·
                        rfl

theorem cell23_1689560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 2, 2, 4, 1, 3].length) (baseStart_1689560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689560 prefixEnd_1689560 := by exact prefixLift 1689560
  have htrace : WordTrace (prefixWord ++ tailWord_1689560) baseStart_1689560 baseEnd_1689560 := by
    simpa [prefixWord, tailWord_1689560, baseEnd_1689560] using wordTrace_append hprefix tailTrace_1689560
  have hstable : (prefixWord ++ tailWord_1689560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689560).length < 2 ^ (prefixWord ++ tailWord_1689560).sum := by decide
  have hdescent : baseEnd_1689560 < baseStart_1689560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689561 : List Nat := [1, 2, 1, 2, 6, 1, 2, 3, 1, 2, 2]
def baseStart_1689561 : Nat := 118140960795 + 1689561 * 2 ^ 59
def prefixEnd_1689561 : Nat := 4983230072969 + 3 ^ 40 * 1689561 * 2
def baseEnd_1689561 : Nat := 867556888091169318517357

theorem tailTrace_1689561 : CollatzResearch.WordTrace tailWord_1689561 prefixEnd_1689561 867556888091169318517357 := by
  unfold tailWord_1689561
  simp only [CollatzResearch.WordTrace]
  refine ⟨61623352232016525890948537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41082234821344350593965691 61623352232016525890948537)
  ·
    refine ⟨46217514174012394418211403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61623352232016525890948537 46217514174012394418211403)
    ·
      refine ⟨69326271261018591627317105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46217514174012394418211403 69326271261018591627317105)
      ·
        refine ⟨51994703445763943720487829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69326271261018591627317105 51994703445763943720487829)
        ·
          refine ⟨2437251724020184861897867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51994703445763943720487829 2437251724020184861897867)
          ·
            refine ⟨3655877586030277292846801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437251724020184861897867 3655877586030277292846801)
            ·
              refine ⟨2741908189522707969635101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3655877586030277292846801 2741908189522707969635101)
              ·
                refine ⟨1028215571071015488613163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2741908189522707969635101 1028215571071015488613163)
                ·
                  refine ⟨1542323356606523232919745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028215571071015488613163 1542323356606523232919745)
                  ·
                    refine ⟨1156742517454892424689809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1542323356606523232919745 1156742517454892424689809)
                    ·
                      refine ⟨867556888091169318517357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156742517454892424689809 867556888091169318517357)
                      ·
                        rfl

theorem cell23_1689561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 2, 3, 1, 2, 2].length) (baseStart_1689561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689561 prefixEnd_1689561 := by exact prefixLift 1689561
  have htrace : WordTrace (prefixWord ++ tailWord_1689561) baseStart_1689561 baseEnd_1689561 := by
    simpa [prefixWord, tailWord_1689561, baseEnd_1689561] using wordTrace_append hprefix tailTrace_1689561
  have hstable : (prefixWord ++ tailWord_1689561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689561).length < 2 ^ (prefixWord ++ tailWord_1689561).sum := by decide
  have hdescent : baseEnd_1689561 < baseStart_1689561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689593 : List Nat := [1, 2, 1, 3, 1, 4, 2, 1, 2, 6]
def baseStart_1689593 : Nat := 118140960795 + 1689593 * 2 ^ 59
def prefixEnd_1689593 : Nat := 4983230072969 + 3 ^ 40 * 1689593 * 2
def baseEnd_1689593 : Nat := 289191106490704397772403

theorem tailTrace_1689593 : CollatzResearch.WordTrace tailWord_1689593 prefixEnd_1689593 289191106490704397772403 := by
  unfold tailWord_1689593
  simp only [CollatzResearch.WordTrace]
  refine ⟨61624519367900595356113433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41083012911933730237408955 61624519367900595356113433)
  ·
    refine ⟨46218389525925446517085075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61624519367900595356113433 46218389525925446517085075)
    ·
      refine ⟨69327584288888169775627613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46218389525925446517085075 69327584288888169775627613)
      ·
        refine ⟨25997844108333063665860355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69327584288888169775627613 25997844108333063665860355)
        ·
          refine ⟨38996766162499595498790533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25997844108333063665860355 38996766162499595498790533)
          ·
            refine ⟨7311893655468674156023225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38996766162499595498790533 7311893655468674156023225)
            ·
              refine ⟨5483920241601505617017419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7311893655468674156023225 5483920241601505617017419)
              ·
                refine ⟨8225880362402258425526129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5483920241601505617017419 8225880362402258425526129)
                ·
                  refine ⟨6169410271801693819144597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8225880362402258425526129 6169410271801693819144597)
                  ·
                    refine ⟨289191106490704397772403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6169410271801693819144597 289191106490704397772403)
                    ·
                      rfl

theorem cell23_1689593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 6].length) (baseStart_1689593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689593 prefixEnd_1689593 := by exact prefixLift 1689593
  have htrace : WordTrace (prefixWord ++ tailWord_1689593) baseStart_1689593 baseEnd_1689593 := by
    simpa [prefixWord, tailWord_1689593, baseEnd_1689593] using wordTrace_append hprefix tailTrace_1689593
  have hstable : (prefixWord ++ tailWord_1689593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689593).length < 2 ^ (prefixWord ++ tailWord_1689593).sum := by decide
  have hdescent : baseEnd_1689593 < baseStart_1689593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689600 : List Nat := [2, 1, 1, 2, 1, 1, 1, 7, 1, 4, 2]
def baseStart_1689600 : Nat := 118140960795 + 1689600 * 2 ^ 59
def prefixEnd_1689600 : Nat := 4983230072969 + 3 ^ 40 * 1689600 * 2
def baseEnd_1689600 : Nat := 867576913836694665929677

theorem tailTrace_1689600 : CollatzResearch.WordTrace tailWord_1689600 prefixEnd_1689600 867576913836694665929677 := by
  unfold tailWord_1689600
  simp only [CollatzResearch.WordTrace]
  refine ⟨30812387339437617775809127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41083183119250157034412169 30812387339437617775809127)
  ·
    refine ⟨46218581009156426663713691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30812387339437617775809127 46218581009156426663713691)
    ·
      refine ⟨69327871513734639995570537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46218581009156426663713691 69327871513734639995570537)
      ·
        refine ⟨51995903635300979996677903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69327871513734639995570537 51995903635300979996677903)
        ·
          refine ⟨77993855452951469995016855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51995903635300979996677903 77993855452951469995016855)
          ·
            refine ⟨116990783179427204992525283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77993855452951469995016855 116990783179427204992525283)
            ·
              refine ⟨175486174769140807488787925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116990783179427204992525283 175486174769140807488787925)
              ·
                refine ⟨4112957221151737675518467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 175486174769140807488787925 4112957221151737675518467)
                ·
                  refine ⟨6169435831727606513277701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4112957221151737675518467 6169435831727606513277701)
                  ·
                    refine ⟨1156769218448926221239569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6169435831727606513277701 1156769218448926221239569)
                    ·
                      refine ⟨867576913836694665929677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156769218448926221239569 867576913836694665929677)
                      ·
                        rfl

theorem cell23_1689600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 7, 1, 4, 2].length) (baseStart_1689600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689600 prefixEnd_1689600 := by exact prefixLift 1689600
  have htrace : WordTrace (prefixWord ++ tailWord_1689600) baseStart_1689600 baseEnd_1689600 := by
    simpa [prefixWord, tailWord_1689600, baseEnd_1689600] using wordTrace_append hprefix tailTrace_1689600
  have hstable : (prefixWord ++ tailWord_1689600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689600).length < 2 ^ (prefixWord ++ tailWord_1689600).sum := by decide
  have hdescent : baseEnd_1689600 < baseStart_1689600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689603 : List Nat := [1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 3]
def baseStart_1689603 : Nat := 118140960795 + 1689603 * 2 ^ 59
def prefixEnd_1689603 : Nat := 4983230072969 + 3 ^ 40 * 1689603 * 2
def baseEnd_1689603 : Nat := 867578454278658154192163

theorem tailTrace_1689603 : CollatzResearch.WordTrace tailWord_1689603 prefixEnd_1689603 867578454278658154192163 := by
  unfold tailWord_1689603
  simp only [CollatzResearch.WordTrace]
  refine ⟨61624884097864367063977463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41083256065242911375984975 61624884097864367063977463)
  ·
    refine ⟨92437326146796550595966195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61624884097864367063977463 92437326146796550595966195)
    ·
      refine ⟨138655989220194825893949293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92437326146796550595966195 138655989220194825893949293)
      ·
        refine ⟨51995995957573059710230985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138655989220194825893949293 51995995957573059710230985)
        ·
          refine ⟨38996996968179794782673239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51995995957573059710230985 38996996968179794782673239)
          ·
            refine ⟨58495495452269692174009859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38996996968179794782673239 58495495452269692174009859)
            ·
              refine ⟨87743243178404538261014789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58495495452269692174009859 87743243178404538261014789)
              ·
                refine ⟨16451858095950850923940273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87743243178404538261014789 16451858095950850923940273)
                ·
                  refine ⟨12338893571963138192955205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16451858095950850923940273 12338893571963138192955205)
                  ·
                    refine ⟨2313542544743088411179101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12338893571963138192955205 2313542544743088411179101)
                    ·
                      refine ⟨867578454278658154192163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2313542544743088411179101 867578454278658154192163)
                      ·
                        rfl

theorem cell23_1689603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 4, 2, 4, 3].length) (baseStart_1689603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689603 prefixEnd_1689603 := by exact prefixLift 1689603
  have htrace : WordTrace (prefixWord ++ tailWord_1689603) baseStart_1689603 baseEnd_1689603 := by
    simpa [prefixWord, tailWord_1689603, baseEnd_1689603] using wordTrace_append hprefix tailTrace_1689603
  have hstable : (prefixWord ++ tailWord_1689603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689603).length < 2 ^ (prefixWord ++ tailWord_1689603).sum := by decide
  have hdescent : baseEnd_1689603 < baseStart_1689603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689634 : List Nat := [3, 3, 1, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_1689634 : Nat := 118140960795 + 1689634 * 2 ^ 59
def prefixEnd_1689634 : Nat := 4983230072969 + 3 ^ 40 * 1689634 * 2
def baseEnd_1689634 : Nat := 867594372178947532904521

theorem tailTrace_1689634 : CollatzResearch.WordTrace tailWord_1689634 prefixEnd_1689634 867594372178947532904521 := by
  unfold tailWord_1689634
  simp only [CollatzResearch.WordTrace]
  refine ⟨15406503690188014839588989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41084009840501372905570637 15406503690188014839588989)
  ·
    refine ⟨5777438883820505564845871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15406503690188014839588989 5777438883820505564845871)
    ·
      refine ⟨8666158325730758347268807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5777438883820505564845871 8666158325730758347268807)
      ·
        refine ⟨12999237488596137520903211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666158325730758347268807 12999237488596137520903211)
        ·
          refine ⟨19498856232894206281354817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12999237488596137520903211 19498856232894206281354817)
          ·
            refine ⟨14624142174670654711016113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19498856232894206281354817 14624142174670654711016113)
            ·
              refine ⟨10968106631002991033262085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14624142174670654711016113 10968106631002991033262085)
              ·
                refine ⟨2056519993313060818736641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10968106631002991033262085 2056519993313060818736641)
                ·
                  refine ⟨1542389994984795614052481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2056519993313060818736641 1542389994984795614052481)
                  ·
                    refine ⟨1156792496238596710539361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1542389994984795614052481 1156792496238596710539361)
                    ·
                      refine ⟨867594372178947532904521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156792496238596710539361 867594372178947532904521)
                      ·
                        rfl

theorem cell23_1689634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_1689634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689634 prefixEnd_1689634 := by exact prefixLift 1689634
  have htrace : WordTrace (prefixWord ++ tailWord_1689634) baseStart_1689634 baseEnd_1689634 := by
    simpa [prefixWord, tailWord_1689634, baseEnd_1689634] using wordTrace_append hprefix tailTrace_1689634
  have hstable : (prefixWord ++ tailWord_1689634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689634).length < 2 ^ (prefixWord ++ tailWord_1689634).sum := by decide
  have hdescent : baseEnd_1689634 < baseStart_1689634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689653 : List Nat := [1, 3, 3, 1, 1, 1, 2, 1, 3, 7]
def baseStart_1689653 : Nat := 118140960795 + 1689653 * 2 ^ 59
def prefixEnd_1689653 : Nat := 4983230072969 + 3 ^ 40 * 1689653 * 2
def baseEnd_1689653 : Nat := 289201376103794319522311

theorem tailTrace_1689653 : CollatzResearch.WordTrace tailWord_1689653 prefixEnd_1689653 289201376103794319522311 := by
  unfold tailWord_1689653
  simp only [CollatzResearch.WordTrace]
  refine ⟨61626707747683225603297613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41084471831788817068865075 61626707747683225603297613)
  ·
    refine ⟨23110015405381209601236605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61626707747683225603297613 23110015405381209601236605)
    ·
      refine ⟨8666255777017953600463727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23110015405381209601236605 8666255777017953600463727)
      ·
        refine ⟨12999383665526930400695591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8666255777017953600463727 12999383665526930400695591)
        ·
          refine ⟨19499075498290395601043387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12999383665526930400695591 19499075498290395601043387)
          ·
            refine ⟨29248613247435593401565081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19499075498290395601043387 29248613247435593401565081)
            ·
              refine ⟨21936459935576695051173811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29248613247435593401565081 21936459935576695051173811)
              ·
                refine ⟨32904689903365042576760717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21936459935576695051173811 32904689903365042576760717)
                ·
                  refine ⟨12339258713761890966285269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32904689903365042576760717 12339258713761890966285269)
                  ·
                    refine ⟨289201376103794319522311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12339258713761890966285269 289201376103794319522311)
                    ·
                      rfl

theorem cell23_1689653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 7].length) (baseStart_1689653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689653 prefixEnd_1689653 := by exact prefixLift 1689653
  have htrace : WordTrace (prefixWord ++ tailWord_1689653) baseStart_1689653 baseEnd_1689653 := by
    simpa [prefixWord, tailWord_1689653, baseEnd_1689653] using wordTrace_append hprefix tailTrace_1689653
  have hstable : (prefixWord ++ tailWord_1689653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689653).length < 2 ^ (prefixWord ++ tailWord_1689653).sum := by decide
  have hdescent : baseEnd_1689653 < baseStart_1689653 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689690 : List Nat := [3, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4]
def baseStart_1689690 : Nat := 118140960795 + 1689690 * 2 ^ 59
def prefixEnd_1689690 : Nat := 4983230072969 + 3 ^ 40 * 1689690 * 2
def baseEnd_1689690 : Nat := 867623127095599313804263

theorem tailTrace_1689690 : CollatzResearch.WordTrace tailWord_1689690 prefixEnd_1689690 867623127095599313804263 := by
  unfold tailWord_1689690
  simp only [CollatzResearch.WordTrace]
  refine ⟨15407014312137295230598631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41085371499032787281596349 15407014312137295230598631)
  ·
    refine ⟨23110521468205942845897947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15407014312137295230598631 23110521468205942845897947)
    ·
      refine ⟨34665782202308914268846921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23110521468205942845897947 34665782202308914268846921)
      ·
        refine ⟨25999336651731685701635191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34665782202308914268846921 25999336651731685701635191)
        ·
          refine ⟨38999004977597528552452787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25999336651731685701635191 38999004977597528552452787)
          ·
            refine ⟨58498507466396292828679181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38999004977597528552452787 58498507466396292828679181)
            ·
              refine ⟨21936940299898609810754693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58498507466396292828679181 21936940299898609810754693)
              ·
                refine ⟨4113176306230989339516505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21936940299898609810754693 4113176306230989339516505)
                ·
                  refine ⟨3084882229673242004637379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4113176306230989339516505 3084882229673242004637379)
                  ·
                    refine ⟨4627323344509863006956069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3084882229673242004637379 4627323344509863006956069)
                    ·
                      refine ⟨867623127095599313804263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4627323344509863006956069 867623127095599313804263)
                      ·
                        rfl

theorem cell23_1689690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_1689690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689690 prefixEnd_1689690 := by exact prefixLift 1689690
  have htrace : WordTrace (prefixWord ++ tailWord_1689690) baseStart_1689690 baseEnd_1689690 := by
    simpa [prefixWord, tailWord_1689690, baseEnd_1689690] using wordTrace_append hprefix tailTrace_1689690
  have hstable : (prefixWord ++ tailWord_1689690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689690).length < 2 ^ (prefixWord ++ tailWord_1689690).sum := by decide
  have hdescent : baseEnd_1689690 < baseStart_1689690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689764 : List Nat := [2, 3, 1, 2, 4, 1, 3, 1, 6]
def baseStart_1689764 : Nat := 118140960795 + 1689764 * 2 ^ 59
def prefixEnd_1689764 : Nat := 4983230072969 + 3 ^ 40 * 1689764 * 2
def baseEnd_1689764 : Nat := 96406791629336891586547

theorem tailTrace_1689764 : CollatzResearch.WordTrace tailWord_1689764 prefixEnd_1689764 96406791629336891586547 := by
  unfold tailWord_1689764
  simp only [CollatzResearch.WordTrace]
  refine ⟨30815378125140545780294173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41087170833520727707058897 30815378125140545780294173)
  ·
    refine ⟨11555766796927704667610315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30815378125140545780294173 11555766796927704667610315)
    ·
      refine ⟨17333650195391557001415473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11555766796927704667610315 17333650195391557001415473)
      ·
        refine ⟨13000237646543667751061605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17333650195391557001415473 13000237646543667751061605)
        ·
          refine ⟨2437544558726937703324051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13000237646543667751061605 2437544558726937703324051)
          ·
            refine ⟨3656316838090406554986077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2437544558726937703324051 3656316838090406554986077)
            ·
              refine ⟨1371118814283902458119779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3656316838090406554986077 1371118814283902458119779)
              ·
                refine ⟨2056678221425853687179669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371118814283902458119779 2056678221425853687179669)
                ·
                  refine ⟨96406791629336891586547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2056678221425853687179669 96406791629336891586547)
                  ·
                    rfl

theorem cell23_1689764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 6].length) (baseStart_1689764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689764 prefixEnd_1689764 := by exact prefixLift 1689764
  have htrace : WordTrace (prefixWord ++ tailWord_1689764) baseStart_1689764 baseEnd_1689764 := by
    simpa [prefixWord, tailWord_1689764, baseEnd_1689764] using wordTrace_append hprefix tailTrace_1689764
  have hstable : (prefixWord ++ tailWord_1689764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689764).length < 2 ^ (prefixWord ++ tailWord_1689764).sum := by decide
  have hdescent : baseEnd_1689764 < baseStart_1689764 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689797 : List Nat := [1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 4]
def baseStart_1689797 : Nat := 118140960795 + 1689797 * 2 ^ 59
def prefixEnd_1689797 : Nat := 4983230072969 + 3 ^ 40 * 1689797 * 2
def baseEnd_1689797 : Nat := 867678069525630395166271

theorem tailTrace_1689797 : CollatzResearch.WordTrace tailWord_1689797 prefixEnd_1689797 867678069525630395166271 := by
  unfold tailWord_1689797
  simp only [CollatzResearch.WordTrace]
  refine ⟨61631959859161538196539645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41087973239441025464359763 61631959859161538196539645)
  ·
    refine ⟨23111984947185576823702367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61631959859161538196539645 23111984947185576823702367)
    ·
      refine ⟨34667977420778365235553551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23111984947185576823702367 34667977420778365235553551)
      ·
        refine ⟨52001966131167547853330327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34667977420778365235553551 52001966131167547853330327)
        ·
          refine ⟨78002949196751321779995491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52001966131167547853330327 78002949196751321779995491)
          ·
            refine ⟨117004423795126982669993237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78002949196751321779995491 117004423795126982669993237)
            ·
              refine ⟨5484582365396577312655933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 117004423795126982669993237 5484582365396577312655933)
              ·
                refine ⟨2056718387023716492245975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5484582365396577312655933 2056718387023716492245975)
                ·
                  refine ⟨3085077580535574738368963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056718387023716492245975 3085077580535574738368963)
                  ·
                    refine ⟨4627616370803362107553445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3085077580535574738368963 4627616370803362107553445)
                    ·
                      refine ⟨867678069525630395166271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4627616370803362107553445 867678069525630395166271)
                      ·
                        rfl

theorem cell23_1689797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 6, 3, 1, 1, 4].length) (baseStart_1689797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689797 prefixEnd_1689797 := by exact prefixLift 1689797
  have htrace : WordTrace (prefixWord ++ tailWord_1689797) baseStart_1689797 baseEnd_1689797 := by
    simpa [prefixWord, tailWord_1689797, baseEnd_1689797] using wordTrace_append hprefix tailTrace_1689797
  have hstable : (prefixWord ++ tailWord_1689797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689797).length < 2 ^ (prefixWord ++ tailWord_1689797).sum := by decide
  have hdescent : baseEnd_1689797 < baseStart_1689797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689807 : List Nat := [1, 1, 2, 1, 1, 3, 4, 4, 2, 4]
def baseStart_1689807 : Nat := 118140960795 + 1689807 * 2 ^ 59
def prefixEnd_1689807 : Nat := 4983230072969 + 3 ^ 40 * 1689807 * 2
def baseEnd_1689807 : Nat := 289227734777391785347075

theorem tailTrace_1689807 : CollatzResearch.WordTrace tailWord_1689807 prefixEnd_1689807 289227734777391785347075 := by
  unfold tailWord_1689807
  simp only [CollatzResearch.WordTrace]
  refine ⟨61632324589125309904403675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41088216392750206602935783 61632324589125309904403675)
  ·
    refine ⟨92448486883687964856605513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61632324589125309904403675 92448486883687964856605513)
    ·
      refine ⟨69336365162765973642454135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92448486883687964856605513 69336365162765973642454135)
      ·
        refine ⟨104004547744148960463681203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69336365162765973642454135 104004547744148960463681203)
        ·
          refine ⟨156006821616223440695521805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104004547744148960463681203 156006821616223440695521805)
          ·
            refine ⟨58502558106083790260820677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 156006821616223440695521805 58502558106083790260820677)
            ·
              refine ⟨10969229644890710673903877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58502558106083790260820677 10969229644890710673903877)
              ·
                refine ⟨2056730558417008251356977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10969229644890710673903877 2056730558417008251356977)
                ·
                  refine ⟨1542547918812756188517733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2056730558417008251356977 1542547918812756188517733)
                  ·
                    refine ⟨289227734777391785347075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542547918812756188517733 289227734777391785347075)
                    ·
                      rfl

theorem cell23_1689807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 4, 2, 4].length) (baseStart_1689807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689807 prefixEnd_1689807 := by exact prefixLift 1689807
  have htrace : WordTrace (prefixWord ++ tailWord_1689807) baseStart_1689807 baseEnd_1689807 := by
    simpa [prefixWord, tailWord_1689807, baseEnd_1689807] using wordTrace_append hprefix tailTrace_1689807
  have hstable : (prefixWord ++ tailWord_1689807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689807).length < 2 ^ (prefixWord ++ tailWord_1689807).sum := by decide
  have hdescent : baseEnd_1689807 < baseStart_1689807 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689831 : List Nat := [1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 4]
def baseStart_1689831 : Nat := 118140960795 + 1689831 * 2 ^ 59
def prefixEnd_1689831 : Nat := 4983230072969 + 3 ^ 40 * 1689831 * 2
def baseEnd_1689831 : Nat := 867695527867883262141115

theorem tailTrace_1689831 : CollatzResearch.WordTrace tailWord_1689831 prefixEnd_1689831 867695527867883262141115 := by
  unfold tailWord_1689831
  simp only [CollatzResearch.WordTrace]
  refine ⟨61633199941038362003277347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41088799960692241335518231 61633199941038362003277347)
  ·
    refine ⟨92449799911557543004916021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61633199941038362003277347 92449799911557543004916021)
    ·
      refine ⟨8667168741708519656710877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 92449799911557543004916021 8667168741708519656710877)
      ·
        refine ⟨3250188278140694871266579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8667168741708519656710877 3250188278140694871266579)
        ·
          refine ⟨4875282417211042306899869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250188278140694871266579 4875282417211042306899869)
          ·
            refine ⟨1828230906454140865087451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4875282417211042306899869 1828230906454140865087451)
            ·
              refine ⟨2742346359681211297631177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828230906454140865087451 2742346359681211297631177)
              ·
                refine ⟨2056759769760908473223383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742346359681211297631177 2056759769760908473223383)
                ·
                  refine ⟨3085139654641362709835075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056759769760908473223383 3085139654641362709835075)
                  ·
                    refine ⟨4627709481962044064752613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3085139654641362709835075 4627709481962044064752613)
                    ·
                      refine ⟨867695527867883262141115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4627709481962044064752613 867695527867883262141115)
                      ·
                        rfl

theorem cell23_1689831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 3, 1, 2, 1, 1, 4].length) (baseStart_1689831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689831 prefixEnd_1689831 := by exact prefixLift 1689831
  have htrace : WordTrace (prefixWord ++ tailWord_1689831) baseStart_1689831 baseEnd_1689831 := by
    simpa [prefixWord, tailWord_1689831, baseEnd_1689831] using wordTrace_append hprefix tailTrace_1689831
  have hstable : (prefixWord ++ tailWord_1689831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689831).length < 2 ^ (prefixWord ++ tailWord_1689831).sum := by decide
  have hdescent : baseEnd_1689831 < baseStart_1689831 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689865 : List Nat := [1, 2, 1, 1, 3, 6, 2, 2, 1, 2, 2]
def baseStart_1689865 : Nat := 118140960795 + 1689865 * 2 ^ 59
def prefixEnd_1689865 : Nat := 4983230072969 + 3 ^ 40 * 1689865 * 2
def baseEnd_1689865 : Nat := 867712986210136129115959

theorem tailTrace_1689865 : CollatzResearch.WordTrace tailWord_1689865 prefixEnd_1689865 867712986210136129115959 := by
  unfold tailWord_1689865
  simp only [CollatzResearch.WordTrace]
  refine ⟨61634440022915185810015049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41089626681943457206676699 61634440022915185810015049)
  ·
    refine ⟨46225830017186389357511287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61634440022915185810015049 46225830017186389357511287)
    ·
      refine ⟨69338745025779584036266931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46225830017186389357511287 69338745025779584036266931)
      ·
        refine ⟨104008117538669376054400397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69338745025779584036266931 104008117538669376054400397)
        ·
          refine ⟨39003044077001016020400149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104008117538669376054400397 39003044077001016020400149)
          ·
            refine ⟨1828267691109422625956257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 39003044077001016020400149 1828267691109422625956257)
            ·
              refine ⟨1371200768332066969467193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828267691109422625956257 1371200768332066969467193)
              ·
                refine ⟨1028400576249050227100395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371200768332066969467193 1028400576249050227100395)
                ·
                  refine ⟨1542600864373575340650593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028400576249050227100395 1542600864373575340650593)
                  ·
                    refine ⟨1156950648280181505487945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1542600864373575340650593 1156950648280181505487945)
                    ·
                      refine ⟨867712986210136129115959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156950648280181505487945 867712986210136129115959)
                      ·
                        rfl

theorem cell23_1689865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 2, 2, 1, 2, 2].length) (baseStart_1689865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689865 prefixEnd_1689865 := by exact prefixLift 1689865
  have htrace : WordTrace (prefixWord ++ tailWord_1689865) baseStart_1689865 baseEnd_1689865 := by
    simpa [prefixWord, tailWord_1689865, baseEnd_1689865] using wordTrace_append hprefix tailTrace_1689865
  have hstable : (prefixWord ++ tailWord_1689865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689865).length < 2 ^ (prefixWord ++ tailWord_1689865).sum := by decide
  have hdescent : baseEnd_1689865 < baseStart_1689865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689902 : List Nat := [4, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1689902 : Nat := 118140960795 + 1689902 * 2 ^ 59
def prefixEnd_1689902 : Nat := 4983230072969 + 3 ^ 40 * 1689902 * 2
def baseEnd_1689902 : Nat := 867731984994352484353289

theorem tailTrace_1689902 : CollatzResearch.WordTrace tailWord_1689902 prefixEnd_1689902 867731984994352484353289 := by
  unfold tailWord_1689902
  simp only [CollatzResearch.WordTrace]
  refine ⟨7704473690472642641138995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41090526349187427419407973 7704473690472642641138995)
  ·
    refine ⟨11556710535708963961708493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7704473690472642641138995 11556710535708963961708493)
    ·
      refine ⟨4333766450890861485640685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11556710535708963961708493 4333766450890861485640685)
      ·
        refine ⟨1625162419084073057115257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4333766450890861485640685 1625162419084073057115257)
        ·
          refine ⟨1218871814313054792836443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1625162419084073057115257 1218871814313054792836443)
          ·
            refine ⟨1828307721469582189254665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1218871814313054792836443 1828307721469582189254665)
            ·
              refine ⟨1371230791102186641940999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828307721469582189254665 1371230791102186641940999)
              ·
                refine ⟨2056846186653279962911499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371230791102186641940999 2056846186653279962911499)
                ·
                  refine ⟨3085269279979919944367249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056846186653279962911499 3085269279979919944367249)
                  ·
                    refine ⟨2313951959984939958275437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3085269279979919944367249 2313951959984939958275437)
                    ·
                      refine ⟨867731984994352484353289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2313951959984939958275437 867731984994352484353289)
                      ·
                        rfl

theorem cell23_1689902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1689902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689902 prefixEnd_1689902 := by exact prefixLift 1689902
  have htrace : WordTrace (prefixWord ++ tailWord_1689902) baseStart_1689902 baseEnd_1689902 := by
    simpa [prefixWord, tailWord_1689902, baseEnd_1689902] using wordTrace_append hprefix tailTrace_1689902
  have hstable : (prefixWord ++ tailWord_1689902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689902).length < 2 ^ (prefixWord ++ tailWord_1689902).sum := by decide
  have hdescent : baseEnd_1689902 < baseStart_1689902 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689908 : List Nat := [2, 5, 1, 1, 1, 3, 1, 3, 1, 3, 2]
def baseStart_1689908 : Nat := 118140960795 + 1689908 * 2 ^ 59
def prefixEnd_1689908 : Nat := 4983230072969 + 3 ^ 40 * 1689908 * 2
def baseEnd_1689908 : Nat := 867735065878279460878261

theorem tailTrace_1689908 : CollatzResearch.WordTrace tailWord_1689908 prefixEnd_1689908 867735065878279460878261 := by
  unfold tailWord_1689908
  simp only [CollatzResearch.WordTrace]
  refine ⟨30818004180879702076915189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41090672241172936102553585 30818004180879702076915189)
  ·
    refine ⟨2889187891957472069710799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30818004180879702076915189 2889187891957472069710799)
    ·
      refine ⟨4333781837936208104566199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2889187891957472069710799 4333781837936208104566199)
      ·
        refine ⟨6500672756904312156849299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4333781837936208104566199 6500672756904312156849299)
        ·
          refine ⟨9751009135356468235273949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6500672756904312156849299 9751009135356468235273949)
          ·
            refine ⟨3656628425758675588227731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9751009135356468235273949 3656628425758675588227731)
            ·
              refine ⟨5484942638638013382341597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3656628425758675588227731 5484942638638013382341597)
              ·
                refine ⟨2056853489489255018378099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5484942638638013382341597 2056853489489255018378099)
                ·
                  refine ⟨3085280234233882527567149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2056853489489255018378099 3085280234233882527567149)
                  ·
                    refine ⟨1156980087837705947837681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3085280234233882527567149 1156980087837705947837681)
                    ·
                      refine ⟨867735065878279460878261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1156980087837705947837681 867735065878279460878261)
                      ·
                        rfl

theorem cell23_1689908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_1689908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689908 prefixEnd_1689908 := by exact prefixLift 1689908
  have htrace : WordTrace (prefixWord ++ tailWord_1689908) baseStart_1689908 baseEnd_1689908 := by
    simpa [prefixWord, tailWord_1689908, baseEnd_1689908] using wordTrace_append hprefix tailTrace_1689908
  have hstable : (prefixWord ++ tailWord_1689908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689908).length < 2 ^ (prefixWord ++ tailWord_1689908).sum := by decide
  have hdescent : baseEnd_1689908 < baseStart_1689908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689920 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9]
def baseStart_1689920 : Nat := 118140960795 + 1689920 * 2 ^ 59
def prefixEnd_1689920 : Nat := 4983230072969 + 3 ^ 40 * 1689920 * 2
def baseEnd_1689920 : Nat := 867741227646133413928205

theorem tailTrace_1689920 : CollatzResearch.WordTrace tailWord_1689920 prefixEnd_1689920 867741227646133413928205 := by
  unfold tailWord_1689920
  simp only [CollatzResearch.WordTrace]
  refine ⟨30818223018857965101633607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41090964025143953468844809 30818223018857965101633607)
  ·
    refine ⟨46227334528286947652450411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30818223018857965101633607 46227334528286947652450411)
    ·
      refine ⟨69341001792430421478675617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46227334528286947652450411 69341001792430421478675617)
      ·
        refine ⟨52005751344322816109006713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69341001792430421478675617 52005751344322816109006713)
        ·
          refine ⟨39004313508242112081755035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52005751344322816109006713 39004313508242112081755035)
          ·
            refine ⟨58506470262363168122632553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39004313508242112081755035 58506470262363168122632553)
            ·
              refine ⟨43879852696772376091974415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58506470262363168122632553 43879852696772376091974415)
              ·
                refine ⟨65819779045158564137961623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43879852696772376091974415 65819779045158564137961623)
                ·
                  refine ⟨98729668567737846206942435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65819779045158564137961623 98729668567737846206942435)
                  ·
                    refine ⟨148094502851606769310413653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 98729668567737846206942435 148094502851606769310413653)
                    ·
                      refine ⟨867741227646133413928205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 148094502851606769310413653 867741227646133413928205)
                      ·
                        rfl

theorem cell23_1689920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 9].length) (baseStart_1689920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689920 prefixEnd_1689920 := by exact prefixLift 1689920
  have htrace : WordTrace (prefixWord ++ tailWord_1689920) baseStart_1689920 baseEnd_1689920 := by
    simpa [prefixWord, tailWord_1689920, baseEnd_1689920] using wordTrace_append hprefix tailTrace_1689920
  have hstable : (prefixWord ++ tailWord_1689920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689920).length < 2 ^ (prefixWord ++ tailWord_1689920).sum := by decide
  have hdescent : baseEnd_1689920 < baseStart_1689920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689927 : List Nat := [1, 1, 4, 1, 2, 2, 4, 1, 7]
def baseStart_1689927 : Nat := 118140960795 + 1689927 * 2 ^ 59
def prefixEnd_1689927 : Nat := 4983230072969 + 3 ^ 40 * 1689927 * 2
def baseEnd_1689927 : Nat := 96416091334523876282297

theorem tailTrace_1689927 : CollatzResearch.WordTrace tailWord_1689927 prefixEnd_1689927 96416091334523876282297 := by
  unfold tailWord_1689927
  simp only [CollatzResearch.WordTrace]
  refine ⟨61636701348690570398772035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41091134232460380265848023 61636701348690570398772035)
  ·
    refine ⟨92455052023035855598158053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61636701348690570398772035 92455052023035855598158053)
    ·
      refine ⟨17335322254319222924654635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92455052023035855598158053 17335322254319222924654635)
      ·
        refine ⟨26002983381478834386981953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17335322254319222924654635 26002983381478834386981953)
        ·
          refine ⟨19502237536109125790236465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26002983381478834386981953 19502237536109125790236465)
          ·
            refine ⟨14626678152081844342677349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19502237536109125790236465 14626678152081844342677349)
            ·
              refine ⟨2742502153515345814252003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14626678152081844342677349 2742502153515345814252003)
              ·
                refine ⟨4113753230273018721378005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742502153515345814252003 4113753230273018721378005)
                ·
                  refine ⟨96416091334523876282297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4113753230273018721378005 96416091334523876282297)
                  ·
                    rfl

theorem cell23_1689927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 1, 7].length) (baseStart_1689927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689927 prefixEnd_1689927 := by exact prefixLift 1689927
  have htrace : WordTrace (prefixWord ++ tailWord_1689927) baseStart_1689927 baseEnd_1689927 := by
    simpa [prefixWord, tailWord_1689927, baseEnd_1689927] using wordTrace_append hprefix tailTrace_1689927
  have hstable : (prefixWord ++ tailWord_1689927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689927).length < 2 ^ (prefixWord ++ tailWord_1689927).sum := by decide
  have hdescent : baseEnd_1689927 < baseStart_1689927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1689957 : List Nat := [1, 3, 1, 3, 1, 3, 2, 1, 1, 7]
def baseStart_1689957 : Nat := 118140960795 + 1689957 * 2 ^ 59
def prefixEnd_1689957 : Nat := 4983230072969 + 3 ^ 40 * 1689957 * 2
def baseEnd_1689957 : Nat := 289253408810116589721845

theorem tailTrace_1689957 : CollatzResearch.WordTrace tailWord_1689957 prefixEnd_1689957 289253408810116589721845 := by
  unfold tailWord_1689957
  simp only [CollatzResearch.WordTrace]
  refine ⟨61637795538581885522364125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41091863692387923681576083 61637795538581885522364125)
  ·
    refine ⟨23114173326968207070886547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61637795538581885522364125 23114173326968207070886547)
    ·
      refine ⟨34671259990452310606329821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23114173326968207070886547 34671259990452310606329821)
      ·
        refine ⟨13001722496419616477373683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34671259990452310606329821 13001722496419616477373683)
        ·
          refine ⟨19502583744629424716060525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13001722496419616477373683 19502583744629424716060525)
          ·
            refine ⟨7313468904236034268522697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19502583744629424716060525 7313468904236034268522697)
            ·
              refine ⟨5485101678177025701392023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7313468904236034268522697 5485101678177025701392023)
              ·
                refine ⟨8227652517265538552088035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5485101678177025701392023 8227652517265538552088035)
                ·
                  refine ⟨12341478775898307828132053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8227652517265538552088035 12341478775898307828132053)
                  ·
                    refine ⟨289253408810116589721845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12341478775898307828132053 289253408810116589721845)
                    ·
                      rfl

theorem cell23_1689957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 3, 2, 1, 1, 7].length) (baseStart_1689957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1689957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1689957 prefixEnd_1689957 := by exact prefixLift 1689957
  have htrace : WordTrace (prefixWord ++ tailWord_1689957) baseStart_1689957 baseEnd_1689957 := by
    simpa [prefixWord, tailWord_1689957, baseEnd_1689957] using wordTrace_append hprefix tailTrace_1689957
  have hstable : (prefixWord ++ tailWord_1689957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1689957).length < 2 ^ (prefixWord ++ tailWord_1689957).sum := by decide
  have hdescent : baseEnd_1689957 < baseStart_1689957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1689957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690007 : List Nat := [1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 4]
def baseStart_1690007 : Nat := 118140960795 + 1690007 * 2 ^ 59
def prefixEnd_1690007 : Nat := 4983230072969 + 3 ^ 40 * 1690007 * 2
def baseEnd_1690007 : Nat := 867785900463074573540305

theorem tailTrace_1690007 : CollatzResearch.WordTrace tailWord_1690007 prefixEnd_1690007 867785900463074573540305 := by
  unfold tailWord_1690007
  simp only [CollatzResearch.WordTrace]
  refine ⟨61639619188400744061684275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41093079458933829374456183 61639619188400744061684275)
  ·
    refine ⟨92459428782601116092526413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61639619188400744061684275 92459428782601116092526413)
    ·
      refine ⟨34672285793475418534697405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92459428782601116092526413 34672285793475418534697405)
      ·
        refine ⟨13002107172553281950511527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34672285793475418534697405 13002107172553281950511527)
        ·
          refine ⟨19503160758829922925767291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13002107172553281950511527 19503160758829922925767291)
          ·
            refine ⟨29254741138244884388650937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19503160758829922925767291 29254741138244884388650937)
            ·
              refine ⟨21941055853683663291488203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29254741138244884388650937 21941055853683663291488203)
              ·
                refine ⟨32911583780525494937232305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21941055853683663291488203 32911583780525494937232305)
                ·
                  refine ⟨24683687835394121202924229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32911583780525494937232305 24683687835394121202924229)
                  ·
                    refine ⟨4628191469136397725548293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24683687835394121202924229 4628191469136397725548293)
                    ·
                      refine ⟨867785900463074573540305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4628191469136397725548293 867785900463074573540305)
                      ·
                        rfl

theorem cell23_1690007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 4, 4].length) (baseStart_1690007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690007 prefixEnd_1690007 := by exact prefixLift 1690007
  have htrace : WordTrace (prefixWord ++ tailWord_1690007) baseStart_1690007 baseEnd_1690007 := by
    simpa [prefixWord, tailWord_1690007, baseEnd_1690007] using wordTrace_append hprefix tailTrace_1690007
  have hstable : (prefixWord ++ tailWord_1690007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690007).length < 2 ^ (prefixWord ++ tailWord_1690007).sum := by decide
  have hdescent : baseEnd_1690007 < baseStart_1690007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690021 : List Nat := [1, 3, 1, 2, 1, 1, 4, 5, 1, 4]
def baseStart_1690021 : Nat := 118140960795 + 1690021 * 2 ^ 59
def prefixEnd_1690021 : Nat := 4983230072969 + 3 ^ 40 * 1690021 * 2
def baseEnd_1690021 : Nat := 289264363064079172921747

theorem tailTrace_1690021 : CollatzResearch.WordTrace tailWord_1690021 prefixEnd_1690021 289264363064079172921747 := by
  unfold tailWord_1690021
  simp only [CollatzResearch.WordTrace]
  refine ⟨61640129810350024452693917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41093419873566682968462611 61640129810350024452693917)
  ·
    refine ⟨23115048678881259169760219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61640129810350024452693917 23115048678881259169760219)
    ·
      refine ⟨34672573018321888754640329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23115048678881259169760219 34672573018321888754640329)
      ·
        refine ⟨26004429763741416565980247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34672573018321888754640329 26004429763741416565980247)
        ·
          refine ⟨39006644645612124848970371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26004429763741416565980247 39006644645612124848970371)
          ·
            refine ⟨58509966968418187273455557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39006644645612124848970371 58509966968418187273455557)
            ·
              refine ⟨10970618806578410113772917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58509966968418187273455557 10970618806578410113772917)
              ·
                refine ⟨1028495513116725948166211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10970618806578410113772917 1028495513116725948166211)
                ·
                  refine ⟨1542743269675088922249317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028495513116725948166211 1542743269675088922249317)
                  ·
                    refine ⟨289264363064079172921747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1542743269675088922249317 289264363064079172921747)
                    ·
                      rfl

theorem cell23_1690021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 5, 1, 4].length) (baseStart_1690021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690021 prefixEnd_1690021 := by exact prefixLift 1690021
  have htrace : WordTrace (prefixWord ++ tailWord_1690021) baseStart_1690021 baseEnd_1690021 := by
    simpa [prefixWord, tailWord_1690021, baseEnd_1690021] using wordTrace_append hprefix tailTrace_1690021
  have hstable : (prefixWord ++ tailWord_1690021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690021).length < 2 ^ (prefixWord ++ tailWord_1690021).sum := by decide
  have hdescent : baseEnd_1690021 < baseStart_1690021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690034 : List Nat := [3, 2, 1, 1, 1, 1, 6, 2, 6]
def baseStart_1690034 : Nat := 118140960795 + 1690034 * 2 ^ 59
def prefixEnd_1690034 : Nat := 4983230072969 + 3 ^ 40 * 1690034 * 2
def baseEnd_1690034 : Nat := 96422196048971774211409

theorem tailTrace_1690034 : CollatzResearch.WordTrace tailWord_1690034 prefixEnd_1690034 96422196048971774211409 := by
  unfold tailWord_1690034
  simp only [CollatzResearch.WordTrace]
  refine ⟨15410150989825731918229289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41093735972868618448611437 15410150989825731918229289)
  ·
    refine ⟨11557613242369298938671967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15410150989825731918229289 11557613242369298938671967)
    ·
      refine ⟨17336419863553948408007951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11557613242369298938671967 17336419863553948408007951)
      ·
        refine ⟨26004629795330922612011927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17336419863553948408007951 26004629795330922612011927)
        ·
          refine ⟨39006944692996383918017891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26004629795330922612011927 39006944692996383918017891)
          ·
            refine ⟨58510417039494575877026837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39006944692996383918017891 58510417039494575877026837)
            ·
              refine ⟨2742675798726308244235633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58510417039494575877026837 2742675798726308244235633)
              ·
                refine ⟨2057006849044731183176725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2742675798726308244235633 2057006849044731183176725)
                ·
                  refine ⟨96422196048971774211409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2057006849044731183176725 96422196048971774211409)
                  ·
                    rfl

theorem cell23_1690034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 6].length) (baseStart_1690034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690034 prefixEnd_1690034 := by exact prefixLift 1690034
  have htrace : WordTrace (prefixWord ++ tailWord_1690034) baseStart_1690034 baseEnd_1690034 := by
    simpa [prefixWord, tailWord_1690034, baseEnd_1690034] using wordTrace_append hprefix tailTrace_1690034
  have hstable : (prefixWord ++ tailWord_1690034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690034).length < 2 ^ (prefixWord ++ tailWord_1690034).sum := by decide
  have hdescent : baseEnd_1690034 < baseStart_1690034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690104 : List Nat := [2, 1, 2, 1, 1, 4, 3, 2, 1, 1, 5]
def baseStart_1690104 : Nat := 118140960795 + 1690104 * 2 ^ 59
def prefixEnd_1690104 : Nat := 4983230072969 + 3 ^ 40 * 1690104 * 2
def baseEnd_1690104 : Nat := 867835708086560694027359

theorem tailTrace_1690104 : CollatzResearch.WordTrace tailWord_1690104 prefixEnd_1690104 867835708086560694027359 := by
  unfold tailWord_1690104
  simp only [CollatzResearch.WordTrace]
  refine ⟨30821578534524664813982683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41095438046032886418643577 30821578534524664813982683)
  ·
    refine ⟨46232367801786997220974025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30821578534524664813982683 46232367801786997220974025)
    ·
      refine ⟨34674275851340247915730519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46232367801786997220974025 34674275851340247915730519)
      ·
        refine ⟨52011413777010371873595779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34674275851340247915730519 52011413777010371873595779)
        ·
          refine ⟨78017120665515557810393669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52011413777010371873595779 78017120665515557810393669)
          ·
            refine ⟨14628210124784167089448813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 78017120665515557810393669 14628210124784167089448813)
            ·
              refine ⟨5485578796794062658543305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14628210124784167089448813 5485578796794062658543305)
              ·
                refine ⟨4114184097595546993907479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5485578796794062658543305 4114184097595546993907479)
                ·
                  refine ⟨6171276146393320490861219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114184097595546993907479 6171276146393320490861219)
                  ·
                    refine ⟨9256914219589980736291829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6171276146393320490861219 9256914219589980736291829)
                    ·
                      refine ⟨867835708086560694027359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9256914219589980736291829 867835708086560694027359)
                      ·
                        rfl

theorem cell23_1690104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 3, 2, 1, 1, 5].length) (baseStart_1690104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690104 prefixEnd_1690104 := by exact prefixLift 1690104
  have htrace : WordTrace (prefixWord ++ tailWord_1690104) baseStart_1690104 baseEnd_1690104 := by
    simpa [prefixWord, tailWord_1690104, baseEnd_1690104] using wordTrace_append hprefix tailTrace_1690104
  have hstable : (prefixWord ++ tailWord_1690104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690104).length < 2 ^ (prefixWord ++ tailWord_1690104).sum := by decide
  have hdescent : baseEnd_1690104 < baseStart_1690104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690124 : List Nat := [2, 2, 1, 2, 4, 2, 1, 9]
def baseStart_1690124 : Nat := 118140960795 + 1690124 * 2 ^ 59
def prefixEnd_1690124 : Nat := 4983230072969 + 3 ^ 40 * 1690124 * 2
def baseEnd_1690124 : Nat := 32142443618505578362121

theorem tailTrace_1690124 : CollatzResearch.WordTrace tailWord_1690124 prefixEnd_1690124 32142443618505578362121 := by
  unfold tailWord_1690124
  simp only [CollatzResearch.WordTrace]
  refine ⟨30821943264488436521846713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41095924352651248695795617 30821943264488436521846713)
  ·
    refine ⟨23116457448366327391385035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30821943264488436521846713 23116457448366327391385035)
    ·
      refine ⟨34674686172549491087077553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23116457448366327391385035 34674686172549491087077553)
      ·
        refine ⟨26006014629412118315308165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34674686172549491087077553 26006014629412118315308165)
        ·
          refine ⟨4876127743014772184120281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26006014629412118315308165 4876127743014772184120281)
          ·
            refine ⟨3657095807261079138090211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4876127743014772184120281 3657095807261079138090211)
            ·
              refine ⟨5485643710891618707135317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3657095807261079138090211 5485643710891618707135317)
              ·
                refine ⟨32142443618505578362121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5485643710891618707135317 32142443618505578362121)
                ·
                  rfl

theorem cell23_1690124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 9].length) (baseStart_1690124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690124 prefixEnd_1690124 := by exact prefixLift 1690124
  have htrace : WordTrace (prefixWord ++ tailWord_1690124) baseStart_1690124 baseEnd_1690124 := by
    simpa [prefixWord, tailWord_1690124, baseEnd_1690124] using wordTrace_append hprefix tailTrace_1690124
  have hstable : (prefixWord ++ tailWord_1690124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690124).length < 2 ^ (prefixWord ++ tailWord_1690124).sum := by decide
  have hdescent : baseEnd_1690124 < baseStart_1690124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690152 : List Nat := [2, 1, 5, 2, 1, 3, 1, 1, 3, 2, 2]
def baseStart_1690152 : Nat := 118140960795 + 1690152 * 2 ^ 59
def prefixEnd_1690152 : Nat := 4983230072969 + 3 ^ 40 * 1690152 * 2
def baseEnd_1690152 : Nat := 867860355157976506227139

theorem tailTrace_1690152 : CollatzResearch.WordTrace tailWord_1690152 prefixEnd_1690152 867860355157976506227139 := by
  unfold tailWord_1690152
  simp only [CollatzResearch.WordTrace]
  refine ⟨30822453886437716912856355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41096605181916955883808473 30822453886437716912856355)
  ·
    refine ⟨46233680829656575369284533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30822453886437716912856355 46233680829656575369284533)
    ·
      refine ⟨4334407577780303940870425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46233680829656575369284533 4334407577780303940870425)
      ·
        refine ⟨3250805683335227955652819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4334407577780303940870425 3250805683335227955652819)
        ·
          refine ⟨4876208525002841933479229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3250805683335227955652819 4876208525002841933479229)
          ·
            refine ⟨1828578196876065725054711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4876208525002841933479229 1828578196876065725054711)
            ·
              refine ⟨2742867295314098587582067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828578196876065725054711 2742867295314098587582067)
              ·
                refine ⟨4114300942971147881373101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2742867295314098587582067 4114300942971147881373101)
                ·
                  refine ⟨1542862853614180455514913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4114300942971147881373101 1542862853614180455514913)
                  ·
                    refine ⟨1157147140210635341636185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1542862853614180455514913 1157147140210635341636185)
                    ·
                      refine ⟨867860355157976506227139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157147140210635341636185 867860355157976506227139)
                      ·
                        rfl

theorem cell23_1690152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 3, 1, 1, 3, 2, 2].length) (baseStart_1690152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690152 prefixEnd_1690152 := by exact prefixLift 1690152
  have htrace : WordTrace (prefixWord ++ tailWord_1690152) baseStart_1690152 baseEnd_1690152 := by
    simpa [prefixWord, tailWord_1690152, baseEnd_1690152] using wordTrace_append hprefix tailTrace_1690152
  have hstable : (prefixWord ++ tailWord_1690152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690152).length < 2 ^ (prefixWord ++ tailWord_1690152).sum := by decide
  have hdescent : baseEnd_1690152 < baseStart_1690152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690168 : List Nat := [2, 1, 2, 1, 4, 1, 3, 3, 2, 1, 3]
def baseStart_1690168 : Nat := 118140960795 + 1690168 * 2 ^ 59
def prefixEnd_1690168 : Nat := 4983230072969 + 3 ^ 40 * 1690168 * 2
def baseEnd_1690168 : Nat := 867868570848448443627065

theorem tailTrace_1690168 : CollatzResearch.WordTrace tailWord_1690168 prefixEnd_1690168 867868570848448443627065 := by
  unfold tailWord_1690168
  simp only [CollatzResearch.WordTrace]
  refine ⟨30822745670408734279147579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41096994227211645705530105 30822745670408734279147579)
  ·
    refine ⟨46234118505613101418721369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30822745670408734279147579 46234118505613101418721369)
    ·
      refine ⟨34675588879209826064041027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46234118505613101418721369 34675588879209826064041027)
      ·
        refine ⟨52013383318814739096061541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34675588879209826064041027 52013383318814739096061541)
        ·
          refine ⟨9752509372277763580511539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52013383318814739096061541 9752509372277763580511539)
          ·
            refine ⟨14628764058416645370767309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752509372277763580511539 14628764058416645370767309)
            ·
              refine ⟨5485786521906242014037741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14628764058416645370767309 5485786521906242014037741)
              ·
                refine ⟨2057169945714840755264153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5485786521906242014037741 2057169945714840755264153)
                ·
                  refine ⟨1542877459286130566448115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2057169945714840755264153 1542877459286130566448115)
                  ·
                    refine ⟨2314316188929195849672173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1542877459286130566448115 2314316188929195849672173)
                    ·
                      refine ⟨867868570848448443627065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2314316188929195849672173 867868570848448443627065)
                      ·
                        rfl

theorem cell23_1690168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 2, 1, 3].length) (baseStart_1690168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690168 prefixEnd_1690168 := by exact prefixLift 1690168
  have htrace : WordTrace (prefixWord ++ tailWord_1690168) baseStart_1690168 baseEnd_1690168 := by
    simpa [prefixWord, tailWord_1690168, baseEnd_1690168] using wordTrace_append hprefix tailTrace_1690168
  have hstable : (prefixWord ++ tailWord_1690168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690168).length < 2 ^ (prefixWord ++ tailWord_1690168).sum := by decide
  have hdescent : baseEnd_1690168 < baseStart_1690168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690191 : List Nat := [1, 1, 2, 1, 1, 2, 5, 1, 3, 4, 2]
def baseStart_1690191 : Nat := 118140960795 + 1690191 * 2 ^ 59
def prefixEnd_1690191 : Nat := 4983230072969 + 3 ^ 40 * 1690191 * 2
def baseEnd_1690191 : Nat := 867880380903501853639459

theorem tailTrace_1690191 : CollatzResearch.WordTrace tailWord_1690191 prefixEnd_1690191 867880380903501853639459 := by
  unfold tailWord_1690191
  simp only [CollatzResearch.WordTrace]
  refine ⟨61646330219734143486382427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41097553479822762324254951 61646330219734143486382427)
  ·
    refine ⟨92469495329601215229573641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61646330219734143486382427 92469495329601215229573641)
    ·
      refine ⟨69352121497200911422180231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92469495329601215229573641 69352121497200911422180231)
      ·
        refine ⟨104028182245801367133270347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69352121497200911422180231 104028182245801367133270347)
        ·
          refine ⟨156042273368702050699905521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104028182245801367133270347 156042273368702050699905521)
          ·
            refine ⟨117031705026526538024929141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156042273368702050699905521 117031705026526538024929141)
            ·
              refine ⟨10971722346236862939837107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117031705026526538024929141 10971722346236862939837107)
              ·
                refine ⟨16457583519355294409755661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10971722346236862939837107 16457583519355294409755661)
                ·
                  refine ⟨6171593819758235403658373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16457583519355294409755661 6171593819758235403658373)
                  ·
                    refine ⟨1157173841204669138185945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6171593819758235403658373 1157173841204669138185945)
                    ·
                      refine ⟨867880380903501853639459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157173841204669138185945 867880380903501853639459)
                      ·
                        rfl

theorem cell23_1690191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 5, 1, 3, 4, 2].length) (baseStart_1690191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690191 prefixEnd_1690191 := by exact prefixLift 1690191
  have htrace : WordTrace (prefixWord ++ tailWord_1690191) baseStart_1690191 baseEnd_1690191 := by
    simpa [prefixWord, tailWord_1690191, baseEnd_1690191] using wordTrace_append hprefix tailTrace_1690191
  have hstable : (prefixWord ++ tailWord_1690191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690191).length < 2 ^ (prefixWord ++ tailWord_1690191).sum := by decide
  have hdescent : baseEnd_1690191 < baseStart_1690191 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690208 : List Nat := [2, 1, 1, 3, 2, 1, 2, 3, 4, 2, 2]
def baseStart_1690208 : Nat := 118140960795 + 1690208 * 2 ^ 59
def prefixEnd_1690208 : Nat := 4983230072969 + 3 ^ 40 * 1690208 * 2
def baseEnd_1690208 : Nat := 867889110074628287126881

theorem tailTrace_1690208 : CollatzResearch.WordTrace tailWord_1690208 prefixEnd_1690208 867889110074628287126881 := by
  unfold tailWord_1690208
  simp only [CollatzResearch.WordTrace]
  refine ⟨30823475130336277694875639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41097966840448370259834185 30823475130336277694875639)
  ·
    refine ⟨46235212695504416542313459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30823475130336277694875639 46235212695504416542313459)
    ·
      refine ⟨69352819043256624813470189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46235212695504416542313459 69352819043256624813470189)
      ·
        refine ⟨26007307141221234305051321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69352819043256624813470189 26007307141221234305051321)
        ·
          refine ⟨19505480355915925728788491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26007307141221234305051321 19505480355915925728788491)
          ·
            refine ⟨29258220533873888593182737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19505480355915925728788491 29258220533873888593182737)
            ·
              refine ⟨21943665400405416444887053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29258220533873888593182737 21943665400405416444887053)
              ·
                refine ⟨8228874525152031166832645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21943665400405416444887053 8228874525152031166832645)
                ·
                  refine ⟨1542913973466005843781121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8228874525152031166832645 1542913973466005843781121)
                  ·
                    refine ⟨1157185480099504382835841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1542913973466005843781121 1157185480099504382835841)
                    ·
                      refine ⟨867889110074628287126881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157185480099504382835841 867889110074628287126881)
                      ·
                        rfl

theorem cell23_1690208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_1690208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690208 prefixEnd_1690208 := by exact prefixLift 1690208
  have htrace : WordTrace (prefixWord ++ tailWord_1690208) baseStart_1690208 baseEnd_1690208 := by
    simpa [prefixWord, tailWord_1690208, baseEnd_1690208] using wordTrace_append hprefix tailTrace_1690208
  have hstable : (prefixWord ++ tailWord_1690208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690208).length < 2 ^ (prefixWord ++ tailWord_1690208).sum := by decide
  have hdescent : baseEnd_1690208 < baseStart_1690208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690221 : List Nat := [1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 4]
def baseStart_1690221 : Nat := 118140960795 + 1690221 * 2 ^ 59
def prefixEnd_1690221 : Nat := 4983230072969 + 3 ^ 40 * 1690221 * 2
def baseEnd_1690221 : Nat := 867895785323136736264321

theorem tailTrace_1690221 : CollatzResearch.WordTrace tailWord_1690221 prefixEnd_1690221 867895785323136736264321 := by
  unfold tailWord_1690221
  simp only [CollatzResearch.WordTrace]
  refine ⟨61647424409625458609974517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41098282939750305739983011 61647424409625458609974517)
  ·
    refine ⟨5779446038402386744685111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61647424409625458609974517 5779446038402386744685111)
    ·
      refine ⟨8669169057603580117027667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5779446038402386744685111 8669169057603580117027667)
      ·
        refine ⟨13003753586405370175541501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8669169057603580117027667 13003753586405370175541501)
        ·
          refine ⟨4876407594902013815828063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13003753586405370175541501 4876407594902013815828063)
          ·
            refine ⟨7314611392353020723742095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876407594902013815828063 7314611392353020723742095)
            ·
              refine ⟨10971917088529531085613143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314611392353020723742095 10971917088529531085613143)
              ·
                refine ⟨16457875632794296628419715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10971917088529531085613143 16457875632794296628419715)
                ·
                  refine ⟨24686813449191444942629573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16457875632794296628419715 24686813449191444942629573)
                  ·
                    refine ⟨4628777521723395926743045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24686813449191444942629573 4628777521723395926743045)
                    ·
                      refine ⟨867895785323136736264321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4628777521723395926743045 867895785323136736264321)
                      ·
                        rfl

theorem cell23_1690221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 4, 4].length) (baseStart_1690221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690221 prefixEnd_1690221 := by exact prefixLift 1690221
  have htrace : WordTrace (prefixWord ++ tailWord_1690221) baseStart_1690221 baseEnd_1690221 := by
    simpa [prefixWord, tailWord_1690221, baseEnd_1690221] using wordTrace_append hprefix tailTrace_1690221
  have hstable : (prefixWord ++ tailWord_1690221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690221).length < 2 ^ (prefixWord ++ tailWord_1690221).sum := by decide
  have hdescent : baseEnd_1690221 < baseStart_1690221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690241 : List Nat := [1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 3]
def baseStart_1690241 : Nat := 118140960795 + 1690241 * 2 ^ 59
def prefixEnd_1690241 : Nat := 4983230072969 + 3 ^ 40 * 1690241 * 2
def baseEnd_1690241 : Nat := 867906054936226658014229

theorem tailTrace_1690241 : CollatzResearch.WordTrace tailWord_1690241 prefixEnd_1690241 867906054936226658014229 := by
  unfold tailWord_1690241
  simp only [CollatzResearch.WordTrace]
  refine ⟨61648153869553002025702577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41098769246368668017135051 61648153869553002025702577)
  ·
    refine ⟨46236115402164751519276933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61648153869553002025702577 46236115402164751519276933)
    ·
      refine ⟨8669271637905890909864425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46236115402164751519276933 8669271637905890909864425)
      ·
        refine ⟨6501953728429418182398319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8669271637905890909864425 6501953728429418182398319)
        ·
          refine ⟨9752930592644127273597479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6501953728429418182398319 9752930592644127273597479)
          ·
            refine ⟨14629395888966190910396219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9752930592644127273597479 14629395888966190910396219)
            ·
              refine ⟨21944093833449286365594329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14629395888966190910396219 21944093833449286365594329)
              ·
                refine ⟨16458070375086964774195747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21944093833449286365594329 16458070375086964774195747)
                ·
                  refine ⟨24687105562630447161293621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16458070375086964774195747 24687105562630447161293621)
                  ·
                    refine ⟨2314416146496604421371277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24687105562630447161293621 2314416146496604421371277)
                    ·
                      refine ⟨867906054936226658014229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2314416146496604421371277 867906054936226658014229)
                      ·
                        rfl

theorem cell23_1690241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_1690241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690241 prefixEnd_1690241 := by exact prefixLift 1690241
  have htrace : WordTrace (prefixWord ++ tailWord_1690241) baseStart_1690241 baseEnd_1690241 := by
    simpa [prefixWord, tailWord_1690241, baseEnd_1690241] using wordTrace_append hprefix tailTrace_1690241
  have hstable : (prefixWord ++ tailWord_1690241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690241).length < 2 ^ (prefixWord ++ tailWord_1690241).sum := by decide
  have hdescent : baseEnd_1690241 < baseStart_1690241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690251 : List Nat := [1, 1, 1, 1, 4, 1, 2, 2, 1, 7, 2]
def baseStart_1690251 : Nat := 118140960795 + 1690251 * 2 ^ 59
def prefixEnd_1690251 : Nat := 4983230072969 + 3 ^ 40 * 1690251 * 2
def baseEnd_1690251 : Nat := 867911189742771618889183

theorem tailTrace_1690251 : CollatzResearch.WordTrace tailWord_1690251 prefixEnd_1690251 867911189742771618889183 := by
  unfold tailWord_1690251
  simp only [CollatzResearch.WordTrace]
  refine ⟨61648518599516773733566607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41099012399677849155711071 61648518599516773733566607)
  ·
    refine ⟨92472777899275160600349911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61648518599516773733566607 92472777899275160600349911)
    ·
      refine ⟨138709166848912740900524867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92472777899275160600349911 138709166848912740900524867)
      ·
        refine ⟨208063750273369111350787301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138709166848912740900524867 208063750273369111350787301)
        ·
          refine ⟨39011953176256708378272619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 208063750273369111350787301 39011953176256708378272619)
          ·
            refine ⟨58517929764385062567408929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39011953176256708378272619 58517929764385062567408929)
            ·
              refine ⟨43888447323288796925556697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58517929764385062567408929 43888447323288796925556697)
              ·
                refine ⟨32916335492466597694167523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43888447323288796925556697 32916335492466597694167523)
                ·
                  refine ⟨49374503238699896541251285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32916335492466597694167523 49374503238699896541251285)
                  ·
                    refine ⟨1157214919657028825185577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49374503238699896541251285 1157214919657028825185577)
                    ·
                      refine ⟨867911189742771618889183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157214919657028825185577 867911189742771618889183)
                      ·
                        rfl

theorem cell23_1690251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 2, 1, 7, 2].length) (baseStart_1690251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690251 prefixEnd_1690251 := by exact prefixLift 1690251
  have htrace : WordTrace (prefixWord ++ tailWord_1690251) baseStart_1690251 baseEnd_1690251 := by
    simpa [prefixWord, tailWord_1690251, baseEnd_1690251] using wordTrace_append hprefix tailTrace_1690251
  have hstable : (prefixWord ++ tailWord_1690251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690251).length < 2 ^ (prefixWord ++ tailWord_1690251).sum := by decide
  have hdescent : baseEnd_1690251 < baseStart_1690251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690258 : List Nat := [3, 2, 3, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_1690258 : Nat := 118140960795 + 1690258 * 2 ^ 59
def prefixEnd_1690258 : Nat := 4983230072969 + 3 ^ 40 * 1690258 * 2
def baseEnd_1690258 : Nat := 867914784107353091501651

theorem tailTrace_1690258 : CollatzResearch.WordTrace tailWord_1690258 prefixEnd_1690258 867914784107353091501651 := by
  unfold tailWord_1690258
  simp only [CollatzResearch.WordTrace]
  refine ⟨15412193477622853482267857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41099182606994275952714285 15412193477622853482267857)
  ·
    refine ⟨11559145108217140111700893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15412193477622853482267857 11559145108217140111700893)
    ·
      refine ⟨4334679415581427541887835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11559145108217140111700893 4334679415581427541887835)
      ·
        refine ⟨6502019123372141312831753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4334679415581427541887835 6502019123372141312831753)
        ·
          refine ⟨4876514342529105984623815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6502019123372141312831753 4876514342529105984623815)
          ·
            refine ⟨7314771513793658976935723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4876514342529105984623815 7314771513793658976935723)
            ·
              refine ⟨10972157270690488465403585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7314771513793658976935723 10972157270690488465403585)
              ·
                refine ⟨8229117953017866349052689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10972157270690488465403585 8229117953017866349052689)
                ·
                  refine ⟨6171838464763399761789517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8229117953017866349052689 6171838464763399761789517)
                  ·
                    refine ⟨2314439424286274910671069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6171838464763399761789517 2314439424286274910671069)
                    ·
                      refine ⟨867914784107353091501651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2314439424286274910671069 867914784107353091501651)
                      ·
                        rfl

theorem cell23_1690258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_1690258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690258 prefixEnd_1690258 := by exact prefixLift 1690258
  have htrace : WordTrace (prefixWord ++ tailWord_1690258) baseStart_1690258 baseEnd_1690258 := by
    simpa [prefixWord, tailWord_1690258, baseEnd_1690258] using wordTrace_append hprefix tailTrace_1690258
  have hstable : (prefixWord ++ tailWord_1690258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690258).length < 2 ^ (prefixWord ++ tailWord_1690258).sum := by decide
  have hdescent : baseEnd_1690258 < baseStart_1690258 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690318 : List Nat := [4, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_1690318 : Nat := 118140960795 + 1690318 * 2 ^ 59
def prefixEnd_1690318 : Nat := 4983230072969 + 3 ^ 40 * 1690318 * 2
def baseEnd_1690318 : Nat := 867945592946622856751375

theorem tailTrace_1690318 : CollatzResearch.WordTrace tailWord_1690318 prefixEnd_1690318 867945592946622856751375 := by
  unfold tailWord_1690318
  simp only [CollatzResearch.WordTrace]
  refine ⟨7706370286284255522031951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41100641526849362784170405 7706370286284255522031951)
  ·
    refine ⟨11559555429426383283047927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7706370286284255522031951 11559555429426383283047927)
    ·
      refine ⟨17339333144139574924571891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11559555429426383283047927 17339333144139574924571891)
      ·
        refine ⟨26008999716209362386857837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17339333144139574924571891 26008999716209362386857837)
        ·
          refine ⟨9753374893578510895071689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26008999716209362386857837 9753374893578510895071689)
          ·
            refine ⟨7315031170183883171303767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9753374893578510895071689 7315031170183883171303767)
            ·
              refine ⟨10972546755275824756955651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315031170183883171303767 10972546755275824756955651)
              ·
                refine ⟨16458820132913737135433477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10972546755275824756955651 16458820132913737135433477)
                ·
                  refine ⟨3086028774921325712893777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16458820132913737135433477 3086028774921325712893777)
                  ·
                    refine ⟨2314521581190994284670333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3086028774921325712893777 2314521581190994284670333)
                    ·
                      refine ⟨867945592946622856751375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2314521581190994284670333 867945592946622856751375)
                      ·
                        rfl

theorem cell23_1690318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_1690318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690318 prefixEnd_1690318 := by exact prefixLift 1690318
  have htrace : WordTrace (prefixWord ++ tailWord_1690318) baseStart_1690318 baseEnd_1690318 := by
    simpa [prefixWord, tailWord_1690318, baseEnd_1690318] using wordTrace_append hprefix tailTrace_1690318
  have hstable : (prefixWord ++ tailWord_1690318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690318).length < 2 ^ (prefixWord ++ tailWord_1690318).sum := by decide
  have hdescent : baseEnd_1690318 < baseStart_1690318 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690321 : List Nat := [1, 2, 2, 1, 2, 3, 2, 4, 6]
def baseStart_1690321 : Nat := 118140960795 + 1690321 * 2 ^ 59
def prefixEnd_1690321 : Nat := 4983230072969 + 3 ^ 40 * 1690321 * 2
def baseEnd_1690321 : Nat := 96438570376509593890429

theorem tailTrace_1690321 : CollatzResearch.WordTrace tailWord_1690321 prefixEnd_1690321 96438570376509593890429 := by
  unfold tailWord_1690321
  simp only [CollatzResearch.WordTrace]
  refine ⟨61651071709263175688614817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41100714472842117125743211 61651071709263175688614817)
  ·
    refine ⟨46238303781947381766461113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61651071709263175688614817 46238303781947381766461113)
    ·
      refine ⟨34678727836460536324845835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46238303781947381766461113 34678727836460536324845835)
      ·
        refine ⟨52018091754690804487268753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34678727836460536324845835 52018091754690804487268753)
        ·
          refine ⟨39013568816018103365451565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52018091754690804487268753 39013568816018103365451565)
          ·
            refine ⟨14630088306006788762044337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39013568816018103365451565 14630088306006788762044337)
            ·
              refine ⟨10972566229505091571533253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14630088306006788762044337 10972566229505091571533253)
              ·
                refine ⟨2057356168032204669662485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10972566229505091571533253 2057356168032204669662485)
                ·
                  refine ⟨96438570376509593890429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2057356168032204669662485 96438570376509593890429)
                  ·
                    rfl

theorem cell23_1690321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 3, 2, 4, 6].length) (baseStart_1690321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690321 prefixEnd_1690321 := by exact prefixLift 1690321
  have htrace : WordTrace (prefixWord ++ tailWord_1690321) baseStart_1690321 baseEnd_1690321 := by
    simpa [prefixWord, tailWord_1690321, baseEnd_1690321] using wordTrace_append hprefix tailTrace_1690321
  have hstable : (prefixWord ++ tailWord_1690321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690321).length < 2 ^ (prefixWord ++ tailWord_1690321).sum := by decide
  have hdescent : baseEnd_1690321 < baseStart_1690321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690348 : List Nat := [2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 3]
def baseStart_1690348 : Nat := 118140960795 + 1690348 * 2 ^ 59
def prefixEnd_1690348 : Nat := 4983230072969 + 3 ^ 40 * 1690348 * 2
def baseEnd_1690348 : Nat := 867960997366257739376237

theorem tailTrace_1690348 : CollatzResearch.WordTrace tailWord_1690348 prefixEnd_1690348 867960997366257739376237 := by
  unfold tailWord_1690348
  simp only [CollatzResearch.WordTrace]
  refine ⟨30826028240082679649923849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41101370986776906199898465 30826028240082679649923849)
  ·
    refine ⟨23119521180062009737442887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30826028240082679649923849 23119521180062009737442887)
    ·
      refine ⟨34679281770093014606164331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23119521180062009737442887 34679281770093014606164331)
      ·
        refine ⟨52018922655139521909246497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34679281770093014606164331 52018922655139521909246497)
        ·
          refine ⟨39014191991354641431934873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52018922655139521909246497 39014191991354641431934873)
          ·
            refine ⟨29260643993515981073951155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39014191991354641431934873 29260643993515981073951155)
            ·
              refine ⟨43890965990273971610926733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29260643993515981073951155 43890965990273971610926733)
              ·
                refine ⟨16459112246352739354097525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43890965990273971610926733 16459112246352739354097525)
                ·
                  refine ⟨1543041773095569314446643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16459112246352739354097525 1543041773095569314446643)
                  ·
                    refine ⟨2314562659643353971669965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1543041773095569314446643 2314562659643353971669965)
                    ·
                      refine ⟨867960997366257739376237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2314562659643353971669965 867960997366257739376237)
                      ·
                        rfl

theorem cell23_1690348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 3].length) (baseStart_1690348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690348 prefixEnd_1690348 := by exact prefixLift 1690348
  have htrace : WordTrace (prefixWord ++ tailWord_1690348) baseStart_1690348 baseEnd_1690348 := by
    simpa [prefixWord, tailWord_1690348, baseEnd_1690348] using wordTrace_append hprefix tailTrace_1690348
  have hstable : (prefixWord ++ tailWord_1690348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690348).length < 2 ^ (prefixWord ++ tailWord_1690348).sum := by decide
  have hdescent : baseEnd_1690348 < baseStart_1690348 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690418 : List Nat := [3, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_1690418 : Nat := 118140960795 + 1690418 * 2 ^ 59
def prefixEnd_1690418 : Nat := 4983230072969 + 3 ^ 40 * 1690418 * 2
def baseEnd_1690418 : Nat := 867996941012072465500915

theorem tailTrace_1690418 : CollatzResearch.WordTrace tailWord_1690418 prefixEnd_1690418 867996941012072465500915 := by
  unfold tailWord_1690418
  simp only [CollatzResearch.WordTrace]
  refine ⟨15413652397477940313723977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41103073059941174169930605 15413652397477940313723977)
  ·
    refine ⟨11560239298108455235292983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15413652397477940313723977 11560239298108455235292983)
    ·
      refine ⟨17340358947162682852939475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11560239298108455235292983 17340358947162682852939475)
      ·
        refine ⟨26010538420744024279409213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17340358947162682852939475 26010538420744024279409213)
        ·
          refine ⟨9753951907779009104778455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26010538420744024279409213 9753951907779009104778455)
          ·
            refine ⟨14630927861668513657167683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9753951907779009104778455 14630927861668513657167683)
            ·
              refine ⟨21946391792502770485751525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14630927861668513657167683 21946391792502770485751525)
              ·
                refine ⟨4114948461094269466078411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21946391792502770485751525 4114948461094269466078411)
                ·
                  refine ⟨6172422691641404199117617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4114948461094269466078411 6172422691641404199117617)
                  ·
                    refine ⟨4629317018731053149338213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6172422691641404199117617 4629317018731053149338213)
                    ·
                      refine ⟨867996941012072465500915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4629317018731053149338213 867996941012072465500915)
                      ·
                        rfl

theorem cell23_1690418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_1690418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690418 prefixEnd_1690418 := by exact prefixLift 1690418
  have htrace : WordTrace (prefixWord ++ tailWord_1690418) baseStart_1690418 baseEnd_1690418 := by
    simpa [prefixWord, tailWord_1690418, baseEnd_1690418] using wordTrace_append hprefix tailTrace_1690418
  have hstable : (prefixWord ++ tailWord_1690418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690418).length < 2 ^ (prefixWord ++ tailWord_1690418).sum := by decide
  have hdescent : baseEnd_1690418 < baseStart_1690418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690451 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5]
def baseStart_1690451 : Nat := 118140960795 + 1690451 * 2 ^ 59
def prefixEnd_1690451 : Nat := 4983230072969 + 3 ^ 40 * 1690451 * 2
def baseEnd_1690451 : Nat := 868013885873670836388263

theorem tailTrace_1690451 : CollatzResearch.WordTrace tailWord_1690451 prefixEnd_1690451 868013885873670836388263 := by
  unfold tailWord_1690451
  simp only [CollatzResearch.WordTrace]
  refine ⟨61655813198792207890847207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41103875465861471927231471 61655813198792207890847207)
  ·
    refine ⟨92483719798188311836270811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61655813198792207890847207 92483719798188311836270811)
    ·
      refine ⟨138725579697282467754406217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92483719798188311836270811 138725579697282467754406217)
      ·
        refine ⟨104044184772961850815804663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138725579697282467754406217 104044184772961850815804663)
        ·
          refine ⟨156066277159442776223706995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104044184772961850815804663 156066277159442776223706995)
          ·
            refine ⟨234099415739164164335560493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156066277159442776223706995 234099415739164164335560493)
            ·
              refine ⟨87787280902186561625835185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 234099415739164164335560493 87787280902186561625835185)
              ·
                refine ⟨65840460676639921219376389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87787280902186561625835185 65840460676639921219376389)
                ·
                  refine ⟨12345086376869985228633073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65840460676639921219376389 12345086376869985228633073)
                  ·
                    refine ⟨9258814782652488921474805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12345086376869985228633073 9258814782652488921474805)
                    ·
                      refine ⟨868013885873670836388263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9258814782652488921474805 868013885873670836388263)
                      ·
                        rfl

theorem cell23_1690451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 4, 2, 5].length) (baseStart_1690451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690451 prefixEnd_1690451 := by exact prefixLift 1690451
  have htrace : WordTrace (prefixWord ++ tailWord_1690451) baseStart_1690451 baseEnd_1690451 := by
    simpa [prefixWord, tailWord_1690451, baseEnd_1690451] using wordTrace_append hprefix tailTrace_1690451
  have hstable : (prefixWord ++ tailWord_1690451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690451).length < 2 ^ (prefixWord ++ tailWord_1690451).sum := by decide
  have hdescent : baseEnd_1690451 < baseStart_1690451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690452 : List Nat := [2, 4, 1, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_1690452 : Nat := 118140960795 + 1690452 * 2 ^ 59
def prefixEnd_1690452 : Nat := 4983230072969 + 3 ^ 40 * 1690452 * 2
def baseEnd_1690452 : Nat := 868014399354325332475759

theorem tailTrace_1690452 : CollatzResearch.WordTrace tailWord_1690452 prefixEnd_1690452 868014399354325332475759 := by
  unfold tailWord_1690452
  simp only [CollatzResearch.WordTrace]
  refine ⟨30827924835894292530816805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41103899781192390041089073 30827924835894292530816805)
  ·
    refine ⟨5780235906730179849528151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30827924835894292530816805 5780235906730179849528151)
    ·
      refine ⟨8670353860095269774292227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5780235906730179849528151 8670353860095269774292227)
      ·
        refine ⟨13005530790142904661438341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8670353860095269774292227 13005530790142904661438341)
        ·
          refine ⟨2438537023151794624019689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13005530790142904661438341 2438537023151794624019689)
          ·
            refine ⟨1828902767363845968014767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2438537023151794624019689 1828902767363845968014767)
            ·
              refine ⟨2743354151045768952022151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1828902767363845968014767 2743354151045768952022151)
              ·
                refine ⟨4115031226568653428033227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743354151045768952022151 4115031226568653428033227)
                ·
                  refine ⟨6172546839852980142049841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115031226568653428033227 6172546839852980142049841)
                  ·
                    refine ⟨4629410129889735106537381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6172546839852980142049841 4629410129889735106537381)
                    ·
                      refine ⟨868014399354325332475759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4629410129889735106537381 868014399354325332475759)
                      ·
                        rfl

theorem cell23_1690452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_1690452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690452 prefixEnd_1690452 := by exact prefixLift 1690452
  have htrace : WordTrace (prefixWord ++ tailWord_1690452) baseStart_1690452 baseEnd_1690452 := by
    simpa [prefixWord, tailWord_1690452, baseEnd_1690452] using wordTrace_append hprefix tailTrace_1690452
  have hstable : (prefixWord ++ tailWord_1690452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690452).length < 2 ^ (prefixWord ++ tailWord_1690452).sum := by decide
  have hdescent : baseEnd_1690452 < baseStart_1690452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690455 : List Nat := [1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 3]
def baseStart_1690455 : Nat := 118140960795 + 1690455 * 2 ^ 59
def prefixEnd_1690455 : Nat := 4983230072969 + 3 ^ 40 * 1690455 * 2
def baseEnd_1690455 : Nat := 868015939796288820738245

theorem tailTrace_1690455 : CollatzResearch.WordTrace tailWord_1690455 prefixEnd_1690455 868015939796288820738245 := by
  unfold tailWord_1690455
  simp only [CollatzResearch.WordTrace]
  refine ⟨61655959090777716573992819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41103972727185144382661879 61655959090777716573992819)
  ·
    refine ⟨92483938636166574860989229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61655959090777716573992819 92483938636166574860989229)
    ·
      refine ⟨34681476988562465572870961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92483938636166574860989229 34681476988562465572870961)
      ·
        refine ⟨26011107741421849179653221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34681476988562465572870961 26011107741421849179653221)
        ·
          refine ⟨4877082701516596721184979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26011107741421849179653221 4877082701516596721184979)
          ·
            refine ⟨7315624052274895081777469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877082701516596721184979 7315624052274895081777469)
            ·
              refine ⟨2743359019603085655666551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7315624052274895081777469 2743359019603085655666551)
              ·
                refine ⟨4115038529404628483499827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743359019603085655666551 4115038529404628483499827)
                ·
                  refine ⟨6172557794106942725249741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115038529404628483499827 6172557794106942725249741)
                  ·
                    refine ⟨2314709172790103521968653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6172557794106942725249741 2314709172790103521968653)
                    ·
                      refine ⟨868015939796288820738245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2314709172790103521968653 868015939796288820738245)
                      ·
                        rfl

theorem cell23_1690455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 3, 3].length) (baseStart_1690455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690455 prefixEnd_1690455 := by exact prefixLift 1690455
  have htrace : WordTrace (prefixWord ++ tailWord_1690455) baseStart_1690455 baseEnd_1690455 := by
    simpa [prefixWord, tailWord_1690455, baseEnd_1690455] using wordTrace_append hprefix tailTrace_1690455
  have hstable : (prefixWord ++ tailWord_1690455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690455).length < 2 ^ (prefixWord ++ tailWord_1690455).sum := by decide
  have hdescent : baseEnd_1690455 < baseStart_1690455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690468 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_1690468 : Nat := 118140960795 + 1690468 * 2 ^ 59
def prefixEnd_1690468 : Nat := 4983230072969 + 3 ^ 40 * 1690468 * 2
def baseEnd_1690468 : Nat := 868022615044797269875685

theorem tailTrace_1690468 : CollatzResearch.WordTrace tailWord_1690468 prefixEnd_1690468 868022615044797269875685 := by
  unfold tailWord_1690468
  simp only [CollatzResearch.WordTrace]
  refine ⟨30828216619865309897108029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41104288826487079862810705 30828216619865309897108029)
  ·
    refine ⟨11560581232449491211415511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30828216619865309897108029 11560581232449491211415511)
    ·
      refine ⟨17340871848674236817123267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11560581232449491211415511 17340871848674236817123267)
      ·
        refine ⟨26011307773011355225684901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17340871848674236817123267 26011307773011355225684901)
        ·
          refine ⟨4877120207439629104815919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26011307773011355225684901 4877120207439629104815919)
          ·
            refine ⟨7315680311159443657223879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4877120207439629104815919 7315680311159443657223879)
            ·
              refine ⟨10973520466739165485835819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7315680311159443657223879 10973520466739165485835819)
              ·
                refine ⟨16460280700108748228753729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10973520466739165485835819 16460280700108748228753729)
                ·
                  refine ⟨12345210525081561171565297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16460280700108748228753729 12345210525081561171565297)
                  ·
                    refine ⟨9258907893811170878673973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12345210525081561171565297 9258907893811170878673973)
                    ·
                      refine ⟨868022615044797269875685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9258907893811170878673973 868022615044797269875685)
                      ·
                        rfl

theorem cell23_1690468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_1690468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690468 prefixEnd_1690468 := by exact prefixLift 1690468
  have htrace : WordTrace (prefixWord ++ tailWord_1690468) baseStart_1690468 baseEnd_1690468 := by
    simpa [prefixWord, tailWord_1690468, baseEnd_1690468] using wordTrace_append hprefix tailTrace_1690468
  have hstable : (prefixWord ++ tailWord_1690468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690468).length < 2 ^ (prefixWord ++ tailWord_1690468).sum := by decide
  have hdescent : baseEnd_1690468 < baseStart_1690468 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690482 : List Nat := [3, 2, 1, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_1690482 : Nat := 118140960795 + 1690482 * 2 ^ 59
def prefixEnd_1690482 : Nat := 4983230072969 + 3 ^ 40 * 1690482 * 2
def baseEnd_1690482 : Nat := 868029803773960215100621

theorem tailTrace_1690482 : CollatzResearch.WordTrace tailWord_1690482 prefixEnd_1690482 868029803773960215100621 := by
  unfold tailWord_1690482
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414235965419975046306425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41104629241119933456817133 15414235965419975046306425)
  ·
    refine ⟨11560676974064981284729819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15414235965419975046306425 11560676974064981284729819)
    ·
      refine ⟨17341015461097471927094729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11560676974064981284729819 17341015461097471927094729)
      ·
        refine ⟨13005761595823103945321047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17341015461097471927094729 13005761595823103945321047)
        ·
          refine ⟨19508642393734655917981571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13005761595823103945321047 19508642393734655917981571)
          ·
            refine ⟨29262963590601983876972357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19508642393734655917981571 29262963590601983876972357)
            ·
              refine ⟨5486805673237871976932317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29262963590601983876972357 5486805673237871976932317)
              ·
                refine ⟨2057552127464201991349619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5486805673237871976932317 2057552127464201991349619)
                ·
                  refine ⟨3086328191196302987024429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057552127464201991349619 3086328191196302987024429)
                  ·
                    refine ⟨1157373071698613620134161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3086328191196302987024429 1157373071698613620134161)
                    ·
                      refine ⟨868029803773960215100621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157373071698613620134161 868029803773960215100621)
                      ·
                        rfl

theorem cell23_1690482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_1690482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690482 prefixEnd_1690482 := by exact prefixLift 1690482
  have htrace : WordTrace (prefixWord ++ tailWord_1690482) baseStart_1690482 baseEnd_1690482 := by
    simpa [prefixWord, tailWord_1690482, baseEnd_1690482] using wordTrace_append hprefix tailTrace_1690482
  have hstable : (prefixWord ++ tailWord_1690482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690482).length < 2 ^ (prefixWord ++ tailWord_1690482).sum := by decide
  have hdescent : baseEnd_1690482 < baseStart_1690482 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690506 : List Nat := [3, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_1690506 : Nat := 118140960795 + 1690506 * 2 ^ 59
def prefixEnd_1690506 : Nat := 4983230072969 + 3 ^ 40 * 1690506 * 2
def baseEnd_1690506 : Nat := 868042127309668121200511

theorem tailTrace_1690506 : CollatzResearch.WordTrace tailWord_1690506 prefixEnd_1690506 868042127309668121200511 := by
  unfold tailWord_1690506
  simp only [CollatzResearch.WordTrace]
  refine ⟨15414454803398238071024843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41105212809061968189399581 15414454803398238071024843)
  ·
    refine ⟨23121682205097357106537265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15414454803398238071024843 23121682205097357106537265)
    ·
      refine ⟨17341261653823017829902949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23121682205097357106537265 17341261653823017829902949)
      ·
        refine ⟨3251486560091815843106803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17341261653823017829902949 3251486560091815843106803)
        ·
          refine ⟨4877229840137723764660205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251486560091815843106803 4877229840137723764660205)
          ·
            refine ⟨1828961190051646411747577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4877229840137723764660205 1828961190051646411747577)
            ·
              refine ⟨1371720892538734808810683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1828961190051646411747577 1371720892538734808810683)
              ·
                refine ⟨2057581338808102213216025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371720892538734808810683 2057581338808102213216025)
                ·
                  refine ⟨1543186004106076659912019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2057581338808102213216025 1543186004106076659912019)
                  ·
                    refine ⟨2314779006159114989868029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1543186004106076659912019 2314779006159114989868029)
                    ·
                      refine ⟨868042127309668121200511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2314779006159114989868029 868042127309668121200511)
                      ·
                        rfl

theorem cell23_1690506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_1690506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690506 prefixEnd_1690506 := by exact prefixLift 1690506
  have htrace : WordTrace (prefixWord ++ tailWord_1690506) baseStart_1690506 baseEnd_1690506 := by
    simpa [prefixWord, tailWord_1690506, baseEnd_1690506] using wordTrace_append hprefix tailTrace_1690506
  have hstable : (prefixWord ++ tailWord_1690506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690506).length < 2 ^ (prefixWord ++ tailWord_1690506).sum := by decide
  have hdescent : baseEnd_1690506 < baseStart_1690506 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690508 : List Nat := [2, 2, 1, 2, 1, 2, 2, 3, 2, 2, 4]
def baseStart_1690508 : Nat := 118140960795 + 1690508 * 2 ^ 59
def prefixEnd_1690508 : Nat := 4983230072969 + 3 ^ 40 * 1690508 * 2
def baseEnd_1690508 : Nat := 868043154270977113375501

theorem tailTrace_1690508 : CollatzResearch.WordTrace tailWord_1690508 prefixEnd_1690508 868043154270977113375501 := by
  unfold tailWord_1690508
  simp only [CollatzResearch.WordTrace]
  refine ⟨30828946079792853312836089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41105261439723804417114785 30828946079792853312836089)
  ·
    refine ⟨23121709559844639984627067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30828946079792853312836089 23121709559844639984627067)
    ·
      refine ⟨34682564339766959976940601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23121709559844639984627067 34682564339766959976940601)
      ·
        refine ⟨26011923254825219982705451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34682564339766959976940601 26011923254825219982705451)
        ·
          refine ⟨39017884882237829974058177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26011923254825219982705451 39017884882237829974058177)
          ·
            refine ⟨29263413661678372480543633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39017884882237829974058177 29263413661678372480543633)
            ·
              refine ⟨21947560246258779360407725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29263413661678372480543633 21947560246258779360407725)
              ·
                refine ⟨8230335092347042260152897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21947560246258779360407725 8230335092347042260152897)
                ·
                  refine ⟨6172751319260281695114673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8230335092347042260152897 6172751319260281695114673)
                  ·
                    refine ⟨4629563489445211271336005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6172751319260281695114673 4629563489445211271336005)
                    ·
                      refine ⟨868043154270977113375501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4629563489445211271336005 868043154270977113375501)
                      ·
                        rfl

theorem cell23_1690508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 3, 2, 2, 4].length) (baseStart_1690508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690508 prefixEnd_1690508 := by exact prefixLift 1690508
  have htrace : WordTrace (prefixWord ++ tailWord_1690508) baseStart_1690508 baseEnd_1690508 := by
    simpa [prefixWord, tailWord_1690508, baseEnd_1690508] using wordTrace_append hprefix tailTrace_1690508
  have hstable : (prefixWord ++ tailWord_1690508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690508).length < 2 ^ (prefixWord ++ tailWord_1690508).sum := by decide
  have hdescent : baseEnd_1690508 < baseStart_1690508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690552 : List Nat := [2, 1, 2, 1, 2, 4, 4, 2, 5]
def baseStart_1690552 : Nat := 118140960795 + 1690552 * 2 ^ 59
def prefixEnd_1690552 : Nat := 4983230072969 + 3 ^ 40 * 1690552 * 2
def baseEnd_1690552 : Nat := 96451749713308326802811

theorem tailTrace_1690552 : CollatzResearch.WordTrace tailWord_1690552 prefixEnd_1690552 96451749713308326802811 := by
  unfold tailWord_1690552
  simp only [CollatzResearch.WordTrace]
  refine ⟨30829748485713151070136955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41106331314284201426849273 30829748485713151070136955)
  ·
    refine ⟨46244622728569726605205433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30829748485713151070136955 46244622728569726605205433)
    ·
      refine ⟨34683467046427294953904075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46244622728569726605205433 34683467046427294953904075)
      ·
        refine ⟨52025200569640942430856113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34683467046427294953904075 52025200569640942430856113)
        ·
          refine ⟨39018900427230706823142085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52025200569640942430856113 39018900427230706823142085)
          ·
            refine ⟨7316043830105757529339141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39018900427230706823142085 7316043830105757529339141)
            ·
              refine ⟨1371758218144829536751089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7316043830105757529339141 1371758218144829536751089)
              ·
                refine ⟨1028818663608622152563317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371758218144829536751089 1028818663608622152563317)
                ·
                  refine ⟨96451749713308326802811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1028818663608622152563317 96451749713308326802811)
                  ·
                    rfl

theorem cell23_1690552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 4, 2, 5].length) (baseStart_1690552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690552 prefixEnd_1690552 := by exact prefixLift 1690552
  have htrace : WordTrace (prefixWord ++ tailWord_1690552) baseStart_1690552 baseEnd_1690552 := by
    simpa [prefixWord, tailWord_1690552, baseEnd_1690552] using wordTrace_append hprefix tailTrace_1690552
  have hstable : (prefixWord ++ tailWord_1690552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690552).length < 2 ^ (prefixWord ++ tailWord_1690552).sum := by decide
  have hdescent : baseEnd_1690552 < baseStart_1690552 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690582 : List Nat := [5, 2, 1, 1, 2, 2, 1, 1, 1, 7]
def baseStart_1690582 : Nat := 118140960795 + 1690582 * 2 ^ 59
def prefixEnd_1690582 : Nat := 4983230072969 + 3 ^ 40 * 1690582 * 2
def baseEnd_1690582 : Nat := 289360383946469941283387

theorem tailTrace_1690582 : CollatzResearch.WordTrace tailWord_1690582 prefixEnd_1690582 289360383946469941283387 := by
  unfold tailWord_1690582
  simp only [CollatzResearch.WordTrace]
  refine ⟨3853786947582351078991625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41107060774211744842577333 3853786947582351078991625)
  ·
    refine ⟨2890340210686763309243719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3853786947582351078991625 2890340210686763309243719)
    ·
      refine ⟨4335510316030144963865579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2890340210686763309243719 4335510316030144963865579)
      ·
        refine ⟨6503265474045217445798369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4335510316030144963865579 6503265474045217445798369)
        ·
          refine ⟨4877449105533913084348777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6503265474045217445798369 4877449105533913084348777)
          ·
            refine ⟨3658086829150434813261583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4877449105533913084348777 3658086829150434813261583)
            ·
              refine ⟨5487130243725652219892375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658086829150434813261583 5487130243725652219892375)
              ·
                refine ⟨8230695365588478329838563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487130243725652219892375 8230695365588478329838563)
                ·
                  refine ⟨12346043048382717494757845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8230695365588478329838563 12346043048382717494757845)
                  ·
                    refine ⟨289360383946469941283387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12346043048382717494757845 289360383946469941283387)
                    ·
                      rfl

theorem cell23_1690582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_1690582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690582 prefixEnd_1690582 := by exact prefixLift 1690582
  have htrace : WordTrace (prefixWord ++ tailWord_1690582) baseStart_1690582 baseEnd_1690582 := by
    simpa [prefixWord, tailWord_1690582, baseEnd_1690582] using wordTrace_append hprefix tailTrace_1690582
  have hstable : (prefixWord ++ tailWord_1690582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690582).length < 2 ^ (prefixWord ++ tailWord_1690582).sum := by decide
  have hdescent : baseEnd_1690582 < baseStart_1690582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690585 : List Nat := [1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 4]
def baseStart_1690585 : Nat := 118140960795 + 1690585 * 2 ^ 59
def prefixEnd_1690585 : Nat := 4983230072969 + 3 ^ 40 * 1690585 * 2
def baseEnd_1690585 : Nat := 868082692281373312112647

theorem tailTrace_1690585 : CollatzResearch.WordTrace tailWord_1690585 prefixEnd_1690585 868082692281373312112647 := by
  unfold tailWord_1690585
  simp only [CollatzResearch.WordTrace]
  refine ⟨61660700580306748776225209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41107133720204499184150139 61660700580306748776225209)
  ·
    refine ⟨46245525435230061582168907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61660700580306748776225209 46245525435230061582168907)
    ·
      refine ⟨69368288152845092373253361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46245525435230061582168907 69368288152845092373253361)
      ·
        refine ⟨52026216114633819279940021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69368288152845092373253361 52026216114633819279940021)
        ·
          refine ⟨4877457760746920557494377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 52026216114633819279940021 4877457760746920557494377)
          ·
            refine ⟨3658093320560190418120783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4877457760746920557494377 3658093320560190418120783)
            ·
              refine ⟨5487139980840285627181175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658093320560190418120783 5487139980840285627181175)
              ·
                refine ⟨8230709971260428440771763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5487139980840285627181175 8230709971260428440771763)
                ·
                  refine ⟨12346064956890642661157645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8230709971260428440771763 12346064956890642661157645)
                  ·
                    refine ⟨4629774358833990997934117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12346064956890642661157645 4629774358833990997934117)
                    ·
                      refine ⟨868082692281373312112647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4629774358833990997934117 868082692281373312112647)
                      ·
                        rfl

theorem cell23_1690585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 3, 4].length) (baseStart_1690585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690585 prefixEnd_1690585 := by exact prefixLift 1690585
  have htrace : WordTrace (prefixWord ++ tailWord_1690585) baseStart_1690585 baseEnd_1690585 := by
    simpa [prefixWord, tailWord_1690585, baseEnd_1690585] using wordTrace_append hprefix tailTrace_1690585
  have hstable : (prefixWord ++ tailWord_1690585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690585).length < 2 ^ (prefixWord ++ tailWord_1690585).sum := by decide
  have hdescent : baseEnd_1690585 < baseStart_1690585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690595 : List Nat := [1, 1, 1, 6, 1, 1, 1, 2, 5, 4]
def baseStart_1690595 : Nat := 118140960795 + 1690595 * 2 ^ 59
def prefixEnd_1690595 : Nat := 4983230072969 + 3 ^ 40 * 1690595 * 2
def baseEnd_1690595 : Nat := 289362609029306090995867

theorem tailTrace_1690595 : CollatzResearch.WordTrace tailWord_1690595 prefixEnd_1690595 289362609029306090995867 := by
  unfold tailWord_1690595
  simp only [CollatzResearch.WordTrace]
  refine ⟨61661065310270520484089239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41107376873513680322726159 61661065310270520484089239)
  ·
    refine ⟨92491597965405780726133859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61661065310270520484089239 92491597965405780726133859)
    ·
      refine ⟨138737396948108671089200789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92491597965405780726133859 138737396948108671089200789)
      ·
        refine ⟨6503315481942593957306287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138737396948108671089200789 6503315481942593957306287)
        ·
          refine ⟨9754973222913890935959431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6503315481942593957306287 9754973222913890935959431)
          ·
            refine ⟨14632459834370836403939147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9754973222913890935959431 14632459834370836403939147)
            ·
              refine ⟨21948689751556254605908721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14632459834370836403939147 21948689751556254605908721)
              ·
                refine ⟨16461517313667190954431541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21948689751556254605908721 16461517313667190954431541)
                ·
                  refine ⟨1543267248156299151977957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16461517313667190954431541 1543267248156299151977957)
                  ·
                    refine ⟨289362609029306090995867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1543267248156299151977957 289362609029306090995867)
                    ·
                      rfl

theorem cell23_1690595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 2, 5, 4].length) (baseStart_1690595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690595 prefixEnd_1690595 := by exact prefixLift 1690595
  have htrace : WordTrace (prefixWord ++ tailWord_1690595) baseStart_1690595 baseEnd_1690595 := by
    simpa [prefixWord, tailWord_1690595, baseEnd_1690595] using wordTrace_append hprefix tailTrace_1690595
  have hstable : (prefixWord ++ tailWord_1690595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690595).length < 2 ^ (prefixWord ++ tailWord_1690595).sum := by decide
  have hdescent : baseEnd_1690595 < baseStart_1690595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690602 : List Nat := [3, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_1690602 : Nat := 118140960795 + 1690602 * 2 ^ 59
def prefixEnd_1690602 : Nat := 4983230072969 + 3 ^ 40 * 1690602 * 2
def baseEnd_1690602 : Nat := 868091421452499745600069

theorem tailTrace_1690602 : CollatzResearch.WordTrace tailWord_1690602 prefixEnd_1690602 868091421452499745600069 := by
  unfold tailWord_1690602
  simp only [CollatzResearch.WordTrace]
  refine ⟨15415330155311290169898515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41107547080830107119729373 15415330155311290169898515)
  ·
    refine ⟨23122995232966935254847773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15415330155311290169898515 23122995232966935254847773)
    ·
      refine ⟨8671123212362600720567915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23122995232966935254847773 8671123212362600720567915)
      ·
        refine ⟨13006684818543901080851873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8671123212362600720567915 13006684818543901080851873)
        ·
          refine ⟨9755013613907925810638905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13006684818543901080851873 9755013613907925810638905)
          ·
            refine ⟨7316260210430944357979179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9755013613907925810638905 7316260210430944357979179)
            ·
              refine ⟨10974390315646416536968769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7316260210430944357979179 10974390315646416536968769)
              ·
                refine ⟨8230792736734812402726577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10974390315646416536968769 8230792736734812402726577)
                ·
                  refine ⟨6173094552551109302044933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8230792736734812402726577 6173094552551109302044933)
                  ·
                    refine ⟨1157455228603332994133425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173094552551109302044933 1157455228603332994133425)
                    ·
                      refine ⟨868091421452499745600069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157455228603332994133425 868091421452499745600069)
                      ·
                        rfl

theorem cell23_1690602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_1690602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690602 prefixEnd_1690602 := by exact prefixLift 1690602
  have htrace : WordTrace (prefixWord ++ tailWord_1690602) baseStart_1690602 baseEnd_1690602 := by
    simpa [prefixWord, tailWord_1690602, baseEnd_1690602] using wordTrace_append hprefix tailTrace_1690602
  have hstable : (prefixWord ++ tailWord_1690602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690602).length < 2 ^ (prefixWord ++ tailWord_1690602).sum := by decide
  have hdescent : baseEnd_1690602 < baseStart_1690602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690663 : List Nat := [1, 1, 7, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1690663 : Nat := 118140960795 + 1690663 * 2 ^ 59
def prefixEnd_1690663 : Nat := 4983230072969 + 3 ^ 40 * 1690663 * 2
def baseEnd_1690663 : Nat := 289374247924141335645763

theorem tailTrace_1690663 : CollatzResearch.WordTrace tailWord_1690663 prefixEnd_1690663 289374247924141335645763 := by
  unfold tailWord_1690663
  simp only [CollatzResearch.WordTrace]
  refine ⟨61663545474024168097564643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41109030316016112065043095 61663545474024168097564643)
  ·
    refine ⟨92495318211036252146346965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61663545474024168097564643 92495318211036252146346965)
    ·
      refine ⟨2167859020571162159680007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 92495318211036252146346965 2167859020571162159680007)
      ·
        refine ⟨3251788530856743239520011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2167859020571162159680007 3251788530856743239520011)
        ·
          refine ⟨4877682796285114859280017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251788530856743239520011 4877682796285114859280017)
          ·
            refine ⟨3658262097213836144460013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4877682796285114859280017 3658262097213836144460013)
            ·
              refine ⟨1371848286455188554172505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3658262097213836144460013 1371848286455188554172505)
              ·
                refine ⟨1028886214841391415629379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1371848286455188554172505 1028886214841391415629379)
                ·
                  refine ⟨1543329322262087123444069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028886214841391415629379 1543329322262087123444069)
                  ·
                    refine ⟨289374247924141335645763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1543329322262087123444069 289374247924141335645763)
                    ·
                      rfl

theorem cell23_1690663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1690663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690663 prefixEnd_1690663 := by exact prefixLift 1690663
  have htrace : WordTrace (prefixWord ++ tailWord_1690663) baseStart_1690663 baseEnd_1690663 := by
    simpa [prefixWord, tailWord_1690663, baseEnd_1690663] using wordTrace_append hprefix tailTrace_1690663
  have hstable : (prefixWord ++ tailWord_1690663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690663).length < 2 ^ (prefixWord ++ tailWord_1690663).sum := by decide
  have hdescent : baseEnd_1690663 < baseStart_1690663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690675 : List Nat := [1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 4]
def baseStart_1690675 : Nat := 118140960795 + 1690675 * 2 ^ 59
def prefixEnd_1690675 : Nat := 4983230072969 + 3 ^ 40 * 1690675 * 2
def baseEnd_1690675 : Nat := 868128905540277959987233

theorem tailTrace_1690675 : CollatzResearch.WordTrace tailWord_1690675 prefixEnd_1690675 868128905540277959987233 := by
  unfold tailWord_1690675
  simp only [CollatzResearch.WordTrace]
  refine ⟨61663983149980694147001479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41109322099987129431334319 61663983149980694147001479)
  ·
    refine ⟨92495974724971041220502219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61663983149980694147001479 92495974724971041220502219)
    ·
      refine ⟨138743962087456561830753329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92495974724971041220502219 138743962087456561830753329)
      ·
        refine ⟨104057971565592421373064997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138743962087456561830753329 104057971565592421373064997)
        ·
          refine ⟨19510869668548579007449687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 104057971565592421373064997 19510869668548579007449687)
          ·
            refine ⟨29266304502822868511174531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19510869668548579007449687 29266304502822868511174531)
            ·
              refine ⟨43899456754234302766761797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29266304502822868511174531 43899456754234302766761797)
              ·
                refine ⟨8231148141418931768767837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43899456754234302766761797 8231148141418931768767837)
                ·
                  refine ⟨3086680553032099413287939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8231148141418931768767837 3086680553032099413287939)
                  ·
                    refine ⟨4630020829548149119931909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3086680553032099413287939 4630020829548149119931909)
                    ·
                      refine ⟨868128905540277959987233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4630020829548149119931909 868128905540277959987233)
                      ·
                        rfl

theorem cell23_1690675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 1, 4].length) (baseStart_1690675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690675 prefixEnd_1690675 := by exact prefixLift 1690675
  have htrace : WordTrace (prefixWord ++ tailWord_1690675) baseStart_1690675 baseEnd_1690675 := by
    simpa [prefixWord, tailWord_1690675, baseEnd_1690675] using wordTrace_append hprefix tailTrace_1690675
  have hstable : (prefixWord ++ tailWord_1690675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690675).length < 2 ^ (prefixWord ++ tailWord_1690675).sum := by decide
  have hdescent : baseEnd_1690675 < baseStart_1690675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690676 : List Nat := [2, 5, 1, 2, 1, 3, 2, 1, 6]
def baseStart_1690676 : Nat := 118140960795 + 1690676 * 2 ^ 59
def prefixEnd_1690676 : Nat := 4983230072969 + 3 ^ 40 * 1690676 * 2
def baseEnd_1690676 : Nat := 96458824335659161786081

theorem tailTrace_1690676 : CollatzResearch.WordTrace tailWord_1690676 prefixEnd_1690676 96458824335659161786081 := by
  unfold tailWord_1690676
  simp only [CollatzResearch.WordTrace]
  refine ⟨30832009811488535658893941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41109346415318047545191921 30832009811488535658893941)
  ·
    refine ⟨2890500919827050218021307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30832009811488535658893941 2890500919827050218021307)
    ·
      refine ⟨4335751379740575327031961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2890500919827050218021307 4335751379740575327031961)
      ·
        refine ⟨3251813534805431495273971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4335751379740575327031961 3251813534805431495273971)
        ·
          refine ⟨4877720302208147242910957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3251813534805431495273971 4877720302208147242910957)
          ·
            refine ⟨1829145113328055216091609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4877720302208147242910957 1829145113328055216091609)
            ·
              refine ⟨1371858834996041412068707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829145113328055216091609 1371858834996041412068707)
              ·
                refine ⟨2057788252494062118103061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371858834996041412068707 2057788252494062118103061)
                ·
                  refine ⟨96458824335659161786081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2057788252494062118103061 96458824335659161786081)
                  ·
                    rfl

theorem cell23_1690676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_1690676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690676 prefixEnd_1690676 := by exact prefixLift 1690676
  have htrace : WordTrace (prefixWord ++ tailWord_1690676) baseStart_1690676 baseEnd_1690676 := by
    simpa [prefixWord, tailWord_1690676, baseEnd_1690676] using wordTrace_append hprefix tailTrace_1690676
  have hstable : (prefixWord ++ tailWord_1690676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690676).length < 2 ^ (prefixWord ++ tailWord_1690676).sum := by decide
  have hdescent : baseEnd_1690676 < baseStart_1690676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690705 : List Nat := [1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 4]
def baseStart_1690705 : Nat := 118140960795 + 1690705 * 2 ^ 59
def prefixEnd_1690705 : Nat := 4983230072969 + 3 ^ 40 * 1690705 * 2
def baseEnd_1690705 : Nat := 868144309959912842612095

theorem tailTrace_1690705 : CollatzResearch.WordTrace tailWord_1690705 prefixEnd_1690705 868144309959912842612095 := by
  unfold tailWord_1690705
  simp only [CollatzResearch.WordTrace]
  refine ⟨61665077339872009270593569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41110051559914672847062379 61665077339872009270593569)
  ·
    refine ⟨46248808004904006952945177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61665077339872009270593569 46248808004904006952945177)
    ·
      refine ⟨34686606003678005214708883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46248808004904006952945177 34686606003678005214708883)
      ·
        refine ⟨52029909005517007822063325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34686606003678005214708883 52029909005517007822063325)
        ·
          refine ⟨19511215877068877933273747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52029909005517007822063325 19511215877068877933273747)
          ·
            refine ⟨29266823815603316899910621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19511215877068877933273747 29266823815603316899910621)
            ·
              refine ⟨10975058930851243837466483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29266823815603316899910621 10975058930851243837466483)
              ·
                refine ⟨16462588396276865756199725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10975058930851243837466483 16462588396276865756199725)
                ·
                  refine ⟨6173470648603824658574897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16462588396276865756199725 6173470648603824658574897)
                  ·
                    refine ⟨4630102986452868493931173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6173470648603824658574897 4630102986452868493931173)
                    ·
                      refine ⟨868144309959912842612095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4630102986452868493931173 868144309959912842612095)
                      ·
                        rfl

theorem cell23_1690705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 3, 1, 3, 2, 4].length) (baseStart_1690705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690705 prefixEnd_1690705 := by exact prefixLift 1690705
  have htrace : WordTrace (prefixWord ++ tailWord_1690705) baseStart_1690705 baseEnd_1690705 := by
    simpa [prefixWord, tailWord_1690705, baseEnd_1690705] using wordTrace_append hprefix tailTrace_1690705
  have hstable : (prefixWord ++ tailWord_1690705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690705).length < 2 ^ (prefixWord ++ tailWord_1690705).sum := by decide
  have hdescent : baseEnd_1690705 < baseStart_1690705 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690709 : List Nat := [1, 3, 2, 2, 1, 2, 5, 1, 1, 1, 4]
def baseStart_1690709 : Nat := 118140960795 + 1690709 * 2 ^ 59
def prefixEnd_1690709 : Nat := 4983230072969 + 3 ^ 40 * 1690709 * 2
def baseEnd_1690709 : Nat := 868146363882530826962077

theorem tailTrace_1690709 : CollatzResearch.WordTrace tailWord_1690709 prefixEnd_1690709 868146363882530826962077 := by
  unfold tailWord_1690709
  simp only [CollatzResearch.WordTrace]
  refine ⟨61665223231857517953739181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41110148821238345302492787 61665223231857517953739181)
  ·
    refine ⟨23124458711946569232652193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61665223231857517953739181 23124458711946569232652193)
    ·
      refine ⟨17343344033959926924489145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23124458711946569232652193 17343344033959926924489145)
      ·
        refine ⟨13007508025469945193366859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17343344033959926924489145 13007508025469945193366859)
        ·
          refine ⟨19511262038204917790050289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13007508025469945193366859 19511262038204917790050289)
          ·
            refine ⟨14633446528653688342537717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19511262038204917790050289 14633446528653688342537717)
            ·
              refine ⟨1371885612061283282112911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14633446528653688342537717 1371885612061283282112911)
              ·
                refine ⟨2057828418091924923169367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1371885612061283282112911 2057828418091924923169367)
                ·
                  refine ⟨3086742627137887384754051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2057828418091924923169367 3086742627137887384754051)
                  ·
                    refine ⟨4630113940706831077131077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3086742627137887384754051 4630113940706831077131077)
                    ·
                      refine ⟨868146363882530826962077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4630113940706831077131077 868146363882530826962077)
                      ·
                        rfl

theorem cell23_1690709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 5, 1, 1, 1, 4].length) (baseStart_1690709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690709 prefixEnd_1690709 := by exact prefixLift 1690709
  have htrace : WordTrace (prefixWord ++ tailWord_1690709) baseStart_1690709 baseEnd_1690709 := by
    simpa [prefixWord, tailWord_1690709, baseEnd_1690709] using wordTrace_append hprefix tailTrace_1690709
  have hstable : (prefixWord ++ tailWord_1690709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690709).length < 2 ^ (prefixWord ++ tailWord_1690709).sum := by decide
  have hdescent : baseEnd_1690709 < baseStart_1690709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690755 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5]
def baseStart_1690755 : Nat := 118140960795 + 1690755 * 2 ^ 59
def prefixEnd_1690755 : Nat := 4983230072969 + 3 ^ 40 * 1690755 * 2
def baseEnd_1690755 : Nat := 868169983992637646986865

theorem tailTrace_1690755 : CollatzResearch.WordTrace tailWord_1690755 prefixEnd_1690755 868169983992637646986865 := by
  unfold tailWord_1690755
  simp only [CollatzResearch.WordTrace]
  refine ⟨61666900989690867809913719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41111267326460578539942479 61666900989690867809913719)
  ·
    refine ⟨92500351484536301714870579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61666900989690867809913719 92500351484536301714870579)
    ·
      refine ⟨138750527226804452572305869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92500351484536301714870579 138750527226804452572305869)
      ·
        refine ⟨52031447710051669714614701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138750527226804452572305869 52031447710051669714614701)
        ·
          refine ⟨19511792891269376142980513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52031447710051669714614701 19511792891269376142980513)
          ·
            refine ⟨14633844668452032107235385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19511792891269376142980513 14633844668452032107235385)
            ·
              refine ⟨10975383501339024080426539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14633844668452032107235385 10975383501339024080426539)
              ·
                refine ⟨16463075252008536120639809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10975383501339024080426539 16463075252008536120639809)
                ·
                  refine ⟨12347306439006402090479857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16463075252008536120639809 12347306439006402090479857)
                  ·
                    refine ⟨9260479829254801567859893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12347306439006402090479857 9260479829254801567859893)
                    ·
                      refine ⟨868169983992637646986865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9260479829254801567859893 868169983992637646986865)
                      ·
                        rfl

theorem cell23_1690755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 2, 5].length) (baseStart_1690755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690755 prefixEnd_1690755 := by exact prefixLift 1690755
  have htrace : WordTrace (prefixWord ++ tailWord_1690755) baseStart_1690755 baseEnd_1690755 := by
    simpa [prefixWord, tailWord_1690755, baseEnd_1690755] using wordTrace_append hprefix tailTrace_1690755
  have hstable : (prefixWord ++ tailWord_1690755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690755).length < 2 ^ (prefixWord ++ tailWord_1690755).sum := by decide
  have hdescent : baseEnd_1690755 < baseStart_1690755 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690760 : List Nat := [2, 1, 3, 4, 2, 1, 2, 3, 1, 2, 2]
def baseStart_1690760 : Nat := 118140960795 + 1690760 * 2 ^ 59
def prefixEnd_1690760 : Nat := 4983230072969 + 3 ^ 40 * 1690760 * 2
def baseEnd_1690760 : Nat := 868172551395910127424343

theorem tailTrace_1690760 : CollatzResearch.WordTrace tailWord_1690760 prefixEnd_1690760 868172551395910127424343 := by
  unfold tailWord_1690760
  simp only [CollatzResearch.WordTrace]
  refine ⟨30833541677336376831922867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41111388903115169109230489 30833541677336376831922867)
  ·
    refine ⟨46250312516004565247884301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30833541677336376831922867 46250312516004565247884301)
    ·
      refine ⟨17343867193501711967956613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46250312516004565247884301 17343867193501711967956613)
      ·
        refine ⟨3251975098781570993991865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17343867193501711967956613 3251975098781570993991865)
        ·
          refine ⟨2438981324086178245493899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3251975098781570993991865 2438981324086178245493899)
          ·
            refine ⟨3658471986129267368240849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2438981324086178245493899 3658471986129267368240849)
            ·
              refine ⟨2743853989596950526180637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3658471986129267368240849 2743853989596950526180637)
              ·
                refine ⟨1028945246098856447317739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2743853989596950526180637 1028945246098856447317739)
                ·
                  refine ⟨1543417869148284670976609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1028945246098856447317739 1543417869148284670976609)
                  ·
                    refine ⟨1157563401861213503232457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1543417869148284670976609 1157563401861213503232457)
                    ·
                      refine ⟨868172551395910127424343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157563401861213503232457 868172551395910127424343)
                      ·
                        rfl

theorem cell23_1690760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 1, 2, 2].length) (baseStart_1690760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690760 prefixEnd_1690760 := by exact prefixLift 1690760
  have htrace : WordTrace (prefixWord ++ tailWord_1690760) baseStart_1690760 baseEnd_1690760 := by
    simpa [prefixWord, tailWord_1690760, baseEnd_1690760] using wordTrace_append hprefix tailTrace_1690760
  have hstable : (prefixWord ++ tailWord_1690760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690760).length < 2 ^ (prefixWord ++ tailWord_1690760).sum := by decide
  have hdescent : baseEnd_1690760 < baseStart_1690760 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690776 : List Nat := [2, 1, 2, 4, 2, 1, 3, 2, 2, 1, 3]
def baseStart_1690776 : Nat := 118140960795 + 1690776 * 2 ^ 59
def prefixEnd_1690776 : Nat := 4983230072969 + 3 ^ 40 * 1690776 * 2
def baseEnd_1690776 : Nat := 868180767086382064824269

theorem tailTrace_1690776 : CollatzResearch.WordTrace tailWord_1690776 prefixEnd_1690776 868180767086382064824269 := by
  unfold tailWord_1690776
  simp only [CollatzResearch.WordTrace]
  refine ⟨30833833461307394198214091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41111777948409858930952121 30833833461307394198214091)
  ·
    refine ⟨46250750191961091297321137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30833833461307394198214091 46250750191961091297321137)
    ·
      refine ⟨34688062643970818472990853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46250750191961091297321137 34688062643970818472990853)
      ·
        refine ⟨6504011745744528463685785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34688062643970818472990853 6504011745744528463685785)
        ·
          refine ⟨4878008809308396347764339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6504011745744528463685785 4878008809308396347764339)
          ·
            refine ⟨7317013213962594521646509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4878008809308396347764339 7317013213962594521646509)
            ·
              refine ⟨2743879955235972945617441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7317013213962594521646509 2743879955235972945617441)
              ·
                refine ⟨2057909966426979709213081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2743879955235972945617441 2057909966426979709213081)
                ·
                  refine ⟨1543432474820234781909811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2057909966426979709213081 1543432474820234781909811)
                  ·
                    refine ⟨2315148712230352172864717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1543432474820234781909811 2315148712230352172864717)
                    ·
                      refine ⟨868180767086382064824269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2315148712230352172864717 868180767086382064824269)
                      ·
                        rfl

theorem cell23_1690776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_1690776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690776 prefixEnd_1690776 := by exact prefixLift 1690776
  have htrace : WordTrace (prefixWord ++ tailWord_1690776) baseStart_1690776 baseEnd_1690776 := by
    simpa [prefixWord, tailWord_1690776, baseEnd_1690776] using wordTrace_append hprefix tailTrace_1690776
  have hstable : (prefixWord ++ tailWord_1690776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690776).length < 2 ^ (prefixWord ++ tailWord_1690776).sum := by decide
  have hdescent : baseEnd_1690776 < baseStart_1690776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690799 : List Nat := [1, 1, 2, 1, 2, 3, 5, 1, 1, 4, 2]
def baseStart_1690799 : Nat := 118140960795 + 1690799 * 2 ^ 59
def prefixEnd_1690799 : Nat := 4983230072969 + 3 ^ 40 * 1690799 * 2
def baseEnd_1690799 : Nat := 868192577141435474836663

theorem tailTrace_1690799 : CollatzResearch.WordTrace tailWord_1690799 prefixEnd_1690799 868192577141435474836663 := by
  unfold tailWord_1690799
  simp only [CollatzResearch.WordTrace]
  refine ⟨61668505801531463324515451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41112337201020975549676967 61668505801531463324515451)
  ·
    refine ⟨92502758702297194986773177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61668505801531463324515451 92502758702297194986773177)
    ·
      refine ⟨69377069026722896240079883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92502758702297194986773177 69377069026722896240079883)
      ·
        refine ⟨104065603540084344360119825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69377069026722896240079883 104065603540084344360119825)
        ·
          refine ⟨78049202655063258270089869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104065603540084344360119825 78049202655063258270089869)
          ·
            refine ⟨29268450995648721851283701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78049202655063258270089869 29268450995648721851283701)
            ·
              refine ⟨2743917280842067673557847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29268450995648721851283701 2743917280842067673557847)
              ·
                refine ⟨4115875921263101510336771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2743917280842067673557847 4115875921263101510336771)
                ·
                  refine ⟨6173813881894652265505157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4115875921263101510336771 6173813881894652265505157)
                  ·
                    refine ⟨1157590102855247299782217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6173813881894652265505157 1157590102855247299782217)
                    ·
                      refine ⟨868192577141435474836663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157590102855247299782217 868192577141435474836663)
                      ·
                        rfl

theorem cell23_1690799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 5, 1, 1, 4, 2].length) (baseStart_1690799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690799 prefixEnd_1690799 := by exact prefixLift 1690799
  have htrace : WordTrace (prefixWord ++ tailWord_1690799) baseStart_1690799 baseEnd_1690799 := by
    simpa [prefixWord, tailWord_1690799, baseEnd_1690799] using wordTrace_append hprefix tailTrace_1690799
  have hstable : (prefixWord ++ tailWord_1690799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690799).length < 2 ^ (prefixWord ++ tailWord_1690799).sum := by decide
  have hdescent : baseEnd_1690799 < baseStart_1690799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690875 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11]
def baseStart_1690875 : Nat := 118140960795 + 1690875 * 2 ^ 59
def prefixEnd_1690875 : Nat := 4983230072969 + 3 ^ 40 * 1690875 * 2
def baseEnd_1690875 : Nat := 868231601671177177486313

theorem tailTrace_1690875 : CollatzResearch.WordTrace tailWord_1690875 prefixEnd_1690875 868231601671177177486313 := by
  unfold tailWord_1690875
  simp only [CollatzResearch.WordTrace]
  refine ⟨61671277749256128304282079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41114185166170752202854719 61671277749256128304282079)
  ·
    refine ⟨92506916623884192456423119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61671277749256128304282079 92506916623884192456423119)
    ·
      refine ⟨138760374935826288684634679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92506916623884192456423119 138760374935826288684634679)
      ·
        refine ⟨208140562403739433026952019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 138760374935826288684634679 208140562403739433026952019)
        ·
          refine ⟨312210843605609149540428029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 208140562403739433026952019 312210843605609149540428029)
          ·
            refine ⟨117079066352103431077660511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 312210843605609149540428029 117079066352103431077660511)
            ·
              refine ⟨175618599528155146616490767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 117079066352103431077660511 175618599528155146616490767)
              ·
                refine ⟨263427899292232719924736151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175618599528155146616490767 263427899292232719924736151)
                ·
                  refine ⟨395141848938349079887104227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 263427899292232719924736151 395141848938349079887104227)
                  ·
                    refine ⟨592712773407523619830656341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 395141848938349079887104227 592712773407523619830656341)
                    ·
                      refine ⟨868231601671177177486313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 11 592712773407523619830656341 868231601671177177486313)
                      ·
                        rfl

theorem cell23_1690875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 11].length) (baseStart_1690875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690875 prefixEnd_1690875 := by exact prefixLift 1690875
  have htrace : WordTrace (prefixWord ++ tailWord_1690875) baseStart_1690875 baseEnd_1690875 := by
    simpa [prefixWord, tailWord_1690875, baseEnd_1690875] using wordTrace_append hprefix tailTrace_1690875
  have hstable : (prefixWord ++ tailWord_1690875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690875).length < 2 ^ (prefixWord ++ tailWord_1690875).sum := by decide
  have hdescent : baseEnd_1690875 < baseStart_1690875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690889 : List Nat := [1, 2, 1, 1, 3, 3, 2, 2, 2, 4, 2]
def baseStart_1690889 : Nat := 118140960795 + 1690889 * 2 ^ 59
def prefixEnd_1690889 : Nat := 4983230072969 + 3 ^ 40 * 1690889 * 2
def baseEnd_1690889 : Nat := 868238790400340122711249

theorem tailTrace_1690889 : CollatzResearch.WordTrace tailWord_1690889 prefixEnd_1690889 868238790400340122711249 := by
  unfold tailWord_1690889
  simp only [CollatzResearch.WordTrace]
  refine ⟨61671788371205408695291721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41114525580803605796861147 61671788371205408695291721)
  ·
    refine ⟨46253841278404056521468791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61671788371205408695291721 46253841278404056521468791)
    ·
      refine ⟨69380761917606084782203187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46253841278404056521468791 69380761917606084782203187)
      ·
        refine ⟨104071142876409127173304781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69380761917606084782203187 104071142876409127173304781)
        ·
          refine ⟨39026678578653422689989293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104071142876409127173304781 39026678578653422689989293)
          ·
            refine ⟨14635004466995033508745985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39026678578653422689989293 14635004466995033508745985)
            ·
              refine ⟨10976253350246275131559489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14635004466995033508745985 10976253350246275131559489)
              ·
                refine ⟨8232190012684706348669617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10976253350246275131559489 8232190012684706348669617)
                ·
                  refine ⟨6174142509513529761502213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8232190012684706348669617 6174142509513529761502213)
                  ·
                    refine ⟨1157651720533786830281665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6174142509513529761502213 1157651720533786830281665)
                    ·
                      refine ⟨868238790400340122711249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157651720533786830281665 868238790400340122711249)
                      ·
                        rfl

theorem cell23_1690889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 4, 2].length) (baseStart_1690889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690889 prefixEnd_1690889 := by exact prefixLift 1690889
  have htrace : WordTrace (prefixWord ++ tailWord_1690889) baseStart_1690889 baseEnd_1690889 := by
    simpa [prefixWord, tailWord_1690889, baseEnd_1690889] using wordTrace_append hprefix tailTrace_1690889
  have hstable : (prefixWord ++ tailWord_1690889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690889).length < 2 ^ (prefixWord ++ tailWord_1690889).sum := by decide
  have hdescent : baseEnd_1690889 < baseStart_1690889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690906 : List Nat := [3, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2]
def baseStart_1690906 : Nat := 118140960795 + 1690906 * 2 ^ 59
def prefixEnd_1690906 : Nat := 4983230072969 + 3 ^ 40 * 1690906 * 2
def baseEnd_1690906 : Nat := 868247519571466556198671

theorem tailTrace_1690906 : CollatzResearch.WordTrace tailWord_1690906 prefixEnd_1690906 868247519571466556198671 := by
  unfold tailWord_1690906
  simp only [CollatzResearch.WordTrace]
  refine ⟨15418102103035955149665143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 41114938941429213732440381 15418102103035955149665143)
  ·
    refine ⟨23127153154553932724497715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15418102103035955149665143 23127153154553932724497715)
    ·
      refine ⟨34690729731830899086746573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23127153154553932724497715 34690729731830899086746573)
      ·
        refine ⟨13009023649436587157529965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34690729731830899086746573 13009023649436587157529965)
        ·
          refine ⟨4878383868538720184073737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13009023649436587157529965 4878383868538720184073737)
          ·
            refine ⟨3658787901404040138055303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4878383868538720184073737 3658787901404040138055303)
            ·
              refine ⟨5488181852106060207082955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3658787901404040138055303 5488181852106060207082955)
              ·
                refine ⟨8232272778159090310624433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488181852106060207082955 8232272778159090310624433)
                ·
                  refine ⟨6174204583619317732968325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8232272778159090310624433 6174204583619317732968325)
                  ·
                    refine ⟨1157663359428622074931561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6174204583619317732968325 1157663359428622074931561)
                    ·
                      refine ⟨868247519571466556198671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157663359428622074931561 868247519571466556198671)
                      ·
                        rfl

theorem cell23_1690906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_1690906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690906 prefixEnd_1690906 := by exact prefixLift 1690906
  have htrace : WordTrace (prefixWord ++ tailWord_1690906) baseStart_1690906 baseEnd_1690906 := by
    simpa [prefixWord, tailWord_1690906, baseEnd_1690906] using wordTrace_append hprefix tailTrace_1690906
  have hstable : (prefixWord ++ tailWord_1690906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690906).length < 2 ^ (prefixWord ++ tailWord_1690906).sum := by decide
  have hdescent : baseEnd_1690906 < baseStart_1690906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690933 : List Nat := [1, 3, 3, 1, 2, 3, 2, 3, 1, 4]
def baseStart_1690933 : Nat := 118140960795 + 1690933 * 2 ^ 59
def prefixEnd_1690933 : Nat := 4983230072969 + 3 ^ 40 * 1690933 * 2
def baseEnd_1690933 : Nat := 289420461183045983520349

theorem tailTrace_1690933 : CollatzResearch.WordTrace tailWord_1690933 prefixEnd_1690933 289420461183045983520349 := by
  unfold tailWord_1690933
  simp only [CollatzResearch.WordTrace]
  refine ⟨61673393183046004209893453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41115595455364002806595635 61673393183046004209893453)
  ·
    refine ⟨23127522443642251578710045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61673393183046004209893453 23127522443642251578710045)
    ·
      refine ⟨8672820916365844342016267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23127522443642251578710045 8672820916365844342016267)
      ·
        refine ⟨13009231374548766513024401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8672820916365844342016267 13009231374548766513024401)
        ·
          refine ⟨9756923530911574884768301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13009231374548766513024401 9756923530911574884768301)
          ·
            refine ⟨3658846324091840581788113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9756923530911574884768301 3658846324091840581788113)
            ·
              refine ⟨2744134743068880436341085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3658846324091840581788113 2744134743068880436341085)
              ·
                refine ⟨1029050528650830163627907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2744134743068880436341085 1029050528650830163627907)
                ·
                  refine ⟨1543575792976245245441861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029050528650830163627907 1543575792976245245441861)
                  ·
                    refine ⟨289420461183045983520349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1543575792976245245441861 289420461183045983520349)
                    ·
                      rfl

theorem cell23_1690933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 3, 2, 3, 1, 4].length) (baseStart_1690933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690933 prefixEnd_1690933 := by exact prefixLift 1690933
  have htrace : WordTrace (prefixWord ++ tailWord_1690933) baseStart_1690933 baseEnd_1690933 := by
    simpa [prefixWord, tailWord_1690933, baseEnd_1690933] using wordTrace_append hprefix tailTrace_1690933
  have hstable : (prefixWord ++ tailWord_1690933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690933).length < 2 ^ (prefixWord ++ tailWord_1690933).sum := by decide
  have hdescent : baseEnd_1690933 < baseStart_1690933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690956 : List Nat := [2, 2, 1, 3, 2, 2, 1, 3, 3, 1, 3]
def baseStart_1690956 : Nat := 118140960795 + 1690956 * 2 ^ 59
def prefixEnd_1690956 : Nat := 4983230072969 + 3 ^ 40 * 1690956 * 2
def baseEnd_1690956 : Nat := 868273193604191360573441

theorem tailTrace_1690956 : CollatzResearch.WordTrace tailWord_1690956 prefixEnd_1690956 868273193604191360573441 := by
  unfold tailWord_1690956
  simp only [CollatzResearch.WordTrace]
  refine ⟨30837116030981339568990361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41116154707975119425320481 30837116030981339568990361)
  ·
    refine ⟨23127837023236004676742771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30837116030981339568990361 23127837023236004676742771)
    ·
      refine ⟨34691755534854007015114157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23127837023236004676742771 34691755534854007015114157)
      ·
        refine ⟨13009408325570252630667809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34691755534854007015114157 13009408325570252630667809)
        ·
          refine ⟨9757056244177689473000857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13009408325570252630667809 9757056244177689473000857)
          ·
            refine ⟨7317792183133267104750643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9757056244177689473000857 7317792183133267104750643)
            ·
              refine ⟨10976688274699900657125965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7317792183133267104750643 10976688274699900657125965)
              ·
                refine ⟨4116258103012462746422237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10976688274699900657125965 4116258103012462746422237)
                ·
                  refine ⟨1543596788629673529908339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4116258103012462746422237 1543596788629673529908339)
                  ·
                    refine ⟨2315395182944510294862509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1543596788629673529908339 2315395182944510294862509)
                    ·
                      refine ⟨868273193604191360573441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2315395182944510294862509 868273193604191360573441)
                      ·
                        rfl

theorem cell23_1690956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 3, 3, 1, 3].length) (baseStart_1690956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690956 prefixEnd_1690956 := by exact prefixLift 1690956
  have htrace : WordTrace (prefixWord ++ tailWord_1690956) baseStart_1690956 baseEnd_1690956 := by
    simpa [prefixWord, tailWord_1690956, baseEnd_1690956] using wordTrace_append hprefix tailTrace_1690956
  have hstable : (prefixWord ++ tailWord_1690956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690956).length < 2 ^ (prefixWord ++ tailWord_1690956).sum := by decide
  have hdescent : baseEnd_1690956 < baseStart_1690956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690976 : List Nat := [2, 1, 1, 3, 4, 2, 2, 2, 1, 5]
def baseStart_1690976 : Nat := 118140960795 + 1690976 * 2 ^ 59
def prefixEnd_1690976 : Nat := 4983230072969 + 3 ^ 40 * 1690976 * 2
def baseEnd_1690976 : Nat := 289427821072427094107783

theorem tailTrace_1690976 : CollatzResearch.WordTrace tailWord_1690976 prefixEnd_1690976 289427821072427094107783 := by
  unfold tailWord_1690976
  simp only [CollatzResearch.WordTrace]
  refine ⟨30837480760945111276854391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41116641014593481702472521 30837480760945111276854391)
  ·
    refine ⟨46256221141417666915281587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30837480760945111276854391 46256221141417666915281587)
    ·
      refine ⟨69384331712126500372922381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46256221141417666915281587 69384331712126500372922381)
      ·
        refine ⟨26019124392047437639845893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69384331712126500372922381 26019124392047437639845893)
        ·
          refine ⟨4878585823508894557471105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26019124392047437639845893 4878585823508894557471105)
          ·
            refine ⟨3658939367631670918103329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4878585823508894557471105 3658939367631670918103329)
            ·
              refine ⟨2744204525723753188577497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3658939367631670918103329 2744204525723753188577497)
              ·
                refine ⟨2058153394292814891433123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744204525723753188577497 2058153394292814891433123)
                ·
                  refine ⟨3087230091439222337149685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058153394292814891433123 3087230091439222337149685)
                  ·
                    refine ⟨289427821072427094107783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3087230091439222337149685 289427821072427094107783)
                    ·
                      rfl

theorem cell23_1690976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 2, 1, 5].length) (baseStart_1690976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690976 prefixEnd_1690976 := by exact prefixLift 1690976
  have htrace : WordTrace (prefixWord ++ tailWord_1690976) baseStart_1690976 baseEnd_1690976 := by
    simpa [prefixWord, tailWord_1690976, baseEnd_1690976] using wordTrace_append hprefix tailTrace_1690976
  have hstable : (prefixWord ++ tailWord_1690976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690976).length < 2 ^ (prefixWord ++ tailWord_1690976).sum := by decide
  have hdescent : baseEnd_1690976 < baseStart_1690976 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1690999 : List Nat := [1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 5]
def baseStart_1690999 : Nat := 118140960795 + 1690999 * 2 ^ 59
def prefixEnd_1690999 : Nat := 4983230072969 + 3 ^ 40 * 1690999 * 2
def baseEnd_1690999 : Nat := 868295273272334692335743

theorem tailTrace_1690999 : CollatzResearch.WordTrace tailWord_1690999 prefixEnd_1690999 868295273272334692335743 := by
  unfold tailWord_1690999
  simp only [CollatzResearch.WordTrace]
  refine ⟨61675800400806897481796051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41117200267204598321197367 61675800400806897481796051)
  ·
    refine ⟨92513700601210346222694077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61675800400806897481796051 92513700601210346222694077)
    ·
      refine ⟨34692637725453879833510279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92513700601210346222694077 34692637725453879833510279)
      ·
        refine ⟨52038956588180819750265419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34692637725453879833510279 52038956588180819750265419)
        ·
          refine ⟨78058434882271229625398129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52038956588180819750265419 78058434882271229625398129)
          ·
            refine ⟨58543826161703422219048597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78058434882271229625398129 58543826161703422219048597)
            ·
              refine ⟨2744241851329847916517903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 58543826161703422219048597 2744241851329847916517903)
              ·
                refine ⟨4116362776994771874776855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744241851329847916517903 4116362776994771874776855)
                ·
                  refine ⟨6174544165492157812165283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116362776994771874776855 6174544165492157812165283)
                  ·
                    refine ⟨9261816248238236718247925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6174544165492157812165283 9261816248238236718247925)
                    ·
                      refine ⟨868295273272334692335743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9261816248238236718247925 868295273272334692335743)
                      ·
                        rfl

theorem cell23_1690999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 6, 1, 1, 1, 5].length) (baseStart_1690999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1690999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1690999 prefixEnd_1690999 := by exact prefixLift 1690999
  have htrace : WordTrace (prefixWord ++ tailWord_1690999) baseStart_1690999 baseEnd_1690999 := by
    simpa [prefixWord, tailWord_1690999, baseEnd_1690999] using wordTrace_append hprefix tailTrace_1690999
  have hstable : (prefixWord ++ tailWord_1690999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1690999).length < 2 ^ (prefixWord ++ tailWord_1690999).sum := by decide
  have hdescent : baseEnd_1690999 < baseStart_1690999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1690999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691013 : List Nat := [1, 3, 1, 1, 3, 1, 5, 1, 3, 2, 2]
def baseStart_1691013 : Nat := 118140960795 + 1691013 * 2 ^ 59
def prefixEnd_1691013 : Nat := 4983230072969 + 3 ^ 40 * 1691013 * 2
def baseEnd_1691013 : Nat := 868302462001497637560679

theorem tailTrace_1691013 : CollatzResearch.WordTrace tailWord_1691013 prefixEnd_1691013 868302462001497637560679 := by
  unfold tailWord_1691013
  simp only [CollatzResearch.WordTrace]
  refine ⟨61676311022756177872805693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41117540681837451915203795 61676311022756177872805693)
  ·
    refine ⟨23128616633533566702302135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61676311022756177872805693 23128616633533566702302135)
    ·
      refine ⟨34692924950300350053453203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23128616633533566702302135 34692924950300350053453203)
      ·
        refine ⟨52039387425450525080179805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34692924950300350053453203 52039387425450525080179805)
        ·
          refine ⟨19514770284543946905067427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52039387425450525080179805 19514770284543946905067427)
          ·
            refine ⟨29272155426815920357601141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19514770284543946905067427 29272155426815920357601141)
            ·
              refine ⟨2744264571263992533525107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29272155426815920357601141 2744264571263992533525107)
              ·
                refine ⟨4116396856895988800287661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744264571263992533525107 4116396856895988800287661)
                ·
                  refine ⟨1543648821335995800107873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4116396856895988800287661 1543648821335995800107873)
                  ·
                    refine ⟨1157736616001996850080905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1543648821335995800107873 1157736616001996850080905)
                    ·
                      refine ⟨868302462001497637560679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157736616001996850080905 868302462001497637560679)
                      ·
                        rfl

theorem cell23_1691013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 5, 1, 3, 2, 2].length) (baseStart_1691013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691013 prefixEnd_1691013 := by exact prefixLift 1691013
  have htrace : WordTrace (prefixWord ++ tailWord_1691013) baseStart_1691013 baseEnd_1691013 := by
    simpa [prefixWord, tailWord_1691013, baseEnd_1691013] using wordTrace_append hprefix tailTrace_1691013
  have hstable : (prefixWord ++ tailWord_1691013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691013).length < 2 ^ (prefixWord ++ tailWord_1691013).sum := by decide
  have hdescent : baseEnd_1691013 < baseStart_1691013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691033 : List Nat := [1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 3]
def baseStart_1691033 : Nat := 118140960795 + 1691033 * 2 ^ 59
def prefixEnd_1691033 : Nat := 4983230072969 + 3 ^ 40 * 1691033 * 2
def baseEnd_1691033 : Nat := 868312731614587559310587

theorem tailTrace_1691033 : CollatzResearch.WordTrace tailWord_1691033 prefixEnd_1691033 868312731614587559310587 := by
  unfold tailWord_1691033
  simp only [CollatzResearch.WordTrace]
  refine ⟨61677040482683721288533753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41118026988455814192355835 61677040482683721288533753)
  ·
    refine ⟨46257780362012790966400315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61677040482683721288533753 46257780362012790966400315)
    ·
      refine ⟨69386670543019186449600473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46257780362012790966400315 69386670543019186449600473)
      ·
        refine ⟨52040002907264389837200355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 69386670543019186449600473 52040002907264389837200355)
        ·
          refine ⟨78060004360896584755800533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52040002907264389837200355 78060004360896584755800533)
          ·
            refine ⟨1829531352208513705214075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 78060004360896584755800533 1829531352208513705214075)
            ·
              refine ⟨2744297028312770557821113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829531352208513705214075 2744297028312770557821113)
              ·
                refine ⟨2058222771234577918365835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744297028312770557821113 2058222771234577918365835)
                ·
                  refine ⟨3087334156851866877548753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058222771234577918365835 3087334156851866877548753)
                  ·
                    refine ⟨2315500617638900158161565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3087334156851866877548753 2315500617638900158161565)
                    ·
                      refine ⟨868312731614587559310587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2315500617638900158161565 868312731614587559310587)
                      ·
                        rfl

theorem cell23_1691033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 7, 1, 2, 1, 2, 3].length) (baseStart_1691033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691033 prefixEnd_1691033 := by exact prefixLift 1691033
  have htrace : WordTrace (prefixWord ++ tailWord_1691033) baseStart_1691033 baseEnd_1691033 := by
    simpa [prefixWord, tailWord_1691033, baseEnd_1691033] using wordTrace_append hprefix tailTrace_1691033
  have hstable : (prefixWord ++ tailWord_1691033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691033).length < 2 ^ (prefixWord ++ tailWord_1691033).sum := by decide
  have hdescent : baseEnd_1691033 < baseStart_1691033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691063 : List Nat := [1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 3]
def baseStart_1691063 : Nat := 118140960795 + 1691063 * 2 ^ 59
def prefixEnd_1691063 : Nat := 4983230072969 + 3 ^ 40 * 1691063 * 2
def baseEnd_1691063 : Nat := 868328136034222441935449

theorem tailTrace_1691063 : CollatzResearch.WordTrace tailWord_1691063 prefixEnd_1691063 868328136034222441935449 := by
  unfold tailWord_1691063
  simp only [CollatzResearch.WordTrace]
  refine ⟨61678134672575036412125843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41118756448383357608083895 61678134672575036412125843)
  ·
    refine ⟨92517202008862554618188765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61678134672575036412125843 92517202008862554618188765)
    ·
      refine ⟨34693950753323457981820787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92517202008862554618188765 34693950753323457981820787)
      ·
        refine ⟨52040926129985186972731181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34693950753323457981820787 52040926129985186972731181)
        ·
          refine ⟨19515347298744445114774193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52040926129985186972731181 19515347298744445114774193)
          ·
            refine ⟨14636510474058333836080645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19515347298744445114774193 14636510474058333836080645)
            ·
              refine ⟨2744345713885937594265121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14636510474058333836080645 2744345713885937594265121)
              ·
                refine ⟨2058259285414453195698841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744345713885937594265121 2058259285414453195698841)
                ·
                  refine ⟨1543694464060839896774131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2058259285414453195698841 1543694464060839896774131)
                  ·
                    refine ⟨2315541696091259845161197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1543694464060839896774131 2315541696091259845161197)
                    ·
                      refine ⟨868328136034222441935449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2315541696091259845161197 868328136034222441935449)
                      ·
                        rfl

theorem cell23_1691063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 4, 2, 2, 1, 3].length) (baseStart_1691063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691063 prefixEnd_1691063 := by exact prefixLift 1691063
  have htrace : WordTrace (prefixWord ++ tailWord_1691063) baseStart_1691063 baseEnd_1691063 := by
    simpa [prefixWord, tailWord_1691063, baseEnd_1691063] using wordTrace_append hprefix tailTrace_1691063
  have hstable : (prefixWord ++ tailWord_1691063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691063).length < 2 ^ (prefixWord ++ tailWord_1691063).sum := by decide
  have hdescent : baseEnd_1691063 < baseStart_1691063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691069 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 4]
def baseStart_1691069 : Nat := 118140960795 + 1691069 * 2 ^ 59
def prefixEnd_1691069 : Nat := 4983230072969 + 3 ^ 40 * 1691069 * 2
def baseEnd_1691069 : Nat := 868331216918149418460421

theorem tailTrace_1691069 : CollatzResearch.WordTrace tailWord_1691069 prefixEnd_1691069 868331216918149418460421 := by
  unfold tailWord_1691069
  simp only [CollatzResearch.WordTrace]
  refine ⟨61678353510553299436844261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41118902340368866291229507 61678353510553299436844261)
  ·
    refine ⟨11564691283228743644408299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61678353510553299436844261 11564691283228743644408299)
    ·
      refine ⟨17347036924843115466612449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11564691283228743644408299 17347036924843115466612449)
      ·
        refine ⟨13010277693632336599959337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17347036924843115466612449 13010277693632336599959337)
        ·
          refine ⟨9757708270224252449969503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13010277693632336599959337 9757708270224252449969503)
          ·
            refine ⟨14636562405336378674954255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9757708270224252449969503 14636562405336378674954255)
            ·
              refine ⟨21954843608004568012431383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14636562405336378674954255 21954843608004568012431383)
              ·
                refine ⟨32932265412006852018647075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21954843608004568012431383 32932265412006852018647075)
                ·
                  refine ⟨49398398118010278027970613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32932265412006852018647075 49398398118010278027970613)
                  ·
                    refine ⟨4631099823563463565122245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49398398118010278027970613 4631099823563463565122245)
                    ·
                      refine ⟨868331216918149418460421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4631099823563463565122245 868331216918149418460421)
                      ·
                        rfl

theorem cell23_1691069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 5, 4].length) (baseStart_1691069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691069 prefixEnd_1691069 := by exact prefixLift 1691069
  have htrace : WordTrace (prefixWord ++ tailWord_1691069) baseStart_1691069 baseEnd_1691069 := by
    simpa [prefixWord, tailWord_1691069, baseEnd_1691069] using wordTrace_append hprefix tailTrace_1691069
  have hstable : (prefixWord ++ tailWord_1691069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691069).length < 2 ^ (prefixWord ++ tailWord_1691069).sum := by decide
  have hdescent : baseEnd_1691069 < baseStart_1691069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691079 : List Nat := [1, 1, 4, 1, 1, 3, 3, 1, 2, 6]
def baseStart_1691079 : Nat := 118140960795 + 1691079 * 2 ^ 59
def prefixEnd_1691079 : Nat := 4983230072969 + 3 ^ 40 * 1691079 * 2
def baseEnd_1691079 : Nat := 289445450574898126445125

theorem tailTrace_1691079 : CollatzResearch.WordTrace tailWord_1691079 prefixEnd_1691079 289445450574898126445125 := by
  unfold tailWord_1691079
  simp only [CollatzResearch.WordTrace]
  refine ⟨61678718240517071144708291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41119145493678047429805527 61678718240517071144708291)
  ·
    refine ⟨92518077360775606717062437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61678718240517071144708291 92518077360775606717062437)
    ·
      refine ⟨17347139505145426259449207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 92518077360775606717062437 17347139505145426259449207)
      ·
        refine ⟨26020709257718139389173811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17347139505145426259449207 26020709257718139389173811)
        ·
          refine ⟨39031063886577209083760717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26020709257718139389173811 39031063886577209083760717)
          ·
            refine ⟨14636648957466453406410269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39031063886577209083760717 14636648957466453406410269)
            ·
              refine ⟨5488743359049920027403851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14636648957466453406410269 5488743359049920027403851)
              ·
                refine ⟨8233115038574880041105777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5488743359049920027403851 8233115038574880041105777)
                ·
                  refine ⟨6174836278931160030829333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8233115038574880041105777 6174836278931160030829333)
                  ·
                    refine ⟨289445450574898126445125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6174836278931160030829333 289445450574898126445125)
                    ·
                      rfl

theorem cell23_1691079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_1691079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691079 prefixEnd_1691079 := by exact prefixLift 1691079
  have htrace : WordTrace (prefixWord ++ tailWord_1691079) baseStart_1691079 baseEnd_1691079 := by
    simpa [prefixWord, tailWord_1691079, baseEnd_1691079] using wordTrace_append hprefix tailTrace_1691079
  have hstable : (prefixWord ++ tailWord_1691079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691079).length < 2 ^ (prefixWord ++ tailWord_1691079).sum := by decide
  have hdescent : baseEnd_1691079 < baseStart_1691079 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691103 : List Nat := [1, 1, 2, 3, 3, 1, 2, 2, 4, 2, 2]
def baseStart_1691103 : Nat := 118140960795 + 1691103 * 2 ^ 59
def prefixEnd_1691103 : Nat := 4983230072969 + 3 ^ 40 * 1691103 * 2
def baseEnd_1691103 : Nat := 868348675260402285435265

theorem tailTrace_1691103 : CollatzResearch.WordTrace tailWord_1691103 prefixEnd_1691103 868348675260402285435265 := by
  unfold tailWord_1691103
  simp only [CollatzResearch.WordTrace]
  refine ⟨61679593592430123243581963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41119729061620082162387975 61679593592430123243581963)
  ·
    refine ⟨92519390388645184865372945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61679593592430123243581963 92519390388645184865372945)
    ·
      refine ⟨69389542791483888649029709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92519390388645184865372945 69389542791483888649029709)
      ·
        refine ⟨26021078546806458243386141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 69389542791483888649029709 26021078546806458243386141)
        ·
          refine ⟨9757904455052421841269803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26021078546806458243386141 9757904455052421841269803)
          ·
            refine ⟨14636856682578632761904705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9757904455052421841269803 14636856682578632761904705)
            ·
              refine ⟨10977642511933974571428529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14636856682578632761904705 10977642511933974571428529)
              ·
                refine ⟨8233231883950480928571397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10977642511933974571428529 8233231883950480928571397)
                ·
                  refine ⟨1543730978240715174107137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8233231883950480928571397 1543730978240715174107137)
                  ·
                    refine ⟨1157798233680536380580353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1543730978240715174107137 1157798233680536380580353)
                    ·
                      refine ⟨868348675260402285435265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157798233680536380580353 868348675260402285435265)
                      ·
                        rfl

theorem cell23_1691103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 2, 2, 4, 2, 2].length) (baseStart_1691103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691103 prefixEnd_1691103 := by exact prefixLift 1691103
  have htrace : WordTrace (prefixWord ++ tailWord_1691103) baseStart_1691103 baseEnd_1691103 := by
    simpa [prefixWord, tailWord_1691103, baseEnd_1691103] using wordTrace_append hprefix tailTrace_1691103
  have hstable : (prefixWord ++ tailWord_1691103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691103).length < 2 ^ (prefixWord ++ tailWord_1691103).sum := by decide
  have hdescent : baseEnd_1691103 < baseStart_1691103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691107 : List Nat := [1, 1, 1, 6, 2, 3, 2, 1, 1, 3, 2]
def baseStart_1691107 : Nat := 118140960795 + 1691107 * 2 ^ 59
def prefixEnd_1691107 : Nat := 4983230072969 + 3 ^ 40 * 1691107 * 2
def baseEnd_1691107 : Nat := 868350729183020269785247

theorem tailTrace_1691107 : CollatzResearch.WordTrace tailWord_1691107 prefixEnd_1691107 868350729183020269785247 := by
  unfold tailWord_1691107
  simp only [CollatzResearch.WordTrace]
  refine ⟨61679739484415631926727575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41119826322943754617818383 61679739484415631926727575)
  ·
    refine ⟨92519609226623447890091363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61679739484415631926727575 92519609226623447890091363)
    ·
      refine ⟨138779413839935171835137045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92519609226623447890091363 138779413839935171835137045)
      ·
        refine ⟨6505285023746961179772049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 138779413839935171835137045 6505285023746961179772049)
        ·
          refine ⟨4878963767810220884829037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6505285023746961179772049 4878963767810220884829037)
          ·
            refine ⟨1829611412928832831810889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4878963767810220884829037 1829611412928832831810889)
            ·
              refine ⟨1372208559696624623858167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1829611412928832831810889 1372208559696624623858167)
              ·
                refine ⟨2058312839544936935787251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372208559696624623858167 2058312839544936935787251)
                ·
                  refine ⟨3087469259317405403680877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058312839544936935787251 3087469259317405403680877)
                  ·
                    refine ⟨1157800972244027026380329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087469259317405403680877 1157800972244027026380329)
                    ·
                      refine ⟨868350729183020269785247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157800972244027026380329 868350729183020269785247)
                      ·
                        rfl

theorem cell23_1691107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_1691107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691107 prefixEnd_1691107 := by exact prefixLift 1691107
  have htrace : WordTrace (prefixWord ++ tailWord_1691107) baseStart_1691107 baseEnd_1691107 := by
    simpa [prefixWord, tailWord_1691107, baseEnd_1691107] using wordTrace_append hprefix tailTrace_1691107
  have hstable : (prefixWord ++ tailWord_1691107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691107).length < 2 ^ (prefixWord ++ tailWord_1691107).sum := by decide
  have hdescent : baseEnd_1691107 < baseStart_1691107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691120 : List Nat := [2, 1, 1, 1, 3, 4, 3, 2, 2, 2, 2]
def baseStart_1691120 : Nat := 118140960795 + 1691120 * 2 ^ 59
def prefixEnd_1691120 : Nat := 4983230072969 + 3 ^ 40 * 1691120 * 2
def baseEnd_1691120 : Nat := 868357404431528718922687

theorem tailTrace_1691120 : CollatzResearch.WordTrace tailWord_1691120 prefixEnd_1691120 868357404431528718922687 := by
  unfold tailWord_1691120
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840106816684267573475407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41120142422245690097967209 30840106816684267573475407)
  ·
    refine ⟨46260160225026401360213111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30840106816684267573475407 46260160225026401360213111)
    ·
      refine ⟨69390240337539602040319667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46260160225026401360213111 69390240337539602040319667)
      ·
        refine ⟨104085360506309403060479501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69390240337539602040319667 104085360506309403060479501)
        ·
          refine ⟨39032010189866026147679813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 104085360506309403060479501 39032010189866026147679813)
          ·
            refine ⟨7318501910599879902689965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39032010189866026147679813 7318501910599879902689965)
            ·
              refine ⟨2744438216474954963508737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7318501910599879902689965 2744438216474954963508737)
              ·
                refine ⟨2058328662356216222631553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744438216474954963508737 2058328662356216222631553)
                ·
                  refine ⟨1543746496767162166973665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2058328662356216222631553 1543746496767162166973665)
                  ·
                    refine ⟨1157809872575371625230249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1543746496767162166973665 1157809872575371625230249)
                    ·
                      refine ⟨868357404431528718922687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157809872575371625230249 868357404431528718922687)
                      ·
                        rfl

theorem cell23_1691120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 2, 2, 2].length) (baseStart_1691120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691120 prefixEnd_1691120 := by exact prefixLift 1691120
  have htrace : WordTrace (prefixWord ++ tailWord_1691120) baseStart_1691120 baseEnd_1691120 := by
    simpa [prefixWord, tailWord_1691120, baseEnd_1691120] using wordTrace_append hprefix tailTrace_1691120
  have hstable : (prefixWord ++ tailWord_1691120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691120).length < 2 ^ (prefixWord ++ tailWord_1691120).sum := by decide
  have hdescent : baseEnd_1691120 < baseStart_1691120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691126 : List Nat := [5, 1, 1, 1, 2, 2, 1, 3, 7]
def baseStart_1691126 : Nat := 118140960795 + 1691126 * 2 ^ 59
def prefixEnd_1691126 : Nat := 4983230072969 + 3 ^ 40 * 1691126 * 2
def baseEnd_1691126 : Nat := 96484498368383966160851

theorem tailTrace_1691126 : CollatzResearch.WordTrace tailWord_1691126 prefixEnd_1691126 96484498368383966160851 := by
  unfold tailWord_1691126
  simp only [CollatzResearch.WordTrace]
  refine ⟨3855027029459174885729327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 41120288314231198781112821 3855027029459174885729327)
  ·
    refine ⟨5782540544188762328593991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3855027029459174885729327 5782540544188762328593991)
    ·
      refine ⟨8673810816283143492890987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782540544188762328593991 8673810816283143492890987)
      ·
        refine ⟨13010716224424715239336481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673810816283143492890987 13010716224424715239336481)
        ·
          refine ⟨9758037168318536429502361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13010716224424715239336481 9758037168318536429502361)
          ·
            refine ⟨7318527876238902322126771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9758037168318536429502361 7318527876238902322126771)
            ·
              refine ⟨10977791814358353483190157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7318527876238902322126771 10977791814358353483190157)
              ·
                refine ⟨4116671930384382556196309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10977791814358353483190157 4116671930384382556196309)
                ·
                  refine ⟨96484498368383966160851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4116671930384382556196309 96484498368383966160851)
                  ·
                    rfl

theorem cell23_1691126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 1, 3, 7].length) (baseStart_1691126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691126 prefixEnd_1691126 := by exact prefixLift 1691126
  have htrace : WordTrace (prefixWord ++ tailWord_1691126) baseStart_1691126 baseEnd_1691126 := by
    simpa [prefixWord, tailWord_1691126, baseEnd_1691126] using wordTrace_append hprefix tailTrace_1691126
  have hstable : (prefixWord ++ tailWord_1691126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691126).length < 2 ^ (prefixWord ++ tailWord_1691126).sum := by decide
  have hdescent : baseEnd_1691126 < baseStart_1691126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691137 : List Nat := [1, 2, 4, 1, 5, 1, 1, 1, 1, 4, 2]
def baseStart_1691137 : Nat := 118140960795 + 1691137 * 2 ^ 59
def prefixEnd_1691137 : Nat := 4983230072969 + 3 ^ 40 * 1691137 * 2
def baseEnd_1691137 : Nat := 868366133602655152410109

theorem tailTrace_1691137 : CollatzResearch.WordTrace tailWord_1691137 prefixEnd_1691137 868366133602655152410109 := by
  unfold tailWord_1691137
  simp only [CollatzResearch.WordTrace]
  refine ⟨61680833674306947050319665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41120555782871298033546443 61680833674306947050319665)
  ·
    refine ⟨46260625255730210287739749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61680833674306947050319665 46260625255730210287739749)
    ·
      refine ⟨8673867235449414428951203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46260625255730210287739749 8673867235449414428951203)
      ·
        refine ⟨13010800853174121643426805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8673867235449414428951203 13010800853174121643426805)
        ·
          refine ⟨1219762579985073904071263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 13010800853174121643426805 1219762579985073904071263)
          ·
            refine ⟨1829643869977610856106895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219762579985073904071263 1829643869977610856106895)
            ·
              refine ⟨2744465804966416284160343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829643869977610856106895 2744465804966416284160343)
              ·
                refine ⟨4116698707449624426240515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2744465804966416284160343 4116698707449624426240515)
                ·
                  refine ⟨6175048061174436639360773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4116698707449624426240515 6175048061174436639360773)
                  ·
                    refine ⟨1157821511470206869880145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6175048061174436639360773 1157821511470206869880145)
                    ·
                      refine ⟨868366133602655152410109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157821511470206869880145 868366133602655152410109)
                      ·
                        rfl

theorem cell23_1691137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_1691137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691137 prefixEnd_1691137 := by exact prefixLift 1691137
  have htrace : WordTrace (prefixWord ++ tailWord_1691137) baseStart_1691137 baseEnd_1691137 := by
    simpa [prefixWord, tailWord_1691137, baseEnd_1691137] using wordTrace_append hprefix tailTrace_1691137
  have hstable : (prefixWord ++ tailWord_1691137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691137).length < 2 ^ (prefixWord ++ tailWord_1691137).sum := by decide
  have hdescent : baseEnd_1691137 < baseStart_1691137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691139 : List Nat := [1, 1, 1, 3, 2, 1, 2, 1, 6, 5]
def baseStart_1691139 : Nat := 118140960795 + 1691139 * 2 ^ 59
def prefixEnd_1691139 : Nat := 4983230072969 + 3 ^ 40 * 1691139 * 2
def baseEnd_1691139 : Nat := 289455720187988048195033

theorem tailTrace_1691139 : CollatzResearch.WordTrace tailWord_1691139 prefixEnd_1691139 289455720187988048195033 := by
  unfold tailWord_1691139
  simp only [CollatzResearch.WordTrace]
  refine ⟨61680906620299701391892471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41120604413533134261261647 61680906620299701391892471)
  ·
    refine ⟨92521359930449552087838707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61680906620299701391892471 92521359930449552087838707)
    ·
      refine ⟨138782039895674328131758061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92521359930449552087838707 138782039895674328131758061)
      ·
        refine ⟨52043264960877873049409273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 138782039895674328131758061 52043264960877873049409273)
        ·
          refine ⟨39032448720658404787056955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52043264960877873049409273 39032448720658404787056955)
          ·
            refine ⟨58548673080987607180585433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39032448720658404787056955 58548673080987607180585433)
            ·
              refine ⟨43911504810740705385439075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58548673080987607180585433 43911504810740705385439075)
              ·
                refine ⟨65867257216111058078158613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43911504810740705385439075 65867257216111058078158613)
                ·
                  refine ⟨3087527682005205847413685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65867257216111058078158613 3087527682005205847413685)
                  ·
                    refine ⟨289455720187988048195033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3087527682005205847413685 289455720187988048195033)
                    ·
                      rfl

theorem cell23_1691139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 1, 6, 5].length) (baseStart_1691139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691139 prefixEnd_1691139 := by exact prefixLift 1691139
  have htrace : WordTrace (prefixWord ++ tailWord_1691139) baseStart_1691139 baseEnd_1691139 := by
    simpa [prefixWord, tailWord_1691139, baseEnd_1691139] using wordTrace_append hprefix tailTrace_1691139
  have hstable : (prefixWord ++ tailWord_1691139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691139).length < 2 ^ (prefixWord ++ tailWord_1691139).sum := by decide
  have hdescent : baseEnd_1691139 < baseStart_1691139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691160 : List Nat := [2, 1, 2, 3, 4, 2, 1, 3, 5]
def baseStart_1691160 : Nat := 118140960795 + 1691160 * 2 ^ 59
def prefixEnd_1691160 : Nat := 4983230072969 + 3 ^ 40 * 1691160 * 2
def baseEnd_1691160 : Nat := 96486438184189840269167

theorem tailTrace_1691160 : CollatzResearch.WordTrace tailWord_1691160 prefixEnd_1691160 96486438184189840269167 := by
  unfold tailWord_1691160
  simp only [CollatzResearch.WordTrace]
  refine ⟨30840836276611810989203467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41121115035482414652271289 30840836276611810989203467)
  ·
    refine ⟨46261254414917716483805201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30840836276611810989203467 46261254414917716483805201)
    ·
      refine ⟨34695940811188287362853901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46261254414917716483805201 34695940811188287362853901)
      ·
        refine ⟨13010977804195607761070213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34695940811188287362853901 13010977804195607761070213)
        ·
          refine ⟨2439558338286676455200665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 13010977804195607761070213 2439558338286676455200665)
          ·
            refine ⟨1829668753715007341400499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2439558338286676455200665 1829668753715007341400499)
            ·
              refine ⟨2744503130572511012100749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1829668753715007341400499 2744503130572511012100749)
              ·
                refine ⟨1029188673964691629537781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2744503130572511012100749 1029188673964691629537781)
                ·
                  refine ⟨96486438184189840269167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1029188673964691629537781 96486438184189840269167)
                  ·
                    rfl

theorem cell23_1691160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 1, 3, 5].length) (baseStart_1691160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691160 prefixEnd_1691160 := by exact prefixLift 1691160
  have htrace : WordTrace (prefixWord ++ tailWord_1691160) baseStart_1691160 baseEnd_1691160 := by
    simpa [prefixWord, tailWord_1691160, baseEnd_1691160] using wordTrace_append hprefix tailTrace_1691160
  have hstable : (prefixWord ++ tailWord_1691160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691160).length < 2 ^ (prefixWord ++ tailWord_1691160).sum := by decide
  have hdescent : baseEnd_1691160 < baseStart_1691160 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691219 : List Nat := [1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6]
def baseStart_1691219 : Nat := 118140960795 + 1691219 * 2 ^ 59
def prefixEnd_1691219 : Nat := 4983230072969 + 3 ^ 40 * 1691219 * 2
def baseEnd_1691219 : Nat := 868408239016323831584731

theorem tailTrace_1691219 : CollatzResearch.WordTrace tailWord_1691219 prefixEnd_1691219 868408239016323831584731 := by
  unfold tailWord_1691219
  simp only [CollatzResearch.WordTrace]
  refine ⟨61683824460009875054804711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41122549640006583369869807 61683824460009875054804711)
  ·
    refine ⟨92525736690014812582207067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61683824460009875054804711 92525736690014812582207067)
    ·
      refine ⟨138788605035022218873310601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 92525736690014812582207067 138788605035022218873310601)
      ·
        refine ⟨104091453776266664154982951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 138788605035022218873310601 104091453776266664154982951)
        ·
          refine ⟨156137180664399996232474427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104091453776266664154982951 156137180664399996232474427)
          ·
            refine ⟨234205770996599994348711641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 156137180664399996232474427 234205770996599994348711641)
            ·
              refine ⟨175654328247449995761533731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 234205770996599994348711641 175654328247449995761533731)
              ·
                refine ⟨263481492371174993642300597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 175654328247449995761533731 263481492371174993642300597)
                ·
                  refine ⟨24701389909797655653965681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 263481492371174993642300597 24701389909797655653965681)
                  ·
                    refine ⟨18526042432348241740474261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24701389909797655653965681 18526042432348241740474261)
                    ·
                      refine ⟨868408239016323831584731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 18526042432348241740474261 868408239016323831584731)
                      ·
                        rfl

theorem cell23_1691219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 2, 6].length) (baseStart_1691219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691219 prefixEnd_1691219 := by exact prefixLift 1691219
  have htrace : WordTrace (prefixWord ++ tailWord_1691219) baseStart_1691219 baseEnd_1691219 := by
    simpa [prefixWord, tailWord_1691219, baseEnd_1691219] using wordTrace_append hprefix tailTrace_1691219
  have hstable : (prefixWord ++ tailWord_1691219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691219).length < 2 ^ (prefixWord ++ tailWord_1691219).sum := by decide
  have hdescent : baseEnd_1691219 < baseStart_1691219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691220 : List Nat := [2, 4, 1, 1, 1, 2, 2, 5, 1, 4]
def baseStart_1691220 : Nat := 118140960795 + 1691220 * 2 ^ 59
def prefixEnd_1691220 : Nat := 4983230072969 + 3 ^ 40 * 1691220 * 2
def baseEnd_1691220 : Nat := 289469584165659442557409

theorem tailTrace_1691220 : CollatzResearch.WordTrace tailWord_1691220 prefixEnd_1691220 289469584165659442557409 := by
  unfold tailWord_1691220
  simp only [CollatzResearch.WordTrace]
  refine ⟨30841930466503126112795557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41122573955337501483727409 30841930466503126112795557)
  ·
    refine ⟨5782861962469336146149167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30841930466503126112795557 5782861962469336146149167)
    ·
      refine ⟨8674292943704004219223751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5782861962469336146149167 8674292943704004219223751)
      ·
        refine ⟨13011439415556006328835627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8674292943704004219223751 13011439415556006328835627)
        ·
          refine ⟨19517159123334009493253441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13011439415556006328835627 19517159123334009493253441)
          ·
            refine ⟨14637869342500507119940081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19517159123334009493253441 14637869342500507119940081)
            ·
              refine ⟨10978402006875380339955061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14637869342500507119940081 10978402006875380339955061)
              ·
                refine ⟨1029225188144566906870787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10978402006875380339955061 1029225188144566906870787)
                ·
                  refine ⟨1543837782216850360306181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029225188144566906870787 1543837782216850360306181)
                  ·
                    refine ⟨289469584165659442557409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1543837782216850360306181 289469584165659442557409)
                    ·
                      rfl

theorem cell23_1691220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_1691220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691220 prefixEnd_1691220 := by exact prefixLift 1691220
  have htrace : WordTrace (prefixWord ++ tailWord_1691220) baseStart_1691220 baseEnd_1691220 := by
    simpa [prefixWord, tailWord_1691220, baseEnd_1691220] using wordTrace_append hprefix tailTrace_1691220
  have hstable : (prefixWord ++ tailWord_1691220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691220).length < 2 ^ (prefixWord ++ tailWord_1691220).sum := by decide
  have hdescent : baseEnd_1691220 < baseStart_1691220 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691237 : List Nat := [1, 3, 1, 3, 3, 1, 4, 2, 1, 4]
def baseStart_1691237 : Nat := 118140960795 + 1691237 * 2 ^ 59
def prefixEnd_1691237 : Nat := 4983230072969 + 3 ^ 40 * 1691237 * 2
def baseEnd_1691237 : Nat := 289472493889368253719883

theorem tailTrace_1691237 : CollatzResearch.WordTrace tailWord_1691237 prefixEnd_1691237 289472493889368253719883 := by
  unfold tailWord_1691237
  simp only [CollatzResearch.WordTrace]
  refine ⟨61684480973944664128959965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41122987315963109419306643 61684480973944664128959965)
  ·
    refine ⟨23131680365229249048359987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61684480973944664128959965 23131680365229249048359987)
    ·
      refine ⟨34697520547843873572539981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23131680365229249048359987 34697520547843873572539981)
      ·
        refine ⟨13011570205441452589702493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34697520547843873572539981 13011570205441452589702493)
        ·
          refine ⟨4879338827040544721138435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13011570205441452589702493 4879338827040544721138435)
          ·
            refine ⟨7319008240560817081707653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879338827040544721138435 7319008240560817081707653)
            ·
              refine ⟨1372314045105153202820185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7319008240560817081707653 1372314045105153202820185)
              ·
                refine ⟨1029235533828864902115139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1372314045105153202820185 1029235533828864902115139)
                ·
                  refine ⟨1543853300743297353172709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029235533828864902115139 1543853300743297353172709)
                  ·
                    refine ⟨289472493889368253719883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1543853300743297353172709 289472493889368253719883)
                    ·
                      rfl

theorem cell23_1691237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 4, 2, 1, 4].length) (baseStart_1691237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691237 prefixEnd_1691237 := by exact prefixLift 1691237
  have htrace : WordTrace (prefixWord ++ tailWord_1691237) baseStart_1691237 baseEnd_1691237 := by
    simpa [prefixWord, tailWord_1691237, baseEnd_1691237] using wordTrace_append hprefix tailTrace_1691237
  have hstable : (prefixWord ++ tailWord_1691237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691237).length < 2 ^ (prefixWord ++ tailWord_1691237).sum := by decide
  have hdescent : baseEnd_1691237 < baseStart_1691237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691276 : List Nat := [2, 2, 1, 2, 1, 1, 3, 4, 1, 6]
def baseStart_1691276 : Nat := 118140960795 + 1691276 * 2 ^ 59
def prefixEnd_1691276 : Nat := 4983230072969 + 3 ^ 40 * 1691276 * 2
def baseEnd_1691276 : Nat := 289479169137876702857323

theorem tailTrace_1691276 : CollatzResearch.WordTrace tailWord_1691276 prefixEnd_1691276 289479169137876702857323 := by
  unfold tailWord_1691276
  simp only [CollatzResearch.WordTrace]
  refine ⟨30842951710401686894814841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41123935613868915859753121 30842951710401686894814841)
  ·
    refine ⟨23132213782801265171111131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30842951710401686894814841 23132213782801265171111131)
    ·
      refine ⟨34698320674201897756666697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23132213782801265171111131 34698320674201897756666697)
      ·
        refine ⟨26023740505651423317500023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34698320674201897756666697 26023740505651423317500023)
        ·
          refine ⟨39035610758477134976250035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26023740505651423317500023 39035610758477134976250035)
          ·
            refine ⟨58553416137715702464375053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39035610758477134976250035 58553416137715702464375053)
            ·
              refine ⟨21957531051643388424140645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58553416137715702464375053 21957531051643388424140645)
              ·
                refine ⟨4117037072183135329526371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21957531051643388424140645 4117037072183135329526371)
                ·
                  refine ⟨6175555608274702994289557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117037072183135329526371 6175555608274702994289557)
                  ·
                    refine ⟨289479169137876702857323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6175555608274702994289557 289479169137876702857323)
                    ·
                      rfl

theorem cell23_1691276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 4, 1, 6].length) (baseStart_1691276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691276 prefixEnd_1691276 := by exact prefixLift 1691276
  have htrace : WordTrace (prefixWord ++ tailWord_1691276) baseStart_1691276 baseEnd_1691276 := by
    simpa [prefixWord, tailWord_1691276, baseEnd_1691276] using wordTrace_append hprefix tailTrace_1691276
  have hstable : (prefixWord ++ tailWord_1691276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691276).length < 2 ^ (prefixWord ++ tailWord_1691276).sum := by decide
  have hdescent : baseEnd_1691276 < baseStart_1691276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691294 : List Nat := [4, 3, 1, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_1691294 : Nat := 118140960795 + 1691294 * 2 ^ 59
def prefixEnd_1691294 : Nat := 4983230072969 + 3 ^ 40 * 1691294 * 2
def baseEnd_1691294 : Nat := 868446750065411038146887

theorem tailTrace_1691294 : CollatzResearch.WordTrace tailWord_1691294 prefixEnd_1691294 868446750065411038146887 := by
  unfold tailWord_1691294
  simp only [CollatzResearch.WordTrace]
  refine ⟨7710819991842270357973117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 41124373289825441909189957 7710819991842270357973117)
  ·
    refine ⟨2891557496940851384239919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7710819991842270357973117 2891557496940851384239919)
    ·
      refine ⟨4337336245411277076359879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2891557496940851384239919 4337336245411277076359879)
      ·
        refine ⟨6506004368116915614539819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4337336245411277076359879 6506004368116915614539819)
        ·
          refine ⟨9759006552175373421809729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6506004368116915614539819 9759006552175373421809729)
          ·
            refine ⟨7319254914131530066357297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9759006552175373421809729 7319254914131530066357297)
            ·
              refine ⟨5489441185598647549767973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7319254914131530066357297 5489441185598647549767973)
              ·
                refine ⟨1029270222299746415581495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5489441185598647549767973 1029270222299746415581495)
                ·
                  refine ⟨1543905333449619623372243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029270222299746415581495 1543905333449619623372243)
                  ·
                    refine ⟨2315858000174429435058365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1543905333449619623372243 2315858000174429435058365)
                    ·
                      refine ⟨868446750065411038146887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2315858000174429435058365 868446750065411038146887)
                      ·
                        rfl

theorem cell23_1691294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_1691294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691294 prefixEnd_1691294 := by exact prefixLift 1691294
  have htrace : WordTrace (prefixWord ++ tailWord_1691294) baseStart_1691294 baseEnd_1691294 := by
    simpa [prefixWord, tailWord_1691294, baseEnd_1691294] using wordTrace_append hprefix tailTrace_1691294
  have hstable : (prefixWord ++ tailWord_1691294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691294).length < 2 ^ (prefixWord ++ tailWord_1691294).sum := by decide
  have hdescent : baseEnd_1691294 < baseStart_1691294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691317 : List Nat := [1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 4]
def baseStart_1691317 : Nat := 118140960795 + 1691317 * 2 ^ 59
def prefixEnd_1691317 : Nat := 4983230072969 + 3 ^ 40 * 1691317 * 2
def baseEnd_1691317 : Nat := 868458560120464448159281

theorem tailTrace_1691317 : CollatzResearch.WordTrace tailWord_1691317 prefixEnd_1691317 868458560120464448159281 := by
  unfold tailWord_1691317
  simp only [CollatzResearch.WordTrace]
  refine ⟨61687398813654837791872205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41124932542436558527914803 61687398813654837791872205)
  ·
    refine ⟨23132774555120564171952077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61687398813654837791872205 23132774555120564171952077)
    ·
      refine ⟨8674790458170211564482029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23132774555120564171952077 8674790458170211564482029)
      ·
        refine ⟨3253046421813829336680761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8674790458170211564482029 3253046421813829336680761)
        ·
          refine ⟨2439784816360372002510571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3253046421813829336680761 2439784816360372002510571)
          ·
            refine ⟨3659677224540558003765857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2439784816360372002510571 3659677224540558003765857)
            ·
              refine ⟨2744757918405418502824393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3659677224540558003765857 2744757918405418502824393)
              ·
                refine ⟨2058568438804063877118295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744757918405418502824393 2058568438804063877118295)
                ·
                  refine ⟨3087852658206095815677443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058568438804063877118295 3087852658206095815677443)
                  ·
                    refine ⟨4631778987309143723516165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3087852658206095815677443 4631778987309143723516165)
                    ·
                      refine ⟨868458560120464448159281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4631778987309143723516165 868458560120464448159281)
                      ·
                        rfl

theorem cell23_1691317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_1691317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691317 prefixEnd_1691317 := by exact prefixLift 1691317
  have htrace : WordTrace (prefixWord ++ tailWord_1691317) baseStart_1691317 baseEnd_1691317 := by
    simpa [prefixWord, tailWord_1691317, baseEnd_1691317] using wordTrace_append hprefix tailTrace_1691317
  have hstable : (prefixWord ++ tailWord_1691317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691317).length < 2 ^ (prefixWord ++ tailWord_1691317).sum := by decide
  have hdescent : baseEnd_1691317 < baseStart_1691317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691334 : List Nat := [6, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4]
def baseStart_1691334 : Nat := 118140960795 + 1691334 * 2 ^ 59
def prefixEnd_1691334 : Nat := 4983230072969 + 3 ^ 40 * 1691334 * 2
def baseEnd_1691334 : Nat := 868467289291590881646703

theorem tailTrace_1691334 : CollatzResearch.WordTrace tailWord_1691334 prefixEnd_1691334 868467289291590881646703 := by
  unfold tailWord_1691334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1927750589206039052976283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 41125345903062166463494037 1927750589206039052976283)
  ·
    refine ⟨2891625883809058579464425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1927750589206039052976283 2891625883809058579464425)
    ·
      refine ⟨2168719412856793934598319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2891625883809058579464425 2168719412856793934598319)
      ·
        refine ⟨3253079119285190901897479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2168719412856793934598319 3253079119285190901897479)
        ·
          refine ⟨4879618678927786352846219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3253079119285190901897479 4879618678927786352846219)
          ·
            refine ⟨7319428018391679529269329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4879618678927786352846219 7319428018391679529269329)
            ·
              refine ⟨5489571013793759646951997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7319428018391679529269329 5489571013793759646951997)
              ·
                refine ⟨2058589130172659867606999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5489571013793759646951997 2058589130172659867606999)
                ·
                  refine ⟨3087883695258989801410499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058589130172659867606999 3087883695258989801410499)
                  ·
                    refine ⟨4631825542888484702115749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3087883695258989801410499 4631825542888484702115749)
                    ·
                      refine ⟨868467289291590881646703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4631825542888484702115749 868467289291590881646703)
                      ·
                        rfl

theorem cell23_1691334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_1691334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691334 prefixEnd_1691334 := by exact prefixLift 1691334
  have htrace : WordTrace (prefixWord ++ tailWord_1691334) baseStart_1691334 baseEnd_1691334 := by
    simpa [prefixWord, tailWord_1691334, baseEnd_1691334] using wordTrace_append hprefix tailTrace_1691334
  have hstable : (prefixWord ++ tailWord_1691334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691334).length < 2 ^ (prefixWord ++ tailWord_1691334).sum := by decide
  have hdescent : baseEnd_1691334 < baseStart_1691334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691340 : List Nat := [2, 2, 1, 5, 3, 1, 9]
def baseStart_1691340 : Nat := 118140960795 + 1691340 * 2 ^ 59
def prefixEnd_1691340 : Nat := 4983230072969 + 3 ^ 40 * 1691340 * 2
def baseEnd_1691340 : Nat := 10721856421919973557675

theorem tailTrace_1691340 : CollatzResearch.WordTrace tailWord_1691340 prefixEnd_1691340 10721856421919973557675 := by
  unfold tailWord_1691340
  simp only [CollatzResearch.WordTrace]
  refine ⟨30844118846285756359979737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41125491795047675146639649 30844118846285756359979737)
  ·
    refine ⟨23133089134714317269984803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30844118846285756359979737 23133089134714317269984803)
    ·
      refine ⟨34699633702071475904977205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23133089134714317269984803 34699633702071475904977205)
      ·
        refine ⟨3253090659569200866091613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34699633702071475904977205 3253090659569200866091613)
        ·
          refine ⟨1219908997338450324784355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3253090659569200866091613 1219908997338450324784355)
          ·
            refine ⟨1829863496007675487176533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1219908997338450324784355 1829863496007675487176533)
            ·
              refine ⟨10721856421919973557675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1829863496007675487176533 10721856421919973557675)
              ·
                rfl

theorem cell23_1691340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 9].length) (baseStart_1691340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691340 prefixEnd_1691340 := by exact prefixLift 1691340
  have htrace : WordTrace (prefixWord ++ tailWord_1691340) baseStart_1691340 baseEnd_1691340 := by
    simpa [prefixWord, tailWord_1691340, baseEnd_1691340] using wordTrace_append hprefix tailTrace_1691340
  have hstable : (prefixWord ++ tailWord_1691340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691340).length < 2 ^ (prefixWord ++ tailWord_1691340).sum := by decide
  have hdescent : baseEnd_1691340 < baseStart_1691340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691377 : List Nat := [1, 2, 2, 2, 2, 3, 3, 2, 1, 3, 2]
def baseStart_1691377 : Nat := 118140960795 + 1691377 * 2 ^ 59
def prefixEnd_1691377 : Nat := 4983230072969 + 3 ^ 40 * 1691377 * 2
def baseEnd_1691377 : Nat := 868489368959734213409005

theorem tailTrace_1691377 : CollatzResearch.WordTrace tailWord_1691377 prefixEnd_1691377 868489368959734213409005 := by
  unfold tailWord_1691377
  simp only [CollatzResearch.WordTrace]
  refine ⟨61689587193437468039056385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41126391462291645359370923 61689587193437468039056385)
  ·
    refine ⟨46267190395078101029292289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61689587193437468039056385 46267190395078101029292289)
    ·
      refine ⟨34700392796308575771969217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46267190395078101029292289 34700392796308575771969217)
      ·
        refine ⟨26025294597231431828976913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34700392796308575771969217 26025294597231431828976913)
        ·
          refine ⟨19518970947923573871732685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26025294597231431828976913 19518970947923573871732685)
          ·
            refine ⟨7319614105471340201899757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19518970947923573871732685 7319614105471340201899757)
            ·
              refine ⟨2744855289551752575712409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7319614105471340201899757 2744855289551752575712409)
              ·
                refine ⟨2058641467163814431784307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2744855289551752575712409 2058641467163814431784307)
                ·
                  refine ⟨3087962200745721647676461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058641467163814431784307 3087962200745721647676461)
                  ·
                    refine ⟨1157985825279645617878673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 3087962200745721647676461 1157985825279645617878673)
                    ·
                      refine ⟨868489368959734213409005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1157985825279645617878673 868489368959734213409005)
                      ·
                        rfl

theorem cell23_1691377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 3, 2, 1, 3, 2].length) (baseStart_1691377 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691377 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691377 prefixEnd_1691377 := by exact prefixLift 1691377
  have htrace : WordTrace (prefixWord ++ tailWord_1691377) baseStart_1691377 baseEnd_1691377 := by
    simpa [prefixWord, tailWord_1691377, baseEnd_1691377] using wordTrace_append hprefix tailTrace_1691377
  have hstable : (prefixWord ++ tailWord_1691377).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691377).length < 2 ^ (prefixWord ++ tailWord_1691377).sum := by decide
  have hdescent : baseEnd_1691377 < baseStart_1691377 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691393 : List Nat := [1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 5]
def baseStart_1691393 : Nat := 118140960795 + 1691393 * 2 ^ 59
def prefixEnd_1691393 : Nat := 4983230072969 + 3 ^ 40 * 1691393 * 2
def baseEnd_1691393 : Nat := 868497584650206150808931

theorem tailTrace_1691393 : CollatzResearch.WordTrace tailWord_1691393 prefixEnd_1691393 868497584650206150808931 := by
  unfold tailWord_1691393
  simp only [CollatzResearch.WordTrace]
  refine ⟨61690170761379502771638833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41126780507586335181092555 61690170761379502771638833)
  ·
    refine ⟨46267628071034627078729125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61690170761379502771638833 46267628071034627078729125)
    ·
      refine ⟨8675180263318992577261711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46267628071034627078729125 8675180263318992577261711)
      ·
        refine ⟨13012770394978488865892567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8675180263318992577261711 13012770394978488865892567)
        ·
          refine ⟨19519155592467733298838851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13012770394978488865892567 19519155592467733298838851)
          ·
            refine ⟨29278733388701599948258277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19519155592467733298838851 29278733388701599948258277)
            ·
              refine ⟨5489762510381549990298427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29278733388701599948258277 5489762510381549990298427)
              ·
                refine ⟨8234643765572324985447641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5489762510381549990298427 8234643765572324985447641)
                ·
                  refine ⟨6175982824179243739085731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8234643765572324985447641 6175982824179243739085731)
                  ·
                    refine ⟨9263974236268865608628597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6175982824179243739085731 9263974236268865608628597)
                    ·
                      refine ⟨868497584650206150808931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 9263974236268865608628597 868497584650206150808931)
                      ·
                        rfl

theorem cell23_1691393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_1691393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691393 prefixEnd_1691393 := by exact prefixLift 1691393
  have htrace : WordTrace (prefixWord ++ tailWord_1691393) baseStart_1691393 baseEnd_1691393 := by
    simpa [prefixWord, tailWord_1691393, baseEnd_1691393] using wordTrace_append hprefix tailTrace_1691393
  have hstable : (prefixWord ++ tailWord_1691393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691393).length < 2 ^ (prefixWord ++ tailWord_1691393).sum := by decide
  have hdescent : baseEnd_1691393 < baseStart_1691393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691493 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1691493 : Nat := 118140960795 + 1691493 * 2 ^ 59
def prefixEnd_1691493 : Nat := 4983230072969 + 3 ^ 40 * 1691493 * 2
def baseEnd_1691493 : Nat := 868548932715655759558471

theorem tailTrace_1691493 : CollatzResearch.WordTrace tailWord_1691493 prefixEnd_1691493 868548932715655759558471 := by
  unfold tailWord_1691493
  simp only [CollatzResearch.WordTrace]
  refine ⟨61693818061017219850279133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41129212040678146566852755 61693818061017219850279133)
  ·
    refine ⟨23135181772881457443854675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61693818061017219850279133 23135181772881457443854675)
    ·
      refine ⟨34702772659322186165782013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23135181772881457443854675 34702772659322186165782013)
      ·
        refine ⟨13013539747245819812168255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34702772659322186165782013 13013539747245819812168255)
        ·
          refine ⟨19520309620868729718252383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13013539747245819812168255 19520309620868729718252383)
          ·
            refine ⟨29280464431303094577378575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19520309620868729718252383 29280464431303094577378575)
            ·
              refine ⟨43920696646954641866067863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29280464431303094577378575 43920696646954641866067863)
              ·
                refine ⟨65881044970431962799101795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43920696646954641866067863 65881044970431962799101795)
                ·
                  refine ⟨98821567455647944198652693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65881044970431962799101795 98821567455647944198652693)
                  ·
                    refine ⟨4632260974483497384311845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 98821567455647944198652693 4632260974483497384311845)
                    ·
                      refine ⟨868548932715655759558471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4632260974483497384311845 868548932715655759558471)
                      ·
                        rfl

theorem cell23_1691493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1691493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691493 prefixEnd_1691493 := by exact prefixLift 1691493
  have htrace : WordTrace (prefixWord ++ tailWord_1691493) baseStart_1691493 baseEnd_1691493 := by
    simpa [prefixWord, tailWord_1691493, baseEnd_1691493] using wordTrace_append hprefix tailTrace_1691493
  have hstable : (prefixWord ++ tailWord_1691493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691493).length < 2 ^ (prefixWord ++ tailWord_1691493).sum := by decide
  have hdescent : baseEnd_1691493 < baseStart_1691493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691500 : List Nat := [2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 3]
def baseStart_1691500 : Nat := 118140960795 + 1691500 * 2 ^ 59
def prefixEnd_1691500 : Nat := 4983230072969 + 3 ^ 40 * 1691500 * 2
def baseEnd_1691500 : Nat := 868552527080237232170939

theorem tailTrace_1691500 : CollatzResearch.WordTrace tailWord_1691500 prefixEnd_1691500 868552527080237232170939 := by
  unfold tailWord_1691500
  simp only [CollatzResearch.WordTrace]
  refine ⟨30847036685995930022891977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41129382247994573363855969 30847036685995930022891977)
  ·
    refine ⟨23135277514496947517168983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30847036685995930022891977 23135277514496947517168983)
    ·
      refine ⟨34702916271745421275753475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23135277514496947517168983 34702916271745421275753475)
      ·
        refine ⟨52054374407618131913630213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34702916271745421275753475 52054374407618131913630213)
        ·
          refine ⟨9760195201428399733805665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52054374407618131913630213 9760195201428399733805665)
          ·
            refine ⟨7320146401071299800354249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9760195201428399733805665 7320146401071299800354249)
            ·
              refine ⟨5490109800803474850265687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7320146401071299800354249 5490109800803474850265687)
              ·
                refine ⟨8235164701205212275398531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5490109800803474850265687 8235164701205212275398531)
                ·
                  refine ⟨12352747051807818413097797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8235164701205212275398531 12352747051807818413097797)
                  ·
                    refine ⟨2316140072213965952455837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12352747051807818413097797 2316140072213965952455837)
                    ·
                      refine ⟨868552527080237232170939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2316140072213965952455837 868552527080237232170939)
                      ·
                        rfl

theorem cell23_1691500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 3].length) (baseStart_1691500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691500 prefixEnd_1691500 := by exact prefixLift 1691500
  have htrace : WordTrace (prefixWord ++ tailWord_1691500) baseStart_1691500 baseEnd_1691500 := by
    simpa [prefixWord, tailWord_1691500, baseEnd_1691500] using wordTrace_append hprefix tailTrace_1691500
  have hstable : (prefixWord ++ tailWord_1691500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691500).length < 2 ^ (prefixWord ++ tailWord_1691500).sum := by decide
  have hdescent : baseEnd_1691500 < baseStart_1691500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691567 : List Nat := [1, 1, 2, 1, 2, 2, 7, 1, 1, 5]
def baseStart_1691567 : Nat := 118140960795 + 1691567 * 2 ^ 59
def prefixEnd_1691567 : Nat := 4983230072969 + 3 ^ 40 * 1691567 * 2
def baseEnd_1691567 : Nat := 289528976761362823344377

theorem tailTrace_1691567 : CollatzResearch.WordTrace tailWord_1691567 prefixEnd_1691567 289528976761362823344377 := by
  unfold tailWord_1691567
  simp only [CollatzResearch.WordTrace]
  refine ⟨61696517062749130488472955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41131011375166086992315303 61696517062749130488472955)
  ·
    refine ⟨92544775594123695732709433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61696517062749130488472955 92544775594123695732709433)
    ·
      refine ⟨69408581695592771799532075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 92544775594123695732709433 69408581695592771799532075)
      ·
        refine ⟨104112872543389157699298113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69408581695592771799532075 104112872543389157699298113)
        ·
          refine ⟨78084654407541868274473585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 104112872543389157699298113 78084654407541868274473585)
          ·
            refine ⟨58563490805656401205855189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78084654407541868274473585 58563490805656401205855189)
            ·
              refine ⟨1372581815757571903262231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 58563490805656401205855189 1372581815757571903262231)
              ·
                refine ⟨2058872723636357854893347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1372581815757571903262231 2058872723636357854893347)
                ·
                  refine ⟨3088309085454536782340021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058872723636357854893347 3088309085454536782340021)
                  ·
                    refine ⟨289528976761362823344377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3088309085454536782340021 289528976761362823344377)
                    ·
                      rfl

theorem cell23_1691567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 1, 1, 5].length) (baseStart_1691567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691567 prefixEnd_1691567 := by exact prefixLift 1691567
  have htrace : WordTrace (prefixWord ++ tailWord_1691567) baseStart_1691567 baseEnd_1691567 := by
    simpa [prefixWord, tailWord_1691567, baseEnd_1691567] using wordTrace_append hprefix tailTrace_1691567
  have hstable : (prefixWord ++ tailWord_1691567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691567).length < 2 ^ (prefixWord ++ tailWord_1691567).sum := by decide
  have hdescent : baseEnd_1691567 < baseStart_1691567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691581 : List Nat := [1, 4, 1, 2, 3, 2, 1, 4, 1, 1, 3]
def baseStart_1691581 : Nat := 118140960795 + 1691581 * 2 ^ 59
def prefixEnd_1691581 : Nat := 4983230072969 + 3 ^ 40 * 1691581 * 2
def baseEnd_1691581 : Nat := 868594119013251415258067

theorem tailTrace_1691581 : CollatzResearch.WordTrace tailWord_1691581 prefixEnd_1691581 868594119013251415258067 := by
  unfold tailWord_1691581
  simp only [CollatzResearch.WordTrace]
  refine ⟨61697027684698410879482597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41131351789798940586321731 61697027684698410879482597)
  ·
    refine ⟨11568192690880952039902987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61697027684698410879482597 11568192690880952039902987)
    ·
      refine ⟨17352289036321428059854481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11568192690880952039902987 17352289036321428059854481)
      ·
        refine ⟨13014216777241071044890861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17352289036321428059854481 13014216777241071044890861)
        ·
          refine ⟨4880331291465401641834073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13014216777241071044890861 4880331291465401641834073)
          ·
            refine ⟨3660248468599051231375555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4880331291465401641834073 3660248468599051231375555)
            ·
              refine ⟨5490372702898576847063333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3660248468599051231375555 5490372702898576847063333)
              ·
                refine ⟨1029444881793483158824375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5490372702898576847063333 1029444881793483158824375)
                ·
                  refine ⟨1544167322690224738236563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1029444881793483158824375 1544167322690224738236563)
                  ·
                    refine ⟨2316250984035337107354845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1544167322690224738236563 2316250984035337107354845)
                    ·
                      refine ⟨868594119013251415258067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2316250984035337107354845 868594119013251415258067)
                      ·
                        rfl

theorem cell23_1691581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 1, 1, 3].length) (baseStart_1691581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691581 prefixEnd_1691581 := by exact prefixLift 1691581
  have htrace : WordTrace (prefixWord ++ tailWord_1691581) baseStart_1691581 baseEnd_1691581 := by
    simpa [prefixWord, tailWord_1691581, baseEnd_1691581] using wordTrace_append hprefix tailTrace_1691581
  have hstable : (prefixWord ++ tailWord_1691581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691581).length < 2 ^ (prefixWord ++ tailWord_1691581).sum := by decide
  have hdescent : baseEnd_1691581 < baseStart_1691581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691600 : List Nat := [2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4]
def baseStart_1691600 : Nat := 118140960795 + 1691600 * 2 ^ 59
def prefixEnd_1691600 : Nat := 4983230072969 + 3 ^ 40 * 1691600 * 2
def baseEnd_1691600 : Nat := 868603875145686840920479

theorem tailTrace_1691600 : CollatzResearch.WordTrace tailWord_1691600 prefixEnd_1691600 868603875145686840920479 := by
  unfold tailWord_1691600
  simp only [CollatzResearch.WordTrace]
  refine ⟨30848860335814788562212127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 41131813781086384749616169 30848860335814788562212127)
  ·
    refine ⟨46273290503722182843318191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30848860335814788562212127 46273290503722182843318191)
    ·
      refine ⟨69409935755583274264977287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46273290503722182843318191 69409935755583274264977287)
      ·
        refine ⟨104114903633374911397465931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 69409935755583274264977287 104114903633374911397465931)
        ·
          refine ⟨156172355450062367096198897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 104114903633374911397465931 156172355450062367096198897)
          ·
            refine ⟨117129266587546775322149173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 156172355450062367096198897 117129266587546775322149173)
            ·
              refine ⟨10980868742582510186451485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 117129266587546775322149173 10980868742582510186451485)
              ·
                refine ⟨4117825778468441319919307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10980868742582510186451485 4117825778468441319919307)
                ·
                  refine ⟨6176738667702661979878961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4117825778468441319919307 6176738667702661979878961)
                  ·
                    refine ⟨4632554000776996484909221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6176738667702661979878961 4632554000776996484909221)
                    ·
                      refine ⟨868603875145686840920479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4632554000776996484909221 868603875145686840920479)
                      ·
                        rfl

theorem cell23_1691600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 4].length) (baseStart_1691600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691600 prefixEnd_1691600 := by exact prefixLift 1691600
  have htrace : WordTrace (prefixWord ++ tailWord_1691600) baseStart_1691600 baseEnd_1691600 := by
    simpa [prefixWord, tailWord_1691600, baseEnd_1691600] using wordTrace_append hprefix tailTrace_1691600
  have hstable : (prefixWord ++ tailWord_1691600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691600).length < 2 ^ (prefixWord ++ tailWord_1691600).sum := by decide
  have hdescent : baseEnd_1691600 < baseStart_1691600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1691607 : List Nat := [1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 3]
def baseStart_1691607 : Nat := 118140960795 + 1691607 * 2 ^ 59
def prefixEnd_1691607 : Nat := 4983230072969 + 3 ^ 40 * 1691607 * 2
def baseEnd_1691607 : Nat := 868607469510268313532947

theorem tailTrace_1691607 : CollatzResearch.WordTrace tailWord_1691607 prefixEnd_1691607 868607469510268313532947 := by
  unfold tailWord_1691607
  simp only [CollatzResearch.WordTrace]
  refine ⟨61697975982604217319929075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 41131983988402811546619383 61697975982604217319929075)
  ·
    refine ⟨92546963973906325979893613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61697975982604217319929075 92546963973906325979893613)
    ·
      refine ⟨34705111490214872242460105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 92546963973906325979893613 34705111490214872242460105)
      ·
        refine ⟨26028833617661154181845079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34705111490214872242460105 26028833617661154181845079)
        ·
          refine ⟨39043250426491731272767619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26028833617661154181845079 39043250426491731272767619)
          ·
            refine ⟨58564875639737596909151429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39043250426491731272767619 58564875639737596909151429)
            ·
              refine ⟨10980914182450799420465893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58564875639737596909151429 10980914182450799420465893)
              ·
                refine ⟨2058921409209524891337355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10980914182450799420465893 2058921409209524891337355)
                ·
                  refine ⟨3088382113814287337006033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2058921409209524891337355 3088382113814287337006033)
                  ·
                    refine ⟨2316286585360715502754525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3088382113814287337006033 2316286585360715502754525)
                    ·
                      refine ⟨868607469510268313532947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2316286585360715502754525 868607469510268313532947)
                      ·
                        rfl

theorem cell23_1691607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 4, 4, 1, 2, 3].length) (baseStart_1691607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1691607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1691607 prefixEnd_1691607 := by exact prefixLift 1691607
  have htrace : WordTrace (prefixWord ++ tailWord_1691607) baseStart_1691607 baseEnd_1691607 := by
    simpa [prefixWord, tailWord_1691607, baseEnd_1691607] using wordTrace_append hprefix tailTrace_1691607
  have hstable : (prefixWord ++ tailWord_1691607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1691607).length < 2 ^ (prefixWord ++ tailWord_1691607).sum := by decide
  have hdescent : baseEnd_1691607 < baseStart_1691607 := by decide
  rcases family_descends (prefixWord ++ tailWord_1691607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
