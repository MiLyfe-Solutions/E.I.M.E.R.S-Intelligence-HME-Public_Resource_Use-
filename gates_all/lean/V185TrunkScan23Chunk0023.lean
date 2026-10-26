import V185TrunkScan23Chunk0022

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_136405 : List Nat := [1, 3, 2, 4, 1, 3, 1, 1, 2, 5]
def baseStart_136405 : Nat := 118140960795 + 136405 * 2 ^ 59
def prefixEnd_136405 : Nat := 4983230072969 + 3 ^ 40 * 136405 * 2
def baseEnd_136405 : Nat := 23347109558881349503397

theorem tailTrace_136405 : CollatzResearch.WordTrace tailWord_136405 prefixEnd_136405 23347109558881349503397 := by
  unfold tailWord_136405
  simp only [CollatzResearch.WordTrace]
  refine ⟨4975099070835455964410669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3316732713890303976273779 4975099070835455964410669)
  ·
    refine ⟨1865662151563295986654001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4975099070835455964410669 1865662151563295986654001)
    ·
      refine ⟨1399246613672471989990501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1865662151563295986654001 1399246613672471989990501)
      ·
        refine ⟨262358740063588498123219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1399246613672471989990501 262358740063588498123219)
        ·
          refine ⟨393538110095382747184829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 262358740063588498123219 393538110095382747184829)
          ·
            refine ⟨147576791285768530194311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 393538110095382747184829 147576791285768530194311)
            ·
              refine ⟨221365186928652795291467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147576791285768530194311 221365186928652795291467)
              ·
                refine ⟨332047780392979192937201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221365186928652795291467 332047780392979192937201)
                ·
                  refine ⟨249035835294734394702901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 332047780392979192937201 249035835294734394702901)
                  ·
                    refine ⟨23347109558881349503397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 249035835294734394702901 23347109558881349503397)
                    ·
                      rfl

theorem cell23_136405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 1, 2, 5].length) (baseStart_136405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136405 prefixEnd_136405 := by exact prefixLift 136405
  have htrace : WordTrace (prefixWord ++ tailWord_136405) baseStart_136405 baseEnd_136405 := by
    simpa [prefixWord, tailWord_136405, baseEnd_136405] using wordTrace_append hprefix tailTrace_136405
  have hstable : (prefixWord ++ tailWord_136405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136405).length < 2 ^ (prefixWord ++ tailWord_136405).sum := by decide
  have hdescent : baseEnd_136405 < baseStart_136405 := by decide
  rcases family_descends (prefixWord ++ tailWord_136405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136408 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 1, 3, 4]
def baseStart_136408 : Nat := 118140960795 + 136408 * 2 ^ 59
def prefixEnd_136408 : Nat := 4983230072969 + 3 ^ 40 * 136408 * 2
def baseEnd_136408 : Nat := 70042869118607536772677

theorem tailTrace_136408 : CollatzResearch.WordTrace tailWord_136408 prefixEnd_136408 70042869118607536772677 := by
  unfold tailWord_136408
  simp only [CollatzResearch.WordTrace]
  refine ⟨2487604244912293738384939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3316805659883058317846585 2487604244912293738384939)
  ·
    refine ⟨3731406367368440607577409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2487604244912293738384939 3731406367368440607577409)
    ·
      refine ⟨2798554775526330455683057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3731406367368440607577409 2798554775526330455683057)
      ·
        refine ⟨2098916081644747841762293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2798554775526330455683057 2098916081644747841762293)
        ·
          refine ⟨196773382654195110165215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2098916081644747841762293 196773382654195110165215)
          ·
            refine ⟨295160073981292665247823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 196773382654195110165215 295160073981292665247823)
            ·
              refine ⟨442740110971938997871735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 295160073981292665247823 442740110971938997871735)
              ·
                refine ⟨664110166457908496807603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 442740110971938997871735 664110166457908496807603)
                ·
                  refine ⟨996165249686862745211405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 664110166457908496807603 996165249686862745211405)
                  ·
                    refine ⟨373561968632573529454277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 996165249686862745211405 373561968632573529454277)
                    ·
                      refine ⟨70042869118607536772677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 373561968632573529454277 70042869118607536772677)
                      ·
                        rfl

theorem cell23_136408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 1, 3, 4].length) (baseStart_136408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136408 prefixEnd_136408 := by exact prefixLift 136408
  have htrace : WordTrace (prefixWord ++ tailWord_136408) baseStart_136408 baseEnd_136408 := by
    simpa [prefixWord, tailWord_136408, baseEnd_136408] using wordTrace_append hprefix tailTrace_136408
  have hstable : (prefixWord ++ tailWord_136408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136408).length < 2 ^ (prefixWord ++ tailWord_136408).sum := by decide
  have hdescent : baseEnd_136408 < baseStart_136408 := by decide
  rcases family_descends (prefixWord ++ tailWord_136408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136435 : List Nat := [1, 1, 1, 2, 2, 5, 2, 4, 1, 4]
def baseStart_136435 : Nat := 118140960795 + 136435 * 2 ^ 59
def prefixEnd_136435 : Nat := 4983230072969 + 3 ^ 40 * 136435 * 2
def baseEnd_136435 : Nat := 23352244365426310378351

theorem tailTrace_136435 : CollatzResearch.WordTrace tailWord_136435 prefixEnd_136435 23352244365426310378351 := by
  unfold tailWord_136435
  simp only [CollatzResearch.WordTrace]
  refine ⟨4976193260726771088002759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3317462173817847392001839 4976193260726771088002759)
  ·
    refine ⟨7464289891090156632004139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4976193260726771088002759 7464289891090156632004139)
    ·
      refine ⟨11196434836635234948006209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7464289891090156632004139 11196434836635234948006209)
      ·
        refine ⟨8397326127476426211004657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11196434836635234948006209 8397326127476426211004657)
        ·
          refine ⟨6297994595607319658253493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8397326127476426211004657 6297994595607319658253493)
          ·
            refine ⟨590436993338186217961265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6297994595607319658253493 590436993338186217961265)
            ·
              refine ⟨442827745003639663470949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 590436993338186217961265 442827745003639663470949)
              ·
                refine ⟨83030202188182436900803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 442827745003639663470949 83030202188182436900803)
                ·
                  refine ⟨124545303282273655351205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83030202188182436900803 124545303282273655351205)
                  ·
                    refine ⟨23352244365426310378351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124545303282273655351205 23352244365426310378351)
                    ·
                      rfl

theorem cell23_136435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 4, 1, 4].length) (baseStart_136435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136435 prefixEnd_136435 := by exact prefixLift 136435
  have htrace : WordTrace (prefixWord ++ tailWord_136435) baseStart_136435 baseEnd_136435 := by
    simpa [prefixWord, tailWord_136435, baseEnd_136435] using wordTrace_append hprefix tailTrace_136435
  have hstable : (prefixWord ++ tailWord_136435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136435).length < 2 ^ (prefixWord ++ tailWord_136435).sum := by decide
  have hdescent : baseEnd_136435 < baseStart_136435 := by decide
  rcases family_descends (prefixWord ++ tailWord_136435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136485 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 4, 3, 2]
def baseStart_136485 : Nat := 118140960795 + 136485 * 2 ^ 59
def prefixEnd_136485 : Nat := 4983230072969 + 3 ^ 40 * 136485 * 2
def baseEnd_136485 : Nat := 70082407129003735509823

theorem tailTrace_136485 : CollatzResearch.WordTrace tailWord_136485 prefixEnd_136485 70082407129003735509823 := by
  unfold tailWord_136485
  simp only [CollatzResearch.WordTrace]
  refine ⟨4978016910545629627322909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3318677940363753084881939 4978016910545629627322909)
  ·
    refine ⟨1866756341454611110246091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4978016910545629627322909 1866756341454611110246091)
    ·
      refine ⟨2800134512181916665369137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1866756341454611110246091 2800134512181916665369137)
      ·
        refine ⟨2100100884136437499026853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2800134512181916665369137 2100100884136437499026853)
        ·
          refine ⟨393768915775582031067535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2100100884136437499026853 393768915775582031067535)
          ·
            refine ⟨590653373663373046601303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 393768915775582031067535 590653373663373046601303)
            ·
              refine ⟨885980060495059569901955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 590653373663373046601303 885980060495059569901955)
              ·
                refine ⟨1328970090742589354852933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 885980060495059569901955 1328970090742589354852933)
                ·
                  refine ⟨249181892014235504034925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1328970090742589354852933 249181892014235504034925)
                  ·
                    refine ⟨93443209505338314013097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 249181892014235504034925 93443209505338314013097)
                    ·
                      refine ⟨70082407129003735509823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93443209505338314013097 70082407129003735509823)
                      ·
                        rfl

theorem cell23_136485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 4, 3, 2].length) (baseStart_136485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136485 prefixEnd_136485 := by exact prefixLift 136485
  have htrace : WordTrace (prefixWord ++ tailWord_136485) baseStart_136485 baseEnd_136485 := by
    simpa [prefixWord, tailWord_136485, baseEnd_136485] using wordTrace_append hprefix tailTrace_136485
  have hstable : (prefixWord ++ tailWord_136485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136485).length < 2 ^ (prefixWord ++ tailWord_136485).sum := by decide
  have hdescent : baseEnd_136485 < baseStart_136485 := by decide
  rcases family_descends (prefixWord ++ tailWord_136485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136515 : List Nat := [1, 1, 1, 3, 1, 3, 1, 3, 5, 2, 2]
def baseStart_136515 : Nat := 118140960795 + 136515 * 2 ^ 59
def prefixEnd_136515 : Nat := 4983230072969 + 3 ^ 40 * 136515 * 2
def baseEnd_136515 : Nat := 70097811548638618134685

theorem tailTrace_136515 : CollatzResearch.WordTrace tailWord_136515 prefixEnd_136515 70097811548638618134685 := by
  unfold tailWord_136515
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979111100436944750914999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3319407400291296500609999 4979111100436944750914999)
  ·
    refine ⟨7468666650655417126372499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4979111100436944750914999 7468666650655417126372499)
    ·
      refine ⟨11202999975983125689558749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7468666650655417126372499 11202999975983125689558749)
      ·
        refine ⟨4201124990993672133584531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11202999975983125689558749 4201124990993672133584531)
        ·
          refine ⟨6301687486490508200376797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4201124990993672133584531 6301687486490508200376797)
          ·
            refine ⟨2363132807433940575141299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6301687486490508200376797 2363132807433940575141299)
            ·
              refine ⟨3544699211150910862711949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2363132807433940575141299 3544699211150910862711949)
              ·
                refine ⟨1329262204181591573516981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3544699211150910862711949 1329262204181591573516981)
                ·
                  refine ⟨124618331642024210017217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1329262204181591573516981 124618331642024210017217)
                  ·
                    refine ⟨93463748731518157512913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124618331642024210017217 93463748731518157512913)
                    ·
                      refine ⟨70097811548638618134685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93463748731518157512913 70097811548638618134685)
                      ·
                        rfl

theorem cell23_136515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 3, 5, 2, 2].length) (baseStart_136515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136515 prefixEnd_136515 := by exact prefixLift 136515
  have htrace : WordTrace (prefixWord ++ tailWord_136515) baseStart_136515 baseEnd_136515 := by
    simpa [prefixWord, tailWord_136515, baseEnd_136515] using wordTrace_append hprefix tailTrace_136515
  have hstable : (prefixWord ++ tailWord_136515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136515).length < 2 ^ (prefixWord ++ tailWord_136515).sum := by decide
  have hdescent : baseEnd_136515 < baseStart_136515 := by decide
  rcases family_descends (prefixWord ++ tailWord_136515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136521 : List Nat := [1, 2, 1, 1, 2, 3, 4, 9]
def baseStart_136521 : Nat := 118140960795 + 136521 * 2 ^ 59
def prefixEnd_136521 : Nat := 4983230072969 + 3 ^ 40 * 136521 * 2
def baseEnd_136521 : Nat := 2596329349354281283691

theorem tailTrace_136521 : CollatzResearch.WordTrace tailWord_136521 prefixEnd_136521 2596329349354281283691 := by
  unfold tailWord_136521
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979329938415207775633417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3319553292276805183755611 4979329938415207775633417)
  ·
    refine ⟨3734497453811405831725063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4979329938415207775633417 3734497453811405831725063)
    ·
      refine ⟨5601746180717108747587595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734497453811405831725063 5601746180717108747587595)
      ·
        refine ⟨8402619271075663121381393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5601746180717108747587595 8402619271075663121381393)
        ·
          refine ⟨6301964453306747341036045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8402619271075663121381393 6301964453306747341036045)
          ·
            refine ⟨2363236669990030252888517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6301964453306747341036045 2363236669990030252888517)
            ·
              refine ⟨443106875623130672416597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2363236669990030252888517 443106875623130672416597)
              ·
                refine ⟨2596329349354281283691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 443106875623130672416597 2596329349354281283691)
                ·
                  rfl

theorem cell23_136521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 9].length) (baseStart_136521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136521 prefixEnd_136521 := by exact prefixLift 136521
  have htrace : WordTrace (prefixWord ++ tailWord_136521) baseStart_136521 baseEnd_136521 := by
    simpa [prefixWord, tailWord_136521, baseEnd_136521] using wordTrace_append hprefix tailTrace_136521
  have hstable : (prefixWord ++ tailWord_136521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136521).length < 2 ^ (prefixWord ++ tailWord_136521).sum := by decide
  have hdescent : baseEnd_136521 < baseStart_136521 := by decide
  rcases family_descends (prefixWord ++ tailWord_136521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136528 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4]
def baseStart_136528 : Nat := 118140960795 + 136528 * 2 ^ 59
def prefixEnd_136528 : Nat := 4983230072969 + 3 ^ 40 * 136528 * 2
def baseEnd_136528 : Nat := 70104486797147067272125

theorem tailTrace_136528 : CollatzResearch.WordTrace tailWord_136528 prefixEnd_136528 70104486797147067272125 := by
  unfold tailWord_136528
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489792624694923985569119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3319723499593231980758825 2489792624694923985569119)
  ·
    refine ⟨3734688937042385978353679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2489792624694923985569119 3734688937042385978353679)
    ·
      refine ⟨5602033405563578967530519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3734688937042385978353679 5602033405563578967530519)
      ·
        refine ⟨8403050108345368451295779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5602033405563578967530519 8403050108345368451295779)
        ·
          refine ⟨12604575162518052676943669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8403050108345368451295779 12604575162518052676943669)
          ·
            refine ⟨1181678921486067438463469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12604575162518052676943669 1181678921486067438463469)
            ·
              refine ⟨443129595557275289423801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1181678921486067438463469 443129595557275289423801)
              ·
                refine ⟨332347196667956467067851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 443129595557275289423801 332347196667956467067851)
                ·
                  refine ⟨498520795001934700601777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332347196667956467067851 498520795001934700601777)
                  ·
                    refine ⟨373890596251451025451333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 498520795001934700601777 373890596251451025451333)
                    ·
                      refine ⟨70104486797147067272125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 373890596251451025451333 70104486797147067272125)
                      ·
                        rfl

theorem cell23_136528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 1, 2, 4].length) (baseStart_136528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136528 prefixEnd_136528 := by exact prefixLift 136528
  have htrace : WordTrace (prefixWord ++ tailWord_136528) baseStart_136528 baseEnd_136528 := by
    simpa [prefixWord, tailWord_136528, baseEnd_136528] using wordTrace_append hprefix tailTrace_136528
  have hstable : (prefixWord ++ tailWord_136528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136528).length < 2 ^ (prefixWord ++ tailWord_136528).sum := by decide
  have hdescent : baseEnd_136528 < baseStart_136528 := by decide
  rcases family_descends (prefixWord ++ tailWord_136528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136532 : List Nat := [2, 4, 1, 1, 2, 1, 5, 1, 1, 1, 4]
def baseStart_136532 : Nat := 118140960795 + 136532 * 2 ^ 59
def prefixEnd_136532 : Nat := 4983230072969 + 3 ^ 40 * 136532 * 2
def baseEnd_136532 : Nat := 70106540719765051622107

theorem tailTrace_136532 : CollatzResearch.WordTrace tailWord_136532 prefixEnd_136532 70106540719765051622107 := by
  unfold tailWord_136532
  simp only [CollatzResearch.WordTrace]
  refine ⟨2489865570687678327141925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3319820760916904436189233 2489865570687678327141925)
  ·
    refine ⟨466849794503939686339111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2489865570687678327141925 466849794503939686339111)
    ·
      refine ⟨700274691755909529508667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 466849794503939686339111 700274691755909529508667)
      ·
        refine ⟨1050412037633864294263001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 700274691755909529508667 1050412037633864294263001)
        ·
          refine ⟨787809028225398220697251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1050412037633864294263001 787809028225398220697251)
          ·
            refine ⟨1181713542338097331045877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 787809028225398220697251 1181713542338097331045877)
            ·
              refine ⟨110785644594196624785551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1181713542338097331045877 110785644594196624785551)
              ·
                refine ⟨166178466891294937178327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 110785644594196624785551 166178466891294937178327)
                ·
                  refine ⟨249267700336942405767491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166178466891294937178327 249267700336942405767491)
                  ·
                    refine ⟨373901550505413608651237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 249267700336942405767491 373901550505413608651237)
                    ·
                      refine ⟨70106540719765051622107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 373901550505413608651237 70106540719765051622107)
                      ·
                        rfl

theorem cell23_136532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 5, 1, 1, 1, 4].length) (baseStart_136532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136532 prefixEnd_136532 := by exact prefixLift 136532
  have htrace : WordTrace (prefixWord ++ tailWord_136532) baseStart_136532 baseEnd_136532 := by
    simpa [prefixWord, tailWord_136532, baseEnd_136532] using wordTrace_append hprefix tailTrace_136532
  have hstable : (prefixWord ++ tailWord_136532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136532).length < 2 ^ (prefixWord ++ tailWord_136532).sum := by decide
  have hdescent : baseEnd_136532 < baseStart_136532 := by decide
  rcases family_descends (prefixWord ++ tailWord_136532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136535 : List Nat := [1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 5]
def baseStart_136535 : Nat := 118140960795 + 136535 * 2 ^ 59
def prefixEnd_136535 : Nat := 4983230072969 + 3 ^ 40 * 136535 * 2
def baseEnd_136535 : Nat := 70108081161728539884593

theorem tailTrace_136535 : CollatzResearch.WordTrace tailWord_136535 prefixEnd_136535 70108081161728539884593 := by
  unfold tailWord_136535
  simp only [CollatzResearch.WordTrace]
  refine ⟨4979840560364488166643059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3319893706909658777762039 4979840560364488166643059)
  ·
    refine ⟨7469760840546732249964589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4979840560364488166643059 7469760840546732249964589)
    ·
      refine ⟨2801160315205024593736721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7469760840546732249964589 2801160315205024593736721)
      ·
        refine ⟨2100870236403768445302541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2801160315205024593736721 2100870236403768445302541)
        ·
          refine ⟨787826338651413166988453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2100870236403768445302541 787826338651413166988453)
          ·
            refine ⟨147717438497139968810335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 787826338651413166988453 147717438497139968810335)
            ·
              refine ⟨221576157745709953215503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147717438497139968810335 221576157745709953215503)
              ·
                refine ⟨332364236618564929823255, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221576157745709953215503 332364236618564929823255)
                ·
                  refine ⟨498546354927847394734883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332364236618564929823255 498546354927847394734883)
                  ·
                    refine ⟨747819532391771092102325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 498546354927847394734883 747819532391771092102325)
                    ·
                      refine ⟨70108081161728539884593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 747819532391771092102325 70108081161728539884593)
                      ·
                        rfl

theorem cell23_136535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 1, 5].length) (baseStart_136535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136535 prefixEnd_136535 := by exact prefixLift 136535
  have htrace : WordTrace (prefixWord ++ tailWord_136535) baseStart_136535 baseEnd_136535 := by
    simpa [prefixWord, tailWord_136535, baseEnd_136535] using wordTrace_append hprefix tailTrace_136535
  have hstable : (prefixWord ++ tailWord_136535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136535).length < 2 ^ (prefixWord ++ tailWord_136535).sum := by decide
  have hdescent : baseEnd_136535 < baseStart_136535 := by decide
  rcases family_descends (prefixWord ++ tailWord_136535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136549 : List Nat := [1, 3, 1, 3, 1, 2, 3, 4, 1, 2, 2]
def baseStart_136549 : Nat := 118140960795 + 136549 * 2 ^ 59
def prefixEnd_136549 : Nat := 4983230072969 + 3 ^ 40 * 136549 * 2
def baseEnd_136549 : Nat := 70115269890891485109529

theorem tailTrace_136549 : CollatzResearch.WordTrace tailWord_136549 prefixEnd_136549 70115269890891485109529 := by
  unfold tailWord_136549
  simp only [CollatzResearch.WordTrace]
  refine ⟨4980351182313768557652701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3320234121542512371768467 4980351182313768557652701)
  ·
    refine ⟨1867631693367663209119763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4980351182313768557652701 1867631693367663209119763)
    ·
      refine ⟨2801447540051494813679645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1867631693367663209119763 2801447540051494813679645)
      ·
        refine ⟨1050542827519310555129867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2801447540051494813679645 1050542827519310555129867)
        ·
          refine ⟨1575814241278965832694801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1050542827519310555129867 1575814241278965832694801)
          ·
            refine ⟨1181860680959224374521101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1575814241278965832694801 1181860680959224374521101)
            ·
              refine ⟨443197755359709140445413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1181860680959224374521101 443197755359709140445413)
              ·
                refine ⟨83099579129945463833515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 443197755359709140445413 83099579129945463833515)
                ·
                  refine ⟨124649368694918195750273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83099579129945463833515 124649368694918195750273)
                  ·
                    refine ⟨93487026521188646812705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 124649368694918195750273 93487026521188646812705)
                    ·
                      refine ⟨70115269890891485109529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93487026521188646812705 70115269890891485109529)
                      ·
                        rfl

theorem cell23_136549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 4, 1, 2, 2].length) (baseStart_136549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136549 prefixEnd_136549 := by exact prefixLift 136549
  have htrace : WordTrace (prefixWord ++ tailWord_136549) baseStart_136549 baseEnd_136549 := by
    simpa [prefixWord, tailWord_136549, baseEnd_136549] using wordTrace_append hprefix tailTrace_136549
  have hstable : (prefixWord ++ tailWord_136549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136549).length < 2 ^ (prefixWord ++ tailWord_136549).sum := by decide
  have hdescent : baseEnd_136549 < baseStart_136549 := by decide
  rcases family_descends (prefixWord ++ tailWord_136549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136616 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_136616 : Nat := 118140960795 + 136616 * 2 ^ 59
def prefixEnd_136616 : Nat := 4983230072969 + 3 ^ 40 * 136616 * 2
def baseEnd_136616 : Nat := 70149673094742722971721

theorem tailTrace_136616 : CollatzResearch.WordTrace tailWord_136616 prefixEnd_136616 70149673094742722971721 := by
  unfold tailWord_136616
  simp only [CollatzResearch.WordTrace]
  refine ⟨2491397436535519500170851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3321863248714026000227801 2491397436535519500170851)
  ·
    refine ⟨3737096154803279250256277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2491397436535519500170851 3737096154803279250256277)
    ·
      refine ⟨175176382256403714855763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3737096154803279250256277 175176382256403714855763)
      ·
        refine ⟨262764573384605572283645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 175176382256403714855763 262764573384605572283645)
        ·
          refine ⟨98536715019227089606367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 262764573384605572283645 98536715019227089606367)
          ·
            refine ⟨147805072528840634409551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 98536715019227089606367 147805072528840634409551)
            ·
              refine ⟨221707608793260951614327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 147805072528840634409551 221707608793260951614327)
              ·
                refine ⟨332561413189891427421491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221707608793260951614327 332561413189891427421491)
                ·
                  refine ⟨498842119784837141132237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 332561413189891427421491 498842119784837141132237)
                  ·
                    refine ⟨187065794919313927924589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 498842119784837141132237 187065794919313927924589)
                    ·
                      refine ⟨70149673094742722971721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 187065794919313927924589 70149673094742722971721)
                      ·
                        rfl

theorem cell23_136616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_136616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136616 prefixEnd_136616 := by exact prefixLift 136616
  have htrace : WordTrace (prefixWord ++ tailWord_136616) baseStart_136616 baseEnd_136616 := by
    simpa [prefixWord, tailWord_136616, baseEnd_136616] using wordTrace_append hprefix tailTrace_136616
  have hstable : (prefixWord ++ tailWord_136616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136616).length < 2 ^ (prefixWord ++ tailWord_136616).sum := by decide
  have hdescent : baseEnd_136616 < baseStart_136616 := by decide
  rcases family_descends (prefixWord ++ tailWord_136616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136662 : List Nat := [5, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_136662 : Nat := 118140960795 + 136662 * 2 ^ 59
def prefixEnd_136662 : Nat := 4983230072969 + 3 ^ 40 * 136662 * 2
def baseEnd_136662 : Nat := 7797032578316615888501

theorem tailTrace_136662 : CollatzResearch.WordTrace tailWord_136662 prefixEnd_136662 7797032578316615888501 := by
  unfold tailWord_136662
  simp only [CollatzResearch.WordTrace]
  refine ⟨311529539431524303532265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3322981753936259237677493 311529539431524303532265)
  ·
    refine ⟨233647154573643227649199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 311529539431524303532265 233647154573643227649199)
    ·
      refine ⟨350470731860464841473799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 233647154573643227649199 350470731860464841473799)
      ·
        refine ⟨525706097790697262210699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 350470731860464841473799 525706097790697262210699)
        ·
          refine ⟨788559146686045893316049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 525706097790697262210699 788559146686045893316049)
          ·
            refine ⟨591419360014534419987037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 788559146686045893316049 591419360014534419987037)
            ·
              refine ⟨221782260005450407495139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 591419360014534419987037 221782260005450407495139)
              ·
                refine ⟨332673390008175611242709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 221782260005450407495139 332673390008175611242709)
                ·
                  refine ⟨7797032578316615888501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 332673390008175611242709 7797032578316615888501)
                  ·
                    rfl

theorem cell23_136662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_136662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136662 prefixEnd_136662 := by exact prefixLift 136662
  have htrace : WordTrace (prefixWord ++ tailWord_136662) baseStart_136662 baseEnd_136662 := by
    simpa [prefixWord, tailWord_136662, baseEnd_136662] using wordTrace_append hprefix tailTrace_136662
  have hstable : (prefixWord ++ tailWord_136662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136662).length < 2 ^ (prefixWord ++ tailWord_136662).sum := by decide
  have hdescent : baseEnd_136662 < baseStart_136662 := by decide
  rcases family_descends (prefixWord ++ tailWord_136662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136695 : List Nat := [1, 1, 3, 1, 1, 1, 1, 3, 3, 6, 2]
def baseStart_136695 : Nat := 118140960795 + 136695 * 2 ^ 59
def prefixEnd_136695 : Nat := 4983230072969 + 3 ^ 40 * 136695 * 2
def baseEnd_136695 : Nat := 70190238066447913883857

theorem tailTrace_136695 : CollatzResearch.WordTrace tailWord_136695 prefixEnd_136695 70190238066447913883857 := by
  unfold tailWord_136695
  simp only [CollatzResearch.WordTrace]
  refine ⟨4985676239784835492467539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3323784159856556994978359 4985676239784835492467539)
  ·
    refine ⟨7478514359677253238701309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4985676239784835492467539 7478514359677253238701309)
    ·
      refine ⟨2804442884878969964512991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7478514359677253238701309 2804442884878969964512991)
      ·
        refine ⟨4206664327318454946769487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2804442884878969964512991 4206664327318454946769487)
        ·
          refine ⟨6309996490977682420154231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4206664327318454946769487 6309996490977682420154231)
          ·
            refine ⟨9464994736466523630231347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6309996490977682420154231 9464994736466523630231347)
            ·
              refine ⟨14197492104699785445347021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9464994736466523630231347 14197492104699785445347021)
              ·
                refine ⟨5324059539262419542005133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14197492104699785445347021 5324059539262419542005133)
                ·
                  refine ⟨1996522327223407328251925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5324059539262419542005133 1996522327223407328251925)
                  ·
                    refine ⟨93586984088597218511809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1996522327223407328251925 93586984088597218511809)
                    ·
                      refine ⟨70190238066447913883857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93586984088597218511809 70190238066447913883857)
                      ·
                        rfl

theorem cell23_136695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 6, 2].length) (baseStart_136695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136695 prefixEnd_136695 := by exact prefixLift 136695
  have htrace : WordTrace (prefixWord ++ tailWord_136695) baseStart_136695 baseEnd_136695 := by
    simpa [prefixWord, tailWord_136695, baseEnd_136695] using wordTrace_append hprefix tailTrace_136695
  have hstable : (prefixWord ++ tailWord_136695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136695).length < 2 ^ (prefixWord ++ tailWord_136695).sum := by decide
  have hdescent : baseEnd_136695 < baseStart_136695 := by decide
  rcases family_descends (prefixWord ++ tailWord_136695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136735 : List Nat := [1, 1, 2, 4, 1, 1, 4, 3, 6]
def baseStart_136735 : Nat := 118140960795 + 136735 * 2 ^ 59
def prefixEnd_136735 : Nat := 4983230072969 + 3 ^ 40 * 136735 * 2
def baseEnd_136735 : Nat := 7801197476958639709297

theorem tailTrace_136735 : CollatzResearch.WordTrace tailWord_136735 prefixEnd_136735 7801197476958639709297 := by
  unfold tailWord_136735
  simp only [CollatzResearch.WordTrace]
  refine ⟨4987135159639922323923659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3324756773093281549282439 4987135159639922323923659)
  ·
    refine ⟨7480702739459883485885489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4987135159639922323923659 7480702739459883485885489)
    ·
      refine ⟨5610527054594912614414117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7480702739459883485885489 5610527054594912614414117)
      ·
        refine ⟨1051973822736546115202647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5610527054594912614414117 1051973822736546115202647)
        ·
          refine ⟨1577960734104819172803971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1051973822736546115202647 1577960734104819172803971)
          ·
            refine ⟨2366941101157228759205957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1577960734104819172803971 2366941101157228759205957)
            ·
              refine ⟨443801456466980392351117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2366941101157228759205957 443801456466980392351117)
              ·
                refine ⟨166425546175117647131669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 443801456466980392351117 166425546175117647131669)
                ·
                  refine ⟨7801197476958639709297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 166425546175117647131669 7801197476958639709297)
                  ·
                    rfl

theorem cell23_136735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 3, 6].length) (baseStart_136735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136735 prefixEnd_136735 := by exact prefixLift 136735
  have htrace : WordTrace (prefixWord ++ tailWord_136735) baseStart_136735 baseEnd_136735 := by
    simpa [prefixWord, tailWord_136735, baseEnd_136735] using wordTrace_append hprefix tailTrace_136735
  have hstable : (prefixWord ++ tailWord_136735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136735).length < 2 ^ (prefixWord ++ tailWord_136735).sum := by decide
  have hdescent : baseEnd_136735 < baseStart_136735 := by decide
  rcases family_descends (prefixWord ++ tailWord_136735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136762 : List Nat := [3, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3]
def baseStart_136762 : Nat := 118140960795 + 136762 * 2 ^ 59
def prefixEnd_136762 : Nat := 4983230072969 + 3 ^ 40 * 136762 * 2
def baseEnd_136762 : Nat := 70224641270299151746049

theorem tailTrace_136762 : CollatzResearch.WordTrace tailWord_136762 prefixEnd_136762 70224641270299151746049 := by
  unfold tailWord_136762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247029982635526483789135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3325413287028070623437693 1247029982635526483789135)
  ·
    refine ⟨1870544973953289725683703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1247029982635526483789135 1870544973953289725683703)
    ·
      refine ⟨2805817460929934588525555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1870544973953289725683703 2805817460929934588525555)
      ·
        refine ⟨4208726191394901882788333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2805817460929934588525555 4208726191394901882788333)
        ·
          refine ⟨1578272321773088206045625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4208726191394901882788333 1578272321773088206045625)
          ·
            refine ⟨1183704241329816154534219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1578272321773088206045625 1183704241329816154534219)
            ·
              refine ⟨1775556361994724231801329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1183704241329816154534219 1775556361994724231801329)
              ·
                refine ⟨1331667271496043173850997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1775556361994724231801329 1331667271496043173850997)
                ·
                  refine ⟨124843806702754047548531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1331667271496043173850997 124843806702754047548531)
                  ·
                    refine ⟨187265710054131071322797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 124843806702754047548531 187265710054131071322797)
                    ·
                      refine ⟨70224641270299151746049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 187265710054131071322797 70224641270299151746049)
                      ·
                        rfl

theorem cell23_136762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 5, 1, 3].length) (baseStart_136762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136762 prefixEnd_136762 := by exact prefixLift 136762
  have htrace : WordTrace (prefixWord ++ tailWord_136762) baseStart_136762 baseEnd_136762 := by
    simpa [prefixWord, tailWord_136762, baseEnd_136762] using wordTrace_append hprefix tailTrace_136762
  have hstable : (prefixWord ++ tailWord_136762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136762).length < 2 ^ (prefixWord ++ tailWord_136762).sum := by decide
  have hdescent : baseEnd_136762 < baseStart_136762 := by decide
  rcases family_descends (prefixWord ++ tailWord_136762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136815 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 4]
def baseStart_136815 : Nat := 118140960795 + 136815 * 2 ^ 59
def prefixEnd_136815 : Nat := 4983230072969 + 3 ^ 40 * 136815 * 2
def baseEnd_136815 : Nat := 70251855744987444383305

theorem tailTrace_136815 : CollatzResearch.WordTrace tailWord_136815 prefixEnd_136815 70251855744987444383305 := by
  unfold tailWord_136815
  simp only [CollatzResearch.WordTrace]
  refine ⟨4990052999350095986835899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3326701999566730657890599 4990052999350095986835899)
  ·
    refine ⟨7485079499025143980253849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4990052999350095986835899 7485079499025143980253849)
    ·
      refine ⟨5613809624268857985190387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7485079499025143980253849 5613809624268857985190387)
      ·
        refine ⟨8420714436403286977785581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5613809624268857985190387 8420714436403286977785581)
        ·
          refine ⟨3157767913651232616669593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8420714436403286977785581 3157767913651232616669593)
          ·
            refine ⟨2368325935238424462502195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3157767913651232616669593 2368325935238424462502195)
            ·
              refine ⟨3552488902857636693753293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2368325935238424462502195 3552488902857636693753293)
              ·
                refine ⟨1332183338571613760157485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3552488902857636693753293 1332183338571613760157485)
                ·
                  refine ⟨499568751964355160059057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1332183338571613760157485 499568751964355160059057)
                  ·
                    refine ⟨374676563973266370044293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 499568751964355160059057 374676563973266370044293)
                    ·
                      refine ⟨70251855744987444383305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 374676563973266370044293 70251855744987444383305)
                      ·
                        rfl

theorem cell23_136815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 2, 4].length) (baseStart_136815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136815 prefixEnd_136815 := by exact prefixLift 136815
  have htrace : WordTrace (prefixWord ++ tailWord_136815) baseStart_136815 baseEnd_136815 := by
    simpa [prefixWord, tailWord_136815, baseEnd_136815] using wordTrace_append hprefix tailTrace_136815
  have hstable : (prefixWord ++ tailWord_136815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136815).length < 2 ^ (prefixWord ++ tailWord_136815).sum := by decide
  have hdescent : baseEnd_136815 < baseStart_136815 := by decide
  rcases family_descends (prefixWord ++ tailWord_136815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136842 : List Nat := [3, 1, 2, 3, 2, 2, 2, 8]
def baseStart_136842 : Nat := 118140960795 + 136842 * 2 ^ 59
def prefixEnd_136842 : Nat := 4983230072969 + 3 ^ 40 * 136842 * 2
def baseEnd_136842 : Nat := 2602434063802179212803

theorem tailTrace_136842 : CollatzResearch.WordTrace tailWord_136842 prefixEnd_136842 2602434063802179212803 := by
  unfold tailWord_136842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247759442563069899517195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3327358513501519732045853 1247759442563069899517195)
  ·
    refine ⟨1871639163844604849275793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1247759442563069899517195 1871639163844604849275793)
    ·
      refine ⟨1403729372883453636956845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1871639163844604849275793 1403729372883453636956845)
      ·
        refine ⟨526398514831295113858817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1403729372883453636956845 526398514831295113858817)
        ·
          refine ⟨394798886123471335394113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 526398514831295113858817 394798886123471335394113)
          ·
            refine ⟨296099164592603501545585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 394798886123471335394113 296099164592603501545585)
            ·
              refine ⟨222074373444452626159189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296099164592603501545585 222074373444452626159189)
              ·
                refine ⟨2602434063802179212803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 222074373444452626159189 2602434063802179212803)
                ·
                  rfl

theorem cell23_136842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_136842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136842 prefixEnd_136842 := by exact prefixLift 136842
  have htrace : WordTrace (prefixWord ++ tailWord_136842) baseStart_136842 baseEnd_136842 := by
    simpa [prefixWord, tailWord_136842, baseEnd_136842] using wordTrace_append hprefix tailTrace_136842
  have hstable : (prefixWord ++ tailWord_136842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136842).length < 2 ^ (prefixWord ++ tailWord_136842).sum := by decide
  have hdescent : baseEnd_136842 < baseStart_136842 := by decide
  rcases family_descends (prefixWord ++ tailWord_136842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136846 : List Nat := [4, 1, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_136846 : Nat := 118140960795 + 136846 * 2 ^ 59
def prefixEnd_136846 : Nat := 4983230072969 + 3 ^ 40 * 136846 * 2
def baseEnd_136846 : Nat := 23422591215092274365221

theorem tailTrace_136846 : CollatzResearch.WordTrace tailWord_136846 prefixEnd_136846 23422591215092274365221 := by
  unfold tailWord_136846
  simp only [CollatzResearch.WordTrace]
  refine ⟨623897957779723535151799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3327455774825192187476261 623897957779723535151799)
  ·
    refine ⟨935846936669585302727699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 623897957779723535151799 935846936669585302727699)
    ·
      refine ⟨1403770405004377954091549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 935846936669585302727699 1403770405004377954091549)
      ·
        refine ⟨526413901876641732784331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1403770405004377954091549 526413901876641732784331)
        ·
          refine ⟨789620852814962599176497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526413901876641732784331 789620852814962599176497)
          ·
            refine ⟨592215639611221949382373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789620852814962599176497 592215639611221949382373)
            ·
              refine ⟨111040432427104115509195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 592215639611221949382373 111040432427104115509195)
              ·
                refine ⟨166560648640656173263793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111040432427104115509195 166560648640656173263793)
                ·
                  refine ⟨124920486480492129947845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 166560648640656173263793 124920486480492129947845)
                  ·
                    refine ⟨23422591215092274365221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 124920486480492129947845 23422591215092274365221)
                    ·
                      rfl

theorem cell23_136846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_136846 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136846 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136846 prefixEnd_136846 := by exact prefixLift 136846
  have htrace : WordTrace (prefixWord ++ tailWord_136846) baseStart_136846 baseEnd_136846 := by
    simpa [prefixWord, tailWord_136846, baseEnd_136846] using wordTrace_append hprefix tailTrace_136846
  have hstable : (prefixWord ++ tailWord_136846).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136846).length < 2 ^ (prefixWord ++ tailWord_136846).sum := by decide
  have hdescent : baseEnd_136846 < baseStart_136846 := by decide
  rcases family_descends (prefixWord ++ tailWord_136846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136856 : List Nat := [2, 1, 2, 4, 1, 4, 1, 2, 1, 2, 3]
def baseStart_136856 : Nat := 118140960795 + 136856 * 2 ^ 59
def prefixEnd_136856 : Nat := 4983230072969 + 3 ^ 40 * 136856 * 2
def baseEnd_136856 : Nat := 70272908451821783970617

theorem tailTrace_136856 : CollatzResearch.WordTrace tailWord_136856 prefixEnd_136856 70272908451821783970617 := by
  unfold tailWord_136856
  simp only [CollatzResearch.WordTrace]
  refine ⟨2495774196100779994539211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3327698928134373326052281 2495774196100779994539211)
  ·
    refine ⟨3743661294151169991808817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2495774196100779994539211 3743661294151169991808817)
    ·
      refine ⟨2807745970613377493856613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3743661294151169991808817 2807745970613377493856613)
      ·
        refine ⟨526452369490008280098115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2807745970613377493856613 526452369490008280098115)
        ·
          refine ⟨789678554235012420147173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526452369490008280098115 789678554235012420147173)
          ·
            refine ⟨148064728919064828777595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 789678554235012420147173 148064728919064828777595)
            ·
              refine ⟨222097093378597243166393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148064728919064828777595 222097093378597243166393)
              ·
                refine ⟨166572820033947932374795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 222097093378597243166393 166572820033947932374795)
                ·
                  refine ⟨249859230050921898562193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 166572820033947932374795 249859230050921898562193)
                  ·
                    refine ⟨187394422538191423921645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 249859230050921898562193 187394422538191423921645)
                    ·
                      refine ⟨70272908451821783970617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 187394422538191423921645 70272908451821783970617)
                      ·
                        rfl

theorem cell23_136856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_136856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136856 prefixEnd_136856 := by exact prefixLift 136856
  have htrace : WordTrace (prefixWord ++ tailWord_136856) baseStart_136856 baseEnd_136856 := by
    simpa [prefixWord, tailWord_136856, baseEnd_136856] using wordTrace_append hprefix tailTrace_136856
  have hstable : (prefixWord ++ tailWord_136856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136856).length < 2 ^ (prefixWord ++ tailWord_136856).sum := by decide
  have hdescent : baseEnd_136856 < baseStart_136856 := by decide
  rcases family_descends (prefixWord ++ tailWord_136856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136866 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 1, 2, 4]
def baseStart_136866 : Nat := 118140960795 + 136866 * 2 ^ 59
def prefixEnd_136866 : Nat := 4983230072969 + 3 ^ 40 * 136866 * 2
def baseEnd_136866 : Nat := 70278043258366744845571

theorem tailTrace_136866 : CollatzResearch.WordTrace tailWord_136866 prefixEnd_136866 70278043258366744845571 := by
  unfold tailWord_136866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1247978280541332924235613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3327942081443554464628301 1247978280541332924235613)
  ·
    refine ⟨467991855202999846588355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1247978280541332924235613 467991855202999846588355)
    ·
      refine ⟨701987782804499769882533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 467991855202999846588355 701987782804499769882533)
      ·
        refine ⟨131622709275843706852975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 701987782804499769882533 131622709275843706852975)
        ·
          refine ⟨197434063913765560279463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131622709275843706852975 197434063913765560279463)
          ·
            refine ⟨296151095870648340419195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197434063913765560279463 296151095870648340419195)
            ·
              refine ⟨444226643805972510628793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296151095870648340419195 444226643805972510628793)
              ·
                refine ⟨333169982854479382971595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 444226643805972510628793 333169982854479382971595)
                ·
                  refine ⟨499754974281719074457393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333169982854479382971595 499754974281719074457393)
                  ·
                    refine ⟨374816230711289305843045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 499754974281719074457393 374816230711289305843045)
                    ·
                      refine ⟨70278043258366744845571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 374816230711289305843045 70278043258366744845571)
                      ·
                        rfl

theorem cell23_136866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_136866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136866 prefixEnd_136866 := by exact prefixLift 136866
  have htrace : WordTrace (prefixWord ++ tailWord_136866) baseStart_136866 baseEnd_136866 := by
    simpa [prefixWord, tailWord_136866, baseEnd_136866] using wordTrace_append hprefix tailTrace_136866
  have hstable : (prefixWord ++ tailWord_136866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136866).length < 2 ^ (prefixWord ++ tailWord_136866).sum := by decide
  have hdescent : baseEnd_136866 < baseStart_136866 := by decide
  rcases family_descends (prefixWord ++ tailWord_136866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_136892 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 2, 3, 4]
def baseStart_136892 : Nat := 118140960795 + 136892 * 2 ^ 59
def prefixEnd_136892 : Nat := 4983230072969 + 3 ^ 40 * 136892 * 2
def baseEnd_136892 : Nat := 70291393755383643120451

theorem tailTrace_136892 : CollatzResearch.WordTrace tailWord_136892 prefixEnd_136892 70291393755383643120451 := by
  unfold tailWord_136892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2496430710035569068694465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3328574280047425424925953 2496430710035569068694465)
  ·
    refine ⟨1872323032526676801520849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2496430710035569068694465 1872323032526676801520849)
    ·
      refine ⟨1404242274395007601140637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1872323032526676801520849 1404242274395007601140637)
      ·
        refine ⟨526590852898127850427739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1404242274395007601140637 526590852898127850427739)
        ·
          refine ⟨789886279347191775641609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 526590852898127850427739 789886279347191775641609)
          ·
            refine ⟨592414709510393831731207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 789886279347191775641609 592414709510393831731207)
            ·
              refine ⟨888622064265590747596811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 592414709510393831731207 888622064265590747596811)
              ·
                refine ⟨1332933096398386121395217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 888622064265590747596811 1332933096398386121395217)
                ·
                  refine ⟨999699822298789591046413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1332933096398386121395217 999699822298789591046413)
                  ·
                    refine ⟨374887433362046096642405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 999699822298789591046413 374887433362046096642405)
                    ·
                      refine ⟨70291393755383643120451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 374887433362046096642405 70291393755383643120451)
                      ·
                        rfl

theorem cell23_136892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_136892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_136892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_136892 prefixEnd_136892 := by exact prefixLift 136892
  have htrace : WordTrace (prefixWord ++ tailWord_136892) baseStart_136892 baseEnd_136892 := by
    simpa [prefixWord, tailWord_136892, baseEnd_136892] using wordTrace_append hprefix tailTrace_136892
  have hstable : (prefixWord ++ tailWord_136892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_136892).length < 2 ^ (prefixWord ++ tailWord_136892).sum := by decide
  have hdescent : baseEnd_136892 < baseStart_136892 := by decide
  rcases family_descends (prefixWord ++ tailWord_136892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137006 : List Nat := [4, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5]
def baseStart_137006 : Nat := 118140960795 + 137006 * 2 ^ 59
def prefixEnd_137006 : Nat := 4983230072969 + 3 ^ 40 * 137006 * 2
def baseEnd_137006 : Nat := 70349930549996197094927

theorem tailTrace_137006 : CollatzResearch.WordTrace tailWord_137006 prefixEnd_137006 70349930549996197094927 := by
  unfold tailWord_137006
  simp only [CollatzResearch.WordTrace]
  refine ⟨624627417707266950879859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3331346227772090404692581 624627417707266950879859)
  ·
    refine ⟨936941126560900426319789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 624627417707266950879859 936941126560900426319789)
    ·
      refine ⟨351352922460337659869921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 936941126560900426319789 351352922460337659869921)
      ·
        refine ⟨263514691845253244902441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 351352922460337659869921 263514691845253244902441)
        ·
          refine ⟨197636018883939933676831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 263514691845253244902441 197636018883939933676831)
          ·
            refine ⟨296454028325909900515247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197636018883939933676831 296454028325909900515247)
            ·
              refine ⟨444681042488864850772871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 296454028325909900515247 444681042488864850772871)
              ·
                refine ⟨667021563733297276159307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 444681042488864850772871 667021563733297276159307)
                ·
                  refine ⟨1000532345599945914238961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 667021563733297276159307 1000532345599945914238961)
                  ·
                    refine ⟨750399259199959435679221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1000532345599945914238961 750399259199959435679221)
                    ·
                      refine ⟨70349930549996197094927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 750399259199959435679221 70349930549996197094927)
                      ·
                        rfl

theorem cell23_137006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_137006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137006 prefixEnd_137006 := by exact prefixLift 137006
  have htrace : WordTrace (prefixWord ++ tailWord_137006) baseStart_137006 baseEnd_137006 := by
    simpa [prefixWord, tailWord_137006, baseEnd_137006] using wordTrace_append hprefix tailTrace_137006
  have hstable : (prefixWord ++ tailWord_137006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137006).length < 2 ^ (prefixWord ++ tailWord_137006).sum := by decide
  have hdescent : baseEnd_137006 < baseStart_137006 := by decide
  rcases family_descends (prefixWord ++ tailWord_137006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137069 : List Nat := [1, 5, 1, 1, 1, 1, 3, 2, 3, 5]
def baseStart_137069 : Nat := 118140960795 + 137069 * 2 ^ 59
def prefixEnd_137069 : Nat := 4983230072969 + 3 ^ 40 * 137069 * 2
def baseEnd_137069 : Nat := 23460759943743150202379

theorem tailTrace_137069 : CollatzResearch.WordTrace tailWord_137069 prefixEnd_137069 23460759943743150202379 := by
  unfold tailWord_137069
  simp only [CollatzResearch.WordTrace]
  refine ⟨4999317140429897366582261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3332878093619931577721507 4999317140429897366582261)
  ·
    refine ⟨468685981915302878117087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4999317140429897366582261 468685981915302878117087)
    ·
      refine ⟨703028972872954317175631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 468685981915302878117087 703028972872954317175631)
      ·
        refine ⟨1054543459309431475763447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 703028972872954317175631 1054543459309431475763447)
        ·
          refine ⟨1581815188964147213645171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1054543459309431475763447 1581815188964147213645171)
          ·
            refine ⟨2372722783446220820467757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1581815188964147213645171 2372722783446220820467757)
            ·
              refine ⟨889771043792332807675409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2372722783446220820467757 889771043792332807675409)
              ·
                refine ⟨667328282844249605756557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 889771043792332807675409 667328282844249605756557)
                ·
                  refine ⟨250248106066593602158709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 667328282844249605756557 250248106066593602158709)
                  ·
                    refine ⟨23460759943743150202379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 250248106066593602158709 23460759943743150202379)
                    ·
                      rfl

theorem cell23_137069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 2, 3, 5].length) (baseStart_137069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137069 prefixEnd_137069 := by exact prefixLift 137069
  have htrace : WordTrace (prefixWord ++ tailWord_137069) baseStart_137069 baseEnd_137069 := by
    simpa [prefixWord, tailWord_137069, baseEnd_137069] using wordTrace_append hprefix tailTrace_137069
  have hstable : (prefixWord ++ tailWord_137069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137069).length < 2 ^ (prefixWord ++ tailWord_137069).sum := by decide
  have hdescent : baseEnd_137069 < baseStart_137069 := by decide
  rcases family_descends (prefixWord ++ tailWord_137069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137099 : List Nat := [1, 1, 1, 1, 4, 2, 1, 4, 4, 4]
def baseStart_137099 : Nat := 118140960795 + 137099 * 2 ^ 59
def prefixEnd_137099 : Nat := 4983230072969 + 3 ^ 40 * 137099 * 2
def baseEnd_137099 : Nat := 23465894750288111077333

theorem tailTrace_137099 : CollatzResearch.WordTrace tailWord_137099 prefixEnd_137099 23465894750288111077333 := by
  unfold tailWord_137099
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000411330321212490174351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3333607553547474993449567 5000411330321212490174351)
  ·
    refine ⟨7500616995481818735261527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5000411330321212490174351 7500616995481818735261527)
    ·
      refine ⟨11250925493222728102892291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7500616995481818735261527 11250925493222728102892291)
      ·
        refine ⟨16876388239834092154338437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11250925493222728102892291 16876388239834092154338437)
        ·
          refine ⟨3164322794968892278938457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16876388239834092154338437 3164322794968892278938457)
          ·
            refine ⟨2373242096226669209203843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3164322794968892278938457 2373242096226669209203843)
            ·
              refine ⟨3559863144340003813805765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2373242096226669209203843 3559863144340003813805765)
              ·
                refine ⟨667474339563750715088581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3559863144340003813805765 667474339563750715088581)
                ·
                  refine ⟨125151438668203259079109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667474339563750715088581 125151438668203259079109)
                  ·
                    refine ⟨23465894750288111077333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125151438668203259079109 23465894750288111077333)
                    ·
                      rfl

theorem cell23_137099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 4, 4, 4].length) (baseStart_137099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137099 prefixEnd_137099 := by exact prefixLift 137099
  have htrace : WordTrace (prefixWord ++ tailWord_137099) baseStart_137099 baseEnd_137099 := by
    simpa [prefixWord, tailWord_137099, baseEnd_137099] using wordTrace_append hprefix tailTrace_137099
  have hstable : (prefixWord ++ tailWord_137099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137099).length < 2 ^ (prefixWord ++ tailWord_137099).sum := by decide
  have hdescent : baseEnd_137099 < baseStart_137099 := by decide
  rcases family_descends (prefixWord ++ tailWord_137099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137109 : List Nat := [1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 5]
def baseStart_137109 : Nat := 118140960795 + 137109 * 2 ^ 59
def prefixEnd_137109 : Nat := 4983230072969 + 3 ^ 40 * 137109 * 2
def baseEnd_137109 : Nat := 70402819057409294106953

theorem tailTrace_137109 : CollatzResearch.WordTrace tailWord_137109 prefixEnd_137109 70402819057409294106953 := by
  unfold tailWord_137109
  simp only [CollatzResearch.WordTrace]
  refine ⟨5000776060284984198038381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3333850706856656132025587 5000776060284984198038381)
  ·
    refine ⟨1875291022606869074264393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5000776060284984198038381 1875291022606869074264393)
    ·
      refine ⟨1406468266955151805698295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1875291022606869074264393 1406468266955151805698295)
      ·
        refine ⟨2109702400432727708547443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1406468266955151805698295 2109702400432727708547443)
        ·
          refine ⟨3164553600649091562821165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2109702400432727708547443 3164553600649091562821165)
          ·
            refine ⟨1186707600243409336057937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3164553600649091562821165 1186707600243409336057937)
            ·
              refine ⟨890030700182557002043453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1186707600243409336057937 890030700182557002043453)
              ·
                refine ⟨333761512568458875766295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 890030700182557002043453 333761512568458875766295)
                ·
                  refine ⟨500642268852688313649443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 333761512568458875766295 500642268852688313649443)
                  ·
                    refine ⟨750963403279032470474165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 500642268852688313649443 750963403279032470474165)
                    ·
                      refine ⟨70402819057409294106953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 750963403279032470474165 70402819057409294106953)
                      ·
                        rfl

theorem cell23_137109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 1, 5].length) (baseStart_137109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137109 prefixEnd_137109 := by exact prefixLift 137109
  have htrace : WordTrace (prefixWord ++ tailWord_137109) baseStart_137109 baseEnd_137109 := by
    simpa [prefixWord, tailWord_137109, baseEnd_137109] using wordTrace_append hprefix tailTrace_137109
  have hstable : (prefixWord ++ tailWord_137109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137109).length < 2 ^ (prefixWord ++ tailWord_137109).sum := by decide
  have hdescent : baseEnd_137109 < baseStart_137109 := by decide
  rcases family_descends (prefixWord ++ tailWord_137109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137173 : List Nat := [1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 3]
def baseStart_137173 : Nat := 118140960795 + 137173 * 2 ^ 59
def prefixEnd_137173 : Nat := 4983230072969 + 3 ^ 40 * 137173 * 2
def baseEnd_137173 : Nat := 70435681819297043706659

theorem tailTrace_137173 : CollatzResearch.WordTrace tailWord_137173 prefixEnd_137173 70435681819297043706659 := by
  unfold tailWord_137173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5003110332053123128368173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3335406888035415418912115 5003110332053123128368173)
  ·
    refine ⟨1876166374519921173138065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5003110332053123128368173 1876166374519921173138065)
    ·
      refine ⟨1407124780889940879853549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1876166374519921173138065 1407124780889940879853549)
      ·
        refine ⟨527671792833727829945081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1407124780889940879853549 527671792833727829945081)
        ·
          refine ⟨395753844625295872458811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 527671792833727829945081 395753844625295872458811)
          ·
            refine ⟨593630766937943808688217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 395753844625295872458811 593630766937943808688217)
            ·
              refine ⟨445223075203457856516163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 593630766937943808688217 445223075203457856516163)
              ·
                refine ⟨667834612805186784774245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445223075203457856516163 667834612805186784774245)
                ·
                  refine ⟨125218989900972522145171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 667834612805186784774245 125218989900972522145171)
                  ·
                    refine ⟨187828484851458783217757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125218989900972522145171 187828484851458783217757)
                    ·
                      refine ⟨70435681819297043706659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 187828484851458783217757 70435681819297043706659)
                      ·
                        rfl

theorem cell23_137173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_137173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137173 prefixEnd_137173 := by exact prefixLift 137173
  have htrace : WordTrace (prefixWord ++ tailWord_137173) baseStart_137173 baseEnd_137173 := by
    simpa [prefixWord, tailWord_137173, baseEnd_137173] using wordTrace_append hprefix tailTrace_137173
  have hstable : (prefixWord ++ tailWord_137173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137173).length < 2 ^ (prefixWord ++ tailWord_137173).sum := by decide
  have hdescent : baseEnd_137173 < baseStart_137173 := by decide
  rcases family_descends (prefixWord ++ tailWord_137173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137174 : List Nat := [5, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2]
def baseStart_137174 : Nat := 118140960795 + 137174 * 2 ^ 59
def prefixEnd_137174 : Nat := 4983230072969 + 3 ^ 40 * 137174 * 2
def baseEnd_137174 : Nat := 70436195299951539794155

theorem tailTrace_137174 : CollatzResearch.WordTrace tailWord_137174 prefixEnd_137174 70436195299951539794155 := by
  unfold tailWord_137174
  simp only [CollatzResearch.WordTrace]
  refine ⟨312696675315593768697161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3335431203366333532769717 312696675315593768697161)
  ·
    refine ⟨234522506486695326522871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 312696675315593768697161 234522506486695326522871)
    ·
      refine ⟨351783759730042989784307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 234522506486695326522871 351783759730042989784307)
      ·
        refine ⟨527675639595064484676461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 351783759730042989784307 527675639595064484676461)
        ·
          refine ⟨197878364848149181753673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 527675639595064484676461 197878364848149181753673)
          ·
            refine ⟨148408773636111886315255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 197878364848149181753673 148408773636111886315255)
            ·
              refine ⟨222613160454167829472883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148408773636111886315255 222613160454167829472883)
              ·
                refine ⟨333919740681251744209325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 222613160454167829472883 333919740681251744209325)
                ·
                  refine ⟨125219902755469404078497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 333919740681251744209325 125219902755469404078497)
                  ·
                    refine ⟨93914927066602053058873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125219902755469404078497 93914927066602053058873)
                    ·
                      refine ⟨70436195299951539794155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93914927066602053058873 70436195299951539794155)
                      ·
                        rfl

theorem cell23_137174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 1, 3, 2, 2].length) (baseStart_137174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137174 prefixEnd_137174 := by exact prefixLift 137174
  have htrace : WordTrace (prefixWord ++ tailWord_137174) baseStart_137174 baseEnd_137174 := by
    simpa [prefixWord, tailWord_137174, baseEnd_137174] using wordTrace_append hprefix tailTrace_137174
  have hstable : (prefixWord ++ tailWord_137174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137174).length < 2 ^ (prefixWord ++ tailWord_137174).sum := by decide
  have hdescent : baseEnd_137174 < baseStart_137174 := by decide
  rcases family_descends (prefixWord ++ tailWord_137174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137180 : List Nat := [2, 2, 6, 1, 1, 1, 2, 8]
def baseStart_137180 : Nat := 118140960795 + 137180 * 2 ^ 59
def prefixEnd_137180 : Nat := 4983230072969 + 3 ^ 40 * 137180 * 2
def baseEnd_137180 : Nat := 2608862080884389493301

theorem tailTrace_137180 : CollatzResearch.WordTrace tailWord_137180 prefixEnd_137180 2608862080884389493301 := by
  unfold tailWord_137180
  simp only [CollatzResearch.WordTrace]
  refine ⟨2501682821513881661936497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3335577095351842215915329 2501682821513881661936497)
  ·
    refine ⟨1876262116135411246452373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2501682821513881661936497 1876262116135411246452373)
    ·
      refine ⟨87949786693847402177455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1876262116135411246452373 87949786693847402177455)
      ·
        refine ⟨131924680040771103266183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 87949786693847402177455 131924680040771103266183)
        ·
          refine ⟨197887020061156654899275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 131924680040771103266183 197887020061156654899275)
          ·
            refine ⟨296830530091734982348913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 197887020061156654899275 296830530091734982348913)
            ·
              refine ⟨222622897568801236761685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 296830530091734982348913 222622897568801236761685)
              ·
                refine ⟨2608862080884389493301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 222622897568801236761685 2608862080884389493301)
                ·
                  rfl

theorem cell23_137180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 8].length) (baseStart_137180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137180 prefixEnd_137180 := by exact prefixLift 137180
  have htrace : WordTrace (prefixWord ++ tailWord_137180) baseStart_137180 baseEnd_137180 := by
    simpa [prefixWord, tailWord_137180, baseEnd_137180] using wordTrace_append hprefix tailTrace_137180
  have hstable : (prefixWord ++ tailWord_137180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137180).length < 2 ^ (prefixWord ++ tailWord_137180).sum := by decide
  have hdescent : baseEnd_137180 < baseStart_137180 := by decide
  rcases family_descends (prefixWord ++ tailWord_137180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137196 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 5, 4, 2]
def baseStart_137196 : Nat := 118140960795 + 137196 * 2 ^ 59
def prefixEnd_137196 : Nat := 4983230072969 + 3 ^ 40 * 137196 * 2
def baseEnd_137196 : Nat := 70447491874350453719053

theorem tailTrace_137196 : CollatzResearch.WordTrace tailWord_137196 prefixEnd_137196 70447491874350453719053 := by
  unfold tailWord_137196
  simp only [CollatzResearch.WordTrace]
  refine ⟨2501974605484899028227721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3335966140646532037636961 2501974605484899028227721)
  ·
    refine ⟨1876480954113674271170791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2501974605484899028227721 1876480954113674271170791)
    ·
      refine ⟨2814721431170511406756187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1876480954113674271170791 2814721431170511406756187)
      ·
        refine ⟨4222082146755767110134281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2814721431170511406756187 4222082146755767110134281)
        ·
          refine ⟨3166561610066825332600711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4222082146755767110134281 3166561610066825332600711)
          ·
            refine ⟨4749842415100237998901067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3166561610066825332600711 4749842415100237998901067)
            ·
              refine ⟨7124763622650356998351601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4749842415100237998901067 7124763622650356998351601)
              ·
                refine ⟨5343572716987767748763701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7124763622650356998351601 5343572716987767748763701)
                ·
                  refine ⟨500959942217603226446597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5343572716987767748763701 500959942217603226446597)
                  ·
                    refine ⟨93929989165800604958737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 500959942217603226446597 93929989165800604958737)
                    ·
                      refine ⟨70447491874350453719053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93929989165800604958737 70447491874350453719053)
                      ·
                        rfl

theorem cell23_137196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 4, 2].length) (baseStart_137196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137196 prefixEnd_137196 := by exact prefixLift 137196
  have htrace : WordTrace (prefixWord ++ tailWord_137196) baseStart_137196 baseEnd_137196 := by
    simpa [prefixWord, tailWord_137196, baseEnd_137196] using wordTrace_append hprefix tailTrace_137196
  have hstable : (prefixWord ++ tailWord_137196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137196).length < 2 ^ (prefixWord ++ tailWord_137196).sum := by decide
  have hdescent : baseEnd_137196 < baseStart_137196 := by decide
  rcases family_descends (prefixWord ++ tailWord_137196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137199 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 5]
def baseStart_137199 : Nat := 118140960795 + 137199 * 2 ^ 59
def prefixEnd_137199 : Nat := 4983230072969 + 3 ^ 40 * 137199 * 2
def baseEnd_137199 : Nat := 70449032316313941981539

theorem tailTrace_137199 : CollatzResearch.WordTrace tailWord_137199 prefixEnd_137199 70449032316313941981539 := by
  unfold tailWord_137199
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004058629958929568814651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3336039086639286379209767 5004058629958929568814651)
  ·
    refine ⟨7506087944938394353221977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5004058629958929568814651 7506087944938394353221977)
    ·
      refine ⟨5629565958703795764916483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7506087944938394353221977 5629565958703795764916483)
      ·
        refine ⟨8444348938055693647374725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5629565958703795764916483 8444348938055693647374725)
        ·
          refine ⟨1583315425885442558882761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8444348938055693647374725 1583315425885442558882761)
          ·
            refine ⟨1187486569414081919162071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1583315425885442558882761 1187486569414081919162071)
            ·
              refine ⟨1781229854121122878743107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1187486569414081919162071 1781229854121122878743107)
              ·
                refine ⟨2671844781181684318114661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781229854121122878743107 2671844781181684318114661)
                ·
                  refine ⟨500970896471565809646499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2671844781181684318114661 500970896471565809646499)
                  ·
                    refine ⟨751456344707348714469749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 500970896471565809646499 751456344707348714469749)
                    ·
                      refine ⟨70449032316313941981539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 751456344707348714469749 70449032316313941981539)
                      ·
                        rfl

theorem cell23_137199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 1, 5].length) (baseStart_137199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137199 prefixEnd_137199 := by exact prefixLift 137199
  have htrace : WordTrace (prefixWord ++ tailWord_137199) baseStart_137199 baseEnd_137199 := by
    simpa [prefixWord, tailWord_137199, baseEnd_137199] using wordTrace_append hprefix tailTrace_137199
  have hstable : (prefixWord ++ tailWord_137199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137199).length < 2 ^ (prefixWord ++ tailWord_137199).sum := by decide
  have hdescent : baseEnd_137199 < baseStart_137199 := by decide
  rcases family_descends (prefixWord ++ tailWord_137199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137213 : List Nat := [1, 4, 1, 1, 1, 2, 2, 1, 6, 2, 2]
def baseStart_137213 : Nat := 118140960795 + 137213 * 2 ^ 59
def prefixEnd_137213 : Nat := 4983230072969 + 3 ^ 40 * 137213 * 2
def baseEnd_137213 : Nat := 70456221045476887206475

theorem tailTrace_137213 : CollatzResearch.WordTrace tailWord_137213 prefixEnd_137213 70456221045476887206475 := by
  unfold tailWord_137213
  simp only [CollatzResearch.WordTrace]
  refine ⟨5004569251908209959824293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3336379501272139973216195 5004569251908209959824293)
  ·
    refine ⟨938356734732789367467055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5004569251908209959824293 938356734732789367467055)
    ·
      refine ⟨1407535102099184051200583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 938356734732789367467055 1407535102099184051200583)
      ·
        refine ⟨2111302653148776076800875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1407535102099184051200583 2111302653148776076800875)
        ·
          refine ⟨3166953979723164115201313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2111302653148776076800875 3166953979723164115201313)
          ·
            refine ⟨2375215484792373086400985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3166953979723164115201313 2375215484792373086400985)
            ·
              refine ⟨1781411613594279814800739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2375215484792373086400985 1781411613594279814800739)
              ·
                refine ⟨2672117420391419722201109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1781411613594279814800739 2672117420391419722201109)
                ·
                  refine ⟨125255504080847799478177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2672117420391419722201109 125255504080847799478177)
                  ·
                    refine ⟨93941628060635849608633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125255504080847799478177 93941628060635849608633)
                    ·
                      refine ⟨70456221045476887206475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 93941628060635849608633 70456221045476887206475)
                      ·
                        rfl

theorem cell23_137213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 1, 6, 2, 2].length) (baseStart_137213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137213 prefixEnd_137213 := by exact prefixLift 137213
  have htrace : WordTrace (prefixWord ++ tailWord_137213) baseStart_137213 baseEnd_137213 := by
    simpa [prefixWord, tailWord_137213, baseEnd_137213] using wordTrace_append hprefix tailTrace_137213
  have hstable : (prefixWord ++ tailWord_137213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137213).length < 2 ^ (prefixWord ++ tailWord_137213).sum := by decide
  have hdescent : baseEnd_137213 < baseStart_137213 := by decide
  rcases family_descends (prefixWord ++ tailWord_137213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137259 : List Nat := [1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5]
def baseStart_137259 : Nat := 118140960795 + 137259 * 2 ^ 59
def prefixEnd_137259 : Nat := 4983230072969 + 3 ^ 40 * 137259 * 2
def baseEnd_137259 : Nat := 70479841155583707231263

theorem tailTrace_137259 : CollatzResearch.WordTrace tailWord_137259 prefixEnd_137259 70479841155583707231263 := by
  unfold tailWord_137259
  simp only [CollatzResearch.WordTrace]
  refine ⟨5006247009741559815998831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3337498006494373210665887 5006247009741559815998831)
  ·
    refine ⟨7509370514612339723998247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5006247009741559815998831 7509370514612339723998247)
    ·
      refine ⟨11264055771918509585997371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7509370514612339723998247 11264055771918509585997371)
      ·
        refine ⟨16896083657877764378996057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11264055771918509585997371 16896083657877764378996057)
        ·
          refine ⟨12672062743408323284247043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16896083657877764378996057 12672062743408323284247043)
          ·
            refine ⟨19008094115112484926370565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12672062743408323284247043 19008094115112484926370565)
            ·
              refine ⟨3564017646583590923694481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19008094115112484926370565 3564017646583590923694481)
              ·
                refine ⟨2673013234937693192770861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3564017646583590923694481 2673013234937693192770861)
                ·
                  refine ⟨1002379963101634947289073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2673013234937693192770861 1002379963101634947289073)
                  ·
                    refine ⟨751784972326226210466805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1002379963101634947289073 751784972326226210466805)
                    ·
                      refine ⟨70479841155583707231263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 751784972326226210466805 70479841155583707231263)
                      ·
                        rfl

theorem cell23_137259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 2, 5].length) (baseStart_137259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137259 prefixEnd_137259 := by exact prefixLift 137259
  have htrace : WordTrace (prefixWord ++ tailWord_137259) baseStart_137259 baseEnd_137259 := by
    simpa [prefixWord, tailWord_137259, baseEnd_137259] using wordTrace_append hprefix tailTrace_137259
  have hstable : (prefixWord ++ tailWord_137259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137259).length < 2 ^ (prefixWord ++ tailWord_137259).sum := by decide
  have hdescent : baseEnd_137259 < baseStart_137259 := by decide
  rcases family_descends (prefixWord ++ tailWord_137259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137266 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_137266 : Nat := 118140960795 + 137266 * 2 ^ 59
def prefixEnd_137266 : Nat := 4983230072969 + 3 ^ 40 * 137266 * 2
def baseEnd_137266 : Nat := 23494478506721726614577

theorem tailTrace_137266 : CollatzResearch.WordTrace tailWord_137266 prefixEnd_137266 23494478506721726614577 := by
  unfold tailWord_137266
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251625580179050002875913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3337668213810800007669101 1251625580179050002875913)
  ·
    refine ⟨938719185134287502156935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1251625580179050002875913 938719185134287502156935)
    ·
      refine ⟨1408078777701431253235403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 938719185134287502156935 1408078777701431253235403)
      ·
        refine ⟨2112118166552146879853105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1408078777701431253235403 2112118166552146879853105)
        ·
          refine ⟨1584088624914110159889829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2112118166552146879853105 1584088624914110159889829)
          ·
            refine ⟨297016617171395654979343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1584088624914110159889829 297016617171395654979343)
            ·
              refine ⟨445524925757093482469015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297016617171395654979343 445524925757093482469015)
              ·
                refine ⟨668287388635640223703523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445524925757093482469015 668287388635640223703523)
                ·
                  refine ⟨1002431082953460335555285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 668287388635640223703523 1002431082953460335555285)
                  ·
                    refine ⟨23494478506721726614577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1002431082953460335555285 23494478506721726614577)
                    ·
                      rfl

theorem cell23_137266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_137266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137266 prefixEnd_137266 := by exact prefixLift 137266
  have htrace : WordTrace (prefixWord ++ tailWord_137266) baseStart_137266 baseEnd_137266 := by
    simpa [prefixWord, tailWord_137266, baseEnd_137266] using wordTrace_append hprefix tailTrace_137266
  have hstable : (prefixWord ++ tailWord_137266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137266).length < 2 ^ (prefixWord ++ tailWord_137266).sum := by decide
  have hdescent : baseEnd_137266 < baseStart_137266 := by decide
  rcases family_descends (prefixWord ++ tailWord_137266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137270 : List Nat := [5, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_137270 : Nat := 118140960795 + 137270 * 2 ^ 59
def prefixEnd_137270 : Nat := 4983230072969 + 3 ^ 40 * 137270 * 2
def baseEnd_137270 : Nat := 7831721049198129354857

theorem tailTrace_137270 : CollatzResearch.WordTrace tailWord_137270 prefixEnd_137270 7831721049198129354857 := by
  unfold tailWord_137270
  simp only [CollatzResearch.WordTrace]
  refine ⟨312915513293856793415579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3337765475134472463099509 312915513293856793415579)
  ·
    refine ⟨469373269940785190123369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 312915513293856793415579 469373269940785190123369)
    ·
      refine ⟨352029952455588892592527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 469373269940785190123369 352029952455588892592527)
      ·
        refine ⟨528044928683383338888791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 352029952455588892592527 528044928683383338888791)
        ·
          refine ⟨792067393025075008333187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528044928683383338888791 792067393025075008333187)
          ·
            refine ⟨1188101089537612512499781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792067393025075008333187 1188101089537612512499781)
            ·
              refine ⟨222768954288302346093709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1188101089537612512499781 222768954288302346093709)
              ·
                refine ⟨83538357858113379785141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 222768954288302346093709 83538357858113379785141)
                ·
                  refine ⟨7831721049198129354857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83538357858113379785141 7831721049198129354857)
                  ·
                    rfl

theorem cell23_137270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_137270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137270 prefixEnd_137270 := by exact prefixLift 137270
  have htrace : WordTrace (prefixWord ++ tailWord_137270) baseStart_137270 baseEnd_137270 := by
    simpa [prefixWord, tailWord_137270, baseEnd_137270] using wordTrace_append hprefix tailTrace_137270
  have hstable : (prefixWord ++ tailWord_137270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137270).length < 2 ^ (prefixWord ++ tailWord_137270).sum := by decide
  have hdescent : baseEnd_137270 < baseStart_137270 := by decide
  rcases family_descends (prefixWord ++ tailWord_137270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137299 : List Nat := [1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6]
def baseStart_137299 : Nat := 118140960795 + 137299 * 2 ^ 59
def prefixEnd_137299 : Nat := 4983230072969 + 3 ^ 40 * 137299 * 2
def baseEnd_137299 : Nat := 70500380381763550731079

theorem tailTrace_137299 : CollatzResearch.WordTrace tailWord_137299 prefixEnd_137299 70500380381763550731079 := by
  unfold tailWord_137299
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007705929596646647454951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3338470619731097764969967 5007705929596646647454951)
  ·
    refine ⟨7511558894394969971182427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5007705929596646647454951 7511558894394969971182427)
    ·
      refine ⟨11267338341592454956773641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7511558894394969971182427 11267338341592454956773641)
      ·
        refine ⟨8450503756194341217580231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11267338341592454956773641 8450503756194341217580231)
        ·
          refine ⟨12675755634291511826370347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8450503756194341217580231 12675755634291511826370347)
          ·
            refine ⟨19013633451437267739555521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12675755634291511826370347 19013633451437267739555521)
            ·
              refine ⟨14260225088577950804666641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19013633451437267739555521 14260225088577950804666641)
              ·
                refine ⟨10695168816433463103499981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14260225088577950804666641 10695168816433463103499981)
                ·
                  refine ⟨4010688306162548663812493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10695168816433463103499981 4010688306162548663812493)
                  ·
                    refine ⟨1504008114810955748929685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4010688306162548663812493 1504008114810955748929685)
                    ·
                      refine ⟨70500380381763550731079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1504008114810955748929685 70500380381763550731079)
                      ·
                        rfl

theorem cell23_137299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 3, 6].length) (baseStart_137299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137299 prefixEnd_137299 := by exact prefixLift 137299
  have htrace : WordTrace (prefixWord ++ tailWord_137299) baseStart_137299 baseEnd_137299 := by
    simpa [prefixWord, tailWord_137299, baseEnd_137299] using wordTrace_append hprefix tailTrace_137299
  have hstable : (prefixWord ++ tailWord_137299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137299).length < 2 ^ (prefixWord ++ tailWord_137299).sum := by decide
  have hdescent : baseEnd_137299 < baseStart_137299 := by decide
  rcases family_descends (prefixWord ++ tailWord_137299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137303 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 2, 4, 2]
def baseStart_137303 : Nat := 118140960795 + 137303 * 2 ^ 59
def prefixEnd_137303 : Nat := 4983230072969 + 3 ^ 40 * 137303 * 2
def baseEnd_137303 : Nat := 70502434304381535081061

theorem tailTrace_137303 : CollatzResearch.WordTrace tailWord_137303 prefixEnd_137303 70502434304381535081061 := by
  unfold tailWord_137303
  simp only [CollatzResearch.WordTrace]
  refine ⟨5007851821582155330600563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3338567881054770220400375 5007851821582155330600563)
  ·
    refine ⟨7511777732373232995900845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5007851821582155330600563 7511777732373232995900845)
    ·
      refine ⟨2816916649639962373462817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7511777732373232995900845 2816916649639962373462817)
      ·
        refine ⟨2112687487229971780097113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2816916649639962373462817 2112687487229971780097113)
        ·
          refine ⟨1584515615422478835072835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2112687487229971780097113 1584515615422478835072835)
          ·
            refine ⟨2376773423133718252609253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1584515615422478835072835 2376773423133718252609253)
            ·
              refine ⟨445645016837572172364235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2376773423133718252609253 445645016837572172364235)
              ·
                refine ⟨668467525256358258546353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445645016837572172364235 668467525256358258546353)
                ·
                  refine ⟨501350643942268693909765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 668467525256358258546353 501350643942268693909765)
                  ·
                    refine ⟨94003245739175380108081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 501350643942268693909765 94003245739175380108081)
                    ·
                      refine ⟨70502434304381535081061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94003245739175380108081 70502434304381535081061)
                      ·
                        rfl

theorem cell23_137303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 2, 4, 2].length) (baseStart_137303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137303 prefixEnd_137303 := by exact prefixLift 137303
  have htrace : WordTrace (prefixWord ++ tailWord_137303) baseStart_137303 baseEnd_137303 := by
    simpa [prefixWord, tailWord_137303, baseEnd_137303] using wordTrace_append hprefix tailTrace_137303
  have hstable : (prefixWord ++ tailWord_137303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137303).length < 2 ^ (prefixWord ++ tailWord_137303).sum := by decide
  have hdescent : baseEnd_137303 < baseStart_137303 := by decide
  rcases family_descends (prefixWord ++ tailWord_137303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137306 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3]
def baseStart_137306 : Nat := 118140960795 + 137306 * 2 ^ 59
def prefixEnd_137306 : Nat := 4983230072969 + 3 ^ 40 * 137306 * 2
def baseEnd_137306 : Nat := 70503974746345023343547

theorem tailTrace_137306 : CollatzResearch.WordTrace tailWord_137306 prefixEnd_137306 70503974746345023343547 := by
  unfold tailWord_137306
  simp only [CollatzResearch.WordTrace]
  refine ⟨1251990310142821710739943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3338640827047524561973181 1251990310142821710739943)
  ·
    refine ⟨1877985465214232566109915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1251990310142821710739943 1877985465214232566109915)
    ·
      refine ⟨2816978197821348849164873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1877985465214232566109915 2816978197821348849164873)
      ·
        refine ⟨2112733648366011636873655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2816978197821348849164873 2112733648366011636873655)
        ·
          refine ⟨3169100472549017455310483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2112733648366011636873655 3169100472549017455310483)
          ·
            refine ⟨4753650708823526182965725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3169100472549017455310483 4753650708823526182965725)
            ·
              refine ⟨1782619015808822318612147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4753650708823526182965725 1782619015808822318612147)
              ·
                refine ⟨2673928523713233477918221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782619015808822318612147 2673928523713233477918221)
                ·
                  refine ⟨1002723196392462554219333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2673928523713233477918221 1002723196392462554219333)
                  ·
                    refine ⟨188010599323586728916125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1002723196392462554219333 188010599323586728916125)
                    ·
                      refine ⟨70503974746345023343547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188010599323586728916125 70503974746345023343547)
                      ·
                        rfl

theorem cell23_137306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 3, 4, 3].length) (baseStart_137306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137306 prefixEnd_137306 := by exact prefixLift 137306
  have htrace : WordTrace (prefixWord ++ tailWord_137306) baseStart_137306 baseEnd_137306 := by
    simpa [prefixWord, tailWord_137306, baseEnd_137306] using wordTrace_append hprefix tailTrace_137306
  have hstable : (prefixWord ++ tailWord_137306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137306).length < 2 ^ (prefixWord ++ tailWord_137306).sum := by decide
  have hdescent : baseEnd_137306 < baseStart_137306 := by decide
  rcases family_descends (prefixWord ++ tailWord_137306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137326 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_137326 : Nat := 118140960795 + 137326 * 2 ^ 59
def prefixEnd_137326 : Nat := 4983230072969 + 3 ^ 40 * 137326 * 2
def baseEnd_137326 : Nat := 7834916039937216121495

theorem tailTrace_137326 : CollatzResearch.WordTrace tailWord_137326 prefixEnd_137326 7834916039937216121495 := by
  unfold tailWord_137326
  simp only [CollatzResearch.WordTrace]
  refine ⟨626086337562353782335979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3339127133665886839125221 626086337562353782335979)
  ·
    refine ⟨939129506343530673503969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 626086337562353782335979 939129506343530673503969)
    ·
      refine ⟨704347129757648005127977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 939129506343530673503969 704347129757648005127977)
      ·
        refine ⟨528260347318236003845983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 704347129757648005127977 528260347318236003845983)
        ·
          refine ⟨792390520977354005768975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 528260347318236003845983 792390520977354005768975)
          ·
            refine ⟨1188585781466031008653463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 792390520977354005768975 1188585781466031008653463)
            ·
              refine ⟨1782878672199046512980195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1188585781466031008653463 1782878672199046512980195)
              ·
                refine ⟨2674318008298569769470293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1782878672199046512980195 2674318008298569769470293)
                ·
                  refine ⟨7834916039937216121495, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 2674318008298569769470293 7834916039937216121495)
                  ·
                    rfl

theorem cell23_137326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_137326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137326 prefixEnd_137326 := by exact prefixLift 137326
  have htrace : WordTrace (prefixWord ++ tailWord_137326) baseStart_137326 baseEnd_137326 := by
    simpa [prefixWord, tailWord_137326, baseEnd_137326] using wordTrace_append hprefix tailTrace_137326
  have hstable : (prefixWord ++ tailWord_137326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137326).length < 2 ^ (prefixWord ++ tailWord_137326).sum := by decide
  have hdescent : baseEnd_137326 < baseStart_137326 := by decide
  rcases family_descends (prefixWord ++ tailWord_137326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137347 : List Nat := [1, 1, 1, 3, 3, 4, 3, 2, 1, 4]
def baseStart_137347 : Nat := 118140960795 + 137347 * 2 ^ 59
def prefixEnd_137347 : Nat := 4983230072969 + 3 ^ 40 * 137347 * 2
def baseEnd_137347 : Nat := 23508342484393120976953

theorem tailTrace_137347 : CollatzResearch.WordTrace tailWord_137347 prefixEnd_137347 23508342484393120976953 := by
  unfold tailWord_137347
  simp only [CollatzResearch.WordTrace]
  refine ⟨5009456633422750845202295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3339637755615167230134863 5009456633422750845202295)
  ·
    refine ⟨7514184950134126267803443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5009456633422750845202295 7514184950134126267803443)
    ·
      refine ⟨11271277425201189401705165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7514184950134126267803443 11271277425201189401705165)
      ·
        refine ⟨4226729034450446025639437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11271277425201189401705165 4226729034450446025639437)
        ·
          refine ⟨1585023387918917259614789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4226729034450446025639437 1585023387918917259614789)
          ·
            refine ⟨297191885234796986177773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1585023387918917259614789 297191885234796986177773)
            ·
              refine ⟨111446956963048869816665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 297191885234796986177773 111446956963048869816665)
              ·
                refine ⟨83585217722286652362499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111446956963048869816665 83585217722286652362499)
                ·
                  refine ⟨125377826583429978543749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83585217722286652362499 125377826583429978543749)
                  ·
                    refine ⟨23508342484393120976953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125377826583429978543749 23508342484393120976953)
                    ·
                      rfl

theorem cell23_137347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 2, 1, 4].length) (baseStart_137347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137347 prefixEnd_137347 := by exact prefixLift 137347
  have htrace : WordTrace (prefixWord ++ tailWord_137347) baseStart_137347 baseEnd_137347 := by
    simpa [prefixWord, tailWord_137347, baseEnd_137347] using wordTrace_append hprefix tailTrace_137347
  have hstable : (prefixWord ++ tailWord_137347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137347).length < 2 ^ (prefixWord ++ tailWord_137347).sum := by decide
  have hdescent : baseEnd_137347 < baseStart_137347 := by decide
  rcases family_descends (prefixWord ++ tailWord_137347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137363 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 6, 3, 2]
def baseStart_137363 : Nat := 118140960795 + 137363 * 2 ^ 59
def prefixEnd_137363 : Nat := 4983230072969 + 3 ^ 40 * 137363 * 2
def baseEnd_137363 : Nat := 70533243143651300330785

theorem tailTrace_137363 : CollatzResearch.WordTrace tailWord_137363 prefixEnd_137363 70533243143651300330785 := by
  unfold tailWord_137363
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010040201364785577784743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3340026800909857051856495 5010040201364785577784743)
  ·
    refine ⟨7515060302047178366677115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5010040201364785577784743 7515060302047178366677115)
    ·
      refine ⟨11272590453070767550015673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7515060302047178366677115 11272590453070767550015673)
      ·
        refine ⟨8454442839803075662511755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11272590453070767550015673 8454442839803075662511755)
        ·
          refine ⟨12681664259704613493767633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8454442839803075662511755 12681664259704613493767633)
          ·
            refine ⟨9511248194778460120325725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12681664259704613493767633 9511248194778460120325725)
            ·
              refine ⟨3566718073041922545122147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9511248194778460120325725 3566718073041922545122147)
              ·
                refine ⟨5350077109562883817683221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3566718073041922545122147 5350077109562883817683221)
                ·
                  refine ⟨250784864510760178953901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5350077109562883817683221 250784864510760178953901)
                  ·
                    refine ⟨94044324191535067107713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 250784864510760178953901 94044324191535067107713)
                    ·
                      refine ⟨70533243143651300330785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94044324191535067107713 70533243143651300330785)
                      ·
                        rfl

theorem cell23_137363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 6, 3, 2].length) (baseStart_137363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137363 prefixEnd_137363 := by exact prefixLift 137363
  have htrace : WordTrace (prefixWord ++ tailWord_137363) baseStart_137363 baseEnd_137363 := by
    simpa [prefixWord, tailWord_137363, baseEnd_137363] using wordTrace_append hprefix tailTrace_137363
  have hstable : (prefixWord ++ tailWord_137363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137363).length < 2 ^ (prefixWord ++ tailWord_137363).sum := by decide
  have hdescent : baseEnd_137363 < baseStart_137363 := by decide
  rcases family_descends (prefixWord ++ tailWord_137363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137373 : List Nat := [1, 4, 2, 1, 1, 4, 1, 1, 3, 5]
def baseStart_137373 : Nat := 118140960795 + 137373 * 2 ^ 59
def prefixEnd_137373 : Nat := 4983230072969 + 3 ^ 40 * 137373 * 2
def baseEnd_137373 : Nat := 23512792650065420401913

theorem tailTrace_137373 : CollatzResearch.WordTrace tailWord_137373 prefixEnd_137373 23512792650065420401913 := by
  unfold tailWord_137373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5010404931328557285648773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3340269954219038190432515 5010404931328557285648773)
  ·
    refine ⟨939450924624104491059145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5010404931328557285648773 939450924624104491059145)
    ·
      refine ⟨704588193468078368294359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 939450924624104491059145 704588193468078368294359)
      ·
        refine ⟨1056882290202117552441539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 704588193468078368294359 1056882290202117552441539)
        ·
          refine ⟨1585323435303176328662309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1056882290202117552441539 1585323435303176328662309)
          ·
            refine ⟨297248144119345561624183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1585323435303176328662309 297248144119345561624183)
            ·
              refine ⟨445872216179018342436275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297248144119345561624183 445872216179018342436275)
              ·
                refine ⟨668808324268527513654413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 445872216179018342436275 668808324268527513654413)
                ·
                  refine ⟨250803121600697817620405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 668808324268527513654413 250803121600697817620405)
                  ·
                    refine ⟨23512792650065420401913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 250803121600697817620405 23512792650065420401913)
                    ·
                      rfl

theorem cell23_137373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 1, 3, 5].length) (baseStart_137373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137373 prefixEnd_137373 := by exact prefixLift 137373
  have htrace : WordTrace (prefixWord ++ tailWord_137373) baseStart_137373 baseEnd_137373 := by
    simpa [prefixWord, tailWord_137373, baseEnd_137373] using wordTrace_append hprefix tailTrace_137373
  have hstable : (prefixWord ++ tailWord_137373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137373).length < 2 ^ (prefixWord ++ tailWord_137373).sum := by decide
  have hdescent : baseEnd_137373 < baseStart_137373 := by decide
  rcases family_descends (prefixWord ++ tailWord_137373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137404 : List Nat := [2, 2, 2, 3, 3, 1, 1, 4, 1, 1, 3]
def baseStart_137404 : Nat := 118140960795 + 137404 * 2 ^ 59
def prefixEnd_137404 : Nat := 4983230072969 + 3 ^ 40 * 137404 * 2
def baseEnd_137404 : Nat := 70554295850485639918097

theorem tailTrace_137404 : CollatzResearch.WordTrace tailWord_137404 prefixEnd_137404 70554295850485639918097 := by
  unfold tailWord_137404
  simp only [CollatzResearch.WordTrace]
  refine ⟨2505767797108124790013633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3341023729477499720018177 2505767797108124790013633)
  ·
    refine ⟨1879325847831093592510225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2505767797108124790013633 1879325847831093592510225)
    ·
      refine ⟨1409494385873320194382669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1879325847831093592510225 1409494385873320194382669)
      ·
        refine ⟨528560394702495072893501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1409494385873320194382669 528560394702495072893501)
        ·
          refine ⟨198210148013435652335063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 528560394702495072893501 198210148013435652335063)
          ·
            refine ⟨297315222020153478502595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198210148013435652335063 297315222020153478502595)
            ·
              refine ⟨445972833030230217753893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297315222020153478502595 445972833030230217753893)
              ·
                refine ⟨83619906193168165828855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 445972833030230217753893 83619906193168165828855)
                ·
                  refine ⟨125429859289752248743283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83619906193168165828855 125429859289752248743283)
                  ·
                    refine ⟨188144788934628373114925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125429859289752248743283 188144788934628373114925)
                    ·
                      refine ⟨70554295850485639918097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188144788934628373114925 70554295850485639918097)
                      ·
                        rfl

theorem cell23_137404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_137404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137404 prefixEnd_137404 := by exact prefixLift 137404
  have htrace : WordTrace (prefixWord ++ tailWord_137404) baseStart_137404 baseEnd_137404 := by
    simpa [prefixWord, tailWord_137404, baseEnd_137404] using wordTrace_append hprefix tailTrace_137404
  have hstable : (prefixWord ++ tailWord_137404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137404).length < 2 ^ (prefixWord ++ tailWord_137404).sum := by decide
  have hdescent : baseEnd_137404 < baseStart_137404 := by decide
  rcases family_descends (prefixWord ++ tailWord_137404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137413 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 3]
def baseStart_137413 : Nat := 118140960795 + 137413 * 2 ^ 59
def prefixEnd_137413 : Nat := 4983230072969 + 3 ^ 40 * 137413 * 2
def baseEnd_137413 : Nat := 70558917176376104705555

theorem tailTrace_137413 : CollatzResearch.WordTrace tailWord_137413 prefixEnd_137413 70558917176376104705555 := by
  unfold tailWord_137413
  simp only [CollatzResearch.WordTrace]
  refine ⟨5011863851183644117104893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3341242567455762744736595 5011863851183644117104893)
  ·
    refine ⟨1879448944193866543914335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5011863851183644117104893 1879448944193866543914335)
    ·
      refine ⟨2819173416290799815871503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1879448944193866543914335 2819173416290799815871503)
      ·
        refine ⟨4228760124436199723807255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2819173416290799815871503 4228760124436199723807255)
        ·
          refine ⟨6343140186654299585710883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4228760124436199723807255 6343140186654299585710883)
          ·
            refine ⟨9514710279981449378566325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6343140186654299585710883 9514710279981449378566325)
            ·
              refine ⟨892004088748260879240593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9514710279981449378566325 892004088748260879240593)
              ·
                refine ⟨669003066561195659430445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 892004088748260879240593 669003066561195659430445)
                ·
                  refine ⟨250876149960448372286417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 669003066561195659430445 250876149960448372286417)
                  ·
                    refine ⟨188157112470336279214813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 250876149960448372286417 188157112470336279214813)
                    ·
                      refine ⟨70558917176376104705555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188157112470336279214813 70558917176376104705555)
                      ·
                        rfl

theorem cell23_137413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 3, 2, 3].length) (baseStart_137413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137413 prefixEnd_137413 := by exact prefixLift 137413
  have htrace : WordTrace (prefixWord ++ tailWord_137413) baseStart_137413 baseEnd_137413 := by
    simpa [prefixWord, tailWord_137413, baseEnd_137413] using wordTrace_append hprefix tailTrace_137413
  have hstable : (prefixWord ++ tailWord_137413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137413).length < 2 ^ (prefixWord ++ tailWord_137413).sum := by decide
  have hdescent : baseEnd_137413 < baseStart_137413 := by decide
  rcases family_descends (prefixWord ++ tailWord_137413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137423 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 4]
def baseStart_137423 : Nat := 118140960795 + 137423 * 2 ^ 59
def prefixEnd_137423 : Nat := 4983230072969 + 3 ^ 40 * 137423 * 2
def baseEnd_137423 : Nat := 70564051982921065580509

theorem tailTrace_137423 : CollatzResearch.WordTrace tailWord_137423 prefixEnd_137423 70564051982921065580509 := by
  unfold tailWord_137423
  simp only [CollatzResearch.WordTrace]
  refine ⟨5012228581147415824968923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3341485720764943883312615 5012228581147415824968923)
  ·
    refine ⟨7518342871721123737453385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5012228581147415824968923 7518342871721123737453385)
    ·
      refine ⟨5638757153790842803090039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7518342871721123737453385 5638757153790842803090039)
      ·
        refine ⟨8458135730686264204635059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5638757153790842803090039 8458135730686264204635059)
        ·
          refine ⟨12687203596029396306952589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8458135730686264204635059 12687203596029396306952589)
          ·
            refine ⟨4757701348511023615107221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12687203596029396306952589 4757701348511023615107221)
            ·
              refine ⟨223017250711454231958151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4757701348511023615107221 223017250711454231958151)
              ·
                refine ⟨334525876067181347937227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223017250711454231958151 334525876067181347937227)
                ·
                  refine ⟨501788814100772021905841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 334525876067181347937227 501788814100772021905841)
                  ·
                    refine ⟨376341610575579016429381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 501788814100772021905841 376341610575579016429381)
                    ·
                      refine ⟨70564051982921065580509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 376341610575579016429381 70564051982921065580509)
                      ·
                        rfl

theorem cell23_137423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 2, 4].length) (baseStart_137423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137423 prefixEnd_137423 := by exact prefixLift 137423
  have htrace : WordTrace (prefixWord ++ tailWord_137423) baseStart_137423 baseEnd_137423 := by
    simpa [prefixWord, tailWord_137423, baseEnd_137423] using wordTrace_append hprefix tailTrace_137423
  have hstable : (prefixWord ++ tailWord_137423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137423).length < 2 ^ (prefixWord ++ tailWord_137423).sum := by decide
  have hdescent : baseEnd_137423 < baseStart_137423 := by decide
  rcases family_descends (prefixWord ++ tailWord_137423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137447 : List Nat := [1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 3]
def baseStart_137447 : Nat := 118140960795 + 137447 * 2 ^ 59
def prefixEnd_137447 : Nat := 4983230072969 + 3 ^ 40 * 137447 * 2
def baseEnd_137447 : Nat := 70576375518628971680399

theorem tailTrace_137447 : CollatzResearch.WordTrace tailWord_137447 prefixEnd_137447 70576375518628971680399 := by
  unfold tailWord_137447
  simp only [CollatzResearch.WordTrace]
  refine ⟨5013103933060467923842595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3342069288706978615895063 5013103933060467923842595)
  ·
    refine ⟨7519655899590701885763893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5013103933060467923842595 7519655899590701885763893)
    ·
      refine ⟨704967740586628301790365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7519655899590701885763893 704967740586628301790365)
      ·
        refine ⟨264362902719985613171387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 704967740586628301790365 264362902719985613171387)
        ·
          refine ⟨396544354079978419757081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 264362902719985613171387 396544354079978419757081)
          ·
            refine ⟨297408265559983814817811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 396544354079978419757081 297408265559983814817811)
            ·
              refine ⟨446112398339975722226717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297408265559983814817811 446112398339975722226717)
              ·
                refine ⟨167292149377490895835019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446112398339975722226717 167292149377490895835019)
                ·
                  refine ⟨250938224066236343752529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167292149377490895835019 250938224066236343752529)
                  ·
                    refine ⟨188203668049677257814397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 250938224066236343752529 188203668049677257814397)
                    ·
                      refine ⟨70576375518628971680399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188203668049677257814397 70576375518628971680399)
                      ·
                        rfl

theorem cell23_137447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_137447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137447 prefixEnd_137447 := by exact prefixLift 137447
  have htrace : WordTrace (prefixWord ++ tailWord_137447) baseStart_137447 baseEnd_137447 := by
    simpa [prefixWord, tailWord_137447, baseEnd_137447] using wordTrace_append hprefix tailTrace_137447
  have hstable : (prefixWord ++ tailWord_137447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137447).length < 2 ^ (prefixWord ++ tailWord_137447).sum := by decide
  have hdescent : baseEnd_137447 < baseStart_137447 := by decide
  rcases family_descends (prefixWord ++ tailWord_137447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137500 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 3, 4, 2]
def baseStart_137500 : Nat := 118140960795 + 137500 * 2 ^ 59
def prefixEnd_137500 : Nat := 4983230072969 + 3 ^ 40 * 137500 * 2
def baseEnd_137500 : Nat := 70603589993317264317655

theorem tailTrace_137500 : CollatzResearch.WordTrace tailWord_137500 prefixEnd_137500 70603589993317264317655 := by
  unfold tailWord_137500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2507518500934228987760977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3343358001245638650347969 2507518500934228987760977)
  ·
    refine ⟨1880638875700671740820733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2507518500934228987760977 1880638875700671740820733)
    ·
      refine ⟨705239578387751902807775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1880638875700671740820733 705239578387751902807775)
      ·
        refine ⟨1057859367581627854211663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 705239578387751902807775 1057859367581627854211663)
        ·
          refine ⟨1586789051372441781317495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1057859367581627854211663 1586789051372441781317495)
          ·
            refine ⟨2380183577058662671976243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1586789051372441781317495 2380183577058662671976243)
            ·
              refine ⟨3570275365587994007964365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2380183577058662671976243 3570275365587994007964365)
              ·
                refine ⟨1338853262095497752986637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3570275365587994007964365 1338853262095497752986637)
                ·
                  refine ⟨502069973285811657369989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1338853262095497752986637 502069973285811657369989)
                  ·
                    refine ⟨94138119991089685756873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 502069973285811657369989 94138119991089685756873)
                    ·
                      refine ⟨70603589993317264317655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94138119991089685756873 70603589993317264317655)
                      ·
                        rfl

theorem cell23_137500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 3, 4, 2].length) (baseStart_137500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137500 prefixEnd_137500 := by exact prefixLift 137500
  have htrace : WordTrace (prefixWord ++ tailWord_137500) baseStart_137500 baseEnd_137500 := by
    simpa [prefixWord, tailWord_137500, baseEnd_137500] using wordTrace_append hprefix tailTrace_137500
  have hstable : (prefixWord ++ tailWord_137500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137500).length < 2 ^ (prefixWord ++ tailWord_137500).sum := by decide
  have hdescent : baseEnd_137500 < baseStart_137500 := by decide
  rcases family_descends (prefixWord ++ tailWord_137500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137503 : List Nat := [1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 5]
def baseStart_137503 : Nat := 118140960795 + 137503 * 2 ^ 59
def prefixEnd_137503 : Nat := 4983230072969 + 3 ^ 40 * 137503 * 2
def baseEnd_137503 : Nat := 70605130435280752580141

theorem tailTrace_137503 : CollatzResearch.WordTrace tailWord_137503 prefixEnd_137503 70605130435280752580141 := by
  unfold tailWord_137503
  simp only [CollatzResearch.WordTrace]
  refine ⟨5015146420857589487881163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3343430947238392991920775 5015146420857589487881163)
  ·
    refine ⟨7522719631286384231821745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5015146420857589487881163 7522719631286384231821745)
    ·
      refine ⟨5642039723464788173866309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7522719631286384231821745 5642039723464788173866309)
      ·
        refine ⟨1057882448149647782599933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5642039723464788173866309 1057882448149647782599933)
        ·
          refine ⟨396705918056117918474975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1057882448149647782599933 396705918056117918474975)
          ·
            refine ⟨595058877084176877712463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 396705918056117918474975 595058877084176877712463)
            ·
              refine ⟨892588315626265316568695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595058877084176877712463 892588315626265316568695)
              ·
                refine ⟨1338882473439397974853043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 892588315626265316568695 1338882473439397974853043)
                ·
                  refine ⟨2008323710159096962279565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1338882473439397974853043 2008323710159096962279565)
                  ·
                    refine ⟨753121391309661360854837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2008323710159096962279565 753121391309661360854837)
                    ·
                      refine ⟨70605130435280752580141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 753121391309661360854837 70605130435280752580141)
                      ·
                        rfl

theorem cell23_137503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 3, 5].length) (baseStart_137503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137503 prefixEnd_137503 := by exact prefixLift 137503
  have htrace : WordTrace (prefixWord ++ tailWord_137503) baseStart_137503 baseEnd_137503 := by
    simpa [prefixWord, tailWord_137503, baseEnd_137503] using wordTrace_append hprefix tailTrace_137503
  have hstable : (prefixWord ++ tailWord_137503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137503).length < 2 ^ (prefixWord ++ tailWord_137503).sum := by decide
  have hdescent : baseEnd_137503 < baseStart_137503 := by decide
  rcases family_descends (prefixWord ++ tailWord_137503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137634 : List Nat := [3, 3, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_137634 : Nat := 118140960795 + 137634 * 2 ^ 59
def prefixEnd_137634 : Nat := 4983230072969 + 3 ^ 40 * 137634 * 2
def baseEnd_137634 : Nat := 23557465467006580014013

theorem tailTrace_137634 : CollatzResearch.WordTrace tailWord_137634 prefixEnd_137634 23557465467006580014013 := by
  unfold tailWord_137634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1254981095845749715224989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3346616255588665907266637 1254981095845749715224989)
  ·
    refine ⟨470617910942156143209371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1254981095845749715224989 470617910942156143209371)
    ·
      refine ⟨705926866413234214814057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470617910942156143209371 705926866413234214814057)
      ·
        refine ⟨529445149809925661110543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 705926866413234214814057 529445149809925661110543)
        ·
          refine ⟨794167724714888491665815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 529445149809925661110543 794167724714888491665815)
          ·
            refine ⟨1191251587072332737498723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794167724714888491665815 1191251587072332737498723)
            ·
              refine ⟨1786877380608499106248085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191251587072332737498723 1786877380608499106248085)
              ·
                refine ⟨83759877216023395605379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1786877380608499106248085 83759877216023395605379)
                ·
                  refine ⟨125639815824035093408069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83759877216023395605379 125639815824035093408069)
                  ·
                    refine ⟨23557465467006580014013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125639815824035093408069 23557465467006580014013)
                    ·
                      rfl

theorem cell23_137634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_137634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137634 prefixEnd_137634 := by exact prefixLift 137634
  have htrace : WordTrace (prefixWord ++ tailWord_137634) baseStart_137634 baseEnd_137634 := by
    simpa [prefixWord, tailWord_137634, baseEnd_137634] using wordTrace_append hprefix tailTrace_137634
  have hstable : (prefixWord ++ tailWord_137634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137634).length < 2 ^ (prefixWord ++ tailWord_137634).sum := by decide
  have hdescent : baseEnd_137634 < baseStart_137634 := by decide
  rcases family_descends (prefixWord ++ tailWord_137634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137667 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 2, 3, 2]
def baseStart_137667 : Nat := 118140960795 + 137667 * 2 ^ 59
def prefixEnd_137667 : Nat := 4983230072969 + 3 ^ 40 * 137667 * 2
def baseEnd_137667 : Nat := 70689341262618110929387

theorem tailTrace_137667 : CollatzResearch.WordTrace tailWord_137667 prefixEnd_137667 70689341262618110929387 := by
  unfold tailWord_137667
  simp only [CollatzResearch.WordTrace]
  refine ⟨5021127992263445496851255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3347418661508963664567503 5021127992263445496851255)
  ·
    refine ⟨7531691988395168245276883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5021127992263445496851255 7531691988395168245276883)
    ·
      refine ⟨11297537982592752367915325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7531691988395168245276883 11297537982592752367915325)
      ·
        refine ⟨4236576743472282137968247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11297537982592752367915325 4236576743472282137968247)
        ·
          refine ⟨6354865115208423206952371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236576743472282137968247 6354865115208423206952371)
          ·
            refine ⟨9532297672812634810428557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354865115208423206952371 9532297672812634810428557)
            ·
              refine ⟨3574611627304738053910709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9532297672812634810428557 3574611627304738053910709)
              ·
                refine ⟨335119840059819192554129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3574611627304738053910709 335119840059819192554129)
                ·
                  refine ⟨251339880044864394415597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335119840059819192554129 251339880044864394415597)
                  ·
                    refine ⟨94252455016824147905849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251339880044864394415597 94252455016824147905849)
                    ·
                      refine ⟨70689341262618110929387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94252455016824147905849 70689341262618110929387)
                      ·
                        rfl

theorem cell23_137667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 2, 3, 2].length) (baseStart_137667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137667 prefixEnd_137667 := by exact prefixLift 137667
  have htrace : WordTrace (prefixWord ++ tailWord_137667) baseStart_137667 baseEnd_137667 := by
    simpa [prefixWord, tailWord_137667, baseEnd_137667] using wordTrace_append hprefix tailTrace_137667
  have hstable : (prefixWord ++ tailWord_137667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137667).length < 2 ^ (prefixWord ++ tailWord_137667).sum := by decide
  have hdescent : baseEnd_137667 < baseStart_137667 := by decide
  rcases family_descends (prefixWord ++ tailWord_137667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137668 : List Nat := [2, 3, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_137668 : Nat := 118140960795 + 137668 * 2 ^ 59
def prefixEnd_137668 : Nat := 4983230072969 + 3 ^ 40 * 137668 * 2
def baseEnd_137668 : Nat := 23563284914424202338961

theorem tailTrace_137668 : CollatzResearch.WordTrace tailWord_137668 prefixEnd_137668 23563284914424202338961 := by
  unfold tailWord_137668
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510582232629911333818829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3347442976839881778425105 2510582232629911333818829)
  ·
    refine ⟨941468337236216750182061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2510582232629911333818829 941468337236216750182061)
    ·
      refine ⟨353050626463581281318273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 941468337236216750182061 353050626463581281318273)
      ·
        refine ⟨264787969847685960988705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 353050626463581281318273 264787969847685960988705)
        ·
          refine ⟨198590977385764470741529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264787969847685960988705 198590977385764470741529)
          ·
            refine ⟨148943233039323353056147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198590977385764470741529 148943233039323353056147)
            ·
              refine ⟨223414849558985029584221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 148943233039323353056147 223414849558985029584221)
              ·
                refine ⟨83780568584619386094083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 223414849558985029584221 83780568584619386094083)
                ·
                  refine ⟨125670852876929079141125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83780568584619386094083 125670852876929079141125)
                  ·
                    refine ⟨23563284914424202338961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125670852876929079141125 23563284914424202338961)
                    ·
                      rfl

theorem cell23_137668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_137668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137668 prefixEnd_137668 := by exact prefixLift 137668
  have htrace : WordTrace (prefixWord ++ tailWord_137668) baseStart_137668 baseEnd_137668 := by
    simpa [prefixWord, tailWord_137668, baseEnd_137668] using wordTrace_append hprefix tailTrace_137668
  have hstable : (prefixWord ++ tailWord_137668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137668).length < 2 ^ (prefixWord ++ tailWord_137668).sum := by decide
  have hdescent : baseEnd_137668 < baseStart_137668 := by decide
  rcases family_descends (prefixWord ++ tailWord_137668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137684 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 4, 3, 2]
def baseStart_137684 : Nat := 118140960795 + 137684 * 2 ^ 59
def prefixEnd_137684 : Nat := 4983230072969 + 3 ^ 40 * 137684 * 2
def baseEnd_137684 : Nat := 70698070433744544416809

theorem tailTrace_137684 : CollatzResearch.WordTrace tailWord_137684 prefixEnd_137684 70698070433744544416809 := by
  unfold tailWord_137684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2510874016600928700110053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3347832022134571600146737 2510874016600928700110053)
  ·
    refine ⟨470788878112674131270635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2510874016600928700110053 470788878112674131270635)
    ·
      refine ⟨706183317169011196905953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 470788878112674131270635 706183317169011196905953)
      ·
        refine ⟨529637487876758397679465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 706183317169011196905953 529637487876758397679465)
        ·
          refine ⟨397228115907568798259599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 529637487876758397679465 397228115907568798259599)
          ·
            refine ⟨595842173861353197389399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397228115907568798259599 595842173861353197389399)
            ·
              refine ⟨893763260792029796084099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 595842173861353197389399 893763260792029796084099)
              ·
                refine ⟨1340644891188044694126149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893763260792029796084099 1340644891188044694126149)
                ·
                  refine ⟨251370917097758380148653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1340644891188044694126149 251370917097758380148653)
                  ·
                    refine ⟨94264093911659392555745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 251370917097758380148653 94264093911659392555745)
                    ·
                      refine ⟨70698070433744544416809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94264093911659392555745 70698070433744544416809)
                      ·
                        rfl

theorem cell23_137684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 4, 3, 2].length) (baseStart_137684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137684 prefixEnd_137684 := by exact prefixLift 137684
  have htrace : WordTrace (prefixWord ++ tailWord_137684) baseStart_137684 baseEnd_137684 := by
    simpa [prefixWord, tailWord_137684, baseEnd_137684] using wordTrace_append hprefix tailTrace_137684
  have hstable : (prefixWord ++ tailWord_137684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137684).length < 2 ^ (prefixWord ++ tailWord_137684).sum := by decide
  have hdescent : baseEnd_137684 < baseStart_137684 := by decide
  rcases family_descends (prefixWord ++ tailWord_137684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137698 : List Nat := [3, 3, 3, 2, 1, 2, 2, 1, 6]
def baseStart_137698 : Nat := 118140960795 + 137698 * 2 ^ 59
def prefixEnd_137698 : Nat := 4983230072969 + 3 ^ 40 * 137698 * 2
def baseEnd_137698 : Nat := 7856139906989721071305

theorem tailTrace_137698 : CollatzResearch.WordTrace tailWord_137698 prefixEnd_137698 7856139906989721071305 := by
  unfold tailWord_137698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1255564663787784447807437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3348172436767425194153165 1255564663787784447807437)
  ·
    refine ⟨470836748920419167927789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1255564663787784447807437 470836748920419167927789)
    ·
      refine ⟨176563780845157187972921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 470836748920419167927789 176563780845157187972921)
      ·
        refine ⟨132422835633867890979691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176563780845157187972921 132422835633867890979691)
        ·
          refine ⟨198634253450801836469537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132422835633867890979691 198634253450801836469537)
          ·
            refine ⟨148975690088101377352153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 198634253450801836469537 148975690088101377352153)
            ·
              refine ⟨111731767566076033014115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 148975690088101377352153 111731767566076033014115)
              ·
                refine ⟨167597651349114049521173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 111731767566076033014115 167597651349114049521173)
                ·
                  refine ⟨7856139906989721071305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 167597651349114049521173 7856139906989721071305)
                  ·
                    rfl

theorem cell23_137698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_137698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137698 prefixEnd_137698 := by exact prefixLift 137698
  have htrace : WordTrace (prefixWord ++ tailWord_137698) baseStart_137698 baseEnd_137698 := by
    simpa [prefixWord, tailWord_137698, baseEnd_137698] using wordTrace_append hprefix tailTrace_137698
  have hstable : (prefixWord ++ tailWord_137698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137698).length < 2 ^ (prefixWord ++ tailWord_137698).sum := by decide
  have hdescent : baseEnd_137698 < baseStart_137698 := by decide
  rcases family_descends (prefixWord ++ tailWord_137698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137700 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 1, 8, 3]
def baseStart_137700 : Nat := 118140960795 + 137700 * 2 ^ 59
def prefixEnd_137700 : Nat := 4983230072969 + 3 ^ 40 * 137700 * 2
def baseEnd_137700 : Nat := 70706286124216481816735

theorem tailTrace_137700 : CollatzResearch.WordTrace tailWord_137700 prefixEnd_137700 70706286124216481816735 := by
  unfold tailWord_137700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2511165800571946066401277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3348221067429261421868369 2511165800571946066401277)
  ·
    refine ⟨941687175214479774900479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2511165800571946066401277 941687175214479774900479)
    ·
      refine ⟨1412530762821719662350719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941687175214479774900479 1412530762821719662350719)
      ·
        refine ⟨2118796144232579493526079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412530762821719662350719 2118796144232579493526079)
        ·
          refine ⟨3178194216348869240289119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118796144232579493526079 3178194216348869240289119)
          ·
            refine ⟨4767291324523303860433679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178194216348869240289119 4767291324523303860433679)
            ·
              refine ⟨7150936986784955790650519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767291324523303860433679 7150936986784955790650519)
              ·
                refine ⟨10726405480177433685975779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150936986784955790650519 10726405480177433685975779)
                ·
                  refine ⟨16089608220266150528963669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10726405480177433685975779 16089608220266150528963669)
                  ·
                    refine ⟨188550096331243951511293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16089608220266150528963669 188550096331243951511293)
                    ·
                      refine ⟨70706286124216481816735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188550096331243951511293 70706286124216481816735)
                      ·
                        rfl

theorem cell23_137700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 1, 8, 3].length) (baseStart_137700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137700 prefixEnd_137700 := by exact prefixLift 137700
  have htrace : WordTrace (prefixWord ++ tailWord_137700) baseStart_137700 baseEnd_137700 := by
    simpa [prefixWord, tailWord_137700, baseEnd_137700] using wordTrace_append hprefix tailTrace_137700
  have hstable : (prefixWord ++ tailWord_137700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137700).length < 2 ^ (prefixWord ++ tailWord_137700).sum := by decide
  have hdescent : baseEnd_137700 < baseStart_137700 := by decide
  rcases family_descends (prefixWord ++ tailWord_137700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137707 : List Nat := [1, 1, 1, 1, 2, 3, 5, 3, 2, 4]
def baseStart_137707 : Nat := 118140960795 + 137707 * 2 ^ 59
def prefixEnd_137707 : Nat := 4983230072969 + 3 ^ 40 * 137707 * 2
def baseEnd_137707 : Nat := 23569960162932651476401

theorem tailTrace_137707 : CollatzResearch.WordTrace tailWord_137707 prefixEnd_137707 23569960162932651476401 := by
  unfold tailWord_137707
  simp only [CollatzResearch.WordTrace]
  refine ⟨5022586912118532328307375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3348391274745688218871583 5022586912118532328307375)
  ·
    refine ⟨7533880368177798492461063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5022586912118532328307375 7533880368177798492461063)
    ·
      refine ⟨11300820552266697738691595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7533880368177798492461063 11300820552266697738691595)
      ·
        refine ⟨16951230828400046608037393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11300820552266697738691595 16951230828400046608037393)
        ·
          refine ⟨12713423121300034956028045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16951230828400046608037393 12713423121300034956028045)
          ·
            refine ⟨4767533670487513108510517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12713423121300034956028045 4767533670487513108510517)
            ·
              refine ⟨446956281608204353922861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4767533670487513108510517 446956281608204353922861)
              ·
                refine ⟨167608605603076632721073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 446956281608204353922861 167608605603076632721073)
                ·
                  refine ⟨125706454202307474540805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 167608605603076632721073 125706454202307474540805)
                  ·
                    refine ⟨23569960162932651476401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 125706454202307474540805 23569960162932651476401)
                    ·
                      rfl

theorem cell23_137707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 3, 2, 4].length) (baseStart_137707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137707 prefixEnd_137707 := by exact prefixLift 137707
  have htrace : WordTrace (prefixWord ++ tailWord_137707) baseStart_137707 baseEnd_137707 := by
    simpa [prefixWord, tailWord_137707, baseEnd_137707] using wordTrace_append hprefix tailTrace_137707
  have hstable : (prefixWord ++ tailWord_137707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137707).length < 2 ^ (prefixWord ++ tailWord_137707).sum := by decide
  have hdescent : baseEnd_137707 < baseStart_137707 := by decide
  rcases family_descends (prefixWord ++ tailWord_137707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137714 : List Nat := [3, 2, 1, 4, 2, 1, 1, 1, 3, 1, 4]
def baseStart_137714 : Nat := 118140960795 + 137714 * 2 ^ 59
def prefixEnd_137714 : Nat := 4983230072969 + 3 ^ 40 * 137714 * 2
def baseEnd_137714 : Nat := 70713474853379427041671

theorem tailTrace_137714 : CollatzResearch.WordTrace tailWord_137714 prefixEnd_137714 70713474853379427041671 := by
  unfold tailWord_137714
  simp only [CollatzResearch.WordTrace]
  refine ⟨1255710555773293130953049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3348561482062115015874797 1255710555773293130953049)
  ·
    refine ⟨941782916829969848214787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1255710555773293130953049 941782916829969848214787)
    ·
      refine ⟨1412674375244954772322181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 941782916829969848214787 1412674375244954772322181)
      ·
        refine ⟨264876445358429019810409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1412674375244954772322181 264876445358429019810409)
        ·
          refine ⟨198657334018821764857807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 264876445358429019810409 198657334018821764857807)
          ·
            refine ⟨297986001028232647286711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 198657334018821764857807 297986001028232647286711)
            ·
              refine ⟨446979001542348970930067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 297986001028232647286711 446979001542348970930067)
              ·
                refine ⟨670468502313523456395101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 446979001542348970930067 670468502313523456395101)
                ·
                  refine ⟨251425688367571296148163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 670468502313523456395101 251425688367571296148163)
                  ·
                    refine ⟨377138532551356944222245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 251425688367571296148163 377138532551356944222245)
                    ·
                      refine ⟨70713474853379427041671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 377138532551356944222245 70713474853379427041671)
                      ·
                        rfl

theorem cell23_137714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_137714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137714 prefixEnd_137714 := by exact prefixLift 137714
  have htrace : WordTrace (prefixWord ++ tailWord_137714) baseStart_137714 baseEnd_137714 := by
    simpa [prefixWord, tailWord_137714, baseEnd_137714] using wordTrace_append hprefix tailTrace_137714
  have hstable : (prefixWord ++ tailWord_137714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137714).length < 2 ^ (prefixWord ++ tailWord_137714).sum := by decide
  have hdescent : baseEnd_137714 < baseStart_137714 := by decide
  rcases family_descends (prefixWord ++ tailWord_137714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137731 : List Nat := [1, 1, 1, 3, 2, 1, 4, 5, 1, 2, 2]
def baseStart_137731 : Nat := 118140960795 + 137731 * 2 ^ 59
def prefixEnd_137731 : Nat := 4983230072969 + 3 ^ 40 * 137731 * 2
def baseEnd_137731 : Nat := 70722204024505860529093

theorem tailTrace_137731 : CollatzResearch.WordTrace tailWord_137731 prefixEnd_137731 70722204024505860529093 := by
  unfold tailWord_137731
  simp only [CollatzResearch.WordTrace]
  refine ⟨5023462264031584427181047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3348974842687722951454031 5023462264031584427181047)
  ·
    refine ⟨7535193396047376640771571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5023462264031584427181047 7535193396047376640771571)
    ·
      refine ⟨11302790094071064961157357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7535193396047376640771571 11302790094071064961157357)
      ·
        refine ⟨4238546285276649360434009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11302790094071064961157357 4238546285276649360434009)
        ·
          refine ⟨3178909713957487020325507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4238546285276649360434009 3178909713957487020325507)
          ·
            refine ⟨4768364570936230530488261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3178909713957487020325507 4768364570936230530488261)
            ·
              refine ⟨894068357050543224466549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4768364570936230530488261 894068357050543224466549)
              ·
                refine ⟨83818908473488427293739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 894068357050543224466549 83818908473488427293739)
                ·
                  refine ⟨125728362710232640940609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83818908473488427293739 125728362710232640940609)
                  ·
                    refine ⟨94296272032674480705457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 125728362710232640940609 94296272032674480705457)
                    ·
                      refine ⟨70722204024505860529093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94296272032674480705457 70722204024505860529093)
                      ·
                        rfl

theorem cell23_137731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 5, 1, 2, 2].length) (baseStart_137731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137731 prefixEnd_137731 := by exact prefixLift 137731
  have htrace : WordTrace (prefixWord ++ tailWord_137731) baseStart_137731 baseEnd_137731 := by
    simpa [prefixWord, tailWord_137731, baseEnd_137731] using wordTrace_append hprefix tailTrace_137731
  have hstable : (prefixWord ++ tailWord_137731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137731).length < 2 ^ (prefixWord ++ tailWord_137731).sum := by decide
  have hdescent : baseEnd_137731 < baseStart_137731 := by decide
  rcases family_descends (prefixWord ++ tailWord_137731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137787 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 7, 4, 2]
def baseStart_137787 : Nat := 118140960795 + 137787 * 2 ^ 59
def prefixEnd_137787 : Nat := 4983230072969 + 3 ^ 40 * 137787 * 2
def baseEnd_137787 : Nat := 70750958941157641428835

theorem tailTrace_137787 : CollatzResearch.WordTrace tailWord_137787 prefixEnd_137787 70750958941157641428835 := by
  unfold tailWord_137787
  simp only [CollatzResearch.WordTrace]
  refine ⟨5025504751828705991219615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3350336501219137327479743 5025504751828705991219615)
  ·
    refine ⟨7538257127743058986829423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5025504751828705991219615 7538257127743058986829423)
    ·
      refine ⟨11307385691614588480244135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7538257127743058986829423 11307385691614588480244135)
      ·
        refine ⟨16961078537421882720366203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11307385691614588480244135 16961078537421882720366203)
        ·
          refine ⟨25441617806132824080549305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16961078537421882720366203 25441617806132824080549305)
          ·
            refine ⟨19081213354599618060411979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25441617806132824080549305 19081213354599618060411979)
            ·
              refine ⟨28621820031899427090617969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19081213354599618060411979 28621820031899427090617969)
              ·
                refine ⟨21466365023924570317963477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28621820031899427090617969 21466365023924570317963477)
                ·
                  refine ⟨503117930248232116827269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21466365023924570317963477 503117930248232116827269)
                  ·
                    refine ⟨94334611921543521905113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 503117930248232116827269 94334611921543521905113)
                    ·
                      refine ⟨70750958941157641428835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94334611921543521905113 70750958941157641428835)
                      ·
                        rfl

theorem cell23_137787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 7, 4, 2].length) (baseStart_137787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137787 prefixEnd_137787 := by exact prefixLift 137787
  have htrace : WordTrace (prefixWord ++ tailWord_137787) baseStart_137787 baseEnd_137787 := by
    simpa [prefixWord, tailWord_137787, baseEnd_137787] using wordTrace_append hprefix tailTrace_137787
  have hstable : (prefixWord ++ tailWord_137787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137787).length < 2 ^ (prefixWord ++ tailWord_137787).sum := by decide
  have hdescent : baseEnd_137787 < baseStart_137787 := by decide
  rcases family_descends (prefixWord ++ tailWord_137787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137798 : List Nat := [6, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3]
def baseStart_137798 : Nat := 118140960795 + 137798 * 2 ^ 59
def prefixEnd_137798 : Nat := 4983230072969 + 3 ^ 40 * 137798 * 2
def baseEnd_137798 : Nat := 70756607228357098391285

theorem tailTrace_137798 : CollatzResearch.WordTrace tailWord_137798 prefixEnd_137798 70756607228357098391285 := by
  unfold tailWord_137798
  simp only [CollatzResearch.WordTrace]
  refine ⟨157059561087151714683439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3350603969859236579913365 157059561087151714683439)
  ·
    refine ⟨235589341630727572025159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 157059561087151714683439 235589341630727572025159)
    ·
      refine ⟨353384012446091358037739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 235589341630727572025159 353384012446091358037739)
      ·
        refine ⟨530076018669137037056609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 353384012446091358037739 530076018669137037056609)
        ·
          refine ⟨397557014001852777792457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 530076018669137037056609 397557014001852777792457)
          ·
            refine ⟨298167760501389583344343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 397557014001852777792457 298167760501389583344343)
            ·
              refine ⟨447251640752084375016515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298167760501389583344343 447251640752084375016515)
              ·
                refine ⟨670877461128126562524773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 447251640752084375016515 670877461128126562524773)
                ·
                  refine ⟨125789523961523730473395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 670877461128126562524773 125789523961523730473395)
                  ·
                    refine ⟨188684285942285595710093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125789523961523730473395 188684285942285595710093)
                    ·
                      refine ⟨70756607228357098391285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188684285942285595710093 70756607228357098391285)
                      ·
                        rfl

theorem cell23_137798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 4, 1, 3].length) (baseStart_137798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137798 prefixEnd_137798 := by exact prefixLift 137798
  have htrace : WordTrace (prefixWord ++ tailWord_137798) baseStart_137798 baseEnd_137798 := by
    simpa [prefixWord, tailWord_137798, baseEnd_137798] using wordTrace_append hprefix tailTrace_137798
  have hstable : (prefixWord ++ tailWord_137798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137798).length < 2 ^ (prefixWord ++ tailWord_137798).sum := by decide
  have hdescent : baseEnd_137798 < baseStart_137798 := by decide
  rcases family_descends (prefixWord ++ tailWord_137798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137861 : List Nat := [1, 3, 1, 1, 4, 3, 3, 2, 5]
def baseStart_137861 : Nat := 118140960795 + 137861 * 2 ^ 59
def prefixEnd_137861 : Nat := 4983230072969 + 3 ^ 40 * 137861 * 2
def baseEnd_137861 : Nat := 7865439612176705767055

theorem tailTrace_137861 : CollatzResearch.WordTrace tailWord_137861 prefixEnd_137861 7865439612176705767055 := by
  unfold tailWord_137861
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028203753560616629413437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3352135835707077752942291 5028203753560616629413437)
  ·
    refine ⟨1885576407585231236030039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5028203753560616629413437 1885576407585231236030039)
    ·
      refine ⟨2828364611377846854045059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1885576407585231236030039 2828364611377846854045059)
      ·
        refine ⟨4242546917066770281067589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828364611377846854045059 4242546917066770281067589)
        ·
          refine ⟨795477546950019427700173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4242546917066770281067589 795477546950019427700173)
          ·
            refine ⟨298304080106257285387565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 795477546950019427700173 298304080106257285387565)
            ·
              refine ⟨111864030039846482020337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 298304080106257285387565 111864030039846482020337)
              ·
                refine ⟨83898022529884861515253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 111864030039846482020337 83898022529884861515253)
                ·
                  refine ⟨7865439612176705767055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 83898022529884861515253 7865439612176705767055)
                  ·
                    rfl

theorem cell23_137861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 3, 2, 5].length) (baseStart_137861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137861 prefixEnd_137861 := by exact prefixLift 137861
  have htrace : WordTrace (prefixWord ++ tailWord_137861) baseStart_137861 baseEnd_137861 := by
    simpa [prefixWord, tailWord_137861, baseEnd_137861] using wordTrace_append hprefix tailTrace_137861
  have hstable : (prefixWord ++ tailWord_137861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137861).length < 2 ^ (prefixWord ++ tailWord_137861).sum := by decide
  have hdescent : baseEnd_137861 < baseStart_137861 := by decide
  rcases family_descends (prefixWord ++ tailWord_137861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137914 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3]
def baseStart_137914 : Nat := 118140960795 + 137914 * 2 ^ 59
def prefixEnd_137914 : Nat := 4983230072969 + 3 ^ 40 * 137914 * 2
def baseEnd_137914 : Nat := 70816170984278644540751

theorem tailTrace_137914 : CollatzResearch.WordTrace tailWord_137914 prefixEnd_137914 70816170984278644540751 := by
  unfold tailWord_137914
  simp only [CollatzResearch.WordTrace]
  refine ⟨1257534205592151670273199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3353424548245737787395197 1257534205592151670273199)
  ·
    refine ⟨1886301308388227505409799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1257534205592151670273199 1886301308388227505409799)
    ·
      refine ⟨2829451962582341258114699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1886301308388227505409799 2829451962582341258114699)
      ·
        refine ⟨4244177943873511887172049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2829451962582341258114699 4244177943873511887172049)
        ·
          refine ⟨3183133457905133915379037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4244177943873511887172049 3183133457905133915379037)
          ·
            refine ⟨1193675046714425218267139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3183133457905133915379037 1193675046714425218267139)
            ·
              refine ⟨1790512570071637827400709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193675046714425218267139 1790512570071637827400709)
              ·
                refine ⟨335721106888432092637633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1790512570071637827400709 335721106888432092637633)
                ·
                  refine ⟨251790830166324069478225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335721106888432092637633 251790830166324069478225)
                  ·
                    refine ⟨188843122624743052108669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251790830166324069478225 188843122624743052108669)
                    ·
                      refine ⟨70816170984278644540751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188843122624743052108669 70816170984278644540751)
                      ·
                        rfl

theorem cell23_137914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 2, 2, 3].length) (baseStart_137914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137914 prefixEnd_137914 := by exact prefixLift 137914
  have htrace : WordTrace (prefixWord ++ tailWord_137914) baseStart_137914 baseEnd_137914 := by
    simpa [prefixWord, tailWord_137914, baseEnd_137914] using wordTrace_append hprefix tailTrace_137914
  have hstable : (prefixWord ++ tailWord_137914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137914).length < 2 ^ (prefixWord ++ tailWord_137914).sum := by decide
  have hdescent : baseEnd_137914 < baseStart_137914 := by decide
  rcases family_descends (prefixWord ++ tailWord_137914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137934 : List Nat := [4, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_137934 : Nat := 118140960795 + 137934 * 2 ^ 59
def prefixEnd_137934 : Nat := 4983230072969 + 3 ^ 40 * 137934 * 2
def baseEnd_137934 : Nat := 7869604510818729587851

theorem tailTrace_137934 : CollatzResearch.WordTrace tailWord_137934 prefixEnd_137934 7869604510818729587851 := by
  unfold tailWord_137934
  simp only [CollatzResearch.WordTrace]
  refine ⟨628858285287018762102607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3353910854864100064547237 628858285287018762102607)
  ·
    refine ⟨943287427930528143153911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 628858285287018762102607 943287427930528143153911)
    ·
      refine ⟨1414931141895792214730867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 943287427930528143153911 1414931141895792214730867)
      ·
        refine ⟨2122396712843688322096301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414931141895792214730867 2122396712843688322096301)
        ·
          refine ⟨795898767316383120786113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2122396712843688322096301 795898767316383120786113)
          ·
            refine ⟨596924075487287340589585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 795898767316383120786113 596924075487287340589585)
            ·
              refine ⟨447693056615465505442189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 596924075487287340589585 447693056615465505442189)
              ·
                refine ⟨167884896230799564540821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 447693056615465505442189 167884896230799564540821)
                ·
                  refine ⟨7869604510818729587851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 167884896230799564540821 7869604510818729587851)
                  ·
                    rfl

theorem cell23_137934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_137934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137934 prefixEnd_137934 := by exact prefixLift 137934
  have htrace : WordTrace (prefixWord ++ tailWord_137934) baseStart_137934 baseEnd_137934 := by
    simpa [prefixWord, tailWord_137934, baseEnd_137934] using wordTrace_append hprefix tailTrace_137934
  have hstable : (prefixWord ++ tailWord_137934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137934).length < 2 ^ (prefixWord ++ tailWord_137934).sum := by decide
  have hdescent : baseEnd_137934 < baseStart_137934 := by decide
  rcases family_descends (prefixWord ++ tailWord_137934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137948 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 2, 2, 3]
def baseStart_137948 : Nat := 118140960795 + 137948 * 2 ^ 59
def prefixEnd_137948 : Nat := 4983230072969 + 3 ^ 40 * 137948 * 2
def baseEnd_137948 : Nat := 70833629326531511515595

theorem tailTrace_137948 : CollatzResearch.WordTrace tailWord_137948 prefixEnd_137948 70833629326531511515595 := by
  unfold tailWord_137948
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515688452122715243915249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3354251269496953658553665 2515688452122715243915249)
  ·
    refine ⟨1886766339092036432936437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2515688452122715243915249 1886766339092036432936437)
    ·
      refine ⟨176884344289878415587791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1886766339092036432936437 176884344289878415587791)
      ·
        refine ⟨265326516434817623381687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 176884344289878415587791 265326516434817623381687)
        ·
          refine ⟨397989774652226435072531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265326516434817623381687 397989774652226435072531)
          ·
            refine ⟨596984661978339652608797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 397989774652226435072531 596984661978339652608797)
            ·
              refine ⟨223869248241877369728299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 596984661978339652608797 223869248241877369728299)
              ·
                refine ⟨335803872362816054592449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 223869248241877369728299 335803872362816054592449)
                ·
                  refine ⟨251852904272112040944337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 335803872362816054592449 251852904272112040944337)
                  ·
                    refine ⟨188889678204084030708253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251852904272112040944337 188889678204084030708253)
                    ·
                      refine ⟨70833629326531511515595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188889678204084030708253 70833629326531511515595)
                      ·
                        rfl

theorem cell23_137948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_137948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137948 prefixEnd_137948 := by exact prefixLift 137948
  have htrace : WordTrace (prefixWord ++ tailWord_137948) baseStart_137948 baseEnd_137948 := by
    simpa [prefixWord, tailWord_137948, baseEnd_137948] using wordTrace_append hprefix tailTrace_137948
  have hstable : (prefixWord ++ tailWord_137948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137948).length < 2 ^ (prefixWord ++ tailWord_137948).sum := by decide
  have hdescent : baseEnd_137948 < baseStart_137948 := by decide
  rcases family_descends (prefixWord ++ tailWord_137948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137977 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 3, 6]
def baseStart_137977 : Nat := 118140960795 + 137977 * 2 ^ 59
def prefixEnd_137977 : Nat := 4983230072969 + 3 ^ 40 * 137977 * 2
def baseEnd_137977 : Nat := 23616173421837299350987

theorem tailTrace_137977 : CollatzResearch.WordTrace tailWord_137977 prefixEnd_137977 23616173421837299350987 := by
  unfold tailWord_137977
  simp only [CollatzResearch.WordTrace]
  refine ⟨5032434621140368440636185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3354956414093578960424123 5032434621140368440636185)
  ·
    refine ⟨3774325965855276330477139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5032434621140368440636185 3774325965855276330477139)
    ·
      refine ⟨5661488948782914495715709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3774325965855276330477139 5661488948782914495715709)
      ·
        refine ⟨2123058355793592935893391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5661488948782914495715709 2123058355793592935893391)
        ·
          refine ⟨3184587533690389403840087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123058355793592935893391 3184587533690389403840087)
          ·
            refine ⟨4776881300535584105760131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184587533690389403840087 4776881300535584105760131)
            ·
              refine ⟨7165321950803376158640197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776881300535584105760131 7165321950803376158640197)
              ·
                refine ⟨1343497865775633029745037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7165321950803376158640197 1343497865775633029745037)
                ·
                  refine ⟨503811699665862386154389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1343497865775633029745037 503811699665862386154389)
                  ·
                    refine ⟨23616173421837299350987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 503811699665862386154389 23616173421837299350987)
                    ·
                      rfl

theorem cell23_137977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 3, 6].length) (baseStart_137977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137977 prefixEnd_137977 := by exact prefixLift 137977
  have htrace : WordTrace (prefixWord ++ tailWord_137977) baseStart_137977 baseEnd_137977 := by
    simpa [prefixWord, tailWord_137977, baseEnd_137977] using wordTrace_append hprefix tailTrace_137977
  have hstable : (prefixWord ++ tailWord_137977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137977).length < 2 ^ (prefixWord ++ tailWord_137977).sum := by decide
  have hdescent : baseEnd_137977 < baseStart_137977 := by decide
  rcases family_descends (prefixWord ++ tailWord_137977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137978 : List Nat := [3, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3]
def baseStart_137978 : Nat := 118140960795 + 137978 * 2 ^ 59
def prefixEnd_137978 : Nat := 4983230072969 + 3 ^ 40 * 137978 * 2
def baseEnd_137978 : Nat := 70849033746166394140457

theorem tailTrace_137978 : CollatzResearch.WordTrace tailWord_137978 prefixEnd_137978 70849033746166394140457 := by
  unfold tailWord_137978
  simp only [CollatzResearch.WordTrace]
  refine ⟨1258117773534186402855647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3354980729424497074281725 1258117773534186402855647)
  ·
    refine ⟨1887176660301279604283471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1258117773534186402855647 1887176660301279604283471)
    ·
      refine ⟨2830764990451919406425207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887176660301279604283471 2830764990451919406425207)
      ·
        refine ⟨4246147485677879109637811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830764990451919406425207 4246147485677879109637811)
        ·
          refine ⟨6369221228516818664456717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246147485677879109637811 6369221228516818664456717)
          ·
            refine ⟨2388457960693806999171269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6369221228516818664456717 2388457960693806999171269)
            ·
              refine ⟨447835867630088812344613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2388457960693806999171269 447835867630088812344613)
              ·
                refine ⟨83969225180641652314615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 447835867630088812344613 83969225180641652314615)
                ·
                  refine ⟨125953837770962478471923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 83969225180641652314615 125953837770962478471923)
                  ·
                    refine ⟨188930756656443717707885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 125953837770962478471923 188930756656443717707885)
                    ·
                      refine ⟨70849033746166394140457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188930756656443717707885 70849033746166394140457)
                      ·
                        rfl

theorem cell23_137978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 1, 1, 3].length) (baseStart_137978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137978 prefixEnd_137978 := by exact prefixLift 137978
  have htrace : WordTrace (prefixWord ++ tailWord_137978) baseStart_137978 baseEnd_137978 := by
    simpa [prefixWord, tailWord_137978, baseEnd_137978] using wordTrace_append hprefix tailTrace_137978
  have hstable : (prefixWord ++ tailWord_137978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137978).length < 2 ^ (prefixWord ++ tailWord_137978).sum := by decide
  have hdescent : baseEnd_137978 < baseStart_137978 := by decide
  rcases family_descends (prefixWord ++ tailWord_137978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_137984 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 4, 6, 2]
def baseStart_137984 : Nat := 118140960795 + 137984 * 2 ^ 59
def prefixEnd_137984 : Nat := 4983230072969 + 3 ^ 40 * 137984 * 2
def baseEnd_137984 : Nat := 70852114630093370665429

theorem tailTrace_137984 : CollatzResearch.WordTrace tailWord_137984 prefixEnd_137984 70852114630093370665429 := by
  unfold tailWord_137984
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516344966057504318070503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3355126621410005757427337 2516344966057504318070503)
  ·
    refine ⟨3774517449086256477105755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2516344966057504318070503 3774517449086256477105755)
    ·
      refine ⟨5661776173629384715658633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3774517449086256477105755 5661776173629384715658633)
      ·
        refine ⟨4246332130222038536743975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5661776173629384715658633 4246332130222038536743975)
        ·
          refine ⟨6369498195333057805115963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246332130222038536743975 6369498195333057805115963)
          ·
            refine ⟨9554247292999586707673945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369498195333057805115963 9554247292999586707673945)
            ·
              refine ⟨7165685469749690030755459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9554247292999586707673945 7165685469749690030755459)
              ·
                refine ⟨10748528204624535046133189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7165685469749690030755459 10748528204624535046133189)
                ·
                  refine ⟨2015349038367100321149973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10748528204624535046133189 2015349038367100321149973)
                  ·
                    refine ⟨94469486173457827553905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2015349038367100321149973 94469486173457827553905)
                    ·
                      refine ⟨70852114630093370665429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94469486173457827553905 70852114630093370665429)
                      ·
                        rfl

theorem cell23_137984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 4, 6, 2].length) (baseStart_137984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_137984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_137984 prefixEnd_137984 := by exact prefixLift 137984
  have htrace : WordTrace (prefixWord ++ tailWord_137984) baseStart_137984 baseEnd_137984 := by
    simpa [prefixWord, tailWord_137984, baseEnd_137984] using wordTrace_append hprefix tailTrace_137984
  have hstable : (prefixWord ++ tailWord_137984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_137984).length < 2 ^ (prefixWord ++ tailWord_137984).sum := by decide
  have hdescent : baseEnd_137984 < baseStart_137984 := by decide
  rcases family_descends (prefixWord ++ tailWord_137984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138021 : List Nat := [1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 3]
def baseStart_138021 : Nat := 118140960795 + 138021 * 2 ^ 59
def prefixEnd_138021 : Nat := 4983230072969 + 3 ^ 40 * 138021 * 2
def baseEnd_138021 : Nat := 70871113414309725902759

theorem tailTrace_138021 : CollatzResearch.WordTrace tailWord_138021 prefixEnd_138021 70871113414309725902759 := by
  unfold tailWord_138021
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034039432980963955237917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3356026288653975970158611 5034039432980963955237917)
  ·
    refine ⟨1887764787367861483214219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5034039432980963955237917 1887764787367861483214219)
    ·
      refine ⟨2831647181051792224821329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887764787367861483214219 2831647181051792224821329)
      ·
        refine ⟨2123735385788844168615997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831647181051792224821329 2123735385788844168615997)
        ·
          refine ⟨796400769670816563230999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2123735385788844168615997 796400769670816563230999)
          ·
            refine ⟨1194601154506224844846499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796400769670816563230999 1194601154506224844846499)
            ·
              refine ⟨1791901731759337267269749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194601154506224844846499 1791901731759337267269749)
              ·
                refine ⟨167990787352437868806539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1791901731759337267269749 167990787352437868806539)
                ·
                  refine ⟨251986181028656803209809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 167990787352437868806539 251986181028656803209809)
                  ·
                    refine ⟨188989635771492602407357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 251986181028656803209809 188989635771492602407357)
                    ·
                      refine ⟨70871113414309725902759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 188989635771492602407357 70871113414309725902759)
                      ·
                        rfl

theorem cell23_138021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 5, 1, 2, 3].length) (baseStart_138021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138021 prefixEnd_138021 := by exact prefixLift 138021
  have htrace : WordTrace (prefixWord ++ tailWord_138021) baseStart_138021 baseEnd_138021 := by
    simpa [prefixWord, tailWord_138021, baseEnd_138021] using wordTrace_append hprefix tailTrace_138021
  have hstable : (prefixWord ++ tailWord_138021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138021).length < 2 ^ (prefixWord ++ tailWord_138021).sum := by decide
  have hdescent : baseEnd_138021 < baseStart_138021 := by decide
  rcases family_descends (prefixWord ++ tailWord_138021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138027 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6]
def baseStart_138027 : Nat := 118140960795 + 138027 * 2 ^ 59
def prefixEnd_138027 : Nat := 4983230072969 + 3 ^ 40 * 138027 * 2
def baseEnd_138027 : Nat := 70874194298236702427731

theorem tailTrace_138027 : CollatzResearch.WordTrace tailWord_138027 prefixEnd_138027 70874194298236702427731 := by
  unfold tailWord_138027
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034258270959226979956335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3356172180639484653304223 5034258270959226979956335)
  ·
    refine ⟨7551387406438840469934503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5034258270959226979956335 7551387406438840469934503)
    ·
      refine ⟨11327081109658260704901755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7551387406438840469934503 11327081109658260704901755)
      ·
        refine ⟨16990621664487391057352633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11327081109658260704901755 16990621664487391057352633)
        ·
          refine ⟨12742966248365543293014475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16990621664487391057352633 12742966248365543293014475)
          ·
            refine ⟨19114449372548314939521713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12742966248365543293014475 19114449372548314939521713)
            ·
              refine ⟨14335837029411236204641285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19114449372548314939521713 14335837029411236204641285)
              ·
                refine ⟨2687969443014606788370241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14335837029411236204641285 2687969443014606788370241)
                ·
                  refine ⟨2015977082260955091277681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687969443014606788370241 2015977082260955091277681)
                  ·
                    refine ⟨1511982811695716318458261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2015977082260955091277681 1511982811695716318458261)
                    ·
                      refine ⟨70874194298236702427731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1511982811695716318458261 70874194298236702427731)
                      ·
                        rfl

theorem cell23_138027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 2, 6].length) (baseStart_138027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138027 prefixEnd_138027 := by exact prefixLift 138027
  have htrace : WordTrace (prefixWord ++ tailWord_138027) baseStart_138027 baseEnd_138027 := by
    simpa [prefixWord, tailWord_138027, baseEnd_138027] using wordTrace_append hprefix tailTrace_138027
  have hstable : (prefixWord ++ tailWord_138027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138027).length < 2 ^ (prefixWord ++ tailWord_138027).sum := by decide
  have hdescent : baseEnd_138027 < baseStart_138027 := by decide
  rcases family_descends (prefixWord ++ tailWord_138027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138029 : List Nat := [1, 5, 3, 2, 2, 1, 1, 1, 3, 1, 3]
def baseStart_138029 : Nat := 118140960795 + 138029 * 2 ^ 59
def prefixEnd_138029 : Nat := 4983230072969 + 3 ^ 40 * 138029 * 2
def baseEnd_138029 : Nat := 70875221259545694602723

theorem tailTrace_138029 : CollatzResearch.WordTrace tailWord_138029 prefixEnd_138029 70875221259545694602723 := by
  unfold tailWord_138029
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034331216951981321529141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3356220811301320881019427 5034331216951981321529141)
  ·
    refine ⟨471968551589248248893357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5034331216951981321529141 471968551589248248893357)
    ·
      refine ⟨176988206845968093335009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 471968551589248248893357 176988206845968093335009)
      ·
        refine ⟨132741155134476070001257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 176988206845968093335009 132741155134476070001257)
        ·
          refine ⟨99555866350857052500943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 132741155134476070001257 99555866350857052500943)
          ·
            refine ⟨149333799526285578751415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 99555866350857052500943 149333799526285578751415)
            ·
              refine ⟨224000699289428368127123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149333799526285578751415 224000699289428368127123)
              ·
                refine ⟨336001048934142552190685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224000699289428368127123 336001048934142552190685)
                ·
                  refine ⟨126000393350303457071507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336001048934142552190685 126000393350303457071507)
                  ·
                    refine ⟨189000590025455185607261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126000393350303457071507 189000590025455185607261)
                    ·
                      refine ⟨70875221259545694602723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 189000590025455185607261 70875221259545694602723)
                      ·
                        rfl

theorem cell23_138029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_138029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138029 prefixEnd_138029 := by exact prefixLift 138029
  have htrace : WordTrace (prefixWord ++ tailWord_138029) baseStart_138029 baseEnd_138029 := by
    simpa [prefixWord, tailWord_138029, baseEnd_138029] using wordTrace_append hprefix tailTrace_138029
  have hstable : (prefixWord ++ tailWord_138029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138029).length < 2 ^ (prefixWord ++ tailWord_138029).sum := by decide
  have hdescent : baseEnd_138029 < baseStart_138029 := by decide
  rcases family_descends (prefixWord ++ tailWord_138029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138035 : List Nat := [1, 1, 1, 2, 6, 3, 1, 1, 3, 2, 2]
def baseStart_138035 : Nat := 118140960795 + 138035 * 2 ^ 59
def prefixEnd_138035 : Nat := 4983230072969 + 3 ^ 40 * 138035 * 2
def baseEnd_138035 : Nat := 70878302143472671127695

theorem tailTrace_138035 : CollatzResearch.WordTrace tailWord_138035 prefixEnd_138035 70878302143472671127695 := by
  unfold tailWord_138035
  simp only [CollatzResearch.WordTrace]
  refine ⟨5034550054930244346247559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3356366703286829564165039 5034550054930244346247559)
  ·
    refine ⟨7551825082395366519371339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5034550054930244346247559 7551825082395366519371339)
    ·
      refine ⟨11327737623593049779057009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7551825082395366519371339 11327737623593049779057009)
      ·
        refine ⟨8495803217694787334292757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11327737623593049779057009 8495803217694787334292757)
        ·
          refine ⟨398240775829443156294973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8495803217694787334292757 398240775829443156294973)
          ·
            refine ⟨149340290936041183610615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 398240775829443156294973 149340290936041183610615)
            ·
              refine ⟨224010436404061775415923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149340290936041183610615 224010436404061775415923)
              ·
                refine ⟨336015654606092663123885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224010436404061775415923 336015654606092663123885)
                ·
                  refine ⟨126005870477284748671457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336015654606092663123885 126005870477284748671457)
                  ·
                    refine ⟨94504402857963561503593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126005870477284748671457 94504402857963561503593)
                    ·
                      refine ⟨70878302143472671127695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94504402857963561503593 70878302143472671127695)
                      ·
                        rfl

theorem cell23_138035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 1, 3, 2, 2].length) (baseStart_138035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138035 prefixEnd_138035 := by exact prefixLift 138035
  have htrace : WordTrace (prefixWord ++ tailWord_138035) baseStart_138035 baseEnd_138035 := by
    simpa [prefixWord, tailWord_138035, baseEnd_138035] using wordTrace_append hprefix tailTrace_138035
  have hstable : (prefixWord ++ tailWord_138035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138035).length < 2 ^ (prefixWord ++ tailWord_138035).sum := by decide
  have hdescent : baseEnd_138035 < baseStart_138035 := by decide
  rcases family_descends (prefixWord ++ tailWord_138035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138052 : List Nat := [2, 3, 4, 2, 1, 2, 1, 2, 1, 1, 4]
def baseStart_138052 : Nat := 118140960795 + 138052 * 2 ^ 59
def prefixEnd_138052 : Nat := 4983230072969 + 3 ^ 40 * 138052 * 2
def baseEnd_138052 : Nat := 70887031314599104615117

theorem tailTrace_138052 : CollatzResearch.WordTrace tailWord_138052 prefixEnd_138052 70887031314599104615117 := by
  unfold tailWord_138052
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517585047934328124808205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3356780063912437499744273 2517585047934328124808205)
  ·
    refine ⟨944094392975373046803077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2517585047934328124808205 944094392975373046803077)
    ·
      refine ⟨177017698682882446275577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 944094392975373046803077 177017698682882446275577)
      ·
        refine ⟨132763274012161834706683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 177017698682882446275577 132763274012161834706683)
        ·
          refine ⟨199144911018242752060025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 132763274012161834706683 199144911018242752060025)
          ·
            refine ⟨149358683263682064045019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 199144911018242752060025 149358683263682064045019)
            ·
              refine ⟨224038024895523096067529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 149358683263682064045019 224038024895523096067529)
              ·
                refine ⟨168028518671642322050647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224038024895523096067529 168028518671642322050647)
                ·
                  refine ⟨252042778007463483075971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168028518671642322050647 252042778007463483075971)
                  ·
                    refine ⟨378064167011195224613957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 252042778007463483075971 378064167011195224613957)
                    ·
                      refine ⟨70887031314599104615117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 378064167011195224613957 70887031314599104615117)
                      ·
                        rfl

theorem cell23_138052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_138052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138052 prefixEnd_138052 := by exact prefixLift 138052
  have htrace : WordTrace (prefixWord ++ tailWord_138052) baseStart_138052 baseEnd_138052 := by
    simpa [prefixWord, tailWord_138052, baseEnd_138052] using wordTrace_append hprefix tailTrace_138052
  have hstable : (prefixWord ++ tailWord_138052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138052).length < 2 ^ (prefixWord ++ tailWord_138052).sum := by decide
  have hdescent : baseEnd_138052 < baseStart_138052 := by decide
  rcases family_descends (prefixWord ++ tailWord_138052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138068 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 1, 3, 3]
def baseStart_138068 : Nat := 118140960795 + 138068 * 2 ^ 59
def prefixEnd_138068 : Nat := 4983230072969 + 3 ^ 40 * 138068 * 2
def baseEnd_138068 : Nat := 70895247005071042015043

theorem tailTrace_138068 : CollatzResearch.WordTrace tailWord_138068 prefixEnd_138068 70895247005071042015043 := by
  unfold tailWord_138068
  simp only [CollatzResearch.WordTrace]
  refine ⟨2517876831905345491099429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3357169109207127321465905 2517876831905345491099429)
  ·
    refine ⟨472101905982252279581143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2517876831905345491099429 472101905982252279581143)
    ·
      refine ⟨708152858973378419371715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472101905982252279581143 708152858973378419371715)
      ·
        refine ⟨1062229288460067629057573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708152858973378419371715 1062229288460067629057573)
        ·
          refine ⟨199167991586262680448295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1062229288460067629057573 199167991586262680448295)
          ·
            refine ⟨298751987379394020672443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199167991586262680448295 298751987379394020672443)
            ·
              refine ⟨448127981069091031008665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298751987379394020672443 448127981069091031008665)
              ·
                refine ⟨336095985801818273256499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448127981069091031008665 336095985801818273256499)
                ·
                  refine ⟨504143978702727409884749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 336095985801818273256499 504143978702727409884749)
                  ·
                    refine ⟨189053992013522778706781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504143978702727409884749 189053992013522778706781)
                    ·
                      refine ⟨70895247005071042015043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 189053992013522778706781 70895247005071042015043)
                      ·
                        rfl

theorem cell23_138068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 1, 3, 3].length) (baseStart_138068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138068 prefixEnd_138068 := by exact prefixLift 138068
  have htrace : WordTrace (prefixWord ++ tailWord_138068) baseStart_138068 baseEnd_138068 := by
    simpa [prefixWord, tailWord_138068, baseEnd_138068] using wordTrace_append hprefix tailTrace_138068
  have hstable : (prefixWord ++ tailWord_138068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138068).length < 2 ^ (prefixWord ++ tailWord_138068).sum := by decide
  have hdescent : baseEnd_138068 < baseStart_138068 := by decide
  rcases family_descends (prefixWord ++ tailWord_138068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138101 : List Nat := [1, 3, 4, 1, 1, 3, 1, 1, 2, 6]
def baseStart_138101 : Nat := 118140960795 + 138101 * 2 ^ 59
def prefixEnd_138101 : Nat := 4983230072969 + 3 ^ 40 * 138101 * 2
def baseEnd_138101 : Nat := 23637397288889804300797

theorem tailTrace_138101 : CollatzResearch.WordTrace tailWord_138101 prefixEnd_138101 23637397288889804300797 := by
  unfold tailWord_138101
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036957272691137618150157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3357971515127425078766771 5036957272691137618150157)
  ·
    refine ⟨1888858977259176606806309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5036957272691137618150157 1888858977259176606806309)
    ·
      refine ⟨354161058236095613776183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1888858977259176606806309 354161058236095613776183)
      ·
        refine ⟨531241587354143420664275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354161058236095613776183 531241587354143420664275)
        ·
          refine ⟨796862381031215130996413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 531241587354143420664275 796862381031215130996413)
          ·
            refine ⟨298823392886705674123655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 796862381031215130996413 298823392886705674123655)
            ·
              refine ⟨448235089330058511185483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 298823392886705674123655 448235089330058511185483)
              ·
                refine ⟨672352633995087766778225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448235089330058511185483 672352633995087766778225)
                ·
                  refine ⟨504264475496315825083669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 672352633995087766778225 504264475496315825083669)
                  ·
                    refine ⟨23637397288889804300797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 504264475496315825083669 23637397288889804300797)
                    ·
                      rfl

theorem cell23_138101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 1, 1, 2, 6].length) (baseStart_138101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138101 prefixEnd_138101 := by exact prefixLift 138101
  have htrace : WordTrace (prefixWord ++ tailWord_138101) baseStart_138101 baseEnd_138101 := by
    simpa [prefixWord, tailWord_138101, baseEnd_138101] using wordTrace_append hprefix tailTrace_138101
  have hstable : (prefixWord ++ tailWord_138101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138101).length < 2 ^ (prefixWord ++ tailWord_138101).sum := by decide
  have hdescent : baseEnd_138101 < baseStart_138101 := by decide
  rcases family_descends (prefixWord ++ tailWord_138101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138141 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 3]
def baseStart_138141 : Nat := 118140960795 + 138141 * 2 ^ 59
def prefixEnd_138141 : Nat := 4983230072969 + 3 ^ 40 * 138141 * 2
def baseEnd_138141 : Nat := 70932731092849256402207

theorem tailTrace_138141 : CollatzResearch.WordTrace tailWord_138141 prefixEnd_138141 70932731092849256402207 := by
  unfold tailWord_138141
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038416192546224449606277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3358944128364149633070851 5038416192546224449606277)
  ·
    refine ⟨944703036102417084301177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5038416192546224449606277 944703036102417084301177)
    ·
      refine ⟨708527277076812813225883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 944703036102417084301177 708527277076812813225883)
      ·
        refine ⟨1062790915615219219838825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708527277076812813225883 1062790915615219219838825)
        ·
          refine ⟨797093186711414414879119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062790915615219219838825 797093186711414414879119)
          ·
            refine ⟨1195639780067121622318679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797093186711414414879119 1195639780067121622318679)
            ·
              refine ⟨1793459670100682433478019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195639780067121622318679 1793459670100682433478019)
              ·
                refine ⟨2690189505151023650217029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793459670100682433478019 2690189505151023650217029)
                ·
                  refine ⟨504410532215816934415693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2690189505151023650217029 504410532215816934415693)
                  ·
                    refine ⟨189153949580931350405885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 504410532215816934415693 189153949580931350405885)
                    ·
                      refine ⟨70932731092849256402207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 189153949580931350405885 70932731092849256402207)
                      ·
                        rfl

theorem cell23_138141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_138141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138141 prefixEnd_138141 := by exact prefixLift 138141
  have htrace : WordTrace (prefixWord ++ tailWord_138141) baseStart_138141 baseEnd_138141 := by
    simpa [prefixWord, tailWord_138141, baseEnd_138141] using wordTrace_append hprefix tailTrace_138141
  have hstable : (prefixWord ++ tailWord_138141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138141).length < 2 ^ (prefixWord ++ tailWord_138141).sum := by decide
  have hdescent : baseEnd_138141 < baseStart_138141 := by decide
  rcases family_descends (prefixWord ++ tailWord_138141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138282 : List Nat := [3, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3]
def baseStart_138282 : Nat := 118140960795 + 138282 * 2 ^ 59
def prefixEnd_138282 : Nat := 4983230072969 + 3 ^ 40 * 138282 * 2
def baseEnd_138282 : Nat := 71005131865133204739059

theorem tailTrace_138282 : CollatzResearch.WordTrace tailWord_138282 prefixEnd_138282 71005131865133204739059 := by
  unfold tailWord_138282
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260889721258851382622275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3362372590023603686992733 1260889721258851382622275)
  ·
    refine ⟨1891334581888277073933413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260889721258851382622275 1891334581888277073933413)
    ·
      refine ⟨354625234104051951362515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1891334581888277073933413 354625234104051951362515)
      ·
        refine ⟨531937851156077927043773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354625234104051951362515 531937851156077927043773)
        ·
          refine ⟨199476694183529222641415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 531937851156077927043773 199476694183529222641415)
          ·
            refine ⟨299215041275293833962123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199476694183529222641415 299215041275293833962123)
            ·
              refine ⟨448822561912940750943185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299215041275293833962123 448822561912940750943185)
              ·
                refine ⟨336616921434705563207389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 448822561912940750943185 336616921434705563207389)
                ·
                  refine ⟨126231345538014586202771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336616921434705563207389 126231345538014586202771)
                  ·
                    refine ⟨189347018307021879304157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 126231345538014586202771 189347018307021879304157)
                    ·
                      refine ⟨71005131865133204739059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 189347018307021879304157 71005131865133204739059)
                      ·
                        rfl

theorem cell23_138282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_138282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138282 prefixEnd_138282 := by exact prefixLift 138282
  have htrace : WordTrace (prefixWord ++ tailWord_138282) baseStart_138282 baseEnd_138282 := by
    simpa [prefixWord, tailWord_138282, baseEnd_138282] using wordTrace_append hprefix tailTrace_138282
  have hstable : (prefixWord ++ tailWord_138282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138282).length < 2 ^ (prefixWord ++ tailWord_138282).sum := by decide
  have hdescent : baseEnd_138282 < baseStart_138282 := by decide
  rcases family_descends (prefixWord ++ tailWord_138282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138288 : List Nat := [2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4]
def baseStart_138288 : Nat := 118140960795 + 138288 * 2 ^ 59
def prefixEnd_138288 : Nat := 4983230072969 + 3 ^ 40 * 138288 * 2
def baseEnd_138288 : Nat := 71008212749060181264031

theorem tailTrace_138288 : CollatzResearch.WordTrace tailWord_138288 prefixEnd_138288 71008212749060181264031 := by
  unfold tailWord_138288
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521888861506834277603759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3362518482009112370138345 2521888861506834277603759)
  ·
    refine ⟨3782833292260251416405639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2521888861506834277603759 3782833292260251416405639)
    ·
      refine ⟨5674249938390377124608459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3782833292260251416405639 5674249938390377124608459)
      ·
        refine ⟨8511374907585565686912689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5674249938390377124608459 8511374907585565686912689)
        ·
          refine ⟨6383531180689174265184517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8511374907585565686912689 6383531180689174265184517)
          ·
            refine ⟨1196912096379220174722097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6383531180689174265184517 1196912096379220174722097)
            ·
              refine ⟨897684072284415131041573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196912096379220174722097 897684072284415131041573)
              ·
                refine ⟨168315763553327837070295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 897684072284415131041573 168315763553327837070295)
                ·
                  refine ⟨252473645329991755605443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168315763553327837070295 252473645329991755605443)
                  ·
                    refine ⟨378710467994987633408165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 252473645329991755605443 378710467994987633408165)
                    ·
                      refine ⟨71008212749060181264031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 378710467994987633408165 71008212749060181264031)
                      ·
                        rfl

theorem cell23_138288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 4, 1, 1, 4].length) (baseStart_138288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138288 prefixEnd_138288 := by exact prefixLift 138288
  have htrace : WordTrace (prefixWord ++ tailWord_138288) baseStart_138288 baseEnd_138288 := by
    simpa [prefixWord, tailWord_138288, baseEnd_138288] using wordTrace_append hprefix tailTrace_138288
  have hstable : (prefixWord ++ tailWord_138288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138288).length < 2 ^ (prefixWord ++ tailWord_138288).sum := by decide
  have hdescent : baseEnd_138288 < baseStart_138288 := by decide
  rcases family_descends (prefixWord ++ tailWord_138288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138292 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 1, 5, 2]
def baseStart_138292 : Nat := 118140960795 + 138292 * 2 ^ 59
def prefixEnd_138292 : Nat := 4983230072969 + 3 ^ 40 * 138292 * 2
def baseEnd_138292 : Nat := 71010266671678165614013

theorem tailTrace_138292 : CollatzResearch.WordTrace tailWord_138292 prefixEnd_138292 71010266671678165614013 := by
  unfold tailWord_138292
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521961807499588619176565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3362615743332784825568753 2521961807499588619176565)
  ·
    refine ⟨236433919453086433047803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2521961807499588619176565 236433919453086433047803)
    ·
      refine ⟨354650879179629649571705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 236433919453086433047803 354650879179629649571705)
      ·
        refine ⟨265988159384722237178779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 354650879179629649571705 265988159384722237178779)
        ·
          refine ⟨398982239077083355768169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 265988159384722237178779 398982239077083355768169)
          ·
            refine ⟨299236679307812516826127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 398982239077083355768169 299236679307812516826127)
            ·
              refine ⟨448855018961718775239191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299236679307812516826127 448855018961718775239191)
              ·
                refine ⟨673282528442578162858787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 448855018961718775239191 673282528442578162858787)
                ·
                  refine ⟨1009923792663867244288181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673282528442578162858787 1009923792663867244288181)
                  ·
                    refine ⟨94680355562237554152017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1009923792663867244288181 94680355562237554152017)
                    ·
                      refine ⟨71010266671678165614013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94680355562237554152017 71010266671678165614013)
                      ·
                        rfl

theorem cell23_138292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_138292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138292 prefixEnd_138292 := by exact prefixLift 138292
  have htrace : WordTrace (prefixWord ++ tailWord_138292) baseStart_138292 baseEnd_138292 := by
    simpa [prefixWord, tailWord_138292, baseEnd_138292] using wordTrace_append hprefix tailTrace_138292
  have hstable : (prefixWord ++ tailWord_138292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138292).length < 2 ^ (prefixWord ++ tailWord_138292).sum := by decide
  have hdescent : baseEnd_138292 < baseStart_138292 := by decide
  rcases family_descends (prefixWord ++ tailWord_138292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138302 : List Nat := [4, 2, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_138302 : Nat := 118140960795 + 138302 * 2 ^ 59
def prefixEnd_138302 : Nat := 4983230072969 + 3 ^ 40 * 138302 * 2
def baseEnd_138302 : Nat := 23671800492741042162989

theorem tailTrace_138302 : CollatzResearch.WordTrace tailWord_138302 prefixEnd_138302 23671800492741042162989 := by
  unfold tailWord_138302
  simp only [CollatzResearch.WordTrace]
  refine ⟨630536043120368618277145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3362858896641965964144773 630536043120368618277145)
  ·
    refine ⟨472902032340276463707859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 630536043120368618277145 472902032340276463707859)
    ·
      refine ⟨709353048510414695561789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 472902032340276463707859 709353048510414695561789)
      ·
        refine ⟨266007393191405510835671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 709353048510414695561789 266007393191405510835671)
        ·
          refine ⟨399011089787108266253507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266007393191405510835671 399011089787108266253507)
          ·
            refine ⟨598516634680662399380261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399011089787108266253507 598516634680662399380261)
            ·
              refine ⟨112221869002624199883799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 598516634680662399380261 112221869002624199883799)
              ·
                refine ⟨168332803503936299825699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112221869002624199883799 168332803503936299825699)
                ·
                  refine ⟨252499205255904449738549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168332803503936299825699 252499205255904449738549)
                  ·
                    refine ⟨23671800492741042162989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 252499205255904449738549 23671800492741042162989)
                    ·
                      rfl

theorem cell23_138302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_138302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138302 prefixEnd_138302 := by exact prefixLift 138302
  have htrace : WordTrace (prefixWord ++ tailWord_138302) baseStart_138302 baseEnd_138302 := by
    simpa [prefixWord, tailWord_138302, baseEnd_138302] using wordTrace_append hprefix tailTrace_138302
  have hstable : (prefixWord ++ tailWord_138302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138302).length < 2 ^ (prefixWord ++ tailWord_138302).sum := by decide
  have hdescent : baseEnd_138302 < baseStart_138302 := by decide
  rcases family_descends (prefixWord ++ tailWord_138302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138311 : List Nat := [1, 1, 4, 1, 3, 3, 10]
def baseStart_138311 : Nat := 118140960795 + 138311 * 2 ^ 59
def prefixEnd_138311 : Nat := 4983230072969 + 3 ^ 40 * 138311 * 2
def baseEnd_138311 : Nat := 876790404989056682425

theorem tailTrace_138311 : CollatzResearch.WordTrace tailWord_138311 prefixEnd_138311 876790404989056682425 := by
  unfold tailWord_138311
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044616601930343483294787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3363077734620228988863191 5044616601930343483294787)
  ·
    refine ⟨7566924902895515224942181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5044616601930343483294787 7566924902895515224942181)
    ·
      refine ⟨1418798419292909104676659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7566924902895515224942181 1418798419292909104676659)
      ·
        refine ⟨2128197628939363657014989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418798419292909104676659 2128197628939363657014989)
        ·
          refine ⟨798074110852261371380621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2128197628939363657014989 798074110852261371380621)
          ·
            refine ⟨299277791569598014267733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 798074110852261371380621 299277791569598014267733)
            ·
              refine ⟨876790404989056682425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 299277791569598014267733 876790404989056682425)
              ·
                rfl

theorem cell23_138311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 10].length) (baseStart_138311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138311 prefixEnd_138311 := by exact prefixLift 138311
  have htrace : WordTrace (prefixWord ++ tailWord_138311) baseStart_138311 baseEnd_138311 := by
    simpa [prefixWord, tailWord_138311, baseEnd_138311] using wordTrace_append hprefix tailTrace_138311
  have hstable : (prefixWord ++ tailWord_138311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138311).length < 2 ^ (prefixWord ++ tailWord_138311).sum := by decide
  have hdescent : baseEnd_138311 < baseStart_138311 := by decide
  rcases family_descends (prefixWord ++ tailWord_138311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138322 : List Nat := [3, 2, 2, 1, 3, 1, 1, 3, 3, 2, 2]
def baseStart_138322 : Nat := 118140960795 + 138322 * 2 ^ 59
def prefixEnd_138322 : Nat := 4983230072969 + 3 ^ 40 * 138322 * 2
def baseEnd_138322 : Nat := 71025671091313048238875

theorem tailTrace_138322 : CollatzResearch.WordTrace tailWord_138322 prefixEnd_138322 71025671091313048238875 := by
  unfold tailWord_138322
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261254451222623090486305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3363345203260328241296813 1261254451222623090486305)
  ·
    refine ⟨945940838416967317864729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1261254451222623090486305 945940838416967317864729)
    ·
      refine ⟨709455628812725488398547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945940838416967317864729 709455628812725488398547)
      ·
        refine ⟨1064183443219088232597821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 709455628812725488398547 1064183443219088232597821)
        ·
          refine ⟨399068791207158087224183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1064183443219088232597821 399068791207158087224183)
          ·
            refine ⟨598603186810737130836275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399068791207158087224183 598603186810737130836275)
            ·
              refine ⟨897904780216105696254413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 598603186810737130836275 897904780216105696254413)
              ·
                refine ⟨336714292581039636095405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 897904780216105696254413 336714292581039636095405)
                ·
                  refine ⟨126267859717889863535777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 336714292581039636095405 126267859717889863535777)
                  ·
                    refine ⟨94700894788417397651833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126267859717889863535777 94700894788417397651833)
                    ·
                      refine ⟨71025671091313048238875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94700894788417397651833 71025671091313048238875)
                      ·
                        rfl

theorem cell23_138322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 3, 3, 2, 2].length) (baseStart_138322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138322 prefixEnd_138322 := by exact prefixLift 138322
  have htrace : WordTrace (prefixWord ++ tailWord_138322) baseStart_138322 baseEnd_138322 := by
    simpa [prefixWord, tailWord_138322, baseEnd_138322] using wordTrace_append hprefix tailTrace_138322
  have hstable : (prefixWord ++ tailWord_138322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138322).length < 2 ^ (prefixWord ++ tailWord_138322).sum := by decide
  have hdescent : baseEnd_138322 < baseStart_138322 := by decide
  rcases family_descends (prefixWord ++ tailWord_138322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138332 : List Nat := [2, 2, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_138332 : Nat := 118140960795 + 138332 * 2 ^ 59
def prefixEnd_138332 : Nat := 4983230072969 + 3 ^ 40 * 138332 * 2
def baseEnd_138332 : Nat := 23676935299286003037943

theorem tailTrace_138332 : CollatzResearch.WordTrace tailWord_138332 prefixEnd_138332 23676935299286003037943 := by
  unfold tailWord_138332
  simp only [CollatzResearch.WordTrace]
  refine ⟨2522691267427132034904625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3363588356569509379872833 2522691267427132034904625)
  ·
    refine ⟨1892018450570349026178469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2522691267427132034904625 1892018450570349026178469)
    ·
      refine ⟨354753459481940442408463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1892018450570349026178469 354753459481940442408463)
      ·
        refine ⟨532130189222910663612695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 354753459481940442408463 532130189222910663612695)
        ·
          refine ⟨798195283834365995419043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532130189222910663612695 798195283834365995419043)
          ·
            refine ⟨1197292925751548993128565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798195283834365995419043 1197292925751548993128565)
            ·
              refine ⟨112246211789207718105803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1197292925751548993128565 112246211789207718105803)
              ·
                refine ⟨168369317683811577158705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 112246211789207718105803 168369317683811577158705)
                ·
                  refine ⟨126276988262858682869029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 168369317683811577158705 126276988262858682869029)
                  ·
                    refine ⟨23676935299286003037943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126276988262858682869029 23676935299286003037943)
                    ·
                      rfl

theorem cell23_138332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_138332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138332 prefixEnd_138332 := by exact prefixLift 138332
  have htrace : WordTrace (prefixWord ++ tailWord_138332) baseStart_138332 baseEnd_138332 := by
    simpa [prefixWord, tailWord_138332, baseEnd_138332] using wordTrace_append hprefix tailTrace_138332
  have hstable : (prefixWord ++ tailWord_138332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138332).length < 2 ^ (prefixWord ++ tailWord_138332).sum := by decide
  have hdescent : baseEnd_138332 < baseStart_138332 := by decide
  rcases family_descends (prefixWord ++ tailWord_138332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138351 : List Nat := [1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 5]
def baseStart_138351 : Nat := 118140960795 + 138351 * 2 ^ 59
def prefixEnd_138351 : Nat := 4983230072969 + 3 ^ 40 * 138351 * 2
def baseEnd_138351 : Nat := 71040562030293434776241

theorem tailTrace_138351 : CollatzResearch.WordTrace tailWord_138351 prefixEnd_138351 71040562030293434776241 := by
  unfold tailWord_138351
  simp only [CollatzResearch.WordTrace]
  refine ⟨5046075521785430314750907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3364050347856953543167271 5046075521785430314750907)
  ·
    refine ⟨7569113282678145472126361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5046075521785430314750907 7569113282678145472126361)
    ·
      refine ⟨5676834962008609104094771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7569113282678145472126361 5676834962008609104094771)
      ·
        refine ⟨8515252443012913656142157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5676834962008609104094771 8515252443012913656142157)
        ·
          refine ⟨3193219666129842621053309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8515252443012913656142157 3193219666129842621053309)
          ·
            refine ⟨1197457374798690982894991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3193219666129842621053309 1197457374798690982894991)
            ·
              refine ⟨1796186062198036474342487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197457374798690982894991 1796186062198036474342487)
              ·
                refine ⟨2694279093297054711513731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1796186062198036474342487 2694279093297054711513731)
                ·
                  refine ⟨4041418639945582067270597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2694279093297054711513731 4041418639945582067270597)
                  ·
                    refine ⟨757765994989796637613237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4041418639945582067270597 757765994989796637613237)
                    ·
                      refine ⟨71040562030293434776241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 757765994989796637613237 71040562030293434776241)
                      ·
                        rfl

theorem cell23_138351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 5].length) (baseStart_138351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138351 prefixEnd_138351 := by exact prefixLift 138351
  have htrace : WordTrace (prefixWord ++ tailWord_138351) baseStart_138351 baseEnd_138351 := by
    simpa [prefixWord, tailWord_138351, baseEnd_138351] using wordTrace_append hprefix tailTrace_138351
  have hstable : (prefixWord ++ tailWord_138351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138351).length < 2 ^ (prefixWord ++ tailWord_138351).sum := by decide
  have hdescent : baseEnd_138351 < baseStart_138351 := by decide
  rcases family_descends (prefixWord ++ tailWord_138351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138378 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4]
def baseStart_138378 : Nat := 118140960795 + 138378 * 2 ^ 59
def prefixEnd_138378 : Nat := 4983230072969 + 3 ^ 40 * 138378 * 2
def baseEnd_138378 : Nat := 71054426007964829138617

theorem tailTrace_138378 : CollatzResearch.WordTrace tailWord_138378 prefixEnd_138378 71054426007964829138617 := by
  unfold tailWord_138378
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261765073171903481495947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3364706861791742617322525 1261765073171903481495947)
  ·
    refine ⟨1892647609757855222243921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1261765073171903481495947 1892647609757855222243921)
    ·
      refine ⟨1419485707318391416682941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1892647609757855222243921 1419485707318391416682941)
      ·
        refine ⟨532307140244396781256103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1419485707318391416682941 532307140244396781256103)
        ·
          refine ⟨798460710366595171884155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 532307140244396781256103 798460710366595171884155)
          ·
            refine ⟨1197691065549892757826233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 798460710366595171884155 1197691065549892757826233)
            ·
              refine ⟨898268299162419568369675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1197691065549892757826233 898268299162419568369675)
              ·
                refine ⟨1347402448743629352554513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 898268299162419568369675 1347402448743629352554513)
                ·
                  refine ⟨1010551836557722014415885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1347402448743629352554513 1010551836557722014415885)
                  ·
                    refine ⟨378956938709145755405957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1010551836557722014415885 378956938709145755405957)
                    ·
                      refine ⟨71054426007964829138617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 378956938709145755405957 71054426007964829138617)
                      ·
                        rfl

theorem cell23_138378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_138378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138378 prefixEnd_138378 := by exact prefixLift 138378
  have htrace : WordTrace (prefixWord ++ tailWord_138378) baseStart_138378 baseEnd_138378 := by
    simpa [prefixWord, tailWord_138378, baseEnd_138378] using wordTrace_append hprefix tailTrace_138378
  have hstable : (prefixWord ++ tailWord_138378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138378).length < 2 ^ (prefixWord ++ tailWord_138378).sum := by decide
  have hdescent : baseEnd_138378 < baseStart_138378 := by decide
  rcases family_descends (prefixWord ++ tailWord_138378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138395 : List Nat := [1, 1, 1, 1, 1, 1, 2, 3, 8, 2, 2]
def baseStart_138395 : Nat := 118140960795 + 138395 * 2 ^ 59
def prefixEnd_138395 : Nat := 4983230072969 + 3 ^ 40 * 138395 * 2
def baseEnd_138395 : Nat := 71063155179091262626039

theorem tailTrace_138395 : CollatzResearch.WordTrace tailWord_138395 prefixEnd_138395 71063155179091262626039 := by
  unfold tailWord_138395
  simp only [CollatzResearch.WordTrace]
  refine ⟨5047680333626025829352639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3365120222417350552901759 5047680333626025829352639)
  ·
    refine ⟨7571520500439038744028959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5047680333626025829352639 7571520500439038744028959)
    ·
      refine ⟨11357280750658558116043439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7571520500439038744028959 11357280750658558116043439)
      ·
        refine ⟨17035921125987837174065159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11357280750658558116043439 17035921125987837174065159)
        ·
          refine ⟨25553881688981755761097739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17035921125987837174065159 25553881688981755761097739)
          ·
            refine ⟨38330822533472633641646609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25553881688981755761097739 38330822533472633641646609)
            ·
              refine ⟨28748116900104475231234957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38330822533472633641646609 28748116900104475231234957)
              ·
                refine ⟨10780543837539178211713109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28748116900104475231234957 10780543837539178211713109)
                ·
                  refine ⟨126334498096162244668513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10780543837539178211713109 126334498096162244668513)
                  ·
                    refine ⟨94750873572121683501385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126334498096162244668513 94750873572121683501385)
                    ·
                      refine ⟨71063155179091262626039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94750873572121683501385 71063155179091262626039)
                      ·
                        rfl

theorem cell23_138395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 3, 8, 2, 2].length) (baseStart_138395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138395 prefixEnd_138395 := by exact prefixLift 138395
  have htrace : WordTrace (prefixWord ++ tailWord_138395) baseStart_138395 baseEnd_138395 := by
    simpa [prefixWord, tailWord_138395, baseEnd_138395] using wordTrace_append hprefix tailTrace_138395
  have hstable : (prefixWord ++ tailWord_138395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138395).length < 2 ^ (prefixWord ++ tailWord_138395).sum := by decide
  have hdescent : baseEnd_138395 < baseStart_138395 := by decide
  rcases family_descends (prefixWord ++ tailWord_138395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138452 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 7]
def baseStart_138452 : Nat := 118140960795 + 138452 * 2 ^ 59
def prefixEnd_138452 : Nat := 4983230072969 + 3 ^ 40 * 138452 * 2
def baseEnd_138452 : Nat := 7899158175155282179253

theorem tailTrace_138452 : CollatzResearch.WordTrace tailWord_138452 prefixEnd_138452 7899158175155282179253 := by
  unfold tailWord_138452
  simp only [CollatzResearch.WordTrace]
  refine ⟨2524879647209762282088805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3366506196279683042785073 2524879647209762282088805)
  ·
    refine ⟨473414933851830427891651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2524879647209762282088805 473414933851830427891651)
    ·
      refine ⟨710122400777745641837477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 473414933851830427891651 710122400777745641837477)
      ·
        refine ⟨133147950145827307844527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 710122400777745641837477 133147950145827307844527)
        ·
          refine ⟨199721925218740961766791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 133147950145827307844527 199721925218740961766791)
          ·
            refine ⟨299582887828111442650187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 199721925218740961766791 299582887828111442650187)
            ·
              refine ⟨449374331742167163975281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 299582887828111442650187 449374331742167163975281)
              ·
                refine ⟨337030748806625372981461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 449374331742167163975281 337030748806625372981461)
                ·
                  refine ⟨7899158175155282179253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 337030748806625372981461 7899158175155282179253)
                  ·
                    rfl

theorem cell23_138452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_138452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138452 prefixEnd_138452 := by exact prefixLift 138452
  have htrace : WordTrace (prefixWord ++ tailWord_138452) baseStart_138452 baseEnd_138452 := by
    simpa [prefixWord, tailWord_138452, baseEnd_138452] using wordTrace_append hprefix tailTrace_138452
  have hstable : (prefixWord ++ tailWord_138452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138452).length < 2 ^ (prefixWord ++ tailWord_138452).sum := by decide
  have hdescent : baseEnd_138452 < baseStart_138452 := by decide
  rcases family_descends (prefixWord ++ tailWord_138452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138465 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 2, 5]
def baseStart_138465 : Nat := 118140960795 + 138465 * 2 ^ 59
def prefixEnd_138465 : Nat := 4983230072969 + 3 ^ 40 * 138465 * 2
def baseEnd_138465 : Nat := 23699699608301996250239

theorem tailTrace_138465 : CollatzResearch.WordTrace tailWord_138465 prefixEnd_138465 23699699608301996250239 := by
  unfold tailWord_138465
  simp only [CollatzResearch.WordTrace]
  refine ⟨5050233443372427784400849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3366822295581618522933899 5050233443372427784400849)
  ·
    refine ⟨3787675082529320838300637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5050233443372427784400849 3787675082529320838300637)
    ·
      refine ⟨1420378155948495314362739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3787675082529320838300637 1420378155948495314362739)
      ·
        refine ⟨2130567233922742971544109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1420378155948495314362739 2130567233922742971544109)
        ·
          refine ⟨798962712721028614329041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2130567233922742971544109 798962712721028614329041)
          ·
            refine ⟨599222034540771460746781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 798962712721028614329041 599222034540771460746781)
            ·
              refine ⟨224708262952789297780043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 599222034540771460746781 224708262952789297780043)
              ·
                refine ⟨337062394429183946670065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 224708262952789297780043 337062394429183946670065)
                ·
                  refine ⟨252796795821887960002549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 337062394429183946670065 252796795821887960002549)
                  ·
                    refine ⟨23699699608301996250239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 252796795821887960002549 23699699608301996250239)
                    ·
                      rfl

theorem cell23_138465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 2, 5].length) (baseStart_138465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138465 prefixEnd_138465 := by exact prefixLift 138465
  have htrace : WordTrace (prefixWord ++ tailWord_138465) baseStart_138465 baseEnd_138465 := by
    simpa [prefixWord, tailWord_138465, baseEnd_138465] using wordTrace_append hprefix tailTrace_138465
  have hstable : (prefixWord ++ tailWord_138465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138465).length < 2 ^ (prefixWord ++ tailWord_138465).sum := by decide
  have hdescent : baseEnd_138465 < baseStart_138465 := by decide
  rcases family_descends (prefixWord ++ tailWord_138465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138495 : List Nat := [1, 1, 2, 2, 1, 5, 1, 3, 3, 4]
def baseStart_138495 : Nat := 118140960795 + 138495 * 2 ^ 59
def prefixEnd_138495 : Nat := 4983230072969 + 3 ^ 40 * 138495 * 2
def baseEnd_138495 : Nat := 23704834414846957125193

theorem tailTrace_138495 : CollatzResearch.WordTrace tailWord_138495 prefixEnd_138495 23704834414846957125193 := by
  unfold tailWord_138495
  simp only [CollatzResearch.WordTrace]
  refine ⟨5051327633263742907992939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3367551755509161938661959 5051327633263742907992939)
  ·
    refine ⟨7576991449895614361989409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5051327633263742907992939 7576991449895614361989409)
    ·
      refine ⟨5682743587421710771492057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7576991449895614361989409 5682743587421710771492057)
      ·
        refine ⟨4262057690566283078619043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5682743587421710771492057 4262057690566283078619043)
        ·
          refine ⟨6393086535849424617928565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4262057690566283078619043 6393086535849424617928565)
          ·
            refine ⟨599351862735883557930803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6393086535849424617928565 599351862735883557930803)
            ·
              refine ⟨899027794103825336896205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599351862735883557930803 899027794103825336896205)
              ·
                refine ⟨337135422788934501336077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 899027794103825336896205 337135422788934501336077)
                ·
                  refine ⟨126425783545850438001029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 337135422788934501336077 126425783545850438001029)
                  ·
                    refine ⟨23704834414846957125193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126425783545850438001029 23704834414846957125193)
                    ·
                      rfl

theorem cell23_138495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 3, 3, 4].length) (baseStart_138495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138495 prefixEnd_138495 := by exact prefixLift 138495
  have htrace : WordTrace (prefixWord ++ tailWord_138495) baseStart_138495 baseEnd_138495 := by
    simpa [prefixWord, tailWord_138495, baseEnd_138495] using wordTrace_append hprefix tailTrace_138495
  have hstable : (prefixWord ++ tailWord_138495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138495).length < 2 ^ (prefixWord ++ tailWord_138495).sum := by decide
  have hdescent : baseEnd_138495 < baseStart_138495 := by decide
  rcases family_descends (prefixWord ++ tailWord_138495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138525 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 8]
def baseStart_138525 : Nat := 118140960795 + 138525 * 2 ^ 59
def prefixEnd_138525 : Nat := 4983230072969 + 3 ^ 40 * 138525 * 2
def baseEnd_138525 : Nat := 7903323073797306000049

theorem tailTrace_138525 : CollatzResearch.WordTrace tailWord_138525 prefixEnd_138525 7903323073797306000049 := by
  unfold tailWord_138525
  simp only [CollatzResearch.WordTrace]
  refine ⟨5052421823155058031585029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3368281215436705354390019 5052421823155058031585029)
  ·
    refine ⟨947329091841573380922193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5052421823155058031585029 947329091841573380922193)
    ·
      refine ⟨710496818881180035691645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 947329091841573380922193 710496818881180035691645)
      ·
        refine ⟨266436307080442513384367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 710496818881180035691645 266436307080442513384367)
        ·
          refine ⟨399654460620663770076551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 266436307080442513384367 399654460620663770076551)
          ·
            refine ⟨599481690930995655114827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 399654460620663770076551 599481690930995655114827)
            ·
              refine ⟨899222536396493482672241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 599481690930995655114827 899222536396493482672241)
              ·
                refine ⟨674416902297370112004181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 899222536396493482672241 674416902297370112004181)
                ·
                  refine ⟨7903323073797306000049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 674416902297370112004181 7903323073797306000049)
                  ·
                    rfl

theorem cell23_138525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 8].length) (baseStart_138525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138525 prefixEnd_138525 := by exact prefixLift 138525
  have htrace : WordTrace (prefixWord ++ tailWord_138525) baseStart_138525 baseEnd_138525 := by
    simpa [prefixWord, tailWord_138525, baseEnd_138525] using wordTrace_append hprefix tailTrace_138525
  have hstable : (prefixWord ++ tailWord_138525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138525).length < 2 ^ (prefixWord ++ tailWord_138525).sum := by decide
  have hdescent : baseEnd_138525 < baseStart_138525 := by decide
  rcases family_descends (prefixWord ++ tailWord_138525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138546 : List Nat := [3, 2, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_138546 : Nat := 118140960795 + 138546 * 2 ^ 59
def prefixEnd_138546 : Nat := 4983230072969 + 3 ^ 40 * 138546 * 2
def baseEnd_138546 : Nat := 23713563585973390612615

theorem tailTrace_138546 : CollatzResearch.WordTrace tailWord_138546 prefixEnd_138546 23713563585973390612615 := by
  unfold tailWord_138546
  simp only [CollatzResearch.WordTrace]
  refine ⟨1263296939019744654524873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3368791837385985745399661 1263296939019744654524873)
  ·
    refine ⟨947472704264808490893655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1263296939019744654524873 947472704264808490893655)
    ·
      refine ⟨1421209056397212736340483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 947472704264808490893655 1421209056397212736340483)
      ·
        refine ⟨2131813584595819104510725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1421209056397212736340483 2131813584595819104510725)
        ·
          refine ⟨399715047111716082095761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2131813584595819104510725 399715047111716082095761)
          ·
            refine ⟨299786285333787061571821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 399715047111716082095761 299786285333787061571821)
            ·
              refine ⟨112419857000170148089433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299786285333787061571821 112419857000170148089433)
              ·
                refine ⟨84314892750127611067075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 112419857000170148089433 84314892750127611067075)
                ·
                  refine ⟨126472339125191416600613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84314892750127611067075 126472339125191416600613)
                  ·
                    refine ⟨23713563585973390612615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126472339125191416600613 23713563585973390612615)
                    ·
                      rfl

theorem cell23_138546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_138546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138546 prefixEnd_138546 := by exact prefixLift 138546
  have htrace : WordTrace (prefixWord ++ tailWord_138546) baseStart_138546 baseEnd_138546 := by
    simpa [prefixWord, tailWord_138546, baseEnd_138546] using wordTrace_append hprefix tailTrace_138546
  have hstable : (prefixWord ++ tailWord_138546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138546).length < 2 ^ (prefixWord ++ tailWord_138546).sum := by decide
  have hdescent : baseEnd_138546 < baseStart_138546 := by decide
  rcases family_descends (prefixWord ++ tailWord_138546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138572 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_138572 : Nat := 118140960795 + 138572 * 2 ^ 59
def prefixEnd_138572 : Nat := 4983230072969 + 3 ^ 40 * 138572 * 2
def baseEnd_138572 : Nat := 23718013751645690037575

theorem tailTrace_138572 : CollatzResearch.WordTrace tailWord_138572 prefixEnd_138572 23718013751645690037575 := by
  unfold tailWord_138572
  simp only [CollatzResearch.WordTrace]
  refine ⟨2527068026992392529272985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3369424035989856705697313 2527068026992392529272985)
  ·
    refine ⟨1895301020244294396954739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2527068026992392529272985 1895301020244294396954739)
    ·
      refine ⟨2842951530366441595432109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1895301020244294396954739 2842951530366441595432109)
      ·
        refine ⟨1066106823887415598287041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2842951530366441595432109 1066106823887415598287041)
        ·
          refine ⟨799580117915561698715281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1066106823887415598287041 799580117915561698715281)
          ·
            refine ⟨599685088436671274036461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 799580117915561698715281 599685088436671274036461)
            ·
              refine ⟨224881908163751727763673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 599685088436671274036461 224881908163751727763673)
              ·
                refine ⟨168661431122813795822755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 224881908163751727763673 168661431122813795822755)
                ·
                  refine ⟨252992146684220693734133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 168661431122813795822755 252992146684220693734133)
                  ·
                    refine ⟨23718013751645690037575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 252992146684220693734133 23718013751645690037575)
                    ·
                      rfl

theorem cell23_138572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_138572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138572 prefixEnd_138572 := by exact prefixLift 138572
  have htrace : WordTrace (prefixWord ++ tailWord_138572) baseStart_138572 baseEnd_138572 := by
    simpa [prefixWord, tailWord_138572, baseEnd_138572] using wordTrace_append hprefix tailTrace_138572
  have hstable : (prefixWord ++ tailWord_138572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138572).length < 2 ^ (prefixWord ++ tailWord_138572).sum := by decide
  have hdescent : baseEnd_138572 < baseStart_138572 := by decide
  rcases family_descends (prefixWord ++ tailWord_138572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138585 : List Nat := [1, 2, 1, 2, 2, 2, 2, 1, 6, 4]
def baseStart_138585 : Nat := 118140960795 + 138585 * 2 ^ 59
def prefixEnd_138585 : Nat := 4983230072969 + 3 ^ 40 * 138585 * 2
def baseEnd_138585 : Nat := 23720238834481839750055

theorem tailTrace_138585 : CollatzResearch.WordTrace tailWord_138585 prefixEnd_138585 23720238834481839750055 := by
  unfold tailWord_138585
  simp only [CollatzResearch.WordTrace]
  refine ⟨5054610202937688278769209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3369740135291792185846139 5054610202937688278769209)
  ·
    refine ⟨3790957652203266209076907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5054610202937688278769209 3790957652203266209076907)
    ·
      refine ⟨5686436478304899313615361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3790957652203266209076907 5686436478304899313615361)
      ·
        refine ⟨4264827358728674485211521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5686436478304899313615361 4264827358728674485211521)
        ·
          refine ⟨3198620519046505863908641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4264827358728674485211521 3198620519046505863908641)
          ·
            refine ⟨2398965389284879397931481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3198620519046505863908641 2398965389284879397931481)
            ·
              refine ⟨1799224041963659548448611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2398965389284879397931481 1799224041963659548448611)
              ·
                refine ⟨2698836062945489322672917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1799224041963659548448611 2698836062945489322672917)
                ·
                  refine ⟨126507940450569812000293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2698836062945489322672917 126507940450569812000293)
                  ·
                    refine ⟨23720238834481839750055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126507940450569812000293 23720238834481839750055)
                    ·
                      rfl

theorem cell23_138585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 2, 1, 6, 4].length) (baseStart_138585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138585 prefixEnd_138585 := by exact prefixLift 138585
  have htrace : WordTrace (prefixWord ++ tailWord_138585) baseStart_138585 baseEnd_138585 := by
    simpa [prefixWord, tailWord_138585, baseEnd_138585] using wordTrace_append hprefix tailTrace_138585
  have hstable : (prefixWord ++ tailWord_138585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138585).length < 2 ^ (prefixWord ++ tailWord_138585).sum := by decide
  have hdescent : baseEnd_138585 < baseStart_138585 := by decide
  rcases family_descends (prefixWord ++ tailWord_138585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138632 : List Nat := [2, 1, 3, 3, 1, 3, 3, 7]
def baseStart_138632 : Nat := 118140960795 + 138632 * 2 ^ 59
def prefixEnd_138632 : Nat := 4983230072969 + 3 ^ 40 * 138632 * 2
def baseEnd_138632 : Nat := 2636475929415067976387

theorem tailTrace_138632 : CollatzResearch.WordTrace tailWord_138632 prefixEnd_138632 2636475929415067976387 := by
  unfold tailWord_138632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2528162216883707652865075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3370882955844943537153433 2528162216883707652865075)
  ·
    refine ⟨3792243325325561479297613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2528162216883707652865075 3792243325325561479297613)
    ·
      refine ⟨1422091246997085554736605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3792243325325561479297613 1422091246997085554736605)
      ·
        refine ⟨533284217623907083026227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1422091246997085554736605 533284217623907083026227)
        ·
          refine ⟨799926326435860624539341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533284217623907083026227 799926326435860624539341)
          ·
            refine ⟨299972372413447734202253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 799926326435860624539341 299972372413447734202253)
            ·
              refine ⟨112489639655042900325845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 299972372413447734202253 112489639655042900325845)
              ·
                refine ⟨2636475929415067976387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 112489639655042900325845 2636475929415067976387)
                ·
                  rfl

theorem cell23_138632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 7].length) (baseStart_138632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138632 prefixEnd_138632 := by exact prefixLift 138632
  have htrace : WordTrace (prefixWord ++ tailWord_138632) baseStart_138632 baseEnd_138632 := by
    simpa [prefixWord, tailWord_138632, baseEnd_138632] using wordTrace_append hprefix tailTrace_138632
  have hstable : (prefixWord ++ tailWord_138632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138632).length < 2 ^ (prefixWord ++ tailWord_138632).sum := by decide
  have hdescent : baseEnd_138632 < baseStart_138632 := by decide
  rcases family_descends (prefixWord ++ tailWord_138632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138699 : List Nat := [1, 1, 1, 1, 3, 3, 3, 2, 4, 2, 2]
def baseStart_138699 : Nat := 118140960795 + 138699 * 2 ^ 59
def prefixEnd_138699 : Nat := 4983230072969 + 3 ^ 40 * 138699 * 2
def baseEnd_138699 : Nat := 71219253298058073224641

theorem tailTrace_138699 : CollatzResearch.WordTrace tailWord_138699 prefixEnd_138699 71219253298058073224641 := by
  unfold tailWord_138699
  simp only [CollatzResearch.WordTrace]
  refine ⟨5058768124524685748419151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3372512083016457165612767 5058768124524685748419151)
  ·
    refine ⟨7588152186787028622628727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5058768124524685748419151 7588152186787028622628727)
    ·
      refine ⟨11382228280180542933943091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7588152186787028622628727 11382228280180542933943091)
      ·
        refine ⟨17073342420270814400914637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11382228280180542933943091 17073342420270814400914637)
        ·
          refine ⟨6402503407601555400342989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17073342420270814400914637 6402503407601555400342989)
          ·
            refine ⟨2400938777850583275128621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6402503407601555400342989 2400938777850583275128621)
            ·
              refine ⟨900352041693968728173233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2400938777850583275128621 900352041693968728173233)
              ·
                refine ⟨675264031270476546129925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900352041693968728173233 675264031270476546129925)
                ·
                  refine ⟨126612005863214352399361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 675264031270476546129925 126612005863214352399361)
                  ·
                    refine ⟨94959004397410764299521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126612005863214352399361 94959004397410764299521)
                    ·
                      refine ⟨71219253298058073224641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 94959004397410764299521 71219253298058073224641)
                      ·
                        rfl

theorem cell23_138699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 2, 4, 2, 2].length) (baseStart_138699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138699 prefixEnd_138699 := by exact prefixLift 138699
  have htrace : WordTrace (prefixWord ++ tailWord_138699) baseStart_138699 baseEnd_138699 := by
    simpa [prefixWord, tailWord_138699, baseEnd_138699] using wordTrace_append hprefix tailTrace_138699
  have hstable : (prefixWord ++ tailWord_138699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138699).length < 2 ^ (prefixWord ++ tailWord_138699).sum := by decide
  have hdescent : baseEnd_138699 < baseStart_138699 := by decide
  rcases family_descends (prefixWord ++ tailWord_138699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138735 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 3, 7]
def baseStart_138735 : Nat := 118140960795 + 138735 * 2 ^ 59
def prefixEnd_138735 : Nat := 4983230072969 + 3 ^ 40 * 138735 * 2
def baseEnd_138735 : Nat := 23745912867206644124825

theorem tailTrace_138735 : CollatzResearch.WordTrace tailWord_138735 prefixEnd_138735 23745912867206644124825 := by
  unfold tailWord_138735
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060081152394263896729659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3373387434929509264486439 5060081152394263896729659)
  ·
    refine ⟨7590121728591395845094489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5060081152394263896729659 7590121728591395845094489)
    ·
      refine ⟨5692591296443546883820867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7590121728591395845094489 5692591296443546883820867)
      ·
        refine ⟨8538886944665320325731301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5692591296443546883820867 8538886944665320325731301)
        ·
          refine ⟨1601041302124747561074619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8538886944665320325731301 1601041302124747561074619)
          ·
            refine ⟨2401561953187121341611929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1601041302124747561074619 2401561953187121341611929)
            ·
              refine ⟨1801171464890341006208947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2401561953187121341611929 1801171464890341006208947)
              ·
                refine ⟨2701757197335511509313421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1801171464890341006208947 2701757197335511509313421)
                ·
                  refine ⟨1013158949000816815992533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2701757197335511509313421 1013158949000816815992533)
                  ·
                    refine ⟨23745912867206644124825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1013158949000816815992533 23745912867206644124825)
                    ·
                      rfl

theorem cell23_138735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 7].length) (baseStart_138735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138735 prefixEnd_138735 := by exact prefixLift 138735
  have htrace : WordTrace (prefixWord ++ tailWord_138735) baseStart_138735 baseEnd_138735 := by
    simpa [prefixWord, tailWord_138735, baseEnd_138735] using wordTrace_append hprefix tailTrace_138735
  have hstable : (prefixWord ++ tailWord_138735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138735).length < 2 ^ (prefixWord ++ tailWord_138735).sum := by decide
  have hdescent : baseEnd_138735 < baseStart_138735 := by decide
  rcases family_descends (prefixWord ++ tailWord_138735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138745 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 7]
def baseStart_138745 : Nat := 118140960795 + 138745 * 2 ^ 59
def prefixEnd_138745 : Nat := 4983230072969 + 3 ^ 40 * 138745 * 2
def baseEnd_138745 : Nat := 71242873408164893249429

theorem tailTrace_138745 : CollatzResearch.WordTrace tailWord_138745 prefixEnd_138745 71242873408164893249429 := by
  unfold tailWord_138745
  simp only [CollatzResearch.WordTrace]
  refine ⟨5060445882358035604593689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3373630588238690403062459 5060445882358035604593689)
  ·
    refine ⟨3795334411768526703445267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5060445882358035604593689 3795334411768526703445267)
    ·
      refine ⟨5693001617652790055167901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3795334411768526703445267 5693001617652790055167901)
      ·
        refine ⟨2134875606619796270687963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5693001617652790055167901 2134875606619796270687963)
        ·
          refine ⟨3202313409929694406031945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2134875606619796270687963 3202313409929694406031945)
          ·
            refine ⟨2401735057447270804523959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3202313409929694406031945 2401735057447270804523959)
            ·
              refine ⟨3602602586170906206785939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2401735057447270804523959 3602602586170906206785939)
              ·
                refine ⟨5403903879256359310178909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3602602586170906206785939 5403903879256359310178909)
                ·
                  refine ⟨2026463954721134741317091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5403903879256359310178909 2026463954721134741317091)
                  ·
                    refine ⟨3039695932081702111975637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2026463954721134741317091 3039695932081702111975637)
                    ·
                      refine ⟨71242873408164893249429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3039695932081702111975637 71242873408164893249429)
                      ·
                        rfl

theorem cell23_138745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 3, 1, 7].length) (baseStart_138745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138745 prefixEnd_138745 := by exact prefixLift 138745
  have htrace : WordTrace (prefixWord ++ tailWord_138745) baseStart_138745 baseEnd_138745 := by
    simpa [prefixWord, tailWord_138745, baseEnd_138745] using wordTrace_append hprefix tailTrace_138745
  have hstable : (prefixWord ++ tailWord_138745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138745).length < 2 ^ (prefixWord ++ tailWord_138745).sum := by decide
  have hdescent : baseEnd_138745 < baseStart_138745 := by decide
  rcases family_descends (prefixWord ++ tailWord_138745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138762 : List Nat := [3, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5]
def baseStart_138762 : Nat := 118140960795 + 138762 * 2 ^ 59
def prefixEnd_138762 : Nat := 4983230072969 + 3 ^ 40 * 138762 * 2
def baseEnd_138762 : Nat := 71251602579291326736851

theorem tailTrace_138762 : CollatzResearch.WordTrace tailWord_138762 prefixEnd_138762 71251602579291326736851 := by
  unfold tailWord_138762
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265266480824111876990635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3374043948864298338641693 1265266480824111876990635)
  ·
    refine ⟨1897899721236167815485953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1265266480824111876990635 1897899721236167815485953)
    ·
      refine ⟨1423424790927125861614465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1897899721236167815485953 1423424790927125861614465)
      ·
        refine ⟨1067568593195344396210849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1423424790927125861614465 1067568593195344396210849)
        ·
          refine ⟨800676444896508297158137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1067568593195344396210849 800676444896508297158137)
          ·
            refine ⟨600507333672381222868603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 800676444896508297158137 600507333672381222868603)
            ·
              refine ⟨900761000508571834302905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 600507333672381222868603 900761000508571834302905)
              ·
                refine ⟨675570750381428875727179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 900761000508571834302905 675570750381428875727179)
                ·
                  refine ⟨1013356125572143313590769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675570750381428875727179 1013356125572143313590769)
                  ·
                    refine ⟨760017094179107485193077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1013356125572143313590769 760017094179107485193077)
                    ·
                      refine ⟨71251602579291326736851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 760017094179107485193077 71251602579291326736851)
                      ·
                        rfl

theorem cell23_138762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_138762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138762 prefixEnd_138762 := by exact prefixLift 138762
  have htrace : WordTrace (prefixWord ++ tailWord_138762) baseStart_138762 baseEnd_138762 := by
    simpa [prefixWord, tailWord_138762, baseEnd_138762] using wordTrace_append hprefix tailTrace_138762
  have hstable : (prefixWord ++ tailWord_138762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138762).length < 2 ^ (prefixWord ++ tailWord_138762).sum := by decide
  have hdescent : baseEnd_138762 < baseStart_138762 := by decide
  rcases family_descends (prefixWord ++ tailWord_138762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138795 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 12]
def baseStart_138795 : Nat := 118140960795 + 138795 * 2 ^ 59
def prefixEnd_138795 : Nat := 4983230072969 + 3 ^ 40 * 138795 * 2
def baseEnd_138795 : Nat := 7918727493432188624911

theorem tailTrace_138795 : CollatzResearch.WordTrace tailWord_138795 prefixEnd_138795 7918727493432188624911 := by
  unfold tailWord_138795
  simp only [CollatzResearch.WordTrace]
  refine ⟨5062269532176894143913839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3374846354784596095942559 5062269532176894143913839)
  ·
    refine ⟨7593404298265341215870759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5062269532176894143913839 7593404298265341215870759)
    ·
      refine ⟨11390106447398011823806139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7593404298265341215870759 11390106447398011823806139)
      ·
        refine ⟨17085159671097017735709209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11390106447398011823806139 17085159671097017735709209)
        ·
          refine ⟨12813869753322763301781907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17085159671097017735709209 12813869753322763301781907)
          ·
            refine ⟨19220804629984144952672861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12813869753322763301781907 19220804629984144952672861)
            ·
              refine ⟨7207801736244054357252323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19220804629984144952672861 7207801736244054357252323)
              ·
                refine ⟨10811702604366081535878485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7207801736244054357252323 10811702604366081535878485)
                ·
                  refine ⟨7918727493432188624911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 10811702604366081535878485 7918727493432188624911)
                  ·
                    rfl

theorem cell23_138795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 12].length) (baseStart_138795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138795 prefixEnd_138795 := by exact prefixLift 138795
  have htrace : WordTrace (prefixWord ++ tailWord_138795) baseStart_138795 baseEnd_138795 := by
    simpa [prefixWord, tailWord_138795, baseEnd_138795] using wordTrace_append hprefix tailTrace_138795
  have hstable : (prefixWord ++ tailWord_138795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138795).length < 2 ^ (prefixWord ++ tailWord_138795).sum := by decide
  have hdescent : baseEnd_138795 < baseStart_138795 := by decide
  rcases family_descends (prefixWord ++ tailWord_138795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138806 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4]
def baseStart_138806 : Nat := 118140960795 + 138806 * 2 ^ 59
def prefixEnd_138806 : Nat := 4983230072969 + 3 ^ 40 * 138806 * 2
def baseEnd_138806 : Nat := 71274195728089154586649

theorem tailTrace_138806 : CollatzResearch.WordTrace tailWord_138806 prefixEnd_138806 71274195728089154586649 := by
  unfold tailWord_138806
  simp only [CollatzResearch.WordTrace]
  refine ⟨316416920946065188910267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3375113823424695348376181 316416920946065188910267)
  ·
    refine ⟨474625381419097783365401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 316416920946065188910267 474625381419097783365401)
    ·
      refine ⟨355969036064323337524051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 474625381419097783365401 355969036064323337524051)
      ·
        refine ⟨533953554096485006286077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 355969036064323337524051 533953554096485006286077)
        ·
          refine ⟨200232582786181877357279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 533953554096485006286077 200232582786181877357279)
          ·
            refine ⟨300348874179272816035919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200232582786181877357279 300348874179272816035919)
            ·
              refine ⟨450523311268909224053879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300348874179272816035919 450523311268909224053879)
              ·
                refine ⟨675784966903363836080819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450523311268909224053879 675784966903363836080819)
                ·
                  refine ⟨1013677450355045754121229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675784966903363836080819 1013677450355045754121229)
                  ·
                    refine ⟨380129043883142157795461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1013677450355045754121229 380129043883142157795461)
                    ·
                      refine ⟨71274195728089154586649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 380129043883142157795461 71274195728089154586649)
                      ·
                        rfl

theorem cell23_138806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 1, 3, 4].length) (baseStart_138806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138806 prefixEnd_138806 := by exact prefixLift 138806
  have htrace : WordTrace (prefixWord ++ tailWord_138806) baseStart_138806 baseEnd_138806 := by
    simpa [prefixWord, tailWord_138806, baseEnd_138806] using wordTrace_append hprefix tailTrace_138806
  have hstable : (prefixWord ++ tailWord_138806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138806).length < 2 ^ (prefixWord ++ tailWord_138806).sum := by decide
  have hdescent : baseEnd_138806 < baseStart_138806 := by decide
  rcases family_descends (prefixWord ++ tailWord_138806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138809 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 3]
def baseStart_138809 : Nat := 118140960795 + 138809 * 2 ^ 59
def prefixEnd_138809 : Nat := 4983230072969 + 3 ^ 40 * 138809 * 2
def baseEnd_138809 : Nat := 71275736170052642849135

theorem tailTrace_138809 : CollatzResearch.WordTrace tailWord_138809 prefixEnd_138809 71275736170052642849135 := by
  unfold tailWord_138809
  simp only [CollatzResearch.WordTrace]
  refine ⟨5062780154126174534923481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3375186769417449689948987 5062780154126174534923481)
  ·
    refine ⟨3797085115594630901192611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5062780154126174534923481 3797085115594630901192611)
    ·
      refine ⟨5695627673391946351788917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3797085115594630901192611 5695627673391946351788917)
      ·
        refine ⟨533965094380494970480211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5695627673391946351788917 533965094380494970480211)
        ·
          refine ⟨800947641570742455720317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 533965094380494970480211 800947641570742455720317)
          ·
            refine ⟨300355365589028420895119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 800947641570742455720317 300355365589028420895119)
            ·
              refine ⟨450533048383542631342679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300355365589028420895119 450533048383542631342679)
              ·
                refine ⟨675799572575313947014019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450533048383542631342679 675799572575313947014019)
                ·
                  refine ⟨1013699358862970920521029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 675799572575313947014019 1013699358862970920521029)
                  ·
                    refine ⟨190068629786807047597693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1013699358862970920521029 190068629786807047597693)
                    ·
                      refine ⟨71275736170052642849135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 190068629786807047597693 71275736170052642849135)
                      ·
                        rfl

theorem cell23_138809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 1, 4, 3].length) (baseStart_138809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138809 prefixEnd_138809 := by exact prefixLift 138809
  have htrace : WordTrace (prefixWord ++ tailWord_138809) baseStart_138809 baseEnd_138809 := by
    simpa [prefixWord, tailWord_138809, baseEnd_138809] using wordTrace_append hprefix tailTrace_138809
  have hstable : (prefixWord ++ tailWord_138809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138809).length < 2 ^ (prefixWord ++ tailWord_138809).sum := by decide
  have hdescent : baseEnd_138809 < baseStart_138809 := by decide
  rcases family_descends (prefixWord ++ tailWord_138809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138842 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_138842 : Nat := 118140960795 + 138842 * 2 ^ 59
def prefixEnd_138842 : Nat := 4983230072969 + 3 ^ 40 * 138842 * 2
def baseEnd_138842 : Nat := 23764227010550337912161

theorem tailTrace_138842 : CollatzResearch.WordTrace tailWord_138842 prefixEnd_138842 23764227010550337912161 := by
  unfold tailWord_138842
  simp only [CollatzResearch.WordTrace]
  refine ⟨1265995940751655292718695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3375989175337747447249853 1265995940751655292718695)
  ·
    refine ⟨1898993911127482939078043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1265995940751655292718695 1898993911127482939078043)
    ·
      refine ⟨2848490866691224408617065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1898993911127482939078043 2848490866691224408617065)
      ·
        refine ⟨2136368150018418306462799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2848490866691224408617065 2136368150018418306462799)
        ·
          refine ⟨3204552225027627459694199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136368150018418306462799 3204552225027627459694199)
          ·
            refine ⟨4806828337541441189541299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3204552225027627459694199 4806828337541441189541299)
            ·
              refine ⟨7210242506312161784311949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4806828337541441189541299 7210242506312161784311949)
              ·
                refine ⟨2703840939867060669116981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7210242506312161784311949 2703840939867060669116981)
                ·
                  refine ⟨253485088112536937729717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2703840939867060669116981 253485088112536937729717)
                  ·
                    refine ⟨23764227010550337912161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 253485088112536937729717 23764227010550337912161)
                    ·
                      rfl

theorem cell23_138842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_138842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138842 prefixEnd_138842 := by exact prefixLift 138842
  have htrace : WordTrace (prefixWord ++ tailWord_138842) baseStart_138842 baseEnd_138842 := by
    simpa [prefixWord, tailWord_138842, baseEnd_138842] using wordTrace_append hprefix tailTrace_138842
  have hstable : (prefixWord ++ tailWord_138842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138842).length < 2 ^ (prefixWord ++ tailWord_138842).sum := by decide
  have hdescent : baseEnd_138842 < baseStart_138842 := by decide
  rcases family_descends (prefixWord ++ tailWord_138842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138849 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 3, 5, 2]
def baseStart_138849 : Nat := 118140960795 + 138849 * 2 ^ 59
def prefixEnd_138849 : Nat := 4983230072969 + 3 ^ 40 * 138849 * 2
def baseEnd_138849 : Nat := 71296275396232486348951

theorem tailTrace_138849 : CollatzResearch.WordTrace tailWord_138849 prefixEnd_138849 71296275396232486348951 := by
  unfold tailWord_138849
  simp only [CollatzResearch.WordTrace]
  refine ⟨5064239073981261366379601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3376159382654174244253067 5064239073981261366379601)
  ·
    refine ⟨3798179305485946024784701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5064239073981261366379601 3798179305485946024784701)
    ·
      refine ⟨1424317239557229759294263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3798179305485946024784701 1424317239557229759294263)
      ·
        refine ⟨2136475859335844638941395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1424317239557229759294263 2136475859335844638941395)
        ·
          refine ⟨3204713789003766958412093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2136475859335844638941395 3204713789003766958412093)
          ·
            refine ⟨1201767670876412609404535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3204713789003766958412093 1201767670876412609404535)
            ·
              refine ⟨1802651506314618914106803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1201767670876412609404535 1802651506314618914106803)
              ·
                refine ⟨2703977259471928371160205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1802651506314618914106803 2703977259471928371160205)
                ·
                  refine ⟨1013991472301973139185077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2703977259471928371160205 1013991472301973139185077)
                  ·
                    refine ⟨95061700528309981798601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1013991472301973139185077 95061700528309981798601)
                    ·
                      refine ⟨71296275396232486348951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95061700528309981798601 71296275396232486348951)
                      ·
                        rfl

theorem cell23_138849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 3, 5, 2].length) (baseStart_138849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138849 prefixEnd_138849 := by exact prefixLift 138849
  have htrace : WordTrace (prefixWord ++ tailWord_138849) baseStart_138849 baseEnd_138849 := by
    simpa [prefixWord, tailWord_138849, baseEnd_138849] using wordTrace_append hprefix tailTrace_138849
  have hstable : (prefixWord ++ tailWord_138849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138849).length < 2 ^ (prefixWord ++ tailWord_138849).sum := by decide
  have hdescent : baseEnd_138849 < baseStart_138849 := by decide
  rcases family_descends (prefixWord ++ tailWord_138849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138866 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 1, 5, 2]
def baseStart_138866 : Nat := 118140960795 + 138866 * 2 ^ 59
def prefixEnd_138866 : Nat := 4983230072969 + 3 ^ 40 * 138866 * 2
def baseEnd_138866 : Nat := 71305004567358919836373

theorem tailTrace_138866 : CollatzResearch.WordTrace tailWord_138866 prefixEnd_138866 71305004567358919836373 := by
  unfold tailWord_138866
  simp only [CollatzResearch.WordTrace]
  refine ⟨1266214778729918317437113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3376572743279782179832301 1266214778729918317437113)
  ·
    refine ⟨949661084047438738077835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1266214778729918317437113 949661084047438738077835)
    ·
      refine ⟨1424491626071158107116753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 949661084047438738077835 1424491626071158107116753)
      ·
        refine ⟨1068368719553368580337565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1424491626071158107116753 1068368719553368580337565)
        ·
          refine ⟨400638269832513217626587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1068368719553368580337565 400638269832513217626587)
          ·
            refine ⟨600957404748769826439881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400638269832513217626587 600957404748769826439881)
            ·
              refine ⟨450718053561577369829911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 600957404748769826439881 450718053561577369829911)
              ·
                refine ⟨676077080342366054744867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450718053561577369829911 676077080342366054744867)
                ·
                  refine ⟨1014115620513549082117301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676077080342366054744867 1014115620513549082117301)
                  ·
                    refine ⟨95073339423145226448497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1014115620513549082117301 95073339423145226448497)
                    ·
                      refine ⟨71305004567358919836373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95073339423145226448497 71305004567358919836373)
                      ·
                        rfl

theorem cell23_138866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 1, 5, 2].length) (baseStart_138866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138866 prefixEnd_138866 := by exact prefixLift 138866
  have htrace : WordTrace (prefixWord ++ tailWord_138866) baseStart_138866 baseEnd_138866 := by
    simpa [prefixWord, tailWord_138866, baseEnd_138866] using wordTrace_append hprefix tailTrace_138866
  have hstable : (prefixWord ++ tailWord_138866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138866).length < 2 ^ (prefixWord ++ tailWord_138866).sum := by decide
  have hdescent : baseEnd_138866 < baseStart_138866 := by decide
  rcases family_descends (prefixWord ++ tailWord_138866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138889 : List Nat := [1, 2, 1, 1, 4, 1, 4, 1, 4, 4]
def baseStart_138889 : Nat := 118140960795 + 138889 * 2 ^ 59
def prefixEnd_138889 : Nat := 4983230072969 + 3 ^ 40 * 138889 * 2
def baseEnd_138889 : Nat := 23772271540804109949589

theorem tailTrace_138889 : CollatzResearch.WordTrace tailWord_138889 prefixEnd_138889 23772271540804109949589 := by
  unfold tailWord_138889
  simp only [CollatzResearch.WordTrace]
  refine ⟨5065697993836348197835721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3377131995890898798557147 5065697993836348197835721)
  ·
    refine ⟨3799273495377261148376791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5065697993836348197835721 3799273495377261148376791)
    ·
      refine ⟨5698910243065891722565187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3799273495377261148376791 5698910243065891722565187)
      ·
        refine ⟨8548365364598837583847781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5698910243065891722565187 8548365364598837583847781)
        ·
          refine ⟨1602818505862282046971459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8548365364598837583847781 1602818505862282046971459)
          ·
            refine ⟨2404227758793423070457189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1602818505862282046971459 2404227758793423070457189)
            ·
              refine ⟨450792704773766825710723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2404227758793423070457189 450792704773766825710723)
              ·
                refine ⟨676189057160650238566085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450792704773766825710723 676189057160650238566085)
                ·
                  refine ⟨126785448217621919731141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 676189057160650238566085 126785448217621919731141)
                  ·
                    refine ⟨23772271540804109949589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 126785448217621919731141 23772271540804109949589)
                    ·
                      rfl

theorem cell23_138889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 1, 4, 4].length) (baseStart_138889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138889 prefixEnd_138889 := by exact prefixLift 138889
  have htrace : WordTrace (prefixWord ++ tailWord_138889) baseStart_138889 baseEnd_138889 := by
    simpa [prefixWord, tailWord_138889, baseEnd_138889] using wordTrace_append hprefix tailTrace_138889
  have hstable : (prefixWord ++ tailWord_138889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138889).length < 2 ^ (prefixWord ++ tailWord_138889).sum := by decide
  have hdescent : baseEnd_138889 < baseStart_138889 := by decide
  rcases family_descends (prefixWord ++ tailWord_138889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138892 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 6]
def baseStart_138892 : Nat := 118140960795 + 138892 * 2 ^ 59
def prefixEnd_138892 : Nat := 4983230072969 + 3 ^ 40 * 138892 * 2
def baseEnd_138892 : Nat := 71318355064375818111253

theorem tailTrace_138892 : CollatzResearch.WordTrace tailWord_138892 prefixEnd_138892 71318355064375818111253 := by
  unfold tailWord_138892
  simp only [CollatzResearch.WordTrace]
  refine ⟨2532903706412739855097465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3377204941883653140129953 2532903706412739855097465)
  ·
    refine ⟨1899677779809554891323099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2532903706412739855097465 1899677779809554891323099)
    ·
      refine ⟨2849516669714332336984649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1899677779809554891323099 2849516669714332336984649)
      ·
        refine ⟨2137137502285749252738487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2849516669714332336984649 2137137502285749252738487)
        ·
          refine ⟨3205706253428623879107731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2137137502285749252738487 3205706253428623879107731)
          ·
            refine ⟨4808559380142935818661597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3205706253428623879107731 4808559380142935818661597)
            ·
              refine ⟨1803209767553600931998099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4808559380142935818661597 1803209767553600931998099)
              ·
                refine ⟨2704814651330401397997149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1803209767553600931998099 2704814651330401397997149)
                ·
                  refine ⟨1014305494248900524248931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2704814651330401397997149 1014305494248900524248931)
                  ·
                    refine ⟨1521458241373350786373397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1014305494248900524248931 1521458241373350786373397)
                    ·
                      refine ⟨71318355064375818111253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1521458241373350786373397 71318355064375818111253)
                      ·
                        rfl

theorem cell23_138892_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 3, 1, 6].length) (baseStart_138892 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138892 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138892 prefixEnd_138892 := by exact prefixLift 138892
  have htrace : WordTrace (prefixWord ++ tailWord_138892) baseStart_138892 baseEnd_138892 := by
    simpa [prefixWord, tailWord_138892, baseEnd_138892] using wordTrace_append hprefix tailTrace_138892
  have hstable : (prefixWord ++ tailWord_138892).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138892).length < 2 ^ (prefixWord ++ tailWord_138892).sum := by decide
  have hdescent : baseEnd_138892 < baseStart_138892 := by decide
  rcases family_descends (prefixWord ++ tailWord_138892) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138909 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 4]
def baseStart_138909 : Nat := 118140960795 + 138909 * 2 ^ 59
def prefixEnd_138909 : Nat := 4983230072969 + 3 ^ 40 * 138909 * 2
def baseEnd_138909 : Nat := 71327084235502251598675

theorem tailTrace_138909 : CollatzResearch.WordTrace tailWord_138909 prefixEnd_138909 71327084235502251598675 := by
  unfold tailWord_138909
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066427453763891613563781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3377618302509261075709187 5066427453763891613563781)
  ·
    refine ⟨949955147580729677543209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5066427453763891613563781 949955147580729677543209)
    ·
      refine ⟨712466360685547258157407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 949955147580729677543209 712466360685547258157407)
      ·
        refine ⟨1068699541028320887236111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712466360685547258157407 1068699541028320887236111)
        ·
          refine ⟨1603049311542481330854167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1068699541028320887236111 1603049311542481330854167)
          ·
            refine ⟨2404573967313721996281251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1603049311542481330854167 2404573967313721996281251)
            ·
              refine ⟨3606860950970582994421877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2404573967313721996281251 3606860950970582994421877)
              ·
                refine ⟨338143214153492155727051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3606860950970582994421877 338143214153492155727051)
                ·
                  refine ⟨507214821230238233590577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338143214153492155727051 507214821230238233590577)
                  ·
                    refine ⟨380411115922678675192933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507214821230238233590577 380411115922678675192933)
                    ·
                      refine ⟨71327084235502251598675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 380411115922678675192933 71327084235502251598675)
                      ·
                        rfl

theorem cell23_138909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_138909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138909 prefixEnd_138909 := by exact prefixLift 138909
  have htrace : WordTrace (prefixWord ++ tailWord_138909) baseStart_138909 baseEnd_138909 := by
    simpa [prefixWord, tailWord_138909, baseEnd_138909] using wordTrace_append hprefix tailTrace_138909
  have hstable : (prefixWord ++ tailWord_138909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138909).length < 2 ^ (prefixWord ++ tailWord_138909).sum := by decide
  have hdescent : baseEnd_138909 < baseStart_138909 := by decide
  rcases family_descends (prefixWord ++ tailWord_138909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138913 : List Nat := [1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 4]
def baseStart_138913 : Nat := 118140960795 + 138913 * 2 ^ 59
def prefixEnd_138913 : Nat := 4983230072969 + 3 ^ 40 * 138913 * 2
def baseEnd_138913 : Nat := 71329138158120235948657

theorem tailTrace_138913 : CollatzResearch.WordTrace tailWord_138913 prefixEnd_138913 71329138158120235948657 := by
  unfold tailWord_138913
  simp only [CollatzResearch.WordTrace]
  refine ⟨5066573345749400296709393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3377715563832933531139595 5066573345749400296709393)
  ·
    refine ⟨3799930009312050222532045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5066573345749400296709393 3799930009312050222532045)
    ·
      refine ⟨1424973753492018833449517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3799930009312050222532045 1424973753492018833449517)
      ·
        refine ⟨534365157559507062543569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1424973753492018833449517 534365157559507062543569)
        ·
          refine ⟨400773868169630296907677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 534365157559507062543569 400773868169630296907677)
          ·
            refine ⟨150290200563611361340379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 400773868169630296907677 150290200563611361340379)
            ·
              refine ⟨225435300845417042010569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150290200563611361340379 225435300845417042010569)
              ·
                refine ⟨169076475634062781507927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225435300845417042010569 169076475634062781507927)
                ·
                  refine ⟨253614713451094172261891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169076475634062781507927 253614713451094172261891)
                  ·
                    refine ⟨380422070176641258392837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253614713451094172261891 380422070176641258392837)
                    ·
                      refine ⟨71329138158120235948657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 380422070176641258392837 71329138158120235948657)
                      ·
                        rfl

theorem cell23_138913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 2, 1, 1, 4].length) (baseStart_138913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138913 prefixEnd_138913 := by exact prefixLift 138913
  have htrace : WordTrace (prefixWord ++ tailWord_138913) baseStart_138913 baseEnd_138913 := by
    simpa [prefixWord, tailWord_138913, baseEnd_138913] using wordTrace_append hprefix tailTrace_138913
  have hstable : (prefixWord ++ tailWord_138913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138913).length < 2 ^ (prefixWord ++ tailWord_138913).sum := by decide
  have hdescent : baseEnd_138913 < baseStart_138913 := by decide
  rcases family_descends (prefixWord ++ tailWord_138913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138916 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 3, 2, 3]
def baseStart_138916 : Nat := 118140960795 + 138916 * 2 ^ 59
def prefixEnd_138916 : Nat := 4983230072969 + 3 ^ 40 * 138916 * 2
def baseEnd_138916 : Nat := 71330678600083724211143

theorem tailTrace_138916 : CollatzResearch.WordTrace tailWord_138916 prefixEnd_138916 71330678600083724211143 := by
  unfold tailWord_138916
  simp only [CollatzResearch.WordTrace]
  refine ⟨2533341382369265904534301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3377788509825687872712401 2533341382369265904534301)
  ·
    refine ⟨950003018388474714200363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2533341382369265904534301 950003018388474714200363)
    ·
      refine ⟨1425004527582712071300545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 950003018388474714200363 1425004527582712071300545)
      ·
        refine ⟨1068753395687034053475409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1425004527582712071300545 1068753395687034053475409)
        ·
          refine ⟨801565046765275540106557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1068753395687034053475409 801565046765275540106557)
          ·
            refine ⟨300586892536978327539959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 801565046765275540106557 300586892536978327539959)
            ·
              refine ⟨450880338805467491309939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300586892536978327539959 450880338805467491309939)
              ·
                refine ⟨676320508208201236964909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 450880338805467491309939 676320508208201236964909)
                ·
                  refine ⟨253620190578075463861841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676320508208201236964909 253620190578075463861841)
                  ·
                    refine ⟨190215142933556597896381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253620190578075463861841 190215142933556597896381)
                    ·
                      refine ⟨71330678600083724211143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 190215142933556597896381 71330678600083724211143)
                      ·
                        rfl

theorem cell23_138916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 3, 2, 3].length) (baseStart_138916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138916 prefixEnd_138916 := by exact prefixLift 138916
  have htrace : WordTrace (prefixWord ++ tailWord_138916) baseStart_138916 baseEnd_138916 := by
    simpa [prefixWord, tailWord_138916, baseEnd_138916] using wordTrace_append hprefix tailTrace_138916
  have hstable : (prefixWord ++ tailWord_138916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138916).length < 2 ^ (prefixWord ++ tailWord_138916).sum := by decide
  have hdescent : baseEnd_138916 < baseStart_138916 := by decide
  rcases family_descends (prefixWord ++ tailWord_138916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138933 : List Nat := [1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 5]
def baseStart_138933 : Nat := 118140960795 + 138933 * 2 ^ 59
def prefixEnd_138933 : Nat := 4983230072969 + 3 ^ 40 * 138933 * 2
def baseEnd_138933 : Nat := 71339407771210157698565

theorem tailTrace_138933 : CollatzResearch.WordTrace tailWord_138933 prefixEnd_138933 71339407771210157698565 := by
  unfold tailWord_138933
  simp only [CollatzResearch.WordTrace]
  refine ⟨5067302805676943712437453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3378201870451295808291635 5067302805676943712437453)
  ·
    refine ⟨1900238552128853892164045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5067302805676943712437453 1900238552128853892164045)
    ·
      refine ⟨712589457048320209561517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1900238552128853892164045 712589457048320209561517)
      ·
        refine ⟨267221046393120078585569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 712589457048320209561517 267221046393120078585569)
        ·
          refine ⟨200415784794840058939177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267221046393120078585569 200415784794840058939177)
          ·
            refine ⟨150311838596130044204383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200415784794840058939177 150311838596130044204383)
            ·
              refine ⟨225467757894195066306575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150311838596130044204383 225467757894195066306575)
              ·
                refine ⟨338201636841292599459863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225467757894195066306575 338201636841292599459863)
                ·
                  refine ⟨507302455261938899189795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 338201636841292599459863 507302455261938899189795)
                  ·
                    refine ⟨760953682892908348784693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 507302455261938899189795 760953682892908348784693)
                    ·
                      refine ⟨71339407771210157698565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 760953682892908348784693 71339407771210157698565)
                      ·
                        rfl

theorem cell23_138933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_138933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138933 prefixEnd_138933 := by exact prefixLift 138933
  have htrace : WordTrace (prefixWord ++ tailWord_138933) baseStart_138933 baseEnd_138933 := by
    simpa [prefixWord, tailWord_138933, baseEnd_138933] using wordTrace_append hprefix tailTrace_138933
  have hstable : (prefixWord ++ tailWord_138933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138933).length < 2 ^ (prefixWord ++ tailWord_138933).sum := by decide
  have hdescent : baseEnd_138933 < baseStart_138933 := by decide
  rcases family_descends (prefixWord ++ tailWord_138933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138950 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3]
def baseStart_138950 : Nat := 118140960795 + 138950 * 2 ^ 59
def prefixEnd_138950 : Nat := 4983230072969 + 3 ^ 40 * 138950 * 2
def baseEnd_138950 : Nat := 71348136942336591185987

theorem tailTrace_138950 : CollatzResearch.WordTrace tailWord_138950 prefixEnd_138950 71348136942336591185987 := by
  unfold tailWord_138950
  simp only [CollatzResearch.WordTrace]
  refine ⟨158372588956729862993947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 3378615231076903743870869 158372588956729862993947)
  ·
    refine ⟨237558883435094794490921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 158372588956729862993947 237558883435094794490921)
    ·
      refine ⟨178169162576321095868191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 237558883435094794490921 178169162576321095868191)
      ·
        refine ⟨267253743864481643802287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178169162576321095868191 267253743864481643802287)
        ·
          refine ⟨400880615796722465703431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 267253743864481643802287 400880615796722465703431)
          ·
            refine ⟨601320923695083698555147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 400880615796722465703431 601320923695083698555147)
            ·
              refine ⟨901981385542625547832721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 601320923695083698555147 901981385542625547832721)
              ·
                refine ⟨676486039156969160874541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 901981385542625547832721 676486039156969160874541)
                ·
                  refine ⟨253682264683863435327953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 676486039156969160874541 253682264683863435327953)
                  ·
                    refine ⟨190261698512897576495965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 253682264683863435327953 190261698512897576495965)
                    ·
                      refine ⟨71348136942336591185987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 190261698512897576495965 71348136942336591185987)
                      ·
                        rfl

theorem cell23_138950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 3, 2, 3].length) (baseStart_138950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138950 prefixEnd_138950 := by exact prefixLift 138950
  have htrace : WordTrace (prefixWord ++ tailWord_138950) baseStart_138950 baseEnd_138950 := by
    simpa [prefixWord, tailWord_138950, baseEnd_138950] using wordTrace_append hprefix tailTrace_138950
  have hstable : (prefixWord ++ tailWord_138950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138950).length < 2 ^ (prefixWord ++ tailWord_138950).sum := by decide
  have hdescent : baseEnd_138950 < baseStart_138950 := by decide
  rcases family_descends (prefixWord ++ tailWord_138950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_138999 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 4]
def baseStart_138999 : Nat := 118140960795 + 138999 * 2 ^ 59
def prefixEnd_138999 : Nat := 4983230072969 + 3 ^ 40 * 138999 * 2
def baseEnd_138999 : Nat := 71373297494406899473261

theorem tailTrace_138999 : CollatzResearch.WordTrace tailWord_138999 prefixEnd_138999 71373297494406899473261 := by
  unfold tailWord_138999
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069710023437836984340051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3379806682291891322893367 5069710023437836984340051)
  ·
    refine ⟨7604565035156755476510077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5069710023437836984340051 7604565035156755476510077)
    ·
      refine ⟨2851711888183783303691279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7604565035156755476510077 2851711888183783303691279)
      ·
        refine ⟨4277567832275674955536919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2851711888183783303691279 4277567832275674955536919)
        ·
          refine ⟨6416351748413512433305379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4277567832275674955536919 6416351748413512433305379)
          ·
            refine ⟨9624527622620268649958069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6416351748413512433305379 9624527622620268649958069)
            ·
              refine ⟨902299464620650185933569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9624527622620268649958069 902299464620650185933569)
              ·
                refine ⟨676724598465487639450177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 902299464620650185933569 676724598465487639450177)
                ·
                  refine ⟨507543448849115729587633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 676724598465487639450177 507543448849115729587633)
                  ·
                    refine ⟨380657586636836797190725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 507543448849115729587633 380657586636836797190725)
                    ·
                      refine ⟨71373297494406899473261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 380657586636836797190725 71373297494406899473261)
                      ·
                        rfl

theorem cell23_138999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 2, 4].length) (baseStart_138999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_138999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_138999 prefixEnd_138999 := by exact prefixLift 138999
  have htrace : WordTrace (prefixWord ++ tailWord_138999) baseStart_138999 baseEnd_138999 := by
    simpa [prefixWord, tailWord_138999, baseEnd_138999] using wordTrace_append hprefix tailTrace_138999
  have hstable : (prefixWord ++ tailWord_138999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_138999).length < 2 ^ (prefixWord ++ tailWord_138999).sum := by decide
  have hdescent : baseEnd_138999 < baseStart_138999 := by decide
  rcases family_descends (prefixWord ++ tailWord_138999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139003 : List Nat := [1, 1, 1, 1, 1, 3, 1, 8, 2, 2, 2]
def baseStart_139003 : Nat := 118140960795 + 139003 * 2 ^ 59
def prefixEnd_139003 : Nat := 4983230072969 + 3 ^ 40 * 139003 * 2
def baseEnd_139003 : Nat := 71375351417024883823243

theorem tailTrace_139003 : CollatzResearch.WordTrace tailWord_139003 prefixEnd_139003 71375351417024883823243 := by
  unfold tailWord_139003
  simp only [CollatzResearch.WordTrace]
  refine ⟨5069855915423345667485663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3379903943615563778323775 5069855915423345667485663)
  ·
    refine ⟨7604783873135018501228495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5069855915423345667485663 7604783873135018501228495)
    ·
      refine ⟨11407175809702527751842743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7604783873135018501228495 11407175809702527751842743)
      ·
        refine ⟨17110763714553791627764115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11407175809702527751842743 17110763714553791627764115)
        ·
          refine ⟨25666145571830687441646173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17110763714553791627764115 25666145571830687441646173)
          ·
            refine ⟨9624804589436507790617315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25666145571830687441646173 9624804589436507790617315)
            ·
              refine ⟨14437206884154761685925973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9624804589436507790617315 14437206884154761685925973)
              ·
                refine ⟨169186018173688613506945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 14437206884154761685925973 169186018173688613506945)
                ·
                  refine ⟨126889513630266460130209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169186018173688613506945 126889513630266460130209)
                  ·
                    refine ⟨95167135222699845097657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 126889513630266460130209 95167135222699845097657)
                    ·
                      refine ⟨71375351417024883823243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95167135222699845097657 71375351417024883823243)
                      ·
                        rfl

theorem cell23_139003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 8, 2, 2, 2].length) (baseStart_139003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139003 prefixEnd_139003 := by exact prefixLift 139003
  have htrace : WordTrace (prefixWord ++ tailWord_139003) baseStart_139003 baseEnd_139003 := by
    simpa [prefixWord, tailWord_139003, baseEnd_139003] using wordTrace_append hprefix tailTrace_139003
  have hstable : (prefixWord ++ tailWord_139003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139003).length < 2 ^ (prefixWord ++ tailWord_139003).sum := by decide
  have hdescent : baseEnd_139003 < baseStart_139003 := by decide
  rcases family_descends (prefixWord ++ tailWord_139003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139009 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 7]
def baseStart_139009 : Nat := 118140960795 + 139009 * 2 ^ 59
def prefixEnd_139009 : Nat := 4983230072969 + 3 ^ 40 * 139009 * 2
def baseEnd_139009 : Nat := 7930936922327984483135

theorem tailTrace_139009 : CollatzResearch.WordTrace tailWord_139009 prefixEnd_139009 7930936922327984483135 := by
  unfold tailWord_139009
  simp only [CollatzResearch.WordTrace]
  refine ⟨5070074753401608692204081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3380049835601072461469387 5070074753401608692204081)
  ·
    refine ⟨3802556065051206519153061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5070074753401608692204081 3802556065051206519153061)
    ·
      refine ⟨712979262197101222341199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3802556065051206519153061 712979262197101222341199)
      ·
        refine ⟨1069468893295651833511799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 712979262197101222341199 1069468893295651833511799)
        ·
          refine ⟨1604203339943477750267699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1069468893295651833511799 1604203339943477750267699)
          ·
            refine ⟨2406305009915216625401549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1604203339943477750267699 2406305009915216625401549)
            ·
              refine ⟨902364378718206234525581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2406305009915216625401549 902364378718206234525581)
              ·
                refine ⟨338386642019327337947093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 902364378718206234525581 338386642019327337947093)
                ·
                  refine ⟨7930936922327984483135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 338386642019327337947093 7930936922327984483135)
                  ·
                    rfl

theorem cell23_139009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 7].length) (baseStart_139009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139009 prefixEnd_139009 := by exact prefixLift 139009
  have htrace : WordTrace (prefixWord ++ tailWord_139009) baseStart_139009 baseEnd_139009 := by
    simpa [prefixWord, tailWord_139009, baseEnd_139009] using wordTrace_append hprefix tailTrace_139009
  have hstable : (prefixWord ++ tailWord_139009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139009).length < 2 ^ (prefixWord ++ tailWord_139009).sum := by decide
  have hdescent : baseEnd_139009 < baseStart_139009 := by decide
  rcases family_descends (prefixWord ++ tailWord_139009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139039 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 1, 7]
def baseStart_139039 : Nat := 118140960795 + 139039 * 2 ^ 59
def prefixEnd_139039 : Nat := 4983230072969 + 3 ^ 40 * 139039 * 2
def baseEnd_139039 : Nat := 23797945573528914324359

theorem tailTrace_139039 : CollatzResearch.WordTrace tailWord_139039 prefixEnd_139039 23797945573528914324359 := by
  unfold tailWord_139039
  simp only [CollatzResearch.WordTrace]
  refine ⟨5071168943292923815796171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3380779295528615877197447 5071168943292923815796171)
  ·
    refine ⟨7606753414939385723694257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5071168943292923815796171 7606753414939385723694257)
    ·
      refine ⟨5705065061204539292770693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7606753414939385723694257 5705065061204539292770693)
      ·
        refine ⟨1069699698975851117394505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5705065061204539292770693 1069699698975851117394505)
        ·
          refine ⟨802274774231888338045879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1069699698975851117394505 802274774231888338045879)
          ·
            refine ⟨1203412161347832507068819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 802274774231888338045879 1203412161347832507068819)
            ·
              refine ⟨1805118242021748760603229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1203412161347832507068819 1805118242021748760603229)
              ·
                refine ⟨676919340758155785226211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1805118242021748760603229 676919340758155785226211)
                ·
                  refine ⟨1015379011137233677839317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 676919340758155785226211 1015379011137233677839317)
                  ·
                    refine ⟨23797945573528914324359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1015379011137233677839317 23797945573528914324359)
                    ·
                      rfl

theorem cell23_139039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 7].length) (baseStart_139039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139039 prefixEnd_139039 := by exact prefixLift 139039
  have htrace : WordTrace (prefixWord ++ tailWord_139039) baseStart_139039 baseEnd_139039 := by
    simpa [prefixWord, tailWord_139039, baseEnd_139039] using wordTrace_append hprefix tailTrace_139039
  have hstable : (prefixWord ++ tailWord_139039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139039).length < 2 ^ (prefixWord ++ tailWord_139039).sum := by decide
  have hdescent : baseEnd_139039 < baseStart_139039 := by decide
  rcases family_descends (prefixWord ++ tailWord_139039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139066 : List Nat := [3, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5]
def baseStart_139066 : Nat := 118140960795 + 139066 * 2 ^ 59
def prefixEnd_139066 : Nat := 4983230072969 + 3 ^ 40 * 139066 * 2
def baseEnd_139066 : Nat := 71407700698258137335453

theorem tailTrace_139066 : CollatzResearch.WordTrace tailWord_139066 prefixEnd_139066 71407700698258137335453 := by
  unfold tailWord_139066
  simp only [CollatzResearch.WordTrace]
  refine ⟨1268038428548776856757263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3381435809463404951352701 1268038428548776856757263)
  ·
    refine ⟨1902057642823165285135895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1268038428548776856757263 1902057642823165285135895)
    ·
      refine ⟨2853086464234747927703843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902057642823165285135895 2853086464234747927703843)
      ·
        refine ⟨4279629696352121891555765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2853086464234747927703843 4279629696352121891555765)
        ·
          refine ⟨401215284033011427333353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 4279629696352121891555765 401215284033011427333353)
          ·
            refine ⟨300911463024758570500015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 401215284033011427333353 300911463024758570500015)
            ·
              refine ⟨451367194537137855750023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 300911463024758570500015 451367194537137855750023)
              ·
                refine ⟨677050791805706783625035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451367194537137855750023 677050791805706783625035)
                ·
                  refine ⟨1015576187708560175437553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 677050791805706783625035 1015576187708560175437553)
                  ·
                    refine ⟨761682140781420131578165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1015576187708560175437553 761682140781420131578165)
                    ·
                      refine ⟨71407700698258137335453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 761682140781420131578165 71407700698258137335453)
                      ·
                        rfl

theorem cell23_139066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5].length) (baseStart_139066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139066 prefixEnd_139066 := by exact prefixLift 139066
  have htrace : WordTrace (prefixWord ++ tailWord_139066) baseStart_139066 baseEnd_139066 := by
    simpa [prefixWord, tailWord_139066, baseEnd_139066] using wordTrace_append hprefix tailTrace_139066
  have hstable : (prefixWord ++ tailWord_139066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139066).length < 2 ^ (prefixWord ++ tailWord_139066).sum := by decide
  have hdescent : baseEnd_139066 < baseStart_139066 := by decide
  rcases family_descends (prefixWord ++ tailWord_139066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139093 : List Nat := [1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 4]
def baseStart_139093 : Nat := 118140960795 + 139093 * 2 ^ 59
def prefixEnd_139093 : Nat := 4983230072969 + 3 ^ 40 * 139093 * 2
def baseEnd_139093 : Nat := 71421564675929531697829

theorem tailTrace_139093 : CollatzResearch.WordTrace tailWord_139093 prefixEnd_139093 71421564675929531697829 := by
  unfold tailWord_139093
  simp only [CollatzResearch.WordTrace]
  refine ⟨5073138485097291038261933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3382092323398194025507955 5073138485097291038261933)
  ·
    refine ⟨1902426931911484139348225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5073138485097291038261933 1902426931911484139348225)
    ·
      refine ⟨1426820198933613104511169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1902426931911484139348225 1426820198933613104511169)
      ·
        refine ⟨1070115149200209828383377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1426820198933613104511169 1070115149200209828383377)
        ·
          refine ⟨802586361900157371287533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1070115149200209828383377 802586361900157371287533)
          ·
            refine ⟨300969885712559014232825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 802586361900157371287533 300969885712559014232825)
            ·
              refine ⟨225727414284419260674619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 300969885712559014232825 225727414284419260674619)
              ·
                refine ⟨338591121426628891011929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225727414284419260674619 338591121426628891011929)
                ·
                  refine ⟨253943341069971668258947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 338591121426628891011929 253943341069971668258947)
                  ·
                    refine ⟨380915011604957502388421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 253943341069971668258947 380915011604957502388421)
                    ·
                      refine ⟨71421564675929531697829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 380915011604957502388421 71421564675929531697829)
                      ·
                        rfl

theorem cell23_139093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 1, 2, 1, 4].length) (baseStart_139093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139093 prefixEnd_139093 := by exact prefixLift 139093
  have htrace : WordTrace (prefixWord ++ tailWord_139093) baseStart_139093 baseEnd_139093 := by
    simpa [prefixWord, tailWord_139093, baseEnd_139093] using wordTrace_append hprefix tailTrace_139093
  have hstable : (prefixWord ++ tailWord_139093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139093).length < 2 ^ (prefixWord ++ tailWord_139093).sum := by decide
  have hdescent : baseEnd_139093 < baseStart_139093 := by decide
  rcases family_descends (prefixWord ++ tailWord_139093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139116 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 6]
def baseStart_139116 : Nat := 118140960795 + 139116 * 2 ^ 59
def prefixEnd_139116 : Nat := 4983230072969 + 3 ^ 40 * 139116 * 2
def baseEnd_139116 : Nat := 7937041636775882412247

theorem tailTrace_139116 : CollatzResearch.WordTrace tailWord_139116 prefixEnd_139116 7937041636775882412247 := by
  unfold tailWord_139116
  simp only [CollatzResearch.WordTrace]
  refine ⟨2536988682006982983174601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3382651576009310644232801 2536988682006982983174601)
  ·
    refine ⟨1902741511505237237380951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2536988682006982983174601 1902741511505237237380951)
    ·
      refine ⟨2854112267257855856071427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1902741511505237237380951 2854112267257855856071427)
      ·
        refine ⟨4281168400886783784107141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2854112267257855856071427 4281168400886783784107141)
        ·
          refine ⟨802719075166271959520089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4281168400886783784107141 802719075166271959520089)
          ·
            refine ⟨602039306374703969640067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 802719075166271959520089 602039306374703969640067)
            ·
              refine ⟨903058959562055954460101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 602039306374703969640067 903058959562055954460101)
              ·
                refine ⟨169323554917885491461269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 903058959562055954460101 169323554917885491461269)
                ·
                  refine ⟨7937041636775882412247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169323554917885491461269 7937041636775882412247)
                  ·
                    rfl

theorem cell23_139116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_139116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139116 prefixEnd_139116 := by exact prefixLift 139116
  have htrace : WordTrace (prefixWord ++ tailWord_139116) baseStart_139116 baseEnd_139116 := by
    simpa [prefixWord, tailWord_139116, baseEnd_139116] using wordTrace_append hprefix tailTrace_139116
  have hstable : (prefixWord ++ tailWord_139116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139116).length < 2 ^ (prefixWord ++ tailWord_139116).sum := by decide
  have hdescent : baseEnd_139116 < baseStart_139116 := by decide
  rcases family_descends (prefixWord ++ tailWord_139116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139200 : List Nat := [2, 1, 1, 2, 3, 2, 1, 4, 3, 2, 2]
def baseStart_139200 : Nat := 118140960795 + 139200 * 2 ^ 59
def prefixEnd_139200 : Nat := 4983230072969 + 3 ^ 40 * 139200 * 2
def baseEnd_139200 : Nat := 71476507105960613059837

theorem tailTrace_139200 : CollatzResearch.WordTrace tailWord_139200 prefixEnd_139200 71476507105960613059837 := by
  unfold tailWord_139200
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538520547854824156203527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3384694063806432208271369 2538520547854824156203527)
  ·
    refine ⟨3807780821782236234305291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2538520547854824156203527 3807780821782236234305291)
    ·
      refine ⟨5711671232673354351457937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3807780821782236234305291 5711671232673354351457937)
      ·
        refine ⟨4283753424505015763593453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5711671232673354351457937 4283753424505015763593453)
        ·
          refine ⟨1606407534189380911347545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4283753424505015763593453 1606407534189380911347545)
          ·
            refine ⟨1204805650642035683510659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1606407534189380911347545 1204805650642035683510659)
            ·
              refine ⟨1807208475963053525265989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204805650642035683510659 1807208475963053525265989)
              ·
                refine ⟨338851589243072535987373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1807208475963053525265989 338851589243072535987373)
                ·
                  refine ⟨127069345966152200995265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338851589243072535987373 127069345966152200995265)
                  ·
                    refine ⟨95302009474614150746449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127069345966152200995265 95302009474614150746449)
                    ·
                      refine ⟨71476507105960613059837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95302009474614150746449 71476507105960613059837)
                      ·
                        rfl

theorem cell23_139200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 4, 3, 2, 2].length) (baseStart_139200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139200 prefixEnd_139200 := by exact prefixLift 139200
  have htrace : WordTrace (prefixWord ++ tailWord_139200) baseStart_139200 baseEnd_139200 := by
    simpa [prefixWord, tailWord_139200, baseEnd_139200] using wordTrace_append hprefix tailTrace_139200
  have hstable : (prefixWord ++ tailWord_139200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139200).length < 2 ^ (prefixWord ++ tailWord_139200).sum := by decide
  have hdescent : baseEnd_139200 < baseStart_139200 := by decide
  rcases family_descends (prefixWord ++ tailWord_139200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139217 : List Nat := [1, 2, 2, 1, 2, 1, 2, 7, 1, 2, 2]
def baseStart_139217 : Nat := 118140960795 + 139217 * 2 ^ 59
def prefixEnd_139217 : Nat := 4983230072969 + 3 ^ 40 * 139217 * 2
def baseEnd_139217 : Nat := 71485236277087046547259

theorem tailTrace_139217 : CollatzResearch.WordTrace tailWord_139217 prefixEnd_139217 71485236277087046547259 := by
  unfold tailWord_139217
  simp only [CollatzResearch.WordTrace]
  refine ⟨5077661136648060215775905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3385107424432040143850603 5077661136648060215775905)
  ·
    refine ⟨3808245852486045161831929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5077661136648060215775905 3808245852486045161831929)
    ·
      refine ⟨2856184389364533871373947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3808245852486045161831929 2856184389364533871373947)
      ·
        refine ⟨4284276584046800807060921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2856184389364533871373947 4284276584046800807060921)
        ·
          refine ⟨3213207438035100605295691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4284276584046800807060921 3213207438035100605295691)
          ·
            refine ⟨4819811157052650907943537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3213207438035100605295691 4819811157052650907943537)
            ·
              refine ⟨3614858367789488180957653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4819811157052650907943537 3614858367789488180957653)
              ·
                refine ⟨84723242995066129241195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3614858367789488180957653 84723242995066129241195)
                ·
                  refine ⟨127084864492599193861793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84723242995066129241195 127084864492599193861793)
                  ·
                    refine ⟨95313648369449395396345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127084864492599193861793 95313648369449395396345)
                    ·
                      refine ⟨71485236277087046547259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95313648369449395396345 71485236277087046547259)
                      ·
                        rfl

theorem cell23_139217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 7, 1, 2, 2].length) (baseStart_139217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139217 prefixEnd_139217 := by exact prefixLift 139217
  have htrace : WordTrace (prefixWord ++ tailWord_139217) baseStart_139217 baseEnd_139217 := by
    simpa [prefixWord, tailWord_139217, baseEnd_139217] using wordTrace_append hprefix tailTrace_139217
  have hstable : (prefixWord ++ tailWord_139217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139217).length < 2 ^ (prefixWord ++ tailWord_139217).sum := by decide
  have hdescent : baseEnd_139217 < baseStart_139217 := by decide
  rcases family_descends (prefixWord ++ tailWord_139217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139220 : List Nat := [2, 4, 1, 2, 1, 1, 1, 5, 1, 2, 3]
def baseStart_139220 : Nat := 118140960795 + 139220 * 2 ^ 59
def prefixEnd_139220 : Nat := 4983230072969 + 3 ^ 40 * 139220 * 2
def baseEnd_139220 : Nat := 71486776719050534809745

theorem tailTrace_139220 : CollatzResearch.WordTrace tailWord_139220 prefixEnd_139220 71486776719050534809745 := by
  unfold tailWord_139220
  simp only [CollatzResearch.WordTrace]
  refine ⟨2538885277818595864067557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3385180370424794485423409 2538885277818595864067557)
  ·
    refine ⟨476040989590986724512667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2538885277818595864067557 476040989590986724512667)
    ·
      refine ⟨714061484386480086769001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476040989590986724512667 714061484386480086769001)
      ·
        refine ⟨535546113289860065076751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 714061484386480086769001 535546113289860065076751)
        ·
          refine ⟨803319169934790097615127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 535546113289860065076751 803319169934790097615127)
          ·
            refine ⟨1204978754902185146422691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 803319169934790097615127 1204978754902185146422691)
            ·
              refine ⟨1807468132353277719634037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1204978754902185146422691 1807468132353277719634037)
              ·
                refine ⟨169450137408119786215691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1807468132353277719634037 169450137408119786215691)
                ·
                  refine ⟨254175206112179679323537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169450137408119786215691 254175206112179679323537)
                  ·
                    refine ⟨190631404584134759492653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 254175206112179679323537 190631404584134759492653)
                    ·
                      refine ⟨71486776719050534809745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 190631404584134759492653 71486776719050534809745)
                      ·
                        rfl

theorem cell23_139220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 5, 1, 2, 3].length) (baseStart_139220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139220 prefixEnd_139220 := by exact prefixLift 139220
  have htrace : WordTrace (prefixWord ++ tailWord_139220) baseStart_139220 baseEnd_139220 := by
    simpa [prefixWord, tailWord_139220, baseEnd_139220] using wordTrace_append hprefix tailTrace_139220
  have hstable : (prefixWord ++ tailWord_139220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139220).length < 2 ^ (prefixWord ++ tailWord_139220).sum := by decide
  have hdescent : baseEnd_139220 < baseStart_139220 := by decide
  rcases family_descends (prefixWord ++ tailWord_139220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139228 : List Nat := [2, 2, 6, 1, 2, 1, 1, 1, 3, 1, 3]
def baseStart_139228 : Nat := 118140960795 + 139228 * 2 ^ 59
def prefixEnd_139228 : Nat := 4983230072969 + 3 ^ 40 * 139228 * 2
def baseEnd_139228 : Nat := 71490884564286503509709

theorem tailTrace_139228 : CollatzResearch.WordTrace tailWord_139228 prefixEnd_139228 71490884564286503509709 := by
  unfold tailWord_139228
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539031169804104547213169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3385374893072139396284225 2539031169804104547213169)
  ·
    refine ⟨1904273377353078410409877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2539031169804104547213169 1904273377353078410409877)
    ·
      refine ⟨89262814563425550487963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1904273377353078410409877 89262814563425550487963)
      ·
        refine ⟨133894221845138325731945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 89262814563425550487963 133894221845138325731945)
        ·
          refine ⟨100420666383853744298959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 133894221845138325731945 100420666383853744298959)
          ·
            refine ⟨150630999575780616448439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 100420666383853744298959 150630999575780616448439)
            ·
              refine ⟨225946499363670924672659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150630999575780616448439 225946499363670924672659)
              ·
                refine ⟨338919749045506387008989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 225946499363670924672659 338919749045506387008989)
                ·
                  refine ⟨127094905892064895128371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 338919749045506387008989 127094905892064895128371)
                  ·
                    refine ⟨190642358838097342692557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127094905892064895128371 190642358838097342692557)
                    ·
                      refine ⟨71490884564286503509709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 190642358838097342692557 71490884564286503509709)
                      ·
                        rfl

theorem cell23_139228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_139228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139228 prefixEnd_139228 := by exact prefixLift 139228
  have htrace : WordTrace (prefixWord ++ tailWord_139228) baseStart_139228 baseEnd_139228 := by
    simpa [prefixWord, tailWord_139228, baseEnd_139228] using wordTrace_append hprefix tailTrace_139228
  have hstable : (prefixWord ++ tailWord_139228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139228).length < 2 ^ (prefixWord ++ tailWord_139228).sum := by decide
  have hdescent : baseEnd_139228 < baseStart_139228 := by decide
  rcases family_descends (prefixWord ++ tailWord_139228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139236 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_139236 : Nat := 118140960795 + 139236 * 2 ^ 59
def prefixEnd_139236 : Nat := 4983230072969 + 3 ^ 40 * 139236 * 2
def baseEnd_139236 : Nat := 23831664136507490736557

theorem tailTrace_139236 : CollatzResearch.WordTrace tailWord_139236 prefixEnd_139236 23831664136507490736557 := by
  unfold tailWord_139236
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539177061789613230358781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3385569415719484307145041 2539177061789613230358781)
  ·
    refine ⟨952191398171104961384543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2539177061789613230358781 952191398171104961384543)
    ·
      refine ⟨1428287097256657442076815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952191398171104961384543 1428287097256657442076815)
      ·
        refine ⟨2142430645884986163115223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428287097256657442076815 2142430645884986163115223)
        ·
          refine ⟨3213645968827479244672835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2142430645884986163115223 3213645968827479244672835)
          ·
            refine ⟨4820468953241218867009253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3213645968827479244672835 4820468953241218867009253)
            ·
              refine ⟨903837928732728537564235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4820468953241218867009253 903837928732728537564235)
              ·
                refine ⟨1355756893099092806346353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 903837928732728537564235 1355756893099092806346353)
                ·
                  refine ⟨1016817669824319604759765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1355756893099092806346353 1016817669824319604759765)
                  ·
                    refine ⟨23831664136507490736557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1016817669824319604759765 23831664136507490736557)
                    ·
                      rfl

theorem cell23_139236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_139236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139236 prefixEnd_139236 := by exact prefixLift 139236
  have htrace : WordTrace (prefixWord ++ tailWord_139236) baseStart_139236 baseEnd_139236 := by
    simpa [prefixWord, tailWord_139236, baseEnd_139236] using wordTrace_append hprefix tailTrace_139236
  have hstable : (prefixWord ++ tailWord_139236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139236).length < 2 ^ (prefixWord ++ tailWord_139236).sum := by decide
  have hdescent : baseEnd_139236 < baseStart_139236 := by decide
  rcases family_descends (prefixWord ++ tailWord_139236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139254 : List Nat := [5, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3]
def baseStart_139254 : Nat := 118140960795 + 139254 * 2 ^ 59
def prefixEnd_139254 : Nat := 4983230072969 + 3 ^ 40 * 139254 * 2
def baseEnd_139254 : Nat := 71504235061303401784589

theorem tailTrace_139254 : CollatzResearch.WordTrace tailWord_139254 prefixEnd_139254 71504235061303401784589 := by
  unfold tailWord_139254
  simp only [CollatzResearch.WordTrace]
  refine ⟨317438164844625970929551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3386007091676010356581877 317438164844625970929551)
  ·
    refine ⟨476157247266938956394327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 317438164844625970929551 476157247266938956394327)
    ·
      refine ⟨714235870900408434591491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476157247266938956394327 714235870900408434591491)
      ·
        refine ⟨1071353806350612651887237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714235870900408434591491 1071353806350612651887237)
        ·
          refine ⟨200878838690739872228857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1071353806350612651887237 200878838690739872228857)
          ·
            refine ⟨150659129018054904171643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 200878838690739872228857 150659129018054904171643)
            ·
              refine ⟨225988693527082356257465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150659129018054904171643 225988693527082356257465)
              ·
                refine ⟨169491520145311767193099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 225988693527082356257465 169491520145311767193099)
                ·
                  refine ⟨254237280217967650789649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169491520145311767193099 254237280217967650789649)
                  ·
                    refine ⟨190677960163475738092237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 254237280217967650789649 190677960163475738092237)
                    ·
                      refine ⟨71504235061303401784589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 190677960163475738092237 71504235061303401784589)
                      ·
                        rfl

theorem cell23_139254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 2, 1, 2, 3].length) (baseStart_139254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139254 prefixEnd_139254 := by exact prefixLift 139254
  have htrace : WordTrace (prefixWord ++ tailWord_139254) baseStart_139254 baseEnd_139254 := by
    simpa [prefixWord, tailWord_139254, baseEnd_139254] using wordTrace_append hprefix tailTrace_139254
  have hstable : (prefixWord ++ tailWord_139254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139254).length < 2 ^ (prefixWord ++ tailWord_139254).sum := by decide
  have hdescent : baseEnd_139254 < baseStart_139254 := by decide
  rcases family_descends (prefixWord ++ tailWord_139254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139260 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 3, 3, 2]
def baseStart_139260 : Nat := 118140960795 + 139260 * 2 ^ 59
def prefixEnd_139260 : Nat := 4983230072969 + 3 ^ 40 * 139260 * 2
def baseEnd_139260 : Nat := 71507315945230378309561

theorem tailTrace_139260 : CollatzResearch.WordTrace tailWord_139260 prefixEnd_139260 71507315945230378309561 := by
  unfold tailWord_139260
  simp only [CollatzResearch.WordTrace]
  refine ⟨2539614737746139279795617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3386152983661519039727489 2539614737746139279795617)
  ·
    refine ⟨1904711053309604459846713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2539614737746139279795617 1904711053309604459846713)
    ·
      refine ⟨1428533289982203344885035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1904711053309604459846713 1428533289982203344885035)
      ·
        refine ⟨2142799934973305017327553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1428533289982203344885035 2142799934973305017327553)
        ·
          refine ⟨1607099951229978762995665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2142799934973305017327553 1607099951229978762995665)
          ·
            refine ⟨1205324963422484072246749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1607099951229978762995665 1205324963422484072246749)
            ·
              refine ⟨451996861283431527092531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1205324963422484072246749 451996861283431527092531)
              ·
                refine ⟨677995291925147290638797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 451996861283431527092531 677995291925147290638797)
                ·
                  refine ⟨254248234471930233989549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 677995291925147290638797 254248234471930233989549)
                  ·
                    refine ⟨95343087926973837746081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254248234471930233989549 95343087926973837746081)
                    ·
                      refine ⟨71507315945230378309561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95343087926973837746081 71507315945230378309561)
                      ·
                        rfl

theorem cell23_139260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_139260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139260 prefixEnd_139260 := by exact prefixLift 139260
  have htrace : WordTrace (prefixWord ++ tailWord_139260) baseStart_139260 baseEnd_139260 := by
    simpa [prefixWord, tailWord_139260, baseEnd_139260] using wordTrace_append hprefix tailTrace_139260
  have hstable : (prefixWord ++ tailWord_139260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139260).length < 2 ^ (prefixWord ++ tailWord_139260).sum := by decide
  have hdescent : baseEnd_139260 < baseStart_139260 := by decide
  rcases family_descends (prefixWord ++ tailWord_139260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139300 : List Nat := [2, 3, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_139300 : Nat := 118140960795 + 139300 * 2 ^ 59
def prefixEnd_139300 : Nat := 4983230072969 + 3 ^ 40 * 139300 * 2
def baseEnd_139300 : Nat := 23842618390470073936459

theorem tailTrace_139300 : CollatzResearch.WordTrace tailWord_139300 prefixEnd_139300 23842618390470073936459 := by
  unfold tailWord_139300
  simp only [CollatzResearch.WordTrace]
  refine ⟨2540344197673682695523677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3387125596898243594031569 2540344197673682695523677)
  ·
    refine ⟨952629074127631010821379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2540344197673682695523677 952629074127631010821379)
    ·
      refine ⟨1428943611191446516232069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 952629074127631010821379 1428943611191446516232069)
      ·
        refine ⟨267926927098396221793513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1428943611191446516232069 267926927098396221793513)
        ·
          refine ⟨200945195323797166345135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 267926927098396221793513 200945195323797166345135)
          ·
            refine ⟨301417792985695749517703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 200945195323797166345135 301417792985695749517703)
            ·
              refine ⟨452126689478543624276555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301417792985695749517703 452126689478543624276555)
              ·
                refine ⟨678190034217815436414833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452126689478543624276555 678190034217815436414833)
                ·
                  refine ⟨508642525663361577311125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678190034217815436414833 508642525663361577311125)
                  ·
                    refine ⟨23842618390470073936459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 508642525663361577311125 23842618390470073936459)
                    ·
                      rfl

theorem cell23_139300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_139300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139300 prefixEnd_139300 := by exact prefixLift 139300
  have htrace : WordTrace (prefixWord ++ tailWord_139300) baseStart_139300 baseEnd_139300 := by
    simpa [prefixWord, tailWord_139300, baseEnd_139300] using wordTrace_append hprefix tailTrace_139300
  have hstable : (prefixWord ++ tailWord_139300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139300).length < 2 ^ (prefixWord ++ tailWord_139300).sum := by decide
  have hdescent : baseEnd_139300 < baseStart_139300 := by decide
  rcases family_descends (prefixWord ++ tailWord_139300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139313 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 7]
def baseStart_139313 : Nat := 118140960795 + 139313 * 2 ^ 59
def prefixEnd_139313 : Nat := 4983230072969 + 3 ^ 40 * 139313 * 2
def baseEnd_139313 : Nat := 7948281157768741216313

theorem tailTrace_139313 : CollatzResearch.WordTrace tailWord_139313 prefixEnd_139313 7948281157768741216313 := by
  unfold tailWord_139313
  simp only [CollatzResearch.WordTrace]
  refine ⟨5081162544300268611270593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3387441696200179074180395 5081162544300268611270593)
  ·
    refine ⟨3810871908225201458452945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5081162544300268611270593 3810871908225201458452945)
    ·
      refine ⟨2858153931168901093839709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3810871908225201458452945 2858153931168901093839709)
      ·
        refine ⟨1071807724188337910189891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2858153931168901093839709 1071807724188337910189891)
        ·
          refine ⟨1607711586282506865284837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1071807724188337910189891 1607711586282506865284837)
          ·
            refine ⟨301445922427970037240907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1607711586282506865284837 301445922427970037240907)
            ·
              refine ⟨452168883641955055861361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301445922427970037240907 452168883641955055861361)
              ·
                refine ⟨339126662731466291896021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 452168883641955055861361 339126662731466291896021)
                ·
                  refine ⟨7948281157768741216313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 339126662731466291896021 7948281157768741216313)
                  ·
                    rfl

theorem cell23_139313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 7].length) (baseStart_139313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139313 prefixEnd_139313 := by exact prefixLift 139313
  have htrace : WordTrace (prefixWord ++ tailWord_139313) baseStart_139313 baseEnd_139313 := by
    simpa [prefixWord, tailWord_139313, baseEnd_139313] using wordTrace_append hprefix tailTrace_139313
  have hstable : (prefixWord ++ tailWord_139313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139313).length < 2 ^ (prefixWord ++ tailWord_139313).sum := by decide
  have hdescent : baseEnd_139313 < baseStart_139313 := by decide
  rcases family_descends (prefixWord ++ tailWord_139313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139357 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 3]
def baseStart_139357 : Nat := 118140960795 + 139357 * 2 ^ 59
def prefixEnd_139357 : Nat := 4983230072969 + 3 ^ 40 * 139357 * 2
def baseEnd_139357 : Nat := 71557123568716498796615

theorem tailTrace_139357 : CollatzResearch.WordTrace tailWord_139357 prefixEnd_139357 71557123568716498796615 := by
  unfold tailWord_139357
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082767356140864125872325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3388511570760576083914883 5082767356140864125872325)
  ·
    refine ⟨953018879276412023601061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5082767356140864125872325 953018879276412023601061)
    ·
      refine ⟨178691039864327254425199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 953018879276412023601061 178691039864327254425199)
      ·
        refine ⟨268036559796490881637799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178691039864327254425199 268036559796490881637799)
        ·
          refine ⟨402054839694736322456699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268036559796490881637799 402054839694736322456699)
          ·
            refine ⟨603082259542104483685049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402054839694736322456699 603082259542104483685049)
            ·
              refine ⟨452311694656578362763787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 603082259542104483685049 452311694656578362763787)
              ·
                refine ⟨678467541984867544145681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 452311694656578362763787 678467541984867544145681)
                ·
                  refine ⟨508850656488650658109261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 678467541984867544145681 508850656488650658109261)
                  ·
                    refine ⟨190818996183243996790973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 508850656488650658109261 190818996183243996790973)
                    ·
                      refine ⟨71557123568716498796615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 190818996183243996790973 71557123568716498796615)
                      ·
                        rfl

theorem cell23_139357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_139357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139357 prefixEnd_139357 := by exact prefixLift 139357
  have htrace : WordTrace (prefixWord ++ tailWord_139357) baseStart_139357 baseEnd_139357 := by
    simpa [prefixWord, tailWord_139357, baseEnd_139357] using wordTrace_append hprefix tailTrace_139357
  have hstable : (prefixWord ++ tailWord_139357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139357).length < 2 ^ (prefixWord ++ tailWord_139357).sum := by decide
  have hdescent : baseEnd_139357 < baseStart_139357 := by decide
  rcases family_descends (prefixWord ++ tailWord_139357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139358 : List Nat := [4, 4, 1, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_139358 : Nat := 118140960795 + 139358 * 2 ^ 59
def prefixEnd_139358 : Nat := 4983230072969 + 3 ^ 40 * 139358 * 2
def baseEnd_139358 : Nat := 71557637049370994884111

theorem tailTrace_139358 : CollatzResearch.WordTrace tailWord_139358 prefixEnd_139358 71557637049370994884111 := by
  unfold tailWord_139358
  simp only [CollatzResearch.WordTrace]
  refine ⟨635350478642155162082341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3388535886091494197772485 635350478642155162082341)
  ·
    refine ⟨119128214745404092890439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 635350478642155162082341 119128214745404092890439)
    ·
      refine ⟨178692322118106139335659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119128214745404092890439 178692322118106139335659)
      ·
        refine ⟨268038483177159209003489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178692322118106139335659 268038483177159209003489)
        ·
          refine ⟨201028862382869406752617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268038483177159209003489 201028862382869406752617)
          ·
            refine ⟨150771646787152055064463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201028862382869406752617 150771646787152055064463)
            ·
              refine ⟨226157470180728082596695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150771646787152055064463 226157470180728082596695)
              ·
                refine ⟨339236205271092123895043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226157470180728082596695 339236205271092123895043)
                ·
                  refine ⟨508854307906638185842565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339236205271092123895043 508854307906638185842565)
                  ·
                    refine ⟨95410182732494659845481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 508854307906638185842565 95410182732494659845481)
                    ·
                      refine ⟨71557637049370994884111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95410182732494659845481 71557637049370994884111)
                      ·
                        rfl

theorem cell23_139358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_139358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139358 prefixEnd_139358 := by exact prefixLift 139358
  have htrace : WordTrace (prefixWord ++ tailWord_139358) baseStart_139358 baseEnd_139358 := by
    simpa [prefixWord, tailWord_139358, baseEnd_139358] using wordTrace_append hprefix tailTrace_139358
  have hstable : (prefixWord ++ tailWord_139358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139358).length < 2 ^ (prefixWord ++ tailWord_139358).sum := by decide
  have hdescent : baseEnd_139358 < baseStart_139358 := by decide
  rcases family_descends (prefixWord ++ tailWord_139358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139363 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4]
def baseStart_139363 : Nat := 118140960795 + 139363 * 2 ^ 59
def prefixEnd_139363 : Nat := 4983230072969 + 3 ^ 40 * 139363 * 2
def baseEnd_139363 : Nat := 71560204452643475321587

theorem tailTrace_139363 : CollatzResearch.WordTrace tailWord_139363 prefixEnd_139363 71560204452643475321587 := by
  unfold tailWord_139363
  simp only [CollatzResearch.WordTrace]
  refine ⟨5082986194119127150590743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3388657462746084767060495 5082986194119127150590743)
  ·
    refine ⟨7624479291178690725886115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5082986194119127150590743 7624479291178690725886115)
    ·
      refine ⟨11436718936768036088829173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7624479291178690725886115 11436718936768036088829173)
      ·
        refine ⟨1072192400322003383327735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11436718936768036088829173 1072192400322003383327735)
        ·
          refine ⟨1608288600483005074991603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1072192400322003383327735 1608288600483005074991603)
          ·
            refine ⟨2412432900724507612487405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1608288600483005074991603 2412432900724507612487405)
            ·
              refine ⟨904662337771690354682777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2412432900724507612487405 904662337771690354682777)
              ·
                refine ⟨678496753328767766012083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 904662337771690354682777 678496753328767766012083)
                ·
                  refine ⟨1017745129993151649018125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 678496753328767766012083 1017745129993151649018125)
                  ·
                    refine ⟨381654423747431868381797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1017745129993151649018125 381654423747431868381797)
                    ·
                      refine ⟨71560204452643475321587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 381654423747431868381797 71560204452643475321587)
                      ·
                        rfl

theorem cell23_139363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_139363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139363 prefixEnd_139363 := by exact prefixLift 139363
  have htrace : WordTrace (prefixWord ++ tailWord_139363) baseStart_139363 baseEnd_139363 := by
    simpa [prefixWord, tailWord_139363, baseEnd_139363] using wordTrace_append hprefix tailTrace_139363
  have hstable : (prefixWord ++ tailWord_139363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139363).length < 2 ^ (prefixWord ++ tailWord_139363).sum := by decide
  have hdescent : baseEnd_139363 < baseStart_139363 := by decide
  rcases family_descends (prefixWord ++ tailWord_139363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139373 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 2, 8]
def baseStart_139373 : Nat := 118140960795 + 139373 * 2 ^ 59
def prefixEnd_139373 : Nat := 4983230072969 + 3 ^ 40 * 139373 * 2
def baseEnd_139373 : Nat := 23855113086396145398847

theorem tailTrace_139373 : CollatzResearch.WordTrace tailWord_139373 prefixEnd_139373 23855113086396145398847 := by
  unfold tailWord_139373
  simp only [CollatzResearch.WordTrace]
  refine ⟨5083350924082898858454773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3388900616055265905636515 5083350924082898858454773)
  ·
    refine ⟨476564149132771767980135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5083350924082898858454773 476564149132771767980135)
    ·
      refine ⟨714846223699157651970203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 476564149132771767980135 714846223699157651970203)
      ·
        refine ⟨1072269335548736477955305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 714846223699157651970203 1072269335548736477955305)
        ·
          refine ⟨804202001661552358466479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1072269335548736477955305 804202001661552358466479)
          ·
            refine ⟨1206303002492328537699719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804202001661552358466479 1206303002492328537699719)
            ·
              refine ⟨1809454503738492806549579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1206303002492328537699719 1809454503738492806549579)
              ·
                refine ⟨2714181755607739209824369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1809454503738492806549579 2714181755607739209824369)
                ·
                  refine ⟨2035636316705804407368277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2714181755607739209824369 2035636316705804407368277)
                  ·
                    refine ⟨23855113086396145398847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 2035636316705804407368277 23855113086396145398847)
                    ·
                      rfl

theorem cell23_139373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 8].length) (baseStart_139373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139373 prefixEnd_139373 := by exact prefixLift 139373
  have htrace : WordTrace (prefixWord ++ tailWord_139373) baseStart_139373 baseEnd_139373 := by
    simpa [prefixWord, tailWord_139373, baseEnd_139373] using wordTrace_append hprefix tailTrace_139373
  have hstable : (prefixWord ++ tailWord_139373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139373).length < 2 ^ (prefixWord ++ tailWord_139373).sum := by decide
  have hdescent : baseEnd_139373 < baseStart_139373 := by decide
  rcases family_descends (prefixWord ++ tailWord_139373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139420 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 6]
def baseStart_139420 : Nat := 118140960795 + 139420 * 2 ^ 59
def prefixEnd_139420 : Nat := 4983230072969 + 3 ^ 40 * 139420 * 2
def baseEnd_139420 : Nat := 7954385872216639145425

theorem tailTrace_139420 : CollatzResearch.WordTrace tailWord_139420 prefixEnd_139420 7954385872216639145425 := by
  unfold tailWord_139420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2542532577456312942707857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3390043436608417256943809 2542532577456312942707857)
  ·
    refine ⟨1906899433092234707030893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2542532577456312942707857 1906899433092234707030893)
    ·
      refine ⟨715087287409588015136585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1906899433092234707030893 715087287409588015136585)
      ·
        refine ⟨536315465557191011352439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 715087287409588015136585 536315465557191011352439)
        ·
          refine ⟨804473198335786517028659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 536315465557191011352439 804473198335786517028659)
          ·
            refine ⟨1206709797503679775542989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 804473198335786517028659 1206709797503679775542989)
            ·
              refine ⟨452516174063879915828621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1206709797503679775542989 452516174063879915828621)
              ·
                refine ⟨169693565273954968435733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452516174063879915828621 169693565273954968435733)
                ·
                  refine ⟨7954385872216639145425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 169693565273954968435733 7954385872216639145425)
                  ·
                    rfl

theorem cell23_139420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_139420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139420 prefixEnd_139420 := by exact prefixLift 139420
  have htrace : WordTrace (prefixWord ++ tailWord_139420) baseStart_139420 baseEnd_139420 := by
    simpa [prefixWord, tailWord_139420, baseEnd_139420] using wordTrace_append hprefix tailTrace_139420
  have hstable : (prefixWord ++ tailWord_139420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139420).length < 2 ^ (prefixWord ++ tailWord_139420).sum := by decide
  have hdescent : baseEnd_139420 < baseStart_139420 := by decide
  rcases family_descends (prefixWord ++ tailWord_139420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139450 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_139450 : Nat := 118140960795 + 139450 * 2 ^ 59
def prefixEnd_139450 : Nat := 4983230072969 + 3 ^ 40 * 139450 * 2
def baseEnd_139450 : Nat := 23868292423194878311229

theorem tailTrace_139450 : CollatzResearch.WordTrace tailWord_139450 prefixEnd_139450 23868292423194878311229 := by
  unfold tailWord_139450
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271539836200985252251951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3390772896535960672671869 1271539836200985252251951)
  ·
    refine ⟨1907309754301477878377927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1271539836200985252251951 1907309754301477878377927)
    ·
      refine ⟨2860964631452216817566891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907309754301477878377927 2860964631452216817566891)
      ·
        refine ⟨4291446947178325226350337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2860964631452216817566891 4291446947178325226350337)
        ·
          refine ⟨3218585210383743919762753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4291446947178325226350337 3218585210383743919762753)
          ·
            refine ⟨2413938907787807939822065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3218585210383743919762753 2413938907787807939822065)
            ·
              refine ⟨1810454180840855954866549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2413938907787807939822065 1810454180840855954866549)
              ·
                refine ⟨169730079453830245768739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1810454180840855954866549 169730079453830245768739)
                ·
                  refine ⟨254595119180745368653109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169730079453830245768739 254595119180745368653109)
                  ·
                    refine ⟨23868292423194878311229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 254595119180745368653109 23868292423194878311229)
                    ·
                      rfl

theorem cell23_139450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_139450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139450 prefixEnd_139450 := by exact prefixLift 139450
  have htrace : WordTrace (prefixWord ++ tailWord_139450) baseStart_139450 baseEnd_139450 := by
    simpa [prefixWord, tailWord_139450, baseEnd_139450] using wordTrace_append hprefix tailTrace_139450
  have hstable : (prefixWord ++ tailWord_139450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139450).length < 2 ^ (prefixWord ++ tailWord_139450).sum := by decide
  have hdescent : baseEnd_139450 < baseStart_139450 := by decide
  rcases family_descends (prefixWord ++ tailWord_139450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139458 : List Nat := [3, 5, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_139458 : Nat := 118140960795 + 139458 * 2 ^ 59
def prefixEnd_139458 : Nat := 4983230072969 + 3 ^ 40 * 139458 * 2
def baseEnd_139458 : Nat := 23869661704940201211217

theorem tailTrace_139458 : CollatzResearch.WordTrace tailWord_139458 prefixEnd_139458 23869661704940201211217 := by
  unfold tailWord_139458
  simp only [CollatzResearch.WordTrace]
  refine ⟨1271612782193739593824757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3390967419183305583532685 1271612782193739593824757)
  ·
    refine ⟨119213698330663086921071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1271612782193739593824757 119213698330663086921071)
    ·
      refine ⟨178820547495994630381607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 119213698330663086921071 178820547495994630381607)
      ·
        refine ⟨268230821243991945572411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178820547495994630381607 268230821243991945572411)
        ·
          refine ⟨402346231865987918358617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 268230821243991945572411 402346231865987918358617)
          ·
            refine ⟨301759673899490938768963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 402346231865987918358617 301759673899490938768963)
            ·
              refine ⟨452639510849236408153445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 301759673899490938768963 452639510849236408153445)
              ·
                refine ⟨84869908284231826528771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 452639510849236408153445 84869908284231826528771)
                ·
                  refine ⟨127304862426347739793157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84869908284231826528771 127304862426347739793157)
                  ·
                    refine ⟨23869661704940201211217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127304862426347739793157 23869661704940201211217)
                    ·
                      rfl

theorem cell23_139458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_139458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139458 prefixEnd_139458 := by exact prefixLift 139458
  have htrace : WordTrace (prefixWord ++ tailWord_139458) baseStart_139458 baseEnd_139458 := by
    simpa [prefixWord, tailWord_139458, baseEnd_139458] using wordTrace_append hprefix tailTrace_139458
  have hstable : (prefixWord ++ tailWord_139458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139458).length < 2 ^ (prefixWord ++ tailWord_139458).sum := by decide
  have hdescent : baseEnd_139458 < baseStart_139458 := by decide
  rcases family_descends (prefixWord ++ tailWord_139458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139480 : List Nat := [2, 1, 2, 2, 4, 1, 1, 3, 1, 6]
def baseStart_139480 : Nat := 118140960795 + 139480 * 2 ^ 59
def prefixEnd_139480 : Nat := 4983230072969 + 3 ^ 40 * 139480 * 2
def baseEnd_139480 : Nat := 23873427229739839186183

theorem tailTrace_139480 : CollatzResearch.WordTrace tailWord_139480 prefixEnd_139480 23873427229739839186183 := by
  unfold tailWord_139480
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543626767347628066299947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3391502356463504088399929 2543626767347628066299947)
  ·
    refine ⟨3815440151021442099449921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2543626767347628066299947 3815440151021442099449921)
    ·
      refine ⟨2861580113266081574587441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3815440151021442099449921 2861580113266081574587441)
      ·
        refine ⟨2146185084949561180940581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2861580113266081574587441 2146185084949561180940581)
        ·
          refine ⟨402409703428042721426359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2146185084949561180940581 402409703428042721426359)
          ·
            refine ⟨603614555142064082139539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402409703428042721426359 603614555142064082139539)
            ·
              refine ⟨905421832713096123209309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603614555142064082139539 905421832713096123209309)
              ·
                refine ⟨339533187267411046203491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 905421832713096123209309 339533187267411046203491)
                ·
                  refine ⟨509299780901116569305237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339533187267411046203491 509299780901116569305237)
                  ·
                    refine ⟨23873427229739839186183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 509299780901116569305237 23873427229739839186183)
                    ·
                      rfl

theorem cell23_139480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_139480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139480 prefixEnd_139480 := by exact prefixLift 139480
  have htrace : WordTrace (prefixWord ++ tailWord_139480) baseStart_139480 baseEnd_139480 := by
    simpa [prefixWord, tailWord_139480, baseEnd_139480] using wordTrace_append hprefix tailTrace_139480
  have hstable : (prefixWord ++ tailWord_139480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139480).length < 2 ^ (prefixWord ++ tailWord_139480).sum := by decide
  have hdescent : baseEnd_139480 < baseStart_139480 := by decide
  rcases family_descends (prefixWord ++ tailWord_139480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139500 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 4]
def baseStart_139500 : Nat := 118140960795 + 139500 * 2 ^ 59
def prefixEnd_139500 : Nat := 4983230072969 + 3 ^ 40 * 139500 * 2
def baseEnd_139500 : Nat := 71630551302309439308457

theorem tailTrace_139500 : CollatzResearch.WordTrace tailWord_139500 prefixEnd_139500 71630551302309439308457 := by
  unfold tailWord_139500
  simp only [CollatzResearch.WordTrace]
  refine ⟨2543991497311399774163977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3391988663081866365551969 2543991497311399774163977)
  ·
    refine ⟨1907993622983549830622983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2543991497311399774163977 1907993622983549830622983)
    ·
      refine ⟨2861990434475324745934475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1907993622983549830622983 2861990434475324745934475)
      ·
        refine ⟨4292985651712987118901713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2861990434475324745934475 4292985651712987118901713)
        ·
          refine ⟨3219739238784740339176285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4292985651712987118901713 3219739238784740339176285)
          ·
            refine ⟨1207402214544277627191107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3219739238784740339176285 1207402214544277627191107)
            ·
              refine ⟨1811103321816416440786661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207402214544277627191107 1811103321816416440786661)
              ·
                refine ⟨339581872840578082647499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1811103321816416440786661 339581872840578082647499)
                ·
                  refine ⟨509372809260867123971249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339581872840578082647499 509372809260867123971249)
                  ·
                    refine ⟨382029606945650342978437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 509372809260867123971249 382029606945650342978437)
                    ·
                      refine ⟨71630551302309439308457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 382029606945650342978437 71630551302309439308457)
                      ·
                        rfl

theorem cell23_139500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 2, 4].length) (baseStart_139500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139500 prefixEnd_139500 := by exact prefixLift 139500
  have htrace : WordTrace (prefixWord ++ tailWord_139500) baseStart_139500 baseEnd_139500 := by
    simpa [prefixWord, tailWord_139500, baseEnd_139500] using wordTrace_append hprefix tailTrace_139500
  have hstable : (prefixWord ++ tailWord_139500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139500).length < 2 ^ (prefixWord ++ tailWord_139500).sum := by decide
  have hdescent : baseEnd_139500 < baseStart_139500 := by decide
  rcases family_descends (prefixWord ++ tailWord_139500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139501 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 1, 5]
def baseStart_139501 : Nat := 118140960795 + 139501 * 2 ^ 59
def prefixEnd_139501 : Nat := 4983230072969 + 3 ^ 40 * 139501 * 2
def baseEnd_139501 : Nat := 23877021594321311798651

theorem tailTrace_139501 : CollatzResearch.WordTrace tailWord_139501 prefixEnd_139501 23877021594321311798651 := by
  unfold tailWord_139501
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088019467619176719114357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3392012978412784479409571 5088019467619176719114357)
  ·
    refine ⟨477001825089297817416971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5088019467619176719114357 477001825089297817416971)
    ·
      refine ⟨715502737633946726125457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477001825089297817416971 715502737633946726125457)
      ·
        refine ⟨536627053225460044594093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 715502737633946726125457 536627053225460044594093)
        ·
          refine ⟨201235144959547516722785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 536627053225460044594093 201235144959547516722785)
          ·
            refine ⟨150926358719660637542089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 201235144959547516722785 150926358719660637542089)
            ·
              refine ⟨113194769039745478156567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 150926358719660637542089 113194769039745478156567)
              ·
                refine ⟨169792153559618217234851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113194769039745478156567 169792153559618217234851)
                ·
                  refine ⟨254688230339427325852277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169792153559618217234851 254688230339427325852277)
                  ·
                    refine ⟨23877021594321311798651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 254688230339427325852277 23877021594321311798651)
                    ·
                      rfl

theorem cell23_139501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 1, 5].length) (baseStart_139501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139501 prefixEnd_139501 := by exact prefixLift 139501
  have htrace : WordTrace (prefixWord ++ tailWord_139501) baseStart_139501 baseEnd_139501 := by
    simpa [prefixWord, tailWord_139501, baseEnd_139501] using wordTrace_append hprefix tailTrace_139501
  have hstable : (prefixWord ++ tailWord_139501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139501).length < 2 ^ (prefixWord ++ tailWord_139501).sum := by decide
  have hdescent : baseEnd_139501 < baseStart_139501 := by decide
  rcases family_descends (prefixWord ++ tailWord_139501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139507 : List Nat := [1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 3]
def baseStart_139507 : Nat := 118140960795 + 139507 * 2 ^ 59
def prefixEnd_139507 : Nat := 4983230072969 + 3 ^ 40 * 139507 * 2
def baseEnd_139507 : Nat := 71634145666890911920925

theorem tailTrace_139507 : CollatzResearch.WordTrace tailWord_139507 prefixEnd_139507 71634145666890911920925 := by
  unfold tailWord_139507
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088238305597439743832775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3392158870398293162555183 5088238305597439743832775)
  ·
    refine ⟨7632357458396159615749163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5088238305597439743832775 7632357458396159615749163)
    ·
      refine ⟨11448536187594239423623745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7632357458396159615749163 11448536187594239423623745)
      ·
        refine ⟨8586402140695679567717809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11448536187594239423623745 8586402140695679567717809)
        ·
          refine ⟨6439801605521759675788357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8586402140695679567717809 6439801605521759675788357)
          ·
            refine ⟨1207462801035329939210317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6439801605521759675788357 1207462801035329939210317)
            ·
              refine ⟨452798550388248727203869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1207462801035329939210317 452798550388248727203869)
              ·
                refine ⟨169799456395593272701451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452798550388248727203869 169799456395593272701451)
                ·
                  refine ⟨254699184593389909052177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169799456395593272701451 254699184593389909052177)
                  ·
                    refine ⟨191024388445042431789133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 254699184593389909052177 191024388445042431789133)
                    ·
                      refine ⟨71634145666890911920925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191024388445042431789133 71634145666890911920925)
                      ·
                        rfl

theorem cell23_139507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 3, 1, 2, 3].length) (baseStart_139507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139507 prefixEnd_139507 := by exact prefixLift 139507
  have htrace : WordTrace (prefixWord ++ tailWord_139507) baseStart_139507 baseEnd_139507 := by
    simpa [prefixWord, tailWord_139507, baseEnd_139507] using wordTrace_append hprefix tailTrace_139507
  have hstable : (prefixWord ++ tailWord_139507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139507).length < 2 ^ (prefixWord ++ tailWord_139507).sum := by decide
  have hdescent : baseEnd_139507 < baseStart_139507 := by decide
  rcases family_descends (prefixWord ++ tailWord_139507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139514 : List Nat := [3, 1, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_139514 : Nat := 118140960795 + 139514 * 2 ^ 59
def prefixEnd_139514 : Nat := 4983230072969 + 3 ^ 40 * 139514 * 2
def baseEnd_139514 : Nat := 23879246677157461511131

theorem tailTrace_139514 : CollatzResearch.WordTrace tailWord_139514 prefixEnd_139514 23879246677157461511131 := by
  unfold tailWord_139514
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272123404143019984834399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3392329077714719959558397 1272123404143019984834399)
  ·
    refine ⟨1908185106214529977251599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1272123404143019984834399 1908185106214529977251599)
    ·
      refine ⟨2862277659321794965877399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1908185106214529977251599 2862277659321794965877399)
      ·
        refine ⟨4293416488982692448816099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862277659321794965877399 4293416488982692448816099)
        ·
          refine ⟨6440124733474038673224149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293416488982692448816099 6440124733474038673224149)
          ·
            refine ⟨150940423440797781403691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 6440124733474038673224149 150940423440797781403691)
            ·
              refine ⟨226410635161196672105537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 150940423440797781403691 226410635161196672105537)
              ·
                refine ⟨169807976370897504079153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226410635161196672105537 169807976370897504079153)
                ·
                  refine ⟨127355982278173128059365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169807976370897504079153 127355982278173128059365)
                  ·
                    refine ⟨23879246677157461511131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127355982278173128059365 23879246677157461511131)
                    ·
                      rfl

theorem cell23_139514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_139514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139514 prefixEnd_139514 := by exact prefixLift 139514
  have htrace : WordTrace (prefixWord ++ tailWord_139514) baseStart_139514 baseEnd_139514 := by
    simpa [prefixWord, tailWord_139514, baseEnd_139514] using wordTrace_append hprefix tailTrace_139514
  have hstable : (prefixWord ++ tailWord_139514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139514).length < 2 ^ (prefixWord ++ tailWord_139514).sum := by decide
  have hdescent : baseEnd_139514 < baseStart_139514 := by decide
  rcases family_descends (prefixWord ++ tailWord_139514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139520 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3]
def baseStart_139520 : Nat := 118140960795 + 139520 * 2 ^ 59
def prefixEnd_139520 : Nat := 4983230072969 + 3 ^ 40 * 139520 * 2
def baseEnd_139520 : Nat := 71640820915399361058365

theorem tailTrace_139520 : CollatzResearch.WordTrace tailWord_139520 prefixEnd_139520 71640820915399361058365 := by
  unfold tailWord_139520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2544356227275171482028007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3392474969700228642704009 2544356227275171482028007)
  ·
    refine ⟨3816534340912757223042011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2544356227275171482028007 3816534340912757223042011)
    ·
      refine ⟨5724801511369135834563017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3816534340912757223042011 5724801511369135834563017)
      ·
        refine ⟨4293601133526851875922263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5724801511369135834563017 4293601133526851875922263)
        ·
          refine ⟨6440401700290277813883395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4293601133526851875922263 6440401700290277813883395)
          ·
            refine ⟨9660602550435416720825093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6440401700290277813883395 9660602550435416720825093)
            ·
              refine ⟨1811362978206640635154705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9660602550435416720825093 1811362978206640635154705)
              ·
                refine ⟨1358522233654980476366029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1811362978206640635154705 1358522233654980476366029)
                ·
                  refine ⟨509445837620617678637261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1358522233654980476366029 509445837620617678637261)
                  ·
                    refine ⟨191042189107731629488973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509445837620617678637261 191042189107731629488973)
                    ·
                      refine ⟨71640820915399361058365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191042189107731629488973 71640820915399361058365)
                      ·
                        rfl

theorem cell23_139520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 3, 3, 3].length) (baseStart_139520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139520 prefixEnd_139520 := by exact prefixLift 139520
  have htrace : WordTrace (prefixWord ++ tailWord_139520) baseStart_139520 baseEnd_139520 := by
    simpa [prefixWord, tailWord_139520, baseEnd_139520] using wordTrace_append hprefix tailTrace_139520
  have hstable : (prefixWord ++ tailWord_139520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139520).length < 2 ^ (prefixWord ++ tailWord_139520).sum := by decide
  have hdescent : baseEnd_139520 < baseStart_139520 := by decide
  rcases family_descends (prefixWord ++ tailWord_139520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139521 : List Nat := [1, 2, 4, 1, 1, 2, 1, 6, 1, 2, 2]
def baseStart_139521 : Nat := 118140960795 + 139521 * 2 ^ 59
def prefixEnd_139521 : Nat := 4983230072969 + 3 ^ 40 * 139521 * 2
def baseEnd_139521 : Nat := 71641334396053857145861

theorem tailTrace_139521 : CollatzResearch.WordTrace tailWord_139521 prefixEnd_139521 71641334396053857145861 := by
  unfold tailWord_139521
  simp only [CollatzResearch.WordTrace]
  refine ⟨5088748927546720134842417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3392499285031146756561611 5088748927546720134842417)
  ·
    refine ⟨3816561695660040101131813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5088748927546720134842417 3816561695660040101131813)
    ·
      refine ⟨715605317936257518962215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3816561695660040101131813 715605317936257518962215)
      ·
        refine ⟨1073407976904386278443323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715605317936257518962215 1073407976904386278443323)
        ·
          refine ⟨1610111965356579417664985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073407976904386278443323 1610111965356579417664985)
          ·
            refine ⟨1207583974017434563248739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610111965356579417664985 1207583974017434563248739)
            ·
              refine ⟨1811375961026151844873109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1207583974017434563248739 1811375961026151844873109)
              ·
                refine ⟨84908248173100867728427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1811375961026151844873109 84908248173100867728427)
                ·
                  refine ⟨127362372259651301592641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 84908248173100867728427 127362372259651301592641)
                  ·
                    refine ⟨95521779194738476194481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127362372259651301592641 95521779194738476194481)
                    ·
                      refine ⟨71641334396053857145861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95521779194738476194481 71641334396053857145861)
                      ·
                        rfl

theorem cell23_139521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 6, 1, 2, 2].length) (baseStart_139521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139521 prefixEnd_139521 := by exact prefixLift 139521
  have htrace : WordTrace (prefixWord ++ tailWord_139521) baseStart_139521 baseEnd_139521 := by
    simpa [prefixWord, tailWord_139521, baseEnd_139521] using wordTrace_append hprefix tailTrace_139521
  have hstable : (prefixWord ++ tailWord_139521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139521).length < 2 ^ (prefixWord ++ tailWord_139521).sum := by decide
  have hdescent : baseEnd_139521 < baseStart_139521 := by decide
  rcases family_descends (prefixWord ++ tailWord_139521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139537 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 3]
def baseStart_139537 : Nat := 118140960795 + 139537 * 2 ^ 59
def prefixEnd_139537 : Nat := 4983230072969 + 3 ^ 40 * 139537 * 2
def baseEnd_139537 : Nat := 71649550086525794545787

theorem tailTrace_139537 : CollatzResearch.WordTrace tailWord_139537 prefixEnd_139537 71649550086525794545787 := by
  unfold tailWord_139537
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089332495488754867424865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3392888330325836578283243 5089332495488754867424865)
  ·
    refine ⟨3816999371616566150568649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5089332495488754867424865 3816999371616566150568649)
    ·
      refine ⟨2862749528712424612926487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3816999371616566150568649 2862749528712424612926487)
      ·
        refine ⟨4294124293068636919389731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2862749528712424612926487 4294124293068636919389731)
        ·
          refine ⟨6441186439602955379084597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294124293068636919389731 6441186439602955379084597)
          ·
            refine ⟨603861228712777066789181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6441186439602955379084597 603861228712777066789181)
            ·
              refine ⟨226447960767291400045943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 603861228712777066789181 226447960767291400045943)
              ·
                refine ⟨339671941150937100068915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 226447960767291400045943 339671941150937100068915)
                ·
                  refine ⟨509507911726405650103373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 339671941150937100068915 509507911726405650103373)
                  ·
                    refine ⟨191065466897402118788765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 509507911726405650103373 191065466897402118788765)
                    ·
                      refine ⟨71649550086525794545787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191065466897402118788765 71649550086525794545787)
                      ·
                        rfl

theorem cell23_139537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 3, 3].length) (baseStart_139537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139537 prefixEnd_139537 := by exact prefixLift 139537
  have htrace : WordTrace (prefixWord ++ tailWord_139537) baseStart_139537 baseEnd_139537 := by
    simpa [prefixWord, tailWord_139537, baseEnd_139537] using wordTrace_append hprefix tailTrace_139537
  have hstable : (prefixWord ++ tailWord_139537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139537).length < 2 ^ (prefixWord ++ tailWord_139537).sum := by decide
  have hdescent : baseEnd_139537 < baseStart_139537 := by decide
  rcases family_descends (prefixWord ++ tailWord_139537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139547 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 3, 3, 2]
def baseStart_139547 : Nat := 118140960795 + 139547 * 2 ^ 59
def prefixEnd_139547 : Nat := 4983230072969 + 3 ^ 40 * 139547 * 2
def baseEnd_139547 : Nat := 71654684893070755420741

theorem tailTrace_139547 : CollatzResearch.WordTrace tailWord_139547 prefixEnd_139547 71654684893070755420741 := by
  unfold tailWord_139547
  simp only [CollatzResearch.WordTrace]
  refine ⟨5089697225452526575288895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3393131483635017716859263 5089697225452526575288895)
  ·
    refine ⟨7634545838178789862933343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5089697225452526575288895 7634545838178789862933343)
    ·
      refine ⟨11451818757268184794400015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7634545838178789862933343 11451818757268184794400015)
      ·
        refine ⟨17177728135902277191600023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11451818757268184794400015 17177728135902277191600023)
        ·
          refine ⟨25766592203853415787400035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17177728135902277191600023 25766592203853415787400035)
          ·
            refine ⟨38649888305780123681100053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25766592203853415787400035 38649888305780123681100053)
            ·
              refine ⟨1811713514333443297551565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38649888305780123681100053 1811713514333443297551565)
              ·
                refine ⟨679392567875041236581837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1811713514333443297551565 679392567875041236581837)
                ·
                  refine ⟨254772212953140463718189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 679392567875041236581837 254772212953140463718189)
                  ·
                    refine ⟨95539579857427673894321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254772212953140463718189 95539579857427673894321)
                    ·
                      refine ⟨71654684893070755420741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95539579857427673894321 71654684893070755420741)
                      ·
                        rfl

theorem cell23_139547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 3, 3, 2].length) (baseStart_139547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139547 prefixEnd_139547 := by exact prefixLift 139547
  have htrace : WordTrace (prefixWord ++ tailWord_139547) baseStart_139547 baseEnd_139547 := by
    simpa [prefixWord, tailWord_139547, baseEnd_139547] using wordTrace_append hprefix tailTrace_139547
  have hstable : (prefixWord ++ tailWord_139547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139547).length < 2 ^ (prefixWord ++ tailWord_139547).sum := by decide
  have hdescent : baseEnd_139547 < baseStart_139547 := by decide
  rcases family_descends (prefixWord ++ tailWord_139547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139554 : List Nat := [3, 3, 1, 1, 3, 1, 1, 2, 4, 1, 3]
def baseStart_139554 : Nat := 118140960795 + 139554 * 2 ^ 59
def prefixEnd_139554 : Nat := 4983230072969 + 3 ^ 40 * 139554 * 2
def baseEnd_139554 : Nat := 71658279257652228033209

theorem tailTrace_139554 : CollatzResearch.WordTrace tailWord_139554 prefixEnd_139554 71658279257652228033209 := by
  unfold tailWord_139554
  simp only [CollatzResearch.WordTrace]
  refine ⟨1272488134106791692698429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3393301690951444513862477 1272488134106791692698429)
  ·
    refine ⟨477183050290046884761911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1272488134106791692698429 477183050290046884761911)
    ·
      refine ⟨715774575435070327142867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 477183050290046884761911 715774575435070327142867)
      ·
        refine ⟨1073661863152605490714301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 715774575435070327142867 1073661863152605490714301)
        ·
          refine ⟨402623198682227059017863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1073661863152605490714301 402623198682227059017863)
          ·
            refine ⟨603934798023340588526795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 402623198682227059017863 603934798023340588526795)
            ·
              refine ⟨905902197035010882790193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 603934798023340588526795 905902197035010882790193)
              ·
                refine ⟨679426647776258162092645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 905902197035010882790193 679426647776258162092645)
                ·
                  refine ⟨127392496458048405392371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 679426647776258162092645 127392496458048405392371)
                  ·
                    refine ⟨191088744687072608088557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127392496458048405392371 191088744687072608088557)
                    ·
                      refine ⟨71658279257652228033209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191088744687072608088557 71658279257652228033209)
                      ·
                        rfl

theorem cell23_139554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 2, 4, 1, 3].length) (baseStart_139554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139554 prefixEnd_139554 := by exact prefixLift 139554
  have htrace : WordTrace (prefixWord ++ tailWord_139554) baseStart_139554 baseEnd_139554 := by
    simpa [prefixWord, tailWord_139554, baseEnd_139554] using wordTrace_append hprefix tailTrace_139554
  have hstable : (prefixWord ++ tailWord_139554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139554).length < 2 ^ (prefixWord ++ tailWord_139554).sum := by decide
  have hdescent : baseEnd_139554 < baseStart_139554 := by decide
  rcases family_descends (prefixWord ++ tailWord_139554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139564 : List Nat := [2, 2, 1, 1, 1, 3, 4, 3, 1, 3, 2]
def baseStart_139564 : Nat := 118140960795 + 139564 * 2 ^ 59
def prefixEnd_139564 : Nat := 4983230072969 + 3 ^ 40 * 139564 * 2
def baseEnd_139564 : Nat := 71663414064197188908163

theorem tailTrace_139564 : CollatzResearch.WordTrace tailWord_139564 prefixEnd_139564 71663414064197188908163 := by
  unfold tailWord_139564
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545158633195469239328873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3393544844260625652438497 2545158633195469239328873)
  ·
    refine ⟨1908868974896601929496655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2545158633195469239328873 1908868974896601929496655)
    ·
      refine ⟨2863303462344902894244983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1908868974896601929496655 2863303462344902894244983)
      ·
        refine ⟨4294955193517354341367475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2863303462344902894244983 4294955193517354341367475)
        ·
          refine ⟨6442432790276031512051213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4294955193517354341367475 6442432790276031512051213)
          ·
            refine ⟨2415912296353511817019205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6442432790276031512051213 2415912296353511817019205)
            ·
              refine ⟨452983555566283465691101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2415912296353511817019205 452983555566283465691101)
              ·
                refine ⟨169868833337356299634163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 452983555566283465691101 169868833337356299634163)
                ·
                  refine ⟨254803250006034449451245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 169868833337356299634163 254803250006034449451245)
                  ·
                    refine ⟨95551218752262918544217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 254803250006034449451245 95551218752262918544217)
                    ·
                      refine ⟨71663414064197188908163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95551218752262918544217 71663414064197188908163)
                      ·
                        rfl

theorem cell23_139564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 3, 2].length) (baseStart_139564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139564 prefixEnd_139564 := by exact prefixLift 139564
  have htrace : WordTrace (prefixWord ++ tailWord_139564) baseStart_139564 baseEnd_139564 := by
    simpa [prefixWord, tailWord_139564, baseEnd_139564] using wordTrace_append hprefix tailTrace_139564
  have hstable : (prefixWord ++ tailWord_139564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139564).length < 2 ^ (prefixWord ++ tailWord_139564).sum := by decide
  have hdescent : baseEnd_139564 < baseStart_139564 := by decide
  rcases family_descends (prefixWord ++ tailWord_139564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139580 : List Nat := [2, 2, 2, 2, 1, 2, 1, 2, 1, 3, 5]
def baseStart_139580 : Nat := 118140960795 + 139580 * 2 ^ 59
def prefixEnd_139580 : Nat := 4983230072969 + 3 ^ 40 * 139580 * 2
def baseEnd_139580 : Nat := 71671629754669126308089

theorem tailTrace_139580 : CollatzResearch.WordTrace tailWord_139580 prefixEnd_139580 71671629754669126308089 := by
  unfold tailWord_139580
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545450417166486605620097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3393933889555315474160129 2545450417166486605620097)
  ·
    refine ⟨1909087812874864954215073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2545450417166486605620097 1909087812874864954215073)
    ·
      refine ⟨1431815859656148715661305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1909087812874864954215073 1431815859656148715661305)
      ·
        refine ⟨1073861894742111536745979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1431815859656148715661305 1073861894742111536745979)
        ·
          refine ⟨1610792842113167305118969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1073861894742111536745979 1610792842113167305118969)
          ·
            refine ⟨1208094631584875478839227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1610792842113167305118969 1208094631584875478839227)
            ·
              refine ⟨1812141947377313218258841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1208094631584875478839227 1812141947377313218258841)
              ·
                refine ⟨1359106460532984913694131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1812141947377313218258841 1359106460532984913694131)
                ·
                  refine ⟨2038659690799477370541197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1359106460532984913694131 2038659690799477370541197)
                  ·
                    refine ⟨764497384049804013952949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2038659690799477370541197 764497384049804013952949)
                    ·
                      refine ⟨71671629754669126308089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 764497384049804013952949 71671629754669126308089)
                      ·
                        rfl

theorem cell23_139580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_139580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139580 prefixEnd_139580 := by exact prefixLift 139580
  have htrace : WordTrace (prefixWord ++ tailWord_139580) baseStart_139580 baseEnd_139580 := by
    simpa [prefixWord, tailWord_139580, baseEnd_139580] using wordTrace_append hprefix tailTrace_139580
  have hstable : (prefixWord ++ tailWord_139580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139580).length < 2 ^ (prefixWord ++ tailWord_139580).sum := by decide
  have hdescent : baseEnd_139580 < baseStart_139580 := by decide
  rcases family_descends (prefixWord ++ tailWord_139580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139588 : List Nat := [2, 3, 4, 1, 2, 1, 1, 3, 2, 1, 3]
def baseStart_139588 : Nat := 118140960795 + 139588 * 2 ^ 59
def prefixEnd_139588 : Nat := 4983230072969 + 3 ^ 40 * 139588 * 2
def baseEnd_139588 : Nat := 71675737599905095008053

theorem tailTrace_139588 : CollatzResearch.WordTrace tailWord_139588 prefixEnd_139588 71675737599905095008053 := by
  unfold tailWord_139588
  simp only [CollatzResearch.WordTrace]
  refine ⟨2545596309151995288765709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3394128412202660385020945 2545596309151995288765709)
  ·
    refine ⟨954598615931998233287141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2545596309151995288765709 954598615931998233287141)
    ·
      refine ⟨178987240487249668741339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 954598615931998233287141 178987240487249668741339)
      ·
        refine ⟨268480860730874503112009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 178987240487249668741339 268480860730874503112009)
        ·
          refine ⟨201360645548155877334007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 268480860730874503112009 201360645548155877334007)
          ·
            refine ⟨302040968322233816001011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201360645548155877334007 302040968322233816001011)
            ·
              refine ⟨453061452483350724001517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302040968322233816001011 453061452483350724001517)
              ·
                refine ⟨169898044681256521500569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 453061452483350724001517 169898044681256521500569)
                ·
                  refine ⟨127423533510942391125427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169898044681256521500569 127423533510942391125427)
                  ·
                    refine ⟨191135300266413586688141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127423533510942391125427 191135300266413586688141)
                    ·
                      refine ⟨71675737599905095008053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191135300266413586688141 71675737599905095008053)
                      ·
                        rfl

theorem cell23_139588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_139588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139588 prefixEnd_139588 := by exact prefixLift 139588
  have htrace : WordTrace (prefixWord ++ tailWord_139588) baseStart_139588 baseEnd_139588 := by
    simpa [prefixWord, tailWord_139588, baseEnd_139588] using wordTrace_append hprefix tailTrace_139588
  have hstable : (prefixWord ++ tailWord_139588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139588).length < 2 ^ (prefixWord ++ tailWord_139588).sum := by decide
  have hdescent : baseEnd_139588 < baseStart_139588 := by decide
  rcases family_descends (prefixWord ++ tailWord_139588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139628 : List Nat := [2, 2, 1, 1, 6, 1, 2, 2, 2, 2, 2]
def baseStart_139628 : Nat := 118140960795 + 139628 * 2 ^ 59
def prefixEnd_139628 : Nat := 4983230072969 + 3 ^ 40 * 139628 * 2
def baseEnd_139628 : Nat := 71696276826084938507869

theorem tailTrace_139628 : CollatzResearch.WordTrace tailWord_139628 prefixEnd_139628 71696276826084938507869 := by
  unfold tailWord_139628
  simp only [CollatzResearch.WordTrace]
  refine ⟨2546325769079538704493769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3395101025439384939325025 2546325769079538704493769)
  ·
    refine ⟨1909744326809654028370327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2546325769079538704493769 1909744326809654028370327)
    ·
      refine ⟨2864616490214481042555491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1909744326809654028370327 2864616490214481042555491)
      ·
        refine ⟨4296924735321721563833237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2864616490214481042555491 4296924735321721563833237)
        ·
          refine ⟨201418346968205698304683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 4296924735321721563833237 201418346968205698304683)
          ·
            refine ⟨302127520452308547457025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201418346968205698304683 302127520452308547457025)
            ·
              refine ⟨226595640339231410592769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302127520452308547457025 226595640339231410592769)
              ·
                refine ⟨169946730254423557944577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 226595640339231410592769 169946730254423557944577)
                ·
                  refine ⟨127460047690817668458433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 169946730254423557944577 127460047690817668458433)
                  ·
                    refine ⟨95595035768113251343825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127460047690817668458433 95595035768113251343825)
                    ·
                      refine ⟨71696276826084938507869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95595035768113251343825 71696276826084938507869)
                      ·
                        rfl

theorem cell23_139628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 2, 2].length) (baseStart_139628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139628 prefixEnd_139628 := by exact prefixLift 139628
  have htrace : WordTrace (prefixWord ++ tailWord_139628) baseStart_139628 baseEnd_139628 := by
    simpa [prefixWord, tailWord_139628, baseEnd_139628] using wordTrace_append hprefix tailTrace_139628
  have hstable : (prefixWord ++ tailWord_139628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139628).length < 2 ^ (prefixWord ++ tailWord_139628).sum := by decide
  have hdescent : baseEnd_139628 < baseStart_139628 := by decide
  rcases family_descends (prefixWord ++ tailWord_139628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139634 : List Nat := [3, 2, 1, 2, 1, 4, 1, 4, 5]
def baseStart_139634 : Nat := 118140960795 + 139634 * 2 ^ 59
def prefixEnd_139634 : Nat := 4983230072969 + 3 ^ 40 * 139634 * 2
def baseEnd_139634 : Nat := 7966595301112435003649

theorem tailTrace_139634 : CollatzResearch.WordTrace tailWord_139634 prefixEnd_139634 7966595301112435003649 := by
  unfold tailWord_139634
  simp only [CollatzResearch.WordTrace]
  refine ⟨1273217594034335108426489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3395246917424893622470637 1273217594034335108426489)
  ·
    refine ⟨954913195525751331319867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1273217594034335108426489 954913195525751331319867)
    ·
      refine ⟨1432369793288626996979801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 954913195525751331319867 1432369793288626996979801)
      ·
        refine ⟨1074277344966470247734851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1432369793288626996979801 1074277344966470247734851)
        ·
          refine ⟨1611416017449705371602277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074277344966470247734851 1611416017449705371602277)
          ·
            refine ⟨302140503271819757175427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1611416017449705371602277 302140503271819757175427)
            ·
              refine ⟨453210754907729635763141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302140503271819757175427 453210754907729635763141)
              ·
                refine ⟨84977016545199306705589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 453210754907729635763141 84977016545199306705589)
                ·
                  refine ⟨7966595301112435003649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 84977016545199306705589 7966595301112435003649)
                  ·
                    rfl

theorem cell23_139634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_139634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139634 prefixEnd_139634 := by exact prefixLift 139634
  have htrace : WordTrace (prefixWord ++ tailWord_139634) baseStart_139634 baseEnd_139634 := by
    simpa [prefixWord, tailWord_139634, baseEnd_139634] using wordTrace_append hprefix tailTrace_139634
  have hstable : (prefixWord ++ tailWord_139634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139634).length < 2 ^ (prefixWord ++ tailWord_139634).sum := by decide
  have hdescent : baseEnd_139634 < baseStart_139634 := by decide
  rcases family_descends (prefixWord ++ tailWord_139634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139684 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 2, 4, 2]
def baseStart_139684 : Nat := 118140960795 + 139684 * 2 ^ 59
def prefixEnd_139684 : Nat := 4983230072969 + 3 ^ 40 * 139684 * 2
def baseEnd_139684 : Nat := 71725031742736719407611

theorem tailTrace_139684 : CollatzResearch.WordTrace tailWord_139684 prefixEnd_139684 71725031742736719407611 := by
  unfold tailWord_139684
  simp only [CollatzResearch.WordTrace]
  refine ⟨2547347012978099486513053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3396462683970799315350737 2547347012978099486513053)
  ·
    refine ⟨955255129866787307442395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2547347012978099486513053 955255129866787307442395)
    ·
      refine ⟨1432882694800180961163593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 955255129866787307442395 1432882694800180961163593)
      ·
        refine ⟨1074662021100135720872695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1432882694800180961163593 1074662021100135720872695)
        ·
          refine ⟨1611993031650203581309043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1074662021100135720872695 1611993031650203581309043)
          ·
            refine ⟨2417989547475305371963565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1611993031650203581309043 2417989547475305371963565)
            ·
              refine ⟨906746080303239514486337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2417989547475305371963565 906746080303239514486337)
              ·
                refine ⟨680059560227429635864753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 906746080303239514486337 680059560227429635864753)
                ·
                  refine ⟨510044670170572226898565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 680059560227429635864753 510044670170572226898565)
                  ·
                    refine ⟨95633375656982292543481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 510044670170572226898565 95633375656982292543481)
                    ·
                      refine ⟨71725031742736719407611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95633375656982292543481 71725031742736719407611)
                      ·
                        rfl

theorem cell23_139684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_139684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139684 prefixEnd_139684 := by exact prefixLift 139684
  have htrace : WordTrace (prefixWord ++ tailWord_139684) baseStart_139684 baseEnd_139684 := by
    simpa [prefixWord, tailWord_139684, baseEnd_139684] using wordTrace_append hprefix tailTrace_139684
  have hstable : (prefixWord ++ tailWord_139684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139684).length < 2 ^ (prefixWord ++ tailWord_139684).sum := by decide
  have hdescent : baseEnd_139684 < baseStart_139684 := by decide
  rcases family_descends (prefixWord ++ tailWord_139684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139824 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3]
def baseStart_139824 : Nat := 118140960795 + 139824 * 2 ^ 59
def prefixEnd_139824 : Nat := 4983230072969 + 3 ^ 40 * 139824 * 2
def baseEnd_139824 : Nat := 71796919034366171656967

theorem tailTrace_139824 : CollatzResearch.WordTrace tailWord_139824 prefixEnd_139824 71796919034366171656967 := by
  unfold tailWord_139824
  simp only [CollatzResearch.WordTrace]
  refine ⟨2549900122724501441561263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3399866830299335255415017 2549900122724501441561263)
  ·
    refine ⟨3824850184086752162341895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2549900122724501441561263 3824850184086752162341895)
    ·
      refine ⟨5737275276130128243512843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3824850184086752162341895 5737275276130128243512843)
      ·
        refine ⟨8605912914195192365269265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5737275276130128243512843 8605912914195192365269265)
        ·
          refine ⟨6454434685646394273951949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8605912914195192365269265 6454434685646394273951949)
          ·
            refine ⟨2420413007117397852731981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6454434685646394273951949 2420413007117397852731981)
            ·
              refine ⟨907654877669024194774493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2420413007117397852731981 907654877669024194774493)
              ·
                refine ⟨340370579125884073040435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 907654877669024194774493 340370579125884073040435)
                ·
                  refine ⟨510555868688826109560653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340370579125884073040435 510555868688826109560653)
                  ·
                    refine ⟨191458450758309791085245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510555868688826109560653 191458450758309791085245)
                    ·
                      refine ⟨71796919034366171656967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191458450758309791085245 71796919034366171656967)
                      ·
                        rfl

theorem cell23_139824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 1, 3, 3].length) (baseStart_139824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139824 prefixEnd_139824 := by exact prefixLift 139824
  have htrace : WordTrace (prefixWord ++ tailWord_139824) baseStart_139824 baseEnd_139824 := by
    simpa [prefixWord, tailWord_139824, baseEnd_139824] using wordTrace_append hprefix tailTrace_139824
  have hstable : (prefixWord ++ tailWord_139824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139824).length < 2 ^ (prefixWord ++ tailWord_139824).sum := by decide
  have hdescent : baseEnd_139824 < baseStart_139824 := by decide
  rcases family_descends (prefixWord ++ tailWord_139824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139827 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 2, 7]
def baseStart_139827 : Nat := 118140960795 + 139827 * 2 ^ 59
def prefixEnd_139827 : Nat := 4983230072969 + 3 ^ 40 * 139827 * 2
def baseEnd_139827 : Nat := 23932819825443219973151

theorem tailTrace_139827 : CollatzResearch.WordTrace tailWord_139827 prefixEnd_139827 23932819825443219973151 := by
  unfold tailWord_139827
  simp only [CollatzResearch.WordTrace]
  refine ⟨5099909664438134395481735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3399939776292089596987823 5099909664438134395481735)
  ·
    refine ⟨7649864496657201593222603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5099909664438134395481735 7649864496657201593222603)
    ·
      refine ⟨11474796744985802389833905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7649864496657201593222603 11474796744985802389833905)
      ·
        refine ⟨8606097558739351792375429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11474796744985802389833905 8606097558739351792375429)
        ·
          refine ⟨1613643292263628461070393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8606097558739351792375429 1613643292263628461070393)
          ·
            refine ⟨1210232469197721345802795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1613643292263628461070393 1210232469197721345802795)
            ·
              refine ⟨1815348703796582018704193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1210232469197721345802795 1815348703796582018704193)
              ·
                refine ⟨1361511527847436514028145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1815348703796582018704193 1361511527847436514028145)
                ·
                  refine ⟨1021133645885577385521109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1361511527847436514028145 1021133645885577385521109)
                  ·
                    refine ⟨23932819825443219973151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1021133645885577385521109 23932819825443219973151)
                    ·
                      rfl

theorem cell23_139827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 7].length) (baseStart_139827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139827 prefixEnd_139827 := by exact prefixLift 139827
  have htrace : WordTrace (prefixWord ++ tailWord_139827) baseStart_139827 baseEnd_139827 := by
    simpa [prefixWord, tailWord_139827, baseEnd_139827] using wordTrace_append hprefix tailTrace_139827
  have hstable : (prefixWord ++ tailWord_139827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139827).length < 2 ^ (prefixWord ++ tailWord_139827).sum := by decide
  have hdescent : baseEnd_139827 < baseStart_139827 := by decide
  rcases family_descends (prefixWord ++ tailWord_139827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139841 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 3]
def baseStart_139841 : Nat := 118140960795 + 139841 * 2 ^ 59
def prefixEnd_139841 : Nat := 4983230072969 + 3 ^ 40 * 139841 * 2
def baseEnd_139841 : Nat := 71805648205492605144389

theorem tailTrace_139841 : CollatzResearch.WordTrace tailWord_139841 prefixEnd_139841 71805648205492605144389 := by
  unfold tailWord_139841
  simp only [CollatzResearch.WordTrace]
  refine ⟨5100420286387414786491377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3400280190924943190994251 5100420286387414786491377)
  ·
    refine ⟨3825315214790561089868533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5100420286387414786491377 3825315214790561089868533)
    ·
      refine ⟨358623301386615102175175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3825315214790561089868533 358623301386615102175175)
      ·
        refine ⟨537934952079922653262763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 358623301386615102175175 537934952079922653262763)
        ·
          refine ⟨806902428119883979894145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 537934952079922653262763 806902428119883979894145)
          ·
            refine ⟨605176821089912984920609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 806902428119883979894145 605176821089912984920609)
            ·
              refine ⟨453882615817434738690457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 605176821089912984920609 453882615817434738690457)
              ·
                refine ⟨340411961863076054017843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 453882615817434738690457 340411961863076054017843)
                ·
                  refine ⟨510617942794614081026765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 340411961863076054017843 510617942794614081026765)
                  ·
                    refine ⟨191481728547980280385037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 510617942794614081026765 191481728547980280385037)
                    ·
                      refine ⟨71805648205492605144389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191481728547980280385037 71805648205492605144389)
                      ·
                        rfl

theorem cell23_139841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_139841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139841 prefixEnd_139841 := by exact prefixLift 139841
  have htrace : WordTrace (prefixWord ++ tailWord_139841) baseStart_139841 baseEnd_139841 := by
    simpa [prefixWord, tailWord_139841, baseEnd_139841] using wordTrace_append hprefix tailTrace_139841
  have hstable : (prefixWord ++ tailWord_139841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139841).length < 2 ^ (prefixWord ++ tailWord_139841).sum := by decide
  have hdescent : baseEnd_139841 < baseStart_139841 := by decide
  rcases family_descends (prefixWord ++ tailWord_139841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139884 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 3]
def baseStart_139884 : Nat := 118140960795 + 139884 * 2 ^ 59
def prefixEnd_139884 : Nat := 4983230072969 + 3 ^ 40 * 139884 * 2
def baseEnd_139884 : Nat := 71827727873635936906691

theorem tailTrace_139884 : CollatzResearch.WordTrace tailWord_139884 prefixEnd_139884 71827727873635936906691 := by
  unfold tailWord_139884
  simp only [CollatzResearch.WordTrace]
  refine ⟨2550994312615816565153353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3401325750154422086871137 2550994312615816565153353)
  ·
    refine ⟨1913245734461862423865015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2550994312615816565153353 1913245734461862423865015)
    ·
      refine ⟨2869868601692793635797523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1913245734461862423865015 2869868601692793635797523)
      ·
        refine ⟨4304802902539190453696285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2869868601692793635797523 4304802902539190453696285)
        ·
          refine ⟨1614301088452196420136107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4304802902539190453696285 1614301088452196420136107)
          ·
            refine ⟨2421451632678294630204161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1614301088452196420136107 2421451632678294630204161)
            ·
              refine ⟨1816088724508720972653121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2421451632678294630204161 1816088724508720972653121)
              ·
                refine ⟨1362066543381540729489841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1816088724508720972653121 1362066543381540729489841)
                ·
                  refine ⟨1021549907536155547117381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1362066543381540729489841 1021549907536155547117381)
                  ·
                    refine ⟨191540607663029165084509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1021549907536155547117381 191540607663029165084509)
                    ·
                      refine ⟨71827727873635936906691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191540607663029165084509 71827727873635936906691)
                      ·
                        rfl

theorem cell23_139884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 3].length) (baseStart_139884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139884 prefixEnd_139884 := by exact prefixLift 139884
  have htrace : WordTrace (prefixWord ++ tailWord_139884) baseStart_139884 baseEnd_139884 := by
    simpa [prefixWord, tailWord_139884, baseEnd_139884] using wordTrace_append hprefix tailTrace_139884
  have hstable : (prefixWord ++ tailWord_139884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139884).length < 2 ^ (prefixWord ++ tailWord_139884).sum := by decide
  have hdescent : baseEnd_139884 < baseStart_139884 := by decide
  rcases family_descends (prefixWord ++ tailWord_139884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139885 : List Nat := [1, 5, 1, 1, 3, 2, 2, 2, 1, 3, 2]
def baseStart_139885 : Nat := 118140960795 + 139885 * 2 ^ 59
def prefixEnd_139885 : Nat := 4983230072969 + 3 ^ 40 * 139885 * 2
def baseEnd_139885 : Nat := 71828241354290432994187

theorem tailTrace_139885 : CollatzResearch.WordTrace tailWord_139885 prefixEnd_139885 71828241354290432994187 := by
  unfold tailWord_139885
  simp only [CollatzResearch.WordTrace]
  refine ⟨5102025098228010301093109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3401350065485340200728739 5102025098228010301093109)
  ·
    refine ⟨478314852958875965727479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5102025098228010301093109 478314852958875965727479)
    ·
      refine ⟨717472279438313948591219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 478314852958875965727479 717472279438313948591219)
      ·
        refine ⟨1076208419157470922886829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 717472279438313948591219 1076208419157470922886829)
        ·
          refine ⟨403578157184051596082561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1076208419157470922886829 403578157184051596082561)
          ·
            refine ⟨302683617888038697061921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 403578157184051596082561 302683617888038697061921)
            ·
              refine ⟨227012713416029022796441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302683617888038697061921 227012713416029022796441)
              ·
                refine ⟨170259535062021767097331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227012713416029022796441 170259535062021767097331)
                ·
                  refine ⟨255389302593032650645997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170259535062021767097331 255389302593032650645997)
                  ·
                    refine ⟨95770988472387243992249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 255389302593032650645997 95770988472387243992249)
                    ·
                      refine ⟨71828241354290432994187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95770988472387243992249 71828241354290432994187)
                      ·
                        rfl

theorem cell23_139885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 2, 2, 1, 3, 2].length) (baseStart_139885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139885 prefixEnd_139885 := by exact prefixLift 139885
  have htrace : WordTrace (prefixWord ++ tailWord_139885) baseStart_139885 baseEnd_139885 := by
    simpa [prefixWord, tailWord_139885, baseEnd_139885] using wordTrace_append hprefix tailTrace_139885
  have hstable : (prefixWord ++ tailWord_139885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139885).length < 2 ^ (prefixWord ++ tailWord_139885).sum := by decide
  have hdescent : baseEnd_139885 < baseStart_139885 := by decide
  rcases family_descends (prefixWord ++ tailWord_139885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139901 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 5]
def baseStart_139901 : Nat := 118140960795 + 139901 * 2 ^ 59
def prefixEnd_139901 : Nat := 4983230072969 + 3 ^ 40 * 139901 * 2
def baseEnd_139901 : Nat := 71836457044762370394113

theorem tailTrace_139901 : CollatzResearch.WordTrace tailWord_139901 prefixEnd_139901 71836457044762370394113 := by
  unfold tailWord_139901
  simp only [CollatzResearch.WordTrace]
  refine ⟨5102608666170045033675557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3401739110780030022450371 5102608666170045033675557)
  ·
    refine ⟨956739124906883443814167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5102608666170045033675557 956739124906883443814167)
    ·
      refine ⟨1435108687360325165721251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 956739124906883443814167 1435108687360325165721251)
      ·
        refine ⟨2152663031040487748581877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1435108687360325165721251 2152663031040487748581877)
        ·
          refine ⟨201812159160045726429551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2152663031040487748581877 201812159160045726429551)
          ·
            refine ⟨302718238740068589644327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201812159160045726429551 302718238740068589644327)
            ·
              refine ⟨454077358110102884466491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302718238740068589644327 454077358110102884466491)
              ·
                refine ⟨681116037165154326699737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454077358110102884466491 681116037165154326699737)
                ·
                  refine ⟨510837027873865745024803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 681116037165154326699737 510837027873865745024803)
                  ·
                    refine ⟨766255541810798617537205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 510837027873865745024803 766255541810798617537205)
                    ·
                      refine ⟨71836457044762370394113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 766255541810798617537205 71836457044762370394113)
                      ·
                        rfl

theorem cell23_139901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 1, 5].length) (baseStart_139901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139901 prefixEnd_139901 := by exact prefixLift 139901
  have htrace : WordTrace (prefixWord ++ tailWord_139901) baseStart_139901 baseEnd_139901 := by
    simpa [prefixWord, tailWord_139901, baseEnd_139901] using wordTrace_append hprefix tailTrace_139901
  have hstable : (prefixWord ++ tailWord_139901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139901).length < 2 ^ (prefixWord ++ tailWord_139901).sum := by decide
  have hdescent : baseEnd_139901 < baseStart_139901 := by decide
  rcases family_descends (prefixWord ++ tailWord_139901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139932 : List Nat := [2, 2, 3, 2, 2, 1, 4, 1, 2, 2, 2]
def baseStart_139932 : Nat := 118140960795 + 139932 * 2 ^ 59
def prefixEnd_139932 : Nat := 4983230072969 + 3 ^ 40 * 139932 * 2
def baseEnd_139932 : Nat := 71852374945051749106471

theorem tailTrace_139932 : CollatzResearch.WordTrace tailWord_139932 prefixEnd_139932 71852374945051749106471 := by
  unfold tailWord_139932
  simp only [CollatzResearch.WordTrace]
  refine ⟨2551869664528868664027025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3402492886038491552036033 2551869664528868664027025)
  ·
    refine ⟨1913902248396651498020269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2551869664528868664027025 1913902248396651498020269)
    ·
      refine ⟨717713343148744311757601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1913902248396651498020269 717713343148744311757601)
      ·
        refine ⟨538285007361558233818201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 717713343148744311757601 538285007361558233818201)
        ·
          refine ⟨403713755521168675363651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 538285007361558233818201 403713755521168675363651)
          ·
            refine ⟨605570633281753013045477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 403713755521168675363651 605570633281753013045477)
            ·
              refine ⟨113544493740328689946027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 605570633281753013045477 113544493740328689946027)
              ·
                refine ⟨170316740610493034919041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113544493740328689946027 170316740610493034919041)
                ·
                  refine ⟨127737555457869776189281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170316740610493034919041 127737555457869776189281)
                  ·
                    refine ⟨95803166593402332141961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127737555457869776189281 95803166593402332141961)
                    ·
                      refine ⟨71852374945051749106471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95803166593402332141961 71852374945051749106471)
                      ·
                        rfl

theorem cell23_139932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_139932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139932 prefixEnd_139932 := by exact prefixLift 139932
  have htrace : WordTrace (prefixWord ++ tailWord_139932) baseStart_139932 baseEnd_139932 := by
    simpa [prefixWord, tailWord_139932, baseEnd_139932] using wordTrace_append hprefix tailTrace_139932
  have hstable : (prefixWord ++ tailWord_139932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139932).length < 2 ^ (prefixWord ++ tailWord_139932).sum := by decide
  have hdescent : baseEnd_139932 < baseStart_139932 := by decide
  rcases family_descends (prefixWord ++ tailWord_139932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_139951 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 2, 5]
def baseStart_139951 : Nat := 118140960795 + 139951 * 2 ^ 59
def prefixEnd_139951 : Nat := 4983230072969 + 3 ^ 40 * 139951 * 2
def baseEnd_139951 : Nat := 23954043692495724922961

theorem tailTrace_139951 : CollatzResearch.WordTrace tailWord_139951 prefixEnd_139951 23954043692495724922961 := by
  unfold tailWord_139951
  simp only [CollatzResearch.WordTrace]
  refine ⟨5104432315988903572995707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3402954877325935715330471 5104432315988903572995707)
  ·
    refine ⟨7656648473983355359493561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5104432315988903572995707 7656648473983355359493561)
    ·
      refine ⟨5742486355487516519620171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7656648473983355359493561 5742486355487516519620171)
      ·
        refine ⟨8613729533231274779430257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5742486355487516519620171 8613729533231274779430257)
        ·
          refine ⟨6460297149923456084572693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8613729533231274779430257 6460297149923456084572693)
          ·
            refine ⟨302826428902662003964345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6460297149923456084572693 302826428902662003964345)
            ·
              refine ⟨227119821676996502973259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302826428902662003964345 227119821676996502973259)
              ·
                refine ⟨340679732515494754459889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 227119821676996502973259 340679732515494754459889)
                ·
                  refine ⟨255509799386621065844917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 340679732515494754459889 255509799386621065844917)
                  ·
                    refine ⟨23954043692495724922961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 255509799386621065844917 23954043692495724922961)
                    ·
                      rfl

theorem cell23_139951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 5].length) (baseStart_139951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_139951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_139951 prefixEnd_139951 := by exact prefixLift 139951
  have htrace : WordTrace (prefixWord ++ tailWord_139951) baseStart_139951 baseEnd_139951 := by
    simpa [prefixWord, tailWord_139951, baseEnd_139951] using wordTrace_append hprefix tailTrace_139951
  have hstable : (prefixWord ++ tailWord_139951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_139951).length < 2 ^ (prefixWord ++ tailWord_139951).sum := by decide
  have hdescent : baseEnd_139951 < baseStart_139951 := by decide
  rcases family_descends (prefixWord ++ tailWord_139951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140008 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_140008 : Nat := 118140960795 + 140008 * 2 ^ 59
def prefixEnd_140008 : Nat := 4983230072969 + 3 ^ 40 * 140008 * 2
def baseEnd_140008 : Nat := 71891399474793451756121

theorem tailTrace_140008 : CollatzResearch.WordTrace tailWord_140008 prefixEnd_140008 71891399474793451756121 := by
  unfold tailWord_140008
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553255638391201153910339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3404340851188268205213785 2553255638391201153910339)
  ·
    refine ⟨3829883457586801730865509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2553255638391201153910339 3829883457586801730865509)
    ·
      refine ⟨718103148297525324537283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3829883457586801730865509 718103148297525324537283)
      ·
        refine ⟨1077154722446287986805925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 718103148297525324537283 1077154722446287986805925)
        ·
          refine ⟨201966510458678997526111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1077154722446287986805925 201966510458678997526111)
          ·
            refine ⟨302949765688018496289167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 201966510458678997526111 302949765688018496289167)
            ·
              refine ⟨454424648532027744433751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 302949765688018496289167 454424648532027744433751)
              ·
                refine ⟨681636972798041616650627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 454424648532027744433751 681636972798041616650627)
                ·
                  refine ⟨1022455459197062424975941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 681636972798041616650627 1022455459197062424975941)
                  ·
                    refine ⟨191710398599449204682989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1022455459197062424975941 191710398599449204682989)
                    ·
                      refine ⟨71891399474793451756121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191710398599449204682989 71891399474793451756121)
                      ·
                        rfl

theorem cell23_140008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_140008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140008 prefixEnd_140008 := by exact prefixLift 140008
  have htrace : WordTrace (prefixWord ++ tailWord_140008) baseStart_140008 baseEnd_140008 := by
    simpa [prefixWord, tailWord_140008, baseEnd_140008] using wordTrace_append hprefix tailTrace_140008
  have hstable : (prefixWord ++ tailWord_140008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140008).length < 2 ^ (prefixWord ++ tailWord_140008).sum := by decide
  have hdescent : baseEnd_140008 < baseStart_140008 := by decide
  rcases family_descends (prefixWord ++ tailWord_140008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140015 : List Nat := [1, 1, 2, 1, 5, 3, 2, 3, 1, 4]
def baseStart_140015 : Nat := 118140960795 + 140015 * 2 ^ 59
def prefixEnd_140015 : Nat := 4983230072969 + 3 ^ 40 * 140015 * 2
def baseEnd_140015 : Nat := 23964997946458308122863

theorem tailTrace_140015 : CollatzResearch.WordTrace tailWord_140015 prefixEnd_140015 23964997946458308122863 := by
  unfold tailWord_140015
  simp only [CollatzResearch.WordTrace]
  refine ⟨5106766587757042503325499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3404511058504695002216999 5106766587757042503325499)
  ·
    refine ⟨7660149881635563754988249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5106766587757042503325499 7660149881635563754988249)
    ·
      refine ⟨5745112411226672816241187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7660149881635563754988249 5745112411226672816241187)
      ·
        refine ⟨8617668616840009224361781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5745112411226672816241187 8617668616840009224361781)
        ·
          refine ⟨807906432828750864783917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8617668616840009224361781 807906432828750864783917)
          ·
            refine ⟨302964912310781574293969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 807906432828750864783917 302964912310781574293969)
            ·
              refine ⟨227223684233086180720477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 302964912310781574293969 227223684233086180720477)
              ·
                refine ⟨85208881587407317770179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227223684233086180720477 85208881587407317770179)
                ·
                  refine ⟨127813322381110976655269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85208881587407317770179 127813322381110976655269)
                  ·
                    refine ⟨23964997946458308122863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127813322381110976655269 23964997946458308122863)
                    ·
                      rfl

theorem cell23_140015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 3, 1, 4].length) (baseStart_140015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140015 prefixEnd_140015 := by exact prefixLift 140015
  have htrace : WordTrace (prefixWord ++ tailWord_140015) baseStart_140015 baseEnd_140015 := by
    simpa [prefixWord, tailWord_140015, baseEnd_140015] using wordTrace_append hprefix tailTrace_140015
  have hstable : (prefixWord ++ tailWord_140015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140015).length < 2 ^ (prefixWord ++ tailWord_140015).sum := by decide
  have hdescent : baseEnd_140015 < baseStart_140015 := by decide
  rcases family_descends (prefixWord ++ tailWord_140015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140028 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 6]
def baseStart_140028 : Nat := 118140960795 + 140028 * 2 ^ 59
def prefixEnd_140028 : Nat := 4983230072969 + 3 ^ 40 * 140028 * 2
def baseEnd_140028 : Nat := 7989074343098152611781

theorem tailTrace_140028 : CollatzResearch.WordTrace tailWord_140028 prefixEnd_140028 7989074343098152611781 := by
  unfold tailWord_140028
  simp only [CollatzResearch.WordTrace]
  refine ⟨2553620368354972861774369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3404827157806630482365825 2553620368354972861774369)
  ·
    refine ⟨1915215276266229646330777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2553620368354972861774369 1915215276266229646330777)
    ·
      refine ⟨1436411457199672234748083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1915215276266229646330777 1436411457199672234748083)
      ·
        refine ⟨2154617185799508352122125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1436411457199672234748083 2154617185799508352122125)
        ·
          refine ⟨807981444674815632045797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2154617185799508352122125 807981444674815632045797)
          ·
            refine ⟨151496520876527931008587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 807981444674815632045797 151496520876527931008587)
            ·
              refine ⟨227244781314791896512881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151496520876527931008587 227244781314791896512881)
              ·
                refine ⟨170433585986093922384661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227244781314791896512881 170433585986093922384661)
                ·
                  refine ⟨7989074343098152611781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 170433585986093922384661 7989074343098152611781)
                  ·
                    rfl

theorem cell23_140028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_140028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140028 prefixEnd_140028 := by exact prefixLift 140028
  have htrace : WordTrace (prefixWord ++ tailWord_140028) baseStart_140028 baseEnd_140028 := by
    simpa [prefixWord, tailWord_140028, baseEnd_140028] using wordTrace_append hprefix tailTrace_140028
  have hstable : (prefixWord ++ tailWord_140028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140028).length < 2 ^ (prefixWord ++ tailWord_140028).sum := by decide
  have hdescent : baseEnd_140028 < baseStart_140028 := by decide
  rcases family_descends (prefixWord ++ tailWord_140028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140058 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_140058 : Nat := 118140960795 + 140058 * 2 ^ 59
def prefixEnd_140058 : Nat := 4983230072969 + 3 ^ 40 * 140058 * 2
def baseEnd_140058 : Nat := 23972357835839418710297

theorem tailTrace_140058 : CollatzResearch.WordTrace tailWord_140058 prefixEnd_140058 23972357835839418710297 := by
  unfold tailWord_140058
  simp only [CollatzResearch.WordTrace]
  refine ⟨1277083731650315211785207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3405556617734173898093885 1277083731650315211785207)
  ·
    refine ⟨1915625597475472817677811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1277083731650315211785207 1915625597475472817677811)
    ·
      refine ⟨2873438396213209226516717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1915625597475472817677811 2873438396213209226516717)
      ·
        refine ⟨1077539398579953459943769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2873438396213209226516717 1077539398579953459943769)
        ·
          refine ⟨808154548934965094957827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1077539398579953459943769 808154548934965094957827)
          ·
            refine ⟨1212231823402447642436741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808154548934965094957827 1212231823402447642436741)
            ·
              refine ⟨227293466887958932956889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1212231823402447642436741 227293466887958932956889)
              ·
                refine ⟨170470100165969199717667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227293466887958932956889 170470100165969199717667)
                ·
                  refine ⟨255705150248953799576501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170470100165969199717667 255705150248953799576501)
                  ·
                    refine ⟨23972357835839418710297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 255705150248953799576501 23972357835839418710297)
                    ·
                      rfl

theorem cell23_140058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_140058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140058 prefixEnd_140058 := by exact prefixLift 140058
  have htrace : WordTrace (prefixWord ++ tailWord_140058) baseStart_140058 baseEnd_140058 := by
    simpa [prefixWord, tailWord_140058, baseEnd_140058] using wordTrace_append hprefix tailTrace_140058
  have hstable : (prefixWord ++ tailWord_140058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140058).length < 2 ^ (prefixWord ++ tailWord_140058).sum := by decide
  have hdescent : baseEnd_140058 < baseStart_140058 := by decide
  rcases family_descends (prefixWord ++ tailWord_140058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140088 : List Nat := [2, 1, 2, 1, 3, 2, 2, 4, 2, 4]
def baseStart_140088 : Nat := 118140960795 + 140088 * 2 ^ 59
def prefixEnd_140088 : Nat := 4983230072969 + 3 ^ 40 * 140088 * 2
def baseEnd_140088 : Nat := 23977492642384379585251

theorem tailTrace_140088 : CollatzResearch.WordTrace tailWord_140088 prefixEnd_140088 23977492642384379585251 := by
  unfold tailWord_140088
  simp only [CollatzResearch.WordTrace]
  refine ⟨2554714558246287985366459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3406286077661717313821945 2554714558246287985366459)
  ·
    refine ⟨3832071837369431978049689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2554714558246287985366459 3832071837369431978049689)
    ·
      refine ⟨2874053878027073983537267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3832071837369431978049689 2874053878027073983537267)
      ·
        refine ⟨4311080817040610975305901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2874053878027073983537267 4311080817040610975305901)
        ·
          refine ⟨1616655306390229115739713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4311080817040610975305901 1616655306390229115739713)
          ·
            refine ⟨1212491479792671836804785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1616655306390229115739713 1212491479792671836804785)
            ·
              refine ⟨909368609844503877603589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1212491479792671836804785 909368609844503877603589)
              ·
                refine ⟨170506614345844477050673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 909368609844503877603589 170506614345844477050673)
                ·
                  refine ⟨127879960759383357788005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170506614345844477050673 127879960759383357788005)
                  ·
                    refine ⟨23977492642384379585251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127879960759383357788005 23977492642384379585251)
                    ·
                      rfl

theorem cell23_140088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_140088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140088 prefixEnd_140088 := by exact prefixLift 140088
  have htrace : WordTrace (prefixWord ++ tailWord_140088) baseStart_140088 baseEnd_140088 := by
    simpa [prefixWord, tailWord_140088, baseEnd_140088] using wordTrace_append hprefix tailTrace_140088
  have hstable : (prefixWord ++ tailWord_140088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140088).length < 2 ^ (prefixWord ++ tailWord_140088).sum := by decide
  have hdescent : baseEnd_140088 < baseStart_140088 := by decide
  rcases family_descends (prefixWord ++ tailWord_140088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140105 : List Nat := [1, 2, 1, 1, 2, 5, 4, 1, 2, 4]
def baseStart_140105 : Nat := 118140960795 + 140105 * 2 ^ 59
def prefixEnd_140105 : Nat := 4983230072969 + 3 ^ 40 * 140105 * 2
def baseEnd_140105 : Nat := 23980402366093190747725

theorem tailTrace_140105 : CollatzResearch.WordTrace tailWord_140105 prefixEnd_140105 23980402366093190747725 := by
  unfold tailWord_140105
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110049157430987874101769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3406699438287325249401179 5110049157430987874101769)
  ·
    refine ⟨3832536868073240905576327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5110049157430987874101769 3832536868073240905576327)
    ·
      refine ⟨5748805302109861358364491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3832536868073240905576327 5748805302109861358364491)
      ·
        refine ⟨8623207953164792037546737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5748805302109861358364491 8623207953164792037546737)
        ·
          refine ⟨6467405964873594028160053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8623207953164792037546737 6467405964873594028160053)
          ·
            refine ⟨606319309206899440140005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 6467405964873594028160053 606319309206899440140005)
            ·
              refine ⟨113684870476293645026251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 606319309206899440140005 113684870476293645026251)
              ·
                refine ⟨170527305714440467539377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113684870476293645026251 170527305714440467539377)
                ·
                  refine ⟨127895479285830350654533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170527305714440467539377 127895479285830350654533)
                  ·
                    refine ⟨23980402366093190747725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 127895479285830350654533 23980402366093190747725)
                    ·
                      rfl

theorem cell23_140105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 4, 1, 2, 4].length) (baseStart_140105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140105 prefixEnd_140105 := by exact prefixLift 140105
  have htrace : WordTrace (prefixWord ++ tailWord_140105) baseStart_140105 baseEnd_140105 := by
    simpa [prefixWord, tailWord_140105, baseEnd_140105] using wordTrace_append hprefix tailTrace_140105
  have hstable : (prefixWord ++ tailWord_140105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140105).length < 2 ^ (prefixWord ++ tailWord_140105).sum := by decide
  have hdescent : baseEnd_140105 < baseStart_140105 := by decide
  rcases family_descends (prefixWord ++ tailWord_140105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140109 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 1, 5]
def baseStart_140109 : Nat := 118140960795 + 140109 * 2 ^ 59
def prefixEnd_140109 : Nat := 4983230072969 + 3 ^ 40 * 140109 * 2
def baseEnd_140109 : Nat := 23981087006965852197719

theorem tailTrace_140109 : CollatzResearch.WordTrace tailWord_140109 prefixEnd_140109 23981087006965852197719 := by
  unfold tailWord_140109
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110195049416496557247381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3406796699610997704831587 5110195049416496557247381)
  ·
    refine ⟨239540392941398276120971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 5110195049416496557247381 239540392941398276120971)
    ·
      refine ⟨359310589412097414181457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 239540392941398276120971 359310589412097414181457)
      ·
        refine ⟨269482942059073060636093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 359310589412097414181457 269482942059073060636093)
        ·
          refine ⟨101056103272152397738535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 269482942059073060636093 101056103272152397738535)
          ·
            refine ⟨151584154908228596607803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101056103272152397738535 151584154908228596607803)
            ·
              refine ⟨227376232362342894911705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 151584154908228596607803 227376232362342894911705)
              ·
                refine ⟨170532174271757171183779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 227376232362342894911705 170532174271757171183779)
                ·
                  refine ⟨255798261407635756775669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170532174271757171183779 255798261407635756775669)
                  ·
                    refine ⟨23981087006965852197719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 255798261407635756775669 23981087006965852197719)
                    ·
                      rfl

theorem cell23_140109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_140109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140109 prefixEnd_140109 := by exact prefixLift 140109
  have htrace : WordTrace (prefixWord ++ tailWord_140109) baseStart_140109 baseEnd_140109 := by
    simpa [prefixWord, tailWord_140109, baseEnd_140109] using wordTrace_append hprefix tailTrace_140109
  have hstable : (prefixWord ++ tailWord_140109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140109).length < 2 ^ (prefixWord ++ tailWord_140109).sum := by decide
  have hdescent : baseEnd_140109 < baseStart_140109 := by decide
  rcases family_descends (prefixWord ++ tailWord_140109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140111 : List Nat := [1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 3]
def baseStart_140111 : Nat := 118140960795 + 140111 * 2 ^ 59
def prefixEnd_140111 : Nat := 4983230072969 + 3 ^ 40 * 140111 * 2
def baseEnd_140111 : Nat := 71944287982206548768147

theorem tailTrace_140111 : CollatzResearch.WordTrace tailWord_140111 prefixEnd_140111 71944287982206548768147 := by
  unfold tailWord_140111
  simp only [CollatzResearch.WordTrace]
  refine ⟨5110267995409250898820187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3406845330272833932546791 5110267995409250898820187)
  ·
    refine ⟨7665401993113876348230281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5110267995409250898820187 7665401993113876348230281)
    ·
      refine ⟨5749051494835407261172711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7665401993113876348230281 5749051494835407261172711)
      ·
        refine ⟨8623577242253110891759067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5749051494835407261172711 8623577242253110891759067)
        ·
          refine ⟨12935365863379666337638601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8623577242253110891759067 12935365863379666337638601)
          ·
            refine ⟨9701524397534749753228951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12935365863379666337638601 9701524397534749753228951)
            ·
              refine ⟨14552286596302124629843427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9701524397534749753228951 14552286596302124629843427)
              ·
                refine ⟨21828429894453186944765141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14552286596302124629843427 21828429894453186944765141)
                ·
                  refine ⟨511603825651246569017933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 21828429894453186944765141 511603825651246569017933)
                  ·
                    refine ⟨191851434619217463381725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511603825651246569017933 191851434619217463381725)
                    ·
                      refine ⟨71944287982206548768147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191851434619217463381725 71944287982206548768147)
                      ·
                        rfl

theorem cell23_140111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_140111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140111 prefixEnd_140111 := by exact prefixLift 140111
  have htrace : WordTrace (prefixWord ++ tailWord_140111) baseStart_140111 baseEnd_140111 := by
    simpa [prefixWord, tailWord_140111, baseEnd_140111] using wordTrace_append hprefix tailTrace_140111
  have hstable : (prefixWord ++ tailWord_140111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140111).length < 2 ^ (prefixWord ++ tailWord_140111).sum := by decide
  have hdescent : baseEnd_140111 < baseStart_140111 := by decide
  rcases family_descends (prefixWord ++ tailWord_140111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140128 : List Nat := [2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3]
def baseStart_140128 : Nat := 118140960795 + 140128 * 2 ^ 59
def prefixEnd_140128 : Nat := 4983230072969 + 3 ^ 40 * 140128 * 2
def baseEnd_140128 : Nat := 71953017153332982255569

theorem tailTrace_140128 : CollatzResearch.WordTrace tailWord_140128 prefixEnd_140128 71953017153332982255569 := by
  unfold tailWord_140128
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555444018173831401094519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3407258690898441868126025 2555444018173831401094519)
  ·
    refine ⟨3833166027260747101641779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2555444018173831401094519 3833166027260747101641779)
    ·
      refine ⟨5749749040891120652462669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3833166027260747101641779 5749749040891120652462669)
      ·
        refine ⟨2156155890334170244673501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5749749040891120652462669 2156155890334170244673501)
        ·
          refine ⟨808558458875313841752563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2156155890334170244673501 808558458875313841752563)
          ·
            refine ⟨1212837688312970762628845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 808558458875313841752563 1212837688312970762628845)
            ·
              refine ⟨454814133117364035985817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1212837688312970762628845 454814133117364035985817)
              ·
                refine ⟨341110599838023026989363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 454814133117364035985817 341110599838023026989363)
                ·
                  refine ⟨511665899757034540484045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 341110599838023026989363 511665899757034540484045)
                  ·
                    refine ⟨191874712408887952681517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511665899757034540484045 191874712408887952681517)
                    ·
                      refine ⟨71953017153332982255569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191874712408887952681517 71953017153332982255569)
                      ·
                        rfl

theorem cell23_140128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 3].length) (baseStart_140128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140128 prefixEnd_140128 := by exact prefixLift 140128
  have htrace : WordTrace (prefixWord ++ tailWord_140128) baseStart_140128 baseEnd_140128 := by
    simpa [prefixWord, tailWord_140128, baseEnd_140128] using wordTrace_append hprefix tailTrace_140128
  have hstable : (prefixWord ++ tailWord_140128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140128).length < 2 ^ (prefixWord ++ tailWord_140128).sum := by decide
  have hdescent : baseEnd_140128 < baseStart_140128 := by decide
  rcases family_descends (prefixWord ++ tailWord_140128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140132 : List Nat := [2, 3, 1, 1, 4, 2, 3, 1, 1, 2, 3]
def baseStart_140132 : Nat := 118140960795 + 140132 * 2 ^ 59
def prefixEnd_140132 : Nat := 4983230072969 + 3 ^ 40 * 140132 * 2
def baseEnd_140132 : Nat := 71955071075950966605551

theorem tailTrace_140132 : CollatzResearch.WordTrace tailWord_140132 prefixEnd_140132 71955071075950966605551 := by
  unfold tailWord_140132
  simp only [CollatzResearch.WordTrace]
  refine ⟨2555516964166585742667325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3407355952222114323556433 2555516964166585742667325)
  ·
    refine ⟨958318861562469653500247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2555516964166585742667325 958318861562469653500247)
    ·
      refine ⟨1437478292343704480250371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 958318861562469653500247 1437478292343704480250371)
      ·
        refine ⟨2156217438515556720375557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1437478292343704480250371 2156217438515556720375557)
        ·
          refine ⟨404290769721666885070417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2156217438515556720375557 404290769721666885070417)
          ·
            refine ⟨303218077291250163802813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 404290769721666885070417 303218077291250163802813)
            ·
              refine ⟨113706778984218811426055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303218077291250163802813 113706778984218811426055)
              ·
                refine ⟨170560168476328217139083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113706778984218811426055 170560168476328217139083)
                ·
                  refine ⟨255840252714492325708625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170560168476328217139083 255840252714492325708625)
                  ·
                    refine ⟨191880189535869244281469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 255840252714492325708625 191880189535869244281469)
                    ·
                      refine ⟨71955071075950966605551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191880189535869244281469 71955071075950966605551)
                      ·
                        rfl

theorem cell23_140132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 3, 1, 1, 2, 3].length) (baseStart_140132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140132 prefixEnd_140132 := by exact prefixLift 140132
  have htrace : WordTrace (prefixWord ++ tailWord_140132) baseStart_140132 baseEnd_140132 := by
    simpa [prefixWord, tailWord_140132, baseEnd_140132] using wordTrace_append hprefix tailTrace_140132
  have hstable : (prefixWord ++ tailWord_140132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140132).length < 2 ^ (prefixWord ++ tailWord_140132).sum := by decide
  have hdescent : baseEnd_140132 < baseStart_140132 := by decide
  rcases family_descends (prefixWord ++ tailWord_140132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140145 : List Nat := [1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_140145 : Nat := 118140960795 + 140145 * 2 ^ 59
def prefixEnd_140145 : Nat := 4983230072969 + 3 ^ 40 * 140145 * 2
def baseEnd_140145 : Nat := 71961746324459415742991

theorem tailTrace_140145 : CollatzResearch.WordTrace tailWord_140145 prefixEnd_140145 71961746324459415742991 := by
  unfold tailWord_140145
  simp only [CollatzResearch.WordTrace]
  refine ⟨5111508077286074705557889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3407672051524049803705259 5111508077286074705557889)
  ·
    refine ⟨3833631057964556029168417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5111508077286074705557889 3833631057964556029168417)
    ·
      refine ⟨2875223293473417021876313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3833631057964556029168417 2875223293473417021876313)
      ·
        refine ⟨2156417470105062766407235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2875223293473417021876313 2156417470105062766407235)
        ·
          refine ⟨3234626205157594149610853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2156417470105062766407235 3234626205157594149610853)
          ·
            refine ⟨606492413467048903052035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3234626205157594149610853 606492413467048903052035)
            ·
              refine ⟨909738620200573354578053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 606492413467048903052035 909738620200573354578053)
              ·
                refine ⟨170575991287607503983385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 909738620200573354578053 170575991287607503983385)
                ·
                  refine ⟨127931993465705627987539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170575991287607503983385 127931993465705627987539)
                  ·
                    refine ⟨191897990198558441981309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 127931993465705627987539 191897990198558441981309)
                    ·
                      refine ⟨71961746324459415742991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191897990198558441981309 71961746324459415742991)
                      ·
                        rfl

theorem cell23_140145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_140145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140145 prefixEnd_140145 := by exact prefixLift 140145
  have htrace : WordTrace (prefixWord ++ tailWord_140145) baseStart_140145 baseEnd_140145 := by
    simpa [prefixWord, tailWord_140145, baseEnd_140145] using wordTrace_append hprefix tailTrace_140145
  have hstable : (prefixWord ++ tailWord_140145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140145).length < 2 ^ (prefixWord ++ tailWord_140145).sum := by decide
  have hdescent : baseEnd_140145 < baseStart_140145 := by decide
  rcases family_descends (prefixWord ++ tailWord_140145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140171 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5]
def baseStart_140171 : Nat := 118140960795 + 140171 * 2 ^ 59
def prefixEnd_140171 : Nat := 4983230072969 + 3 ^ 40 * 140171 * 2
def baseEnd_140171 : Nat := 71975096821476314017871

theorem tailTrace_140171 : CollatzResearch.WordTrace tailWord_140171 prefixEnd_140171 71975096821476314017871 := by
  unfold tailWord_140171
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112456375191881146004367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3408304250127920764002911 5112456375191881146004367)
  ·
    refine ⟨7668684562787821719006551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5112456375191881146004367 7668684562787821719006551)
    ·
      refine ⟨11503026844181732578509827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7668684562787821719006551 11503026844181732578509827)
      ·
        refine ⟨17254540266272598867764741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11503026844181732578509827 17254540266272598867764741)
        ·
          refine ⟨3235226299926112287705889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17254540266272598867764741 3235226299926112287705889)
          ·
            refine ⟨2426419724944584215779417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3235226299926112287705889 2426419724944584215779417)
            ·
              refine ⟨1819814793708438161834563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2426419724944584215779417 1819814793708438161834563)
              ·
                refine ⟨2729722190562657242751845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1819814793708438161834563 2729722190562657242751845)
                ·
                  refine ⟨511822910730498233015971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2729722190562657242751845 511822910730498233015971)
                  ·
                    refine ⟨767734366095747349523957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 511822910730498233015971 767734366095747349523957)
                    ·
                      refine ⟨71975096821476314017871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 767734366095747349523957 71975096821476314017871)
                      ·
                        rfl

theorem cell23_140171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_140171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140171 prefixEnd_140171 := by exact prefixLift 140171
  have htrace : WordTrace (prefixWord ++ tailWord_140171) baseStart_140171 baseEnd_140171 := by
    simpa [prefixWord, tailWord_140171, baseEnd_140171] using wordTrace_append hprefix tailTrace_140171
  have hstable : (prefixWord ++ tailWord_140171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140171).length < 2 ^ (prefixWord ++ tailWord_140171).sum := by decide
  have hdescent : baseEnd_140171 < baseStart_140171 := by decide
  rcases family_descends (prefixWord ++ tailWord_140171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140185 : List Nat := [1, 2, 1, 2, 1, 3, 1, 4, 4, 2, 2]
def baseStart_140185 : Nat := 118140960795 + 140185 * 2 ^ 59
def prefixEnd_140185 : Nat := 4983230072969 + 3 ^ 40 * 140185 * 2
def baseEnd_140185 : Nat := 71982285550639259242807

theorem tailTrace_140185 : CollatzResearch.WordTrace tailWord_140185 prefixEnd_140185 71982285550639259242807 := by
  unfold tailWord_140185
  simp only [CollatzResearch.WordTrace]
  refine ⟨5112966997141161537014009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3408644664760774358009339 5112966997141161537014009)
  ·
    refine ⟨3834725247855871152760507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5112966997141161537014009 3834725247855871152760507)
    ·
      refine ⟨5752087871783806729140761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3834725247855871152760507 5752087871783806729140761)
      ·
        refine ⟨4314065903837855046855571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5752087871783806729140761 4314065903837855046855571)
        ·
          refine ⟨6471098855756782570283357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4314065903837855046855571 6471098855756782570283357)
          ·
            refine ⟨2426662070908793463856259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6471098855756782570283357 2426662070908793463856259)
            ·
              refine ⟨3639993106363190195784389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2426662070908793463856259 3639993106363190195784389)
              ·
                refine ⟨682498707443098161709573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3639993106363190195784389 682498707443098161709573)
                ·
                  refine ⟨127968507645580905320545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 682498707443098161709573 127968507645580905320545)
                  ·
                    refine ⟨95976380734185678990409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 127968507645580905320545 95976380734185678990409)
                    ·
                      refine ⟨71982285550639259242807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 95976380734185678990409 71982285550639259242807)
                      ·
                        rfl

theorem cell23_140185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 4, 4, 2, 2].length) (baseStart_140185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140185 prefixEnd_140185 := by exact prefixLift 140185
  have htrace : WordTrace (prefixWord ++ tailWord_140185) baseStart_140185 baseEnd_140185 := by
    simpa [prefixWord, tailWord_140185, baseEnd_140185] using wordTrace_append hprefix tailTrace_140185
  have hstable : (prefixWord ++ tailWord_140185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140185).length < 2 ^ (prefixWord ++ tailWord_140185).sum := by decide
  have hdescent : baseEnd_140185 < baseStart_140185 := by decide
  rcases family_descends (prefixWord ++ tailWord_140185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140218 : List Nat := [3, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3]
def baseStart_140218 : Nat := 118140960795 + 140218 * 2 ^ 59
def prefixEnd_140218 : Nat := 4983230072969 + 3 ^ 40 * 140218 * 2
def baseEnd_140218 : Nat := 71999230412237630130155

theorem tailTrace_140218 : CollatzResearch.WordTrace tailWord_140218 prefixEnd_140218 71999230412237630130155 := by
  unfold tailWord_140218
  simp only [CollatzResearch.WordTrace]
  refine ⟨1278542651505402043241327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3409447070681072115310205 1278542651505402043241327)
  ·
    refine ⟨1917813977258103064861991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1278542651505402043241327 1917813977258103064861991)
    ·
      refine ⟨2876720965887154597292987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1917813977258103064861991 2876720965887154597292987)
      ·
        refine ⟨4315081448830731895939481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2876720965887154597292987 4315081448830731895939481)
        ·
          refine ⟨3236311086623048921954611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4315081448830731895939481 3236311086623048921954611)
          ·
            refine ⟨4854466629934573382931917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3236311086623048921954611 4854466629934573382931917)
            ·
              refine ⟨1820424986225465018599469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4854466629934573382931917 1820424986225465018599469)
              ·
                refine ⟨682659369834549381974801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1820424986225465018599469 682659369834549381974801)
                ·
                  refine ⟨511994527375912036481101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 682659369834549381974801 511994527375912036481101)
                  ·
                    refine ⟨191997947765967013680413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 511994527375912036481101 191997947765967013680413)
                    ·
                      refine ⟨71999230412237630130155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 191997947765967013680413 71999230412237630130155)
                      ·
                        rfl

theorem cell23_140218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3].length) (baseStart_140218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140218 prefixEnd_140218 := by exact prefixLift 140218
  have htrace : WordTrace (prefixWord ++ tailWord_140218) baseStart_140218 baseEnd_140218 := by
    simpa [prefixWord, tailWord_140218, baseEnd_140218] using wordTrace_append hprefix tailTrace_140218
  have hstable : (prefixWord ++ tailWord_140218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140218).length < 2 ^ (prefixWord ++ tailWord_140218).sum := by decide
  have hdescent : baseEnd_140218 < baseStart_140218 := by decide
  rcases family_descends (prefixWord ++ tailWord_140218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140238 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_140238 : Nat := 118140960795 + 140238 * 2 ^ 59
def prefixEnd_140238 : Nat := 4983230072969 + 3 ^ 40 * 140238 * 2
def baseEnd_140238 : Nat := 24003166675109183960021

theorem tailTrace_140238 : CollatzResearch.WordTrace tailWord_140238 prefixEnd_140238 24003166675109183960021 := by
  unfold tailWord_140238
  simp only [CollatzResearch.WordTrace]
  refine ⟨639362508243643948586671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3409933377299434392462245 639362508243643948586671)
  ·
    refine ⟨959043762365465922880007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 639362508243643948586671 959043762365465922880007)
    ·
      refine ⟨1438565643548198884320011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 959043762365465922880007 1438565643548198884320011)
      ·
        refine ⟨2157848465322298326480017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1438565643548198884320011 2157848465322298326480017)
        ·
          refine ⟨1618386348991723744860013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2157848465322298326480017 1618386348991723744860013)
          ·
            refine ⟨606894880871896404322505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1618386348991723744860013 606894880871896404322505)
            ·
              refine ⟨455171160653922303241879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 606894880871896404322505 455171160653922303241879)
              ·
                refine ⟨682756740980883454862819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455171160653922303241879 682756740980883454862819)
                ·
                  refine ⟨1024135111471325182294229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 682756740980883454862819 1024135111471325182294229)
                  ·
                    refine ⟨24003166675109183960021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1024135111471325182294229 24003166675109183960021)
                    ·
                      rfl

theorem cell23_140238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_140238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140238 prefixEnd_140238 := by exact prefixLift 140238
  have htrace : WordTrace (prefixWord ++ tailWord_140238) baseStart_140238 baseEnd_140238 := by
    simpa [prefixWord, tailWord_140238, baseEnd_140238] using wordTrace_append hprefix tailTrace_140238
  have hstable : (prefixWord ++ tailWord_140238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140238).length < 2 ^ (prefixWord ++ tailWord_140238).sum := by decide
  have hdescent : baseEnd_140238 < baseStart_140238 := by decide
  rcases family_descends (prefixWord ++ tailWord_140238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140242 : List Nat := [3, 2, 2, 3, 1, 1, 3, 3, 5]
def baseStart_140242 : Nat := 118140960795 + 140242 * 2 ^ 59
def prefixEnd_140242 : Nat := 4983230072969 + 3 ^ 40 * 140242 * 2
def baseEnd_140242 : Nat := 8001283771993948470005

theorem tailTrace_140242 : CollatzResearch.WordTrace tailWord_140242 prefixEnd_140242 8001283771993948470005 := by
  unfold tailWord_140242
  simp only [CollatzResearch.WordTrace]
  refine ⟨1278761489483665067959745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3410030638623106847892653 1278761489483665067959745)
  ·
    refine ⟨959071117112748800969809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1278761489483665067959745 959071117112748800969809)
    ·
      refine ⟨719303337834561600727357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 959071117112748800969809 719303337834561600727357)
      ·
        refine ⟨269738751687960600272759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 719303337834561600727357 269738751687960600272759)
        ·
          refine ⟨404608127531940900409139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 269738751687960600272759 404608127531940900409139)
          ·
            refine ⟨606912191297911350613709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404608127531940900409139 606912191297911350613709)
            ·
              refine ⟨227592071736716756480141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 606912191297911350613709 227592071736716756480141)
              ·
                refine ⟨85347026901268783680053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227592071736716756480141 85347026901268783680053)
                ·
                  refine ⟨8001283771993948470005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85347026901268783680053 8001283771993948470005)
                  ·
                    rfl

theorem cell23_140242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_140242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140242 prefixEnd_140242 := by exact prefixLift 140242
  have htrace : WordTrace (prefixWord ++ tailWord_140242) baseStart_140242 baseEnd_140242 := by
    simpa [prefixWord, tailWord_140242, baseEnd_140242] using wordTrace_append hprefix tailTrace_140242
  have hstable : (prefixWord ++ tailWord_140242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140242).length < 2 ^ (prefixWord ++ tailWord_140242).sum := by decide
  have hdescent : baseEnd_140242 < baseStart_140242 := by decide
  rcases family_descends (prefixWord ++ tailWord_140242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140255 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 2, 5]
def baseStart_140255 : Nat := 118140960795 + 140255 * 2 ^ 59
def prefixEnd_140255 : Nat := 4983230072969 + 3 ^ 40 * 140255 * 2
def baseEnd_140255 : Nat := 24006076398817995122495

theorem tailTrace_140255 : CollatzResearch.WordTrace tailWord_140255 prefixEnd_140255 24006076398817995122495 := by
  unfold tailWord_140255
  simp only [CollatzResearch.WordTrace]
  refine ⟨5115520106887563492062219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3410346737925042328041479 5115520106887563492062219)
  ·
    refine ⟨7673280160331345238093329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5115520106887563492062219 7673280160331345238093329)
    ·
      refine ⟨5754960120248508928569997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7673280160331345238093329 5754960120248508928569997)
      ·
        refine ⟨2158110045093190848213749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5754960120248508928569997 2158110045093190848213749)
        ·
          refine ⟨202322816727486642020039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2158110045093190848213749 202322816727486642020039)
          ·
            refine ⟨303484225091229963030059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202322816727486642020039 303484225091229963030059)
            ·
              refine ⟨455226337636844944545089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 303484225091229963030059 455226337636844944545089)
              ·
                refine ⟨341419753227633708408817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 455226337636844944545089 341419753227633708408817)
                ·
                  refine ⟨256064814920725281306613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 341419753227633708408817 256064814920725281306613)
                  ·
                    refine ⟨24006076398817995122495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 256064814920725281306613 24006076398817995122495)
                    ·
                      rfl

theorem cell23_140255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_140255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140255 prefixEnd_140255 := by exact prefixLift 140255
  have htrace : WordTrace (prefixWord ++ tailWord_140255) baseStart_140255 baseEnd_140255 := by
    simpa [prefixWord, tailWord_140255, baseEnd_140255] using wordTrace_append hprefix tailTrace_140255
  have hstable : (prefixWord ++ tailWord_140255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140255).length < 2 ^ (prefixWord ++ tailWord_140255).sum := by decide
  have hdescent : baseEnd_140255 < baseStart_140255 := by decide
  rcases family_descends (prefixWord ++ tailWord_140255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140319 : List Nat := [1, 1, 2, 4, 1, 3, 4, 2, 1, 4]
def baseStart_140319 : Nat := 118140960795 + 140319 * 2 ^ 59
def prefixEnd_140319 : Nat := 4983230072969 + 3 ^ 40 * 140319 * 2
def baseEnd_140319 : Nat := 24017030652780578322397

theorem tailTrace_140319 : CollatzResearch.WordTrace tailWord_140319 prefixEnd_140319 24017030652780578322397 := by
  unfold tailWord_140319
  simp only [CollatzResearch.WordTrace]
  refine ⟨5117854378655702422392011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3411902919103801614928007 5117854378655702422392011)
  ·
    refine ⟨7676781567983553633588017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5117854378655702422392011 7676781567983553633588017)
    ·
      refine ⟨5757586175987665225191013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7676781567983553633588017 5757586175987665225191013)
      ·
        refine ⟨1079547407997687229723315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5757586175987665225191013 1079547407997687229723315)
        ·
          refine ⟨1619321111996530844584973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1079547407997687229723315 1619321111996530844584973)
          ·
            refine ⟨607245416998699066719365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1619321111996530844584973 607245416998699066719365)
            ·
              refine ⟨113858515687256075009881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 607245416998699066719365 113858515687256075009881)
              ·
                refine ⟨85393886765442056257411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 113858515687256075009881 85393886765442056257411)
                ·
                  refine ⟨128090830148163084386117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85393886765442056257411 128090830148163084386117)
                  ·
                    refine ⟨24017030652780578322397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 128090830148163084386117 24017030652780578322397)
                    ·
                      rfl

theorem cell23_140319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 4, 2, 1, 4].length) (baseStart_140319 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140319 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140319 prefixEnd_140319 := by exact prefixLift 140319
  have htrace : WordTrace (prefixWord ++ tailWord_140319) baseStart_140319 baseEnd_140319 := by
    simpa [prefixWord, tailWord_140319, baseEnd_140319] using wordTrace_append hprefix tailTrace_140319
  have hstable : (prefixWord ++ tailWord_140319).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140319).length < 2 ^ (prefixWord ++ tailWord_140319).sum := by decide
  have hdescent : baseEnd_140319 < baseStart_140319 := by decide
  rcases family_descends (prefixWord ++ tailWord_140319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140338 : List Nat := [3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7]
def baseStart_140338 : Nat := 118140960795 + 140338 * 2 ^ 59
def prefixEnd_140338 : Nat := 4983230072969 + 3 ^ 40 * 140338 * 2
def baseEnd_140338 : Nat := 72060848090777160629603

theorem tailTrace_140338 : CollatzResearch.WordTrace tailWord_140338 prefixEnd_140338 72060848090777160629603 := by
  unfold tailWord_140338
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279636841396717166833417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3412364910391245778222445 1279636841396717166833417)
  ·
    refine ⟨959727631047537875125063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1279636841396717166833417 959727631047537875125063)
    ·
      refine ⟨1439591446571306812687595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 959727631047537875125063 1439591446571306812687595)
      ·
        refine ⟨2159387169856960219031393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439591446571306812687595 2159387169856960219031393)
        ·
          refine ⟨1619540377392720164273545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2159387169856960219031393 1619540377392720164273545)
          ·
            refine ⟨1214655283044540123205159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1619540377392720164273545 1214655283044540123205159)
            ·
              refine ⟨1821982924566810184807739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1214655283044540123205159 1821982924566810184807739)
              ·
                refine ⟨2732974386850215277211609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1821982924566810184807739 2732974386850215277211609)
                ·
                  refine ⟨2049730790137661457908707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2732974386850215277211609 2049730790137661457908707)
                  ·
                    refine ⟨3074596185206492186863061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2049730790137661457908707 3074596185206492186863061)
                    ·
                      refine ⟨72060848090777160629603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 3074596185206492186863061 72060848090777160629603)
                      ·
                        rfl

theorem cell23_140338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 1, 2, 1, 7].length) (baseStart_140338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140338 prefixEnd_140338 := by exact prefixLift 140338
  have htrace : WordTrace (prefixWord ++ tailWord_140338) baseStart_140338 baseEnd_140338 := by
    simpa [prefixWord, tailWord_140338, baseEnd_140338] using wordTrace_append hprefix tailTrace_140338
  have hstable : (prefixWord ++ tailWord_140338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140338).length < 2 ^ (prefixWord ++ tailWord_140338).sum := by decide
  have hdescent : baseEnd_140338 < baseStart_140338 := by decide
  rcases family_descends (prefixWord ++ tailWord_140338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140345 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 3, 5]
def baseStart_140345 : Nat := 118140960795 + 140345 * 2 ^ 59
def prefixEnd_140345 : Nat := 4983230072969 + 3 ^ 40 * 140345 * 2
def baseEnd_140345 : Nat := 24021480818452877747357

theorem tailTrace_140345 : CollatzResearch.WordTrace tailWord_140345 prefixEnd_140345 24021480818452877747357 := by
  unfold tailWord_140345
  simp only [CollatzResearch.WordTrace]
  refine ⟨5118802676561508862838489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3412535117707672575225659 5118802676561508862838489)
  ·
    refine ⟨3839102007421131647128867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5118802676561508862838489 3839102007421131647128867)
    ·
      refine ⟨5758653011131697470693301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3839102007421131647128867 5758653011131697470693301)
      ·
        refine ⟨539873719793596637877497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5758653011131697470693301 539873719793596637877497)
        ·
          refine ⟨404905289845197478408123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 539873719793596637877497 404905289845197478408123)
          ·
            refine ⟨607357934767796217612185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 404905289845197478408123 607357934767796217612185)
            ·
              refine ⟨455518451075847163209139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 607357934767796217612185 455518451075847163209139)
              ·
                refine ⟨683277676613770744813709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 455518451075847163209139 683277676613770744813709)
                ·
                  refine ⟨256229128730164029305141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 683277676613770744813709 256229128730164029305141)
                  ·
                    refine ⟨24021480818452877747357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 256229128730164029305141 24021480818452877747357)
                    ·
                      rfl

theorem cell23_140345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_140345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140345 prefixEnd_140345 := by exact prefixLift 140345
  have htrace : WordTrace (prefixWord ++ tailWord_140345) baseStart_140345 baseEnd_140345 := by
    simpa [prefixWord, tailWord_140345, baseEnd_140345] using wordTrace_append hprefix tailTrace_140345
  have hstable : (prefixWord ++ tailWord_140345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140345).length < 2 ^ (prefixWord ++ tailWord_140345).sum := by decide
  have hdescent : baseEnd_140345 < baseStart_140345 := by decide
  rcases family_descends (prefixWord ++ tailWord_140345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140359 : List Nat := [1, 1, 4, 1, 3, 2, 1, 5, 1, 1, 3]
def baseStart_140359 : Nat := 118140960795 + 140359 * 2 ^ 59
def prefixEnd_140359 : Nat := 4983230072969 + 3 ^ 40 * 140359 * 2
def baseEnd_140359 : Nat := 72071631184521578467007

theorem tailTrace_140359 : CollatzResearch.WordTrace tailWord_140359 prefixEnd_140359 72071631184521578467007 := by
  unfold tailWord_140359
  simp only [CollatzResearch.WordTrace]
  refine ⟨5119313298510789253848131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3412875532340526169232087 5119313298510789253848131)
  ·
    refine ⟨7678969947766183880772197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5119313298510789253848131 7678969947766183880772197)
    ·
      refine ⟨1439806865206159477644787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7678969947766183880772197 1439806865206159477644787)
      ·
        refine ⟨2159710297809239216467181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439806865206159477644787 2159710297809239216467181)
        ·
          refine ⟨809891361678464706175193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2159710297809239216467181 809891361678464706175193)
          ·
            refine ⟨607418521258848529631395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 809891361678464706175193 607418521258848529631395)
            ·
              refine ⟨911127781888272794447093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 607418521258848529631395 911127781888272794447093)
              ·
                refine ⟨85418229552025574479415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 911127781888272794447093 85418229552025574479415)
                ·
                  refine ⟨128127344328038361719123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85418229552025574479415 128127344328038361719123)
                  ·
                    refine ⟨192191016492057542578685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128127344328038361719123 192191016492057542578685)
                    ·
                      refine ⟨72071631184521578467007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 192191016492057542578685 72071631184521578467007)
                      ·
                        rfl

theorem cell23_140359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 5, 1, 1, 3].length) (baseStart_140359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140359 prefixEnd_140359 := by exact prefixLift 140359
  have htrace : WordTrace (prefixWord ++ tailWord_140359) baseStart_140359 baseEnd_140359 := by
    simpa [prefixWord, tailWord_140359, baseEnd_140359] using wordTrace_append hprefix tailTrace_140359
  have hstable : (prefixWord ++ tailWord_140359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140359).length < 2 ^ (prefixWord ++ tailWord_140359).sum := by decide
  have hdescent : baseEnd_140359 < baseStart_140359 := by decide
  rcases family_descends (prefixWord ++ tailWord_140359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140362 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_140362 : Nat := 118140960795 + 140362 * 2 ^ 59
def prefixEnd_140362 : Nat := 4983230072969 + 3 ^ 40 * 140362 * 2
def baseEnd_140362 : Nat := 24024390542161688909831

theorem tailTrace_140362 : CollatzResearch.WordTrace tailWord_140362 prefixEnd_140362 24024390542161688909831 := by
  unfold tailWord_140362
  simp only [CollatzResearch.WordTrace]
  refine ⟨1279855679374980191551835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3412948478333280510804893 1279855679374980191551835)
  ·
    refine ⟨1919783519062470287327753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1279855679374980191551835 1919783519062470287327753)
    ·
      refine ⟨1439837639296852715495815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1919783519062470287327753 1439837639296852715495815)
      ·
        refine ⟨2159756458945279073243723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1439837639296852715495815 2159756458945279073243723)
        ·
          refine ⟨3239634688417918609865585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2159756458945279073243723 3239634688417918609865585)
          ·
            refine ⟨2429726016313438957399189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3239634688417918609865585 2429726016313438957399189)
            ·
              refine ⟨113893407014692451128087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2429726016313438957399189 113893407014692451128087)
              ·
                refine ⟨170840110522038676692131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113893407014692451128087 170840110522038676692131)
                ·
                  refine ⟨256260165783058015038197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170840110522038676692131 256260165783058015038197)
                  ·
                    refine ⟨24024390542161688909831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 256260165783058015038197 24024390542161688909831)
                    ·
                      rfl

theorem cell23_140362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_140362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140362 prefixEnd_140362 := by exact prefixLift 140362
  have htrace : WordTrace (prefixWord ++ tailWord_140362) baseStart_140362 baseEnd_140362 := by
    simpa [prefixWord, tailWord_140362, baseEnd_140362] using wordTrace_append hprefix tailTrace_140362
  have hstable : (prefixWord ++ tailWord_140362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140362).length < 2 ^ (prefixWord ++ tailWord_140362).sum := by decide
  have hdescent : baseEnd_140362 < baseStart_140362 := by decide
  rcases family_descends (prefixWord ++ tailWord_140362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140368 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5]
def baseStart_140368 : Nat := 118140960795 + 140368 * 2 ^ 59
def prefixEnd_140368 : Nat := 4983230072969 + 3 ^ 40 * 140368 * 2
def baseEnd_140368 : Nat := 72076252510412043254465

theorem tailTrace_140368 : CollatzResearch.WordTrace tailWord_140368 prefixEnd_140368 72076252510412043254465 := by
  unfold tailWord_140368
  simp only [CollatzResearch.WordTrace]
  refine ⟨2559820777739091895462879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3413094370318789193950505 2559820777739091895462879)
  ·
    refine ⟨3839731166608637843194319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2559820777739091895462879 3839731166608637843194319)
    ·
      refine ⟨5759596749912956764791479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3839731166608637843194319 5759596749912956764791479)
      ·
        refine ⟨8639395124869435147187219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5759596749912956764791479 8639395124869435147187219)
        ·
          refine ⟨12959092687304152720780829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8639395124869435147187219 12959092687304152720780829)
          ·
            refine ⟨4859659757739057270292811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12959092687304152720780829 4859659757739057270292811)
            ·
              refine ⟨7289489636608585905439217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4859659757739057270292811 7289489636608585905439217)
              ·
                refine ⟨5467117227456439429079413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7289489636608585905439217 5467117227456439429079413)
                ·
                  refine ⟨512542240074041196476195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 5467117227456439429079413 512542240074041196476195)
                  ·
                    refine ⟨768813360111061794714293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 512542240074041196476195 768813360111061794714293)
                    ·
                      refine ⟨72076252510412043254465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 768813360111061794714293 72076252510412043254465)
                      ·
                        rfl

theorem cell23_140368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 5].length) (baseStart_140368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140368 prefixEnd_140368 := by exact prefixLift 140368
  have htrace : WordTrace (prefixWord ++ tailWord_140368) baseStart_140368 baseEnd_140368 := by
    simpa [prefixWord, tailWord_140368, baseEnd_140368] using wordTrace_append hprefix tailTrace_140368
  have hstable : (prefixWord ++ tailWord_140368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140368).length < 2 ^ (prefixWord ++ tailWord_140368).sum := by decide
  have hdescent : baseEnd_140368 < baseStart_140368 := by decide
  rcases family_descends (prefixWord ++ tailWord_140368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140385 : List Nat := [1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_140385 : Nat := 118140960795 + 140385 * 2 ^ 59
def prefixEnd_140385 : Nat := 4983230072969 + 3 ^ 40 * 140385 * 2
def baseEnd_140385 : Nat := 72084981681538476741887

theorem tailTrace_140385 : CollatzResearch.WordTrace tailWord_140385 prefixEnd_140385 72084981681538476741887 := by
  unfold tailWord_140385
  simp only [CollatzResearch.WordTrace]
  refine ⟨5120261596416595694294609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3413507730944397129529739 5120261596416595694294609)
  ·
    refine ⟨3840196197312446770720957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5120261596416595694294609 3840196197312446770720957)
    ·
      refine ⟨1440073573992167539020359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3840196197312446770720957 1440073573992167539020359)
      ·
        refine ⟨2160110360988251308530539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440073573992167539020359 2160110360988251308530539)
        ·
          refine ⟨3240165541482376962795809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2160110360988251308530539 3240165541482376962795809)
          ·
            refine ⟨2430124156111782722096857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3240165541482376962795809 2430124156111782722096857)
            ·
              refine ⟨1822593117083837041572643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2430124156111782722096857 1822593117083837041572643)
              ·
                refine ⟨2733889675625755562358965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1822593117083837041572643 2733889675625755562358965)
                ·
                  refine ⟨256302157089914583971153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2733889675625755562358965 256302157089914583971153)
                  ·
                    refine ⟨192226617817435937978365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 256302157089914583971153 192226617817435937978365)
                    ·
                      refine ⟨72084981681538476741887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 192226617817435937978365 72084981681538476741887)
                      ·
                        rfl

theorem cell23_140385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_140385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140385 prefixEnd_140385 := by exact prefixLift 140385
  have htrace : WordTrace (prefixWord ++ tailWord_140385) baseStart_140385 baseEnd_140385 := by
    simpa [prefixWord, tailWord_140385, baseEnd_140385] using wordTrace_append hprefix tailTrace_140385
  have hstable : (prefixWord ++ tailWord_140385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140385).length < 2 ^ (prefixWord ++ tailWord_140385).sum := by decide
  have hdescent : baseEnd_140385 < baseStart_140385 := by decide
  rcases family_descends (prefixWord ++ tailWord_140385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140388 : List Nat := [2, 3, 1, 1, 2, 1, 1, 12]
def baseStart_140388 : Nat := 118140960795 + 140388 * 2 ^ 59
def prefixEnd_140388 : Nat := 4983230072969 + 3 ^ 40 * 140388 * 2
def baseEnd_140388 : Nat := 2669871189759332037199

theorem tailTrace_140388 : CollatzResearch.WordTrace tailWord_140388 prefixEnd_140388 2669871189759332037199 := by
  unfold tailWord_140388
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560185507702863603326909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3413580676937151471102545 2560185507702863603326909)
  ·
    refine ⟨960069565388573851247591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2560185507702863603326909 960069565388573851247591)
    ·
      refine ⟨1440104348082860776871387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 960069565388573851247591 1440104348082860776871387)
      ·
        refine ⟨2160156522124291165307081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1440104348082860776871387 2160156522124291165307081)
        ·
          refine ⟨1620117391593218373980311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2160156522124291165307081 1620117391593218373980311)
          ·
            refine ⟨2430176087389827560970467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1620117391593218373980311 2430176087389827560970467)
            ·
              refine ⟨3645264131084741341455701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2430176087389827560970467 3645264131084741341455701)
              ·
                refine ⟨2669871189759332037199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 3645264131084741341455701 2669871189759332037199)
                ·
                  rfl

theorem cell23_140388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 12].length) (baseStart_140388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140388 prefixEnd_140388 := by exact prefixLift 140388
  have htrace : WordTrace (prefixWord ++ tailWord_140388) baseStart_140388 baseEnd_140388 := by
    simpa [prefixWord, tailWord_140388, baseEnd_140388] using wordTrace_append hprefix tailTrace_140388
  have hstable : (prefixWord ++ tailWord_140388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140388).length < 2 ^ (prefixWord ++ tailWord_140388).sum := by decide
  have hdescent : baseEnd_140388 < baseStart_140388 := by decide
  rcases family_descends (prefixWord ++ tailWord_140388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140416 : List Nat := [2, 1, 1, 2, 1, 3, 5, 3, 1, 2, 2]
def baseStart_140416 : Nat := 118140960795 + 140416 * 2 ^ 59
def prefixEnd_140416 : Nat := 4983230072969 + 3 ^ 40 * 140416 * 2
def baseEnd_140416 : Nat := 72100899581827855454245

theorem tailTrace_140416 : CollatzResearch.WordTrace tailWord_140416 prefixEnd_140416 72100899581827855454245 := by
  unfold tailWord_140416
  simp only [CollatzResearch.WordTrace]
  refine ⟨2560696129652143994336551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3414261506202858659115401 2560696129652143994336551)
  ·
    refine ⟨3841044194478215991504827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2560696129652143994336551 3841044194478215991504827)
    ·
      refine ⟨5761566291717323987257241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3841044194478215991504827 5761566291717323987257241)
      ·
        refine ⟨4321174718787992990442931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5761566291717323987257241 4321174718787992990442931)
        ·
          refine ⟨6481762078181989485664397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4321174718787992990442931 6481762078181989485664397)
          ·
            refine ⟨2430660779318246057124149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6481762078181989485664397 2430660779318246057124149)
            ·
              refine ⟨227874448061085567855389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2430660779318246057124149 227874448061085567855389)
              ·
                refine ⟨85452918022907087945771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 227874448061085567855389 85452918022907087945771)
                ·
                  refine ⟨128179377034360631918657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85452918022907087945771 128179377034360631918657)
                  ·
                    refine ⟨96134532775770473938993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128179377034360631918657 96134532775770473938993)
                    ·
                      refine ⟨72100899581827855454245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96134532775770473938993 72100899581827855454245)
                      ·
                        rfl

theorem cell23_140416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 3, 1, 2, 2].length) (baseStart_140416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140416 prefixEnd_140416 := by exact prefixLift 140416
  have htrace : WordTrace (prefixWord ++ tailWord_140416) baseStart_140416 baseEnd_140416 := by
    simpa [prefixWord, tailWord_140416, baseEnd_140416] using wordTrace_append hprefix tailTrace_140416
  have hstable : (prefixWord ++ tailWord_140416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140416).length < 2 ^ (prefixWord ++ tailWord_140416).sum := by decide
  have hdescent : baseEnd_140416 < baseStart_140416 := by decide
  rcases family_descends (prefixWord ++ tailWord_140416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140449 : List Nat := [1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_140449 : Nat := 118140960795 + 140449 * 2 ^ 59
def prefixEnd_140449 : Nat := 4983230072969 + 3 ^ 40 * 140449 * 2
def baseEnd_140449 : Nat := 72117844443426226341593

theorem tailTrace_140449 : CollatzResearch.WordTrace tailWord_140449 prefixEnd_140449 72117844443426226341593 := by
  unfold tailWord_140449
  simp only [CollatzResearch.WordTrace]
  refine ⟨5122595868184734624624401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3415063912123156416416267 5122595868184734624624401)
  ·
    refine ⟨3841946901138550968468301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5122595868184734624624401 3841946901138550968468301)
    ·
      refine ⟨1440730087926956613175613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3841946901138550968468301 1440730087926956613175613)
      ·
        refine ⟨540273782972608729940855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1440730087926956613175613 540273782972608729940855)
        ·
          refine ⟨810410674458913094911283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 540273782972608729940855 810410674458913094911283)
          ·
            refine ⟨1215616011688369642366925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 810410674458913094911283 1215616011688369642366925)
            ·
              refine ⟨455856004383138615887597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1215616011688369642366925 455856004383138615887597)
              ·
                refine ⟨170946001643676980957849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 455856004383138615887597 170946001643676980957849)
                ·
                  refine ⟨128209501232757735718387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 170946001643676980957849 128209501232757735718387)
                  ·
                    refine ⟨192314251849136603577581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128209501232757735718387 192314251849136603577581)
                    ·
                      refine ⟨72117844443426226341593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 192314251849136603577581 72117844443426226341593)
                      ·
                        rfl

theorem cell23_140449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_140449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140449 prefixEnd_140449 := by exact prefixLift 140449
  have htrace : WordTrace (prefixWord ++ tailWord_140449) baseStart_140449 baseEnd_140449 := by
    simpa [prefixWord, tailWord_140449, baseEnd_140449] using wordTrace_append hprefix tailTrace_140449
  have hstable : (prefixWord ++ tailWord_140449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140449).length < 2 ^ (prefixWord ++ tailWord_140449).sum := by decide
  have hdescent : baseEnd_140449 < baseStart_140449 := by decide
  rcases family_descends (prefixWord ++ tailWord_140449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140470 : List Nat := [5, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3]
def baseStart_140470 : Nat := 118140960795 + 140470 * 2 ^ 59
def prefixEnd_140470 : Nat := 4983230072969 + 3 ^ 40 * 140470 * 2
def baseEnd_140470 : Nat := 72128627537170644178997

theorem tailTrace_140470 : CollatzResearch.WordTrace tailWord_140470 prefixEnd_140470 72128627537170644178997 := by
  unfold tailWord_140470
  simp only [CollatzResearch.WordTrace]
  refine ⟨320210112569290950696179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3415574534072436807425909 320210112569290950696179)
  ·
    refine ⟨480315168853936426044269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 320210112569290950696179 480315168853936426044269)
    ·
      refine ⟨180118188320226159766601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 480315168853936426044269 180118188320226159766601)
      ·
        refine ⟨135088641240169619824951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 180118188320226159766601 135088641240169619824951)
        ·
          refine ⟨202632961860254429737427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135088641240169619824951 202632961860254429737427)
          ·
            refine ⟨303949442790381644606141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 202632961860254429737427 303949442790381644606141)
            ·
              refine ⟨113981041046393116727303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 303949442790381644606141 113981041046393116727303)
              ·
                refine ⟨170971561569589675090955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 113981041046393116727303 170971561569589675090955)
                ·
                  refine ⟨256457342354384512636433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 170971561569589675090955 256457342354384512636433)
                  ·
                    refine ⟨192343006765788384477325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 256457342354384512636433 192343006765788384477325)
                    ·
                      refine ⟨72128627537170644178997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 192343006765788384477325 72128627537170644178997)
                      ·
                        rfl

theorem cell23_140470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_140470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140470 prefixEnd_140470 := by exact prefixLift 140470
  have htrace : WordTrace (prefixWord ++ tailWord_140470) baseStart_140470 baseEnd_140470 := by
    simpa [prefixWord, tailWord_140470, baseEnd_140470] using wordTrace_append hprefix tailTrace_140470
  have hstable : (prefixWord ++ tailWord_140470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140470).length < 2 ^ (prefixWord ++ tailWord_140470).sum := by decide
  have hdescent : baseEnd_140470 < baseStart_140470 := by decide
  rcases family_descends (prefixWord ++ tailWord_140470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140485 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_140485 : Nat := 118140960795 + 140485 * 2 ^ 59
def prefixEnd_140485 : Nat := 4983230072969 + 3 ^ 40 * 140485 * 2
def baseEnd_140485 : Nat := 72136329746988085491427

theorem tailTrace_140485 : CollatzResearch.WordTrace tailWord_140485 prefixEnd_140485 72136329746988085491427 := by
  unfold tailWord_140485
  simp only [CollatzResearch.WordTrace]
  refine ⟨5123908896054312772934909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3415939264036208515289939 5123908896054312772934909)
  ·
    refine ⟨1921465836020367289850591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5123908896054312772934909 1921465836020367289850591)
    ·
      refine ⟨2882198754030550934775887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1921465836020367289850591 2882198754030550934775887)
      ·
        refine ⟨4323298131045826402163831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2882198754030550934775887 4323298131045826402163831)
        ·
          refine ⟨6484947196568739603245747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4323298131045826402163831 6484947196568739603245747)
          ·
            refine ⟨9727420794853109404868621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6484947196568739603245747 9727420794853109404868621)
            ·
              refine ⟨3647782798069916026825733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9727420794853109404868621 3647782798069916026825733)
              ·
                refine ⟨683959274638109255029825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3647782798069916026825733 683959274638109255029825)
                ·
                  refine ⟨512969455978581941272369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 683959274638109255029825 512969455978581941272369)
                  ·
                    refine ⟨384727091983936455954277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 512969455978581941272369 384727091983936455954277)
                    ·
                      refine ⟨72136329746988085491427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 384727091983936455954277 72136329746988085491427)
                      ·
                        rfl

theorem cell23_140485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_140485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140485 prefixEnd_140485 := by exact prefixLift 140485
  have htrace : WordTrace (prefixWord ++ tailWord_140485) baseStart_140485 baseEnd_140485 := by
    simpa [prefixWord, tailWord_140485, baseEnd_140485] using wordTrace_append hprefix tailTrace_140485
  have hstable : (prefixWord ++ tailWord_140485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140485).length < 2 ^ (prefixWord ++ tailWord_140485).sum := by decide
  have hdescent : baseEnd_140485 < baseStart_140485 := by decide
  rcases family_descends (prefixWord ++ tailWord_140485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140540 : List Nat := [2, 2, 2, 1, 6, 1, 1, 2, 2, 2, 2]
def baseStart_140540 : Nat := 118140960795 + 140540 * 2 ^ 59
def prefixEnd_140540 : Nat := 4983230072969 + 3 ^ 40 * 140540 * 2
def baseEnd_140540 : Nat := 72164571182985370303675

theorem tailTrace_140540 : CollatzResearch.WordTrace tailWord_140540 prefixEnd_140540 72164571182985370303675 := by
  unfold tailWord_140540
  simp only [CollatzResearch.WordTrace]
  refine ⟨2562957455427528583093537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3417276607236704777458049 2562957455427528583093537)
  ·
    refine ⟨1922218091570646437320153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2562957455427528583093537 1922218091570646437320153)
    ·
      refine ⟨1441663568677984827990115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1922218091570646437320153 1441663568677984827990115)
      ·
        refine ⟨2162495353016977241985173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1441663568677984827990115 2162495353016977241985173)
        ·
          refine ⟨101366969672670808218055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2162495353016977241985173 101366969672670808218055)
          ·
            refine ⟨152050454509006212327083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101366969672670808218055 152050454509006212327083)
            ·
              refine ⟨228075681763509318490625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152050454509006212327083 228075681763509318490625)
              ·
                refine ⟨171056761322631988867969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 228075681763509318490625 171056761322631988867969)
                ·
                  refine ⟨128292570991973991650977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171056761322631988867969 128292570991973991650977)
                  ·
                    refine ⟨96219428243980493738233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128292570991973991650977 96219428243980493738233)
                    ·
                      refine ⟨72164571182985370303675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96219428243980493738233 72164571182985370303675)
                      ·
                        rfl

theorem cell23_140540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_140540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140540 prefixEnd_140540 := by exact prefixLift 140540
  have htrace : WordTrace (prefixWord ++ tailWord_140540) baseStart_140540 baseEnd_140540 := by
    simpa [prefixWord, tailWord_140540, baseEnd_140540] using wordTrace_append hprefix tailTrace_140540
  have hstable : (prefixWord ++ tailWord_140540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140540).length < 2 ^ (prefixWord ++ tailWord_140540).sum := by decide
  have hdescent : baseEnd_140540 < baseStart_140540 := by decide
  rcases family_descends (prefixWord ++ tailWord_140540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140602 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 6]
def baseStart_140602 : Nat := 118140960795 + 140602 * 2 ^ 59
def prefixEnd_140602 : Nat := 4983230072969 + 3 ^ 40 * 140602 * 2
def baseEnd_140602 : Nat := 8021822998173791969821

theorem tailTrace_140602 : CollatzResearch.WordTrace tailWord_140602 prefixEnd_140602 8021822998173791969821 := by
  unfold tailWord_140602
  simp only [CollatzResearch.WordTrace]
  refine ⟨1282044059157610438736015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3418784157753627836629373 1282044059157610438736015)
  ·
    refine ⟨1923066088736415658104023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1282044059157610438736015 1923066088736415658104023)
    ·
      refine ⟨2884599133104623487156035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1923066088736415658104023 2884599133104623487156035)
      ·
        refine ⟨4326898699656935230734053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2884599133104623487156035 4326898699656935230734053)
        ·
          refine ⟨811293506185675355762635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4326898699656935230734053 811293506185675355762635)
          ·
            refine ⟨1216940259278513033643953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 811293506185675355762635 1216940259278513033643953)
            ·
              refine ⟨912705194458884775232965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1216940259278513033643953 912705194458884775232965)
              ·
                refine ⟨171132223961040895356181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 912705194458884775232965 171132223961040895356181)
                ·
                  refine ⟨8021822998173791969821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171132223961040895356181 8021822998173791969821)
                  ·
                    rfl

theorem cell23_140602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_140602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140602 prefixEnd_140602 := by exact prefixLift 140602
  have htrace : WordTrace (prefixWord ++ tailWord_140602) baseStart_140602 baseEnd_140602 := by
    simpa [prefixWord, tailWord_140602, baseEnd_140602] using wordTrace_append hprefix tailTrace_140602
  have hstable : (prefixWord ++ tailWord_140602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140602).length < 2 ^ (prefixWord ++ tailWord_140602).sum := by decide
  have hdescent : baseEnd_140602 < baseStart_140602 := by decide
  rcases family_descends (prefixWord ++ tailWord_140602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140632 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 3, 5]
def baseStart_140632 : Nat := 118140960795 + 140632 * 2 ^ 59
def prefixEnd_140632 : Nat := 4983230072969 + 3 ^ 40 * 140632 * 2
def baseEnd_140632 : Nat := 24070603801066336784417

theorem tailTrace_140632 : CollatzResearch.WordTrace tailWord_140632 prefixEnd_140632 24070603801066336784417 := by
  unfold tailWord_140632
  simp only [CollatzResearch.WordTrace]
  refine ⟨2564635213260878439268075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3419513617681171252357433 2564635213260878439268075)
  ·
    refine ⟨3846952819891317658902113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2564635213260878439268075 3846952819891317658902113)
    ·
      refine ⟨2885214614918488244176585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3846952819891317658902113 2885214614918488244176585)
      ·
        refine ⟨2163910961188866183132439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2885214614918488244176585 2163910961188866183132439)
        ·
          refine ⟨3245866441783299274698659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2163910961188866183132439 3245866441783299274698659)
          ·
            refine ⟨4868799662674948912047989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3245866441783299274698659 4868799662674948912047989)
            ·
              refine ⟨456449968375776460504499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4868799662674948912047989 456449968375776460504499)
              ·
                refine ⟨684674952563664690756749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 456449968375776460504499 684674952563664690756749)
                ·
                  refine ⟨256753107211374259033781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 684674952563664690756749 256753107211374259033781)
                  ·
                    refine ⟨24070603801066336784417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 256753107211374259033781 24070603801066336784417)
                    ·
                      rfl

theorem cell23_140632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_140632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140632 prefixEnd_140632 := by exact prefixLift 140632
  have htrace : WordTrace (prefixWord ++ tailWord_140632) baseStart_140632 baseEnd_140632 := by
    simpa [prefixWord, tailWord_140632, baseEnd_140632] using wordTrace_append hprefix tailTrace_140632
  have hstable : (prefixWord ++ tailWord_140632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140632).length < 2 ^ (prefixWord ++ tailWord_140632).sum := by decide
  have hdescent : baseEnd_140632 < baseStart_140632 := by decide
  rcases family_descends (prefixWord ++ tailWord_140632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140672 : List Nat := [2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5]
def baseStart_140672 : Nat := 118140960795 + 140672 * 2 ^ 59
def prefixEnd_140672 : Nat := 4983230072969 + 3 ^ 40 * 140672 * 2
def baseEnd_140672 : Nat := 72232350629378853853067

theorem tailTrace_140672 : CollatzResearch.WordTrace tailWord_140672 prefixEnd_140672 72232350629378853853067 := by
  unfold tailWord_140672
  simp only [CollatzResearch.WordTrace]
  refine ⟨2565364673188421854996135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3420486230917895806661513 2565364673188421854996135)
  ·
    refine ⟨3848047009782632782494203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2565364673188421854996135 3848047009782632782494203)
    ·
      refine ⟨5772070514673949173741305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3848047009782632782494203 5772070514673949173741305)
      ·
        refine ⟨4329052886005461880305979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5772070514673949173741305 4329052886005461880305979)
        ·
          refine ⟨6493579329008192820458969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4329052886005461880305979 6493579329008192820458969)
          ·
            refine ⟨4870184496756144615344227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6493579329008192820458969 4870184496756144615344227)
            ·
              refine ⟨7305276745134216923016341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4870184496756144615344227 7305276745134216923016341)
              ·
                refine ⟨342434847428166418266391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 7305276745134216923016341 342434847428166418266391)
                ·
                  refine ⟨513652271142249627399587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342434847428166418266391 513652271142249627399587)
                  ·
                    refine ⟨770478406713374441099381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 513652271142249627399587 770478406713374441099381)
                    ·
                      refine ⟨72232350629378853853067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 770478406713374441099381 72232350629378853853067)
                      ·
                        rfl

theorem cell23_140672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 6, 1, 1, 5].length) (baseStart_140672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140672 prefixEnd_140672 := by exact prefixLift 140672
  have htrace : WordTrace (prefixWord ++ tailWord_140672) baseStart_140672 baseEnd_140672 := by
    simpa [prefixWord, tailWord_140672, baseEnd_140672] using wordTrace_append hprefix tailTrace_140672
  have hstable : (prefixWord ++ tailWord_140672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140672).length < 2 ^ (prefixWord ++ tailWord_140672).sum := by decide
  have hdescent : baseEnd_140672 < baseStart_140672 := by decide
  rcases family_descends (prefixWord ++ tailWord_140672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140679 : List Nat := [1, 1, 4, 2, 2, 3, 2, 1, 1, 6]
def baseStart_140679 : Nat := 118140960795 + 140679 * 2 ^ 59
def prefixEnd_140679 : Nat := 4983230072969 + 3 ^ 40 * 140679 * 2
def baseEnd_140679 : Nat := 24078648331320108821845

theorem tailTrace_140679 : CollatzResearch.WordTrace tailWord_140679 prefixEnd_140679 24078648331320108821845 := by
  unfold tailWord_140679
  simp only [CollatzResearch.WordTrace]
  refine ⟨5130984657351483905497091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3420656438234322603664727 5130984657351483905497091)
  ·
    refine ⟨7696476986027225858245637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5130984657351483905497091 7696476986027225858245637)
    ·
      refine ⟨1443089434880104848421057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7696476986027225858245637 1443089434880104848421057)
      ·
        refine ⟨1082317076160078636315793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1443089434880104848421057 1082317076160078636315793)
        ·
          refine ⟨811737807120058977236845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1082317076160078636315793 811737807120058977236845)
          ·
            refine ⟨304401677670022116463817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 811737807120058977236845 304401677670022116463817)
            ·
              refine ⟨228301258252516587347863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 304401677670022116463817 228301258252516587347863)
              ·
                refine ⟨342451887378774881021795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228301258252516587347863 342451887378774881021795)
                ·
                  refine ⟨513677831068162321532693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 342451887378774881021795 513677831068162321532693)
                  ·
                    refine ⟨24078648331320108821845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 513677831068162321532693 24078648331320108821845)
                    ·
                      rfl

theorem cell23_140679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_140679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140679 prefixEnd_140679 := by exact prefixLift 140679
  have htrace : WordTrace (prefixWord ++ tailWord_140679) baseStart_140679 baseEnd_140679 := by
    simpa [prefixWord, tailWord_140679, baseEnd_140679] using wordTrace_append hprefix tailTrace_140679
  have hstable : (prefixWord ++ tailWord_140679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140679).length < 2 ^ (prefixWord ++ tailWord_140679).sum := by decide
  have hdescent : baseEnd_140679 < baseStart_140679 := by decide
  rcases family_descends (prefixWord ++ tailWord_140679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140700 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_140700 : Nat := 118140960795 + 140700 * 2 ^ 59
def prefixEnd_140700 : Nat := 4983230072969 + 3 ^ 40 * 140700 * 2
def baseEnd_140700 : Nat := 24082242695901581434313

theorem tailTrace_140700 : CollatzResearch.WordTrace tailWord_140700 prefixEnd_140700 24082242695901581434313 := by
  unfold tailWord_140700
  simp only [CollatzResearch.WordTrace]
  refine ⟨2565875295137702246005777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3421167060183602994674369 2565875295137702246005777)
  ·
    refine ⟨1924406471353276684504333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2565875295137702246005777 1924406471353276684504333)
    ·
      refine ⟨721652426757478756689125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1924406471353276684504333 721652426757478756689125)
      ·
        refine ⟨135309830017027266879211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 721652426757478756689125 135309830017027266879211)
        ·
          refine ⟨202964745025540900318817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135309830017027266879211 202964745025540900318817)
          ·
            refine ⟨152223558769155675239113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 202964745025540900318817 152223558769155675239113)
            ·
              refine ⟨114167669076866756429335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152223558769155675239113 114167669076866756429335)
              ·
                refine ⟨171251503615300134644003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114167669076866756429335 171251503615300134644003)
                ·
                  refine ⟨256877255422950201966005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171251503615300134644003 256877255422950201966005)
                  ·
                    refine ⟨24082242695901581434313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 256877255422950201966005 24082242695901581434313)
                    ·
                      rfl

theorem cell23_140700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_140700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140700 prefixEnd_140700 := by exact prefixLift 140700
  have htrace : WordTrace (prefixWord ++ tailWord_140700) baseStart_140700 baseEnd_140700 := by
    simpa [prefixWord, tailWord_140700, baseEnd_140700] using wordTrace_append hprefix tailTrace_140700
  have hstable : (prefixWord ++ tailWord_140700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140700).length < 2 ^ (prefixWord ++ tailWord_140700).sum := by decide
  have hdescent : baseEnd_140700 < baseStart_140700 := by decide
  rcases family_descends (prefixWord ++ tailWord_140700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140703 : List Nat := [1, 1, 2, 5, 1, 4, 2, 1, 1, 1, 4]
def baseStart_140703 : Nat := 118140960795 + 140703 * 2 ^ 59
def prefixEnd_140703 : Nat := 4983230072969 + 3 ^ 40 * 140703 * 2
def baseEnd_140703 : Nat := 72248268529668232565425

theorem tailTrace_140703 : CollatzResearch.WordTrace tailWord_140703 prefixEnd_140703 72248268529668232565425 := by
  unfold tailWord_140703
  simp only [CollatzResearch.WordTrace]
  refine ⟨5131860009264536004370763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3421240006176357336247175 5131860009264536004370763)
  ·
    refine ⟨7697790013896804006556145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5131860009264536004370763 7697790013896804006556145)
    ·
      refine ⟨5773342510422603004917109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7697790013896804006556145 5773342510422603004917109)
      ·
        refine ⟨541250860352119031710979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5773342510422603004917109 541250860352119031710979)
        ·
          refine ⟨811876290528178547566469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 541250860352119031710979 811876290528178547566469)
          ·
            refine ⟨152226804474033477668713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 811876290528178547566469 152226804474033477668713)
            ·
              refine ⟨114170103355525108251535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152226804474033477668713 114170103355525108251535)
              ·
                refine ⟨171255155033287662377303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114170103355525108251535 171255155033287662377303)
                ·
                  refine ⟨256882732549931493565955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171255155033287662377303 256882732549931493565955)
                  ·
                    refine ⟨385324098824897240348933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 256882732549931493565955 385324098824897240348933)
                    ·
                      refine ⟨72248268529668232565425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 385324098824897240348933 72248268529668232565425)
                      ·
                        rfl

theorem cell23_140703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_140703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140703 prefixEnd_140703 := by exact prefixLift 140703
  have htrace : WordTrace (prefixWord ++ tailWord_140703) baseStart_140703 baseEnd_140703 := by
    simpa [prefixWord, tailWord_140703, baseEnd_140703] using wordTrace_append hprefix tailTrace_140703
  have hstable : (prefixWord ++ tailWord_140703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140703).length < 2 ^ (prefixWord ++ tailWord_140703).sum := by decide
  have hdescent : baseEnd_140703 < baseStart_140703 := by decide
  rcases family_descends (prefixWord ++ tailWord_140703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140722 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_140722 : Nat := 118140960795 + 140722 * 2 ^ 59
def prefixEnd_140722 : Nat := 4983230072969 + 3 ^ 40 * 140722 * 2
def baseEnd_140722 : Nat := 24086008220701219409279

theorem tailTrace_140722 : CollatzResearch.WordTrace tailWord_140722 prefixEnd_140722 24086008220701219409279 := by
  unfold tailWord_140722
  simp only [CollatzResearch.WordTrace]
  refine ⟨1283138249048925562328105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3421701997463801499541613 1283138249048925562328105)
  ·
    refine ⟨962353686786694171746079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1283138249048925562328105 962353686786694171746079)
    ·
      refine ⟨1443530530180041257619119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 962353686786694171746079 1443530530180041257619119)
      ·
        refine ⟨2165295795270061886428679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1443530530180041257619119 2165295795270061886428679)
        ·
          refine ⟨3247943692905092829643019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2165295795270061886428679 3247943692905092829643019)
          ·
            refine ⟨4871915539357639244464529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3247943692905092829643019 4871915539357639244464529)
            ·
              refine ⟨3653936654518229433348397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4871915539357639244464529 3653936654518229433348397)
              ·
                refine ⟨1370226245444336037505649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3653936654518229433348397 1370226245444336037505649)
                ·
                  refine ⟨1027669684083252028129237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1370226245444336037505649 1027669684083252028129237)
                  ·
                    refine ⟨24086008220701219409279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1027669684083252028129237 24086008220701219409279)
                    ·
                      rfl

theorem cell23_140722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_140722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140722 prefixEnd_140722 := by exact prefixLift 140722
  have htrace : WordTrace (prefixWord ++ tailWord_140722) baseStart_140722 baseEnd_140722 := by
    simpa [prefixWord, tailWord_140722, baseEnd_140722] using wordTrace_append hprefix tailTrace_140722
  have hstable : (prefixWord ++ tailWord_140722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140722).length < 2 ^ (prefixWord ++ tailWord_140722).sum := by decide
  have hdescent : baseEnd_140722 < baseStart_140722 := by decide
  rcases family_descends (prefixWord ++ tailWord_140722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140736 : List Nat := [2, 1, 1, 2, 3, 1, 2, 5, 2, 1, 3]
def baseStart_140736 : Nat := 118140960795 + 140736 * 2 ^ 59
def prefixEnd_140736 : Nat := 4983230072969 + 3 ^ 40 * 140736 * 2
def baseEnd_140736 : Nat := 72265213391266603452773

theorem tailTrace_140736 : CollatzResearch.WordTrace tailWord_140736 prefixEnd_140736 72265213391266603452773 := by
  unfold tailWord_140736
  simp only [CollatzResearch.WordTrace]
  refine ⟨2566531809072491320161031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3422042412096655093548041 2566531809072491320161031)
  ·
    refine ⟨3849797713608736980241547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2566531809072491320161031 3849797713608736980241547)
    ·
      refine ⟨5774696570413105470362321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3849797713608736980241547 5774696570413105470362321)
      ·
        refine ⟨4331022427809829102771741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5774696570413105470362321 4331022427809829102771741)
        ·
          refine ⟨1624133410428685913539403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4331022427809829102771741 1624133410428685913539403)
          ·
            refine ⟨2436200115643028870309105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1624133410428685913539403 2436200115643028870309105)
            ·
              refine ⟨1827150086732271652731829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2436200115643028870309105 1827150086732271652731829)
              ·
                refine ⟨171295320631150467443609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1827150086732271652731829 171295320631150467443609)
                ·
                  refine ⟨128471490473362850582707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 171295320631150467443609 128471490473362850582707)
                  ·
                    refine ⟨192707235710044275874061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128471490473362850582707 192707235710044275874061)
                    ·
                      refine ⟨72265213391266603452773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 192707235710044275874061 72265213391266603452773)
                      ·
                        rfl

theorem cell23_140736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 5, 2, 1, 3].length) (baseStart_140736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140736 prefixEnd_140736 := by exact prefixLift 140736
  have htrace : WordTrace (prefixWord ++ tailWord_140736) baseStart_140736 baseEnd_140736 := by
    simpa [prefixWord, tailWord_140736, baseEnd_140736] using wordTrace_append hprefix tailTrace_140736
  have hstable : (prefixWord ++ tailWord_140736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140736).length < 2 ^ (prefixWord ++ tailWord_140736).sum := by decide
  have hdescent : baseEnd_140736 < baseStart_140736 := by decide
  rcases family_descends (prefixWord ++ tailWord_140736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140833 : List Nat := [1, 2, 3, 2, 2, 2, 4, 2, 5]
def baseStart_140833 : Nat := 118140960795 + 140833 * 2 ^ 59
def prefixEnd_140833 : Nat := 4983230072969 + 3 ^ 40 * 140833 * 2
def baseEnd_140833 : Nat := 8035002334972524882203

theorem tailTrace_140833 : CollatzResearch.WordTrace tailWord_140833 prefixEnd_140833 8035002334972524882203 := by
  unfold tailWord_140833
  simp only [CollatzResearch.WordTrace]
  refine ⟨5136601498793568206603153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3424400999195712137735435 5136601498793568206603153)
  ·
    refine ⟨3852451124095176154952365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5136601498793568206603153 3852451124095176154952365)
    ·
      refine ⟨1444669171535691058107137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3852451124095176154952365 1444669171535691058107137)
      ·
        refine ⟨1083501878651768293580353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1444669171535691058107137 1083501878651768293580353)
        ·
          refine ⟨812626408988826220185265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1083501878651768293580353 812626408988826220185265)
          ·
            refine ⟨609469806741619665138949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 812626408988826220185265 609469806741619665138949)
            ·
              refine ⟨114275588764053687213553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 609469806741619665138949 114275588764053687213553)
              ·
                refine ⟨85706691573040265410165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114275588764053687213553 85706691573040265410165)
                ·
                  refine ⟨8035002334972524882203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85706691573040265410165 8035002334972524882203)
                  ·
                    rfl

theorem cell23_140833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 4, 2, 5].length) (baseStart_140833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140833 prefixEnd_140833 := by exact prefixLift 140833
  have htrace : WordTrace (prefixWord ++ tailWord_140833) baseStart_140833 baseEnd_140833 := by
    simpa [prefixWord, tailWord_140833, baseEnd_140833] using wordTrace_append hprefix tailTrace_140833
  have hstable : (prefixWord ++ tailWord_140833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140833).length < 2 ^ (prefixWord ++ tailWord_140833).sum := by decide
  have hdescent : baseEnd_140833 < baseStart_140833 := by decide
  rcases family_descends (prefixWord ++ tailWord_140833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140849 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_140849 : Nat := 118140960795 + 140849 * 2 ^ 59
def prefixEnd_140849 : Nat := 4983230072969 + 3 ^ 40 * 140849 * 2
def baseEnd_140849 : Nat := 72323236705224661339753

theorem tailTrace_140849 : CollatzResearch.WordTrace tailWord_140849 prefixEnd_140849 72323236705224661339753 := by
  unfold tailWord_140849
  simp only [CollatzResearch.WordTrace]
  refine ⟨5137185066735602939185601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3424790044490401959457067 5137185066735602939185601)
  ·
    refine ⟨3852888800051702204389201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5137185066735602939185601 3852888800051702204389201)
    ·
      refine ⟨2889666600038776653291901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3852888800051702204389201 2889666600038776653291901)
      ·
        refine ⟨1083624975014541244984463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2889666600038776653291901 1083624975014541244984463)
        ·
          refine ⟨1625437462521811867476695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1083624975014541244984463 1625437462521811867476695)
          ·
            refine ⟨2438156193782717801215043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1625437462521811867476695 2438156193782717801215043)
            ·
              refine ⟨3657234290674076701822565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2438156193782717801215043 3657234290674076701822565)
              ·
                refine ⟨685731429501389381591731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3657234290674076701822565 685731429501389381591731)
                ·
                  refine ⟨1028597144252084072387597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 685731429501389381591731 1028597144252084072387597)
                  ·
                    refine ⟨385723929094531527145349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1028597144252084072387597 385723929094531527145349)
                    ·
                      refine ⟨72323236705224661339753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 385723929094531527145349 72323236705224661339753)
                      ·
                        rfl

theorem cell23_140849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_140849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140849 prefixEnd_140849 := by exact prefixLift 140849
  have htrace : WordTrace (prefixWord ++ tailWord_140849) baseStart_140849 baseEnd_140849 := by
    simpa [prefixWord, tailWord_140849, baseEnd_140849] using wordTrace_append hprefix tailTrace_140849
  have hstable : (prefixWord ++ tailWord_140849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140849).length < 2 ^ (prefixWord ++ tailWord_140849).sum := by decide
  have hdescent : baseEnd_140849 < baseStart_140849 := by decide
  rcases family_descends (prefixWord ++ tailWord_140849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140969 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_140969 : Nat := 118140960795 + 140969 * 2 ^ 59
def prefixEnd_140969 : Nat := 4983230072969 + 3 ^ 40 * 140969 * 2
def baseEnd_140969 : Nat := 72384854383764191839201

theorem tailTrace_140969 : CollatzResearch.WordTrace tailWord_140969 prefixEnd_140969 72384854383764191839201 := by
  unfold tailWord_140969
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141561826300863433553961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3427707884200575622369307 5141561826300863433553961)
  ·
    refine ⟨3856171369725647575165471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5141561826300863433553961 3856171369725647575165471)
    ·
      refine ⟨5784257054588471362748207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3856171369725647575165471 5784257054588471362748207)
      ·
        refine ⟨8676385581882707044122311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5784257054588471362748207 8676385581882707044122311)
        ·
          refine ⟨13014578372824060566183467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8676385581882707044122311 13014578372824060566183467)
          ·
            refine ⟨19521867559236090849275201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13014578372824060566183467 19521867559236090849275201)
            ·
              refine ⟨14641400669427068136956401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19521867559236090849275201 14641400669427068136956401)
              ·
                refine ⟨10981050502070301102717301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14641400669427068136956401 10981050502070301102717301)
                ·
                  refine ⟨1029473484569090728379747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10981050502070301102717301 1029473484569090728379747)
                  ·
                    refine ⟨1544210226853636092569621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1029473484569090728379747 1544210226853636092569621)
                    ·
                      refine ⟨72384854383764191839201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1544210226853636092569621 72384854383764191839201)
                      ·
                        rfl

theorem cell23_140969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_140969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140969 prefixEnd_140969 := by exact prefixLift 140969
  have htrace : WordTrace (prefixWord ++ tailWord_140969) baseStart_140969 baseEnd_140969 := by
    simpa [prefixWord, tailWord_140969, baseEnd_140969] using wordTrace_append hprefix tailTrace_140969
  have hstable : (prefixWord ++ tailWord_140969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140969).length < 2 ^ (prefixWord ++ tailWord_140969).sum := by decide
  have hdescent : baseEnd_140969 < baseStart_140969 := by decide
  rcases family_descends (prefixWord ++ tailWord_140969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140973 : List Nat := [1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_140973 : Nat := 118140960795 + 140973 * 2 ^ 59
def prefixEnd_140973 : Nat := 4983230072969 + 3 ^ 40 * 140973 * 2
def baseEnd_140973 : Nat := 72386908306382176189183

theorem tailTrace_140973 : CollatzResearch.WordTrace tailWord_140973 prefixEnd_140973 72386908306382176189183 := by
  unfold tailWord_140973
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141707718286372116699573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3427805145524248077799715 5141707718286372116699573)
  ·
    refine ⟨482035098589347385940585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5141707718286372116699573 482035098589347385940585)
    ·
      refine ⟨361526323942010539455439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 482035098589347385940585 361526323942010539455439)
      ·
        refine ⟨542289485913015809183159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361526323942010539455439 542289485913015809183159)
        ·
          refine ⟨813434228869523713774739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 542289485913015809183159 813434228869523713774739)
          ·
            refine ⟨1220151343304285570662109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 813434228869523713774739 1220151343304285570662109)
            ·
              refine ⟨457556753739107088998291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1220151343304285570662109 457556753739107088998291)
              ·
                refine ⟨686335130608660633497437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 457556753739107088998291 686335130608660633497437)
                ·
                  refine ⟨257375673978247737561539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 686335130608660633497437 257375673978247737561539)
                  ·
                    refine ⟨386063510967371606342309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 257375673978247737561539 386063510967371606342309)
                    ·
                      refine ⟨72386908306382176189183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 386063510967371606342309 72386908306382176189183)
                      ·
                        rfl

theorem cell23_140973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_140973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140973 prefixEnd_140973 := by exact prefixLift 140973
  have htrace : WordTrace (prefixWord ++ tailWord_140973) baseStart_140973 baseEnd_140973 := by
    simpa [prefixWord, tailWord_140973, baseEnd_140973] using wordTrace_append hprefix tailTrace_140973
  have hstable : (prefixWord ++ tailWord_140973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140973).length < 2 ^ (prefixWord ++ tailWord_140973).sum := by decide
  have hdescent : baseEnd_140973 < baseStart_140973 := by decide
  rcases family_descends (prefixWord ++ tailWord_140973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140979 : List Nat := [1, 1, 1, 2, 3, 3, 1, 11]
def baseStart_140979 : Nat := 118140960795 + 140979 * 2 ^ 59
def prefixEnd_140979 : Nat := 4983230072969 + 3 ^ 40 * 140979 * 2
def baseEnd_140979 : Nat := 2681110710752190841265

theorem tailTrace_140979 : CollatzResearch.WordTrace tailWord_140979 prefixEnd_140979 2681110710752190841265 := by
  unfold tailWord_140979
  simp only [CollatzResearch.WordTrace]
  refine ⟨5141926556264635141417991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3427951037509756760945327 5141926556264635141417991)
  ·
    refine ⟨7712889834396952712126987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5141926556264635141417991 7712889834396952712126987)
    ·
      refine ⟨11569334751595429068190481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7712889834396952712126987 11569334751595429068190481)
      ·
        refine ⟨8677001063696571801142861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11569334751595429068190481 8677001063696571801142861)
        ·
          refine ⟨3253875398886214425428573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8677001063696571801142861 3253875398886214425428573)
          ·
            refine ⟨1220203274582330409535715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3253875398886214425428573 1220203274582330409535715)
            ·
              refine ⟨1830304911873495614303573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1220203274582330409535715 1830304911873495614303573)
              ·
                refine ⟨2681110710752190841265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 1830304911873495614303573 2681110710752190841265)
                ·
                  rfl

theorem cell23_140979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 11].length) (baseStart_140979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140979 prefixEnd_140979 := by exact prefixLift 140979
  have htrace : WordTrace (prefixWord ++ tailWord_140979) baseStart_140979 baseEnd_140979 := by
    simpa [prefixWord, tailWord_140979, baseEnd_140979] using wordTrace_append hprefix tailTrace_140979
  have hstable : (prefixWord ++ tailWord_140979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140979).length < 2 ^ (prefixWord ++ tailWord_140979).sum := by decide
  have hdescent : baseEnd_140979 < baseStart_140979 := by decide
  rcases family_descends (prefixWord ++ tailWord_140979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_140986 : List Nat := [3, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4]
def baseStart_140986 : Nat := 118140960795 + 140986 * 2 ^ 59
def prefixEnd_140986 : Nat := 4983230072969 + 3 ^ 40 * 140986 * 2
def baseEnd_140986 : Nat := 72393583554890625326623

theorem tailTrace_140986 : CollatzResearch.WordTrace tailWord_140986 prefixEnd_140986 72393583554890625326623 := by
  unfold tailWord_140986
  simp only [CollatzResearch.WordTrace]
  refine ⟨1285545466809818834230703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3428121244826183557948541 1285545466809818834230703)
  ·
    refine ⟨1928318200214728251346055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1285545466809818834230703 1928318200214728251346055)
    ·
      refine ⟨2892477300322092377019083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1928318200214728251346055 2892477300322092377019083)
      ·
        refine ⟨4338715950483138565528625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2892477300322092377019083 4338715950483138565528625)
        ·
          refine ⟨3254036962862353924146469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4338715950483138565528625 3254036962862353924146469)
          ·
            refine ⟨610131930536691360777463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3254036962862353924146469 610131930536691360777463)
            ·
              refine ⟨915197895805037041166195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 610131930536691360777463 915197895805037041166195)
              ·
                refine ⟨1372796843707555561749293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 915197895805037041166195 1372796843707555561749293)
                ·
                  refine ⟨514798816390333335655985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1372796843707555561749293 514798816390333335655985)
                  ·
                    refine ⟨386099112292750001741989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 514798816390333335655985 386099112292750001741989)
                    ·
                      refine ⟨72393583554890625326623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 386099112292750001741989 72393583554890625326623)
                      ·
                        rfl

theorem cell23_140986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 3, 2, 4].length) (baseStart_140986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_140986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_140986 prefixEnd_140986 := by exact prefixLift 140986
  have htrace : WordTrace (prefixWord ++ tailWord_140986) baseStart_140986 baseEnd_140986 := by
    simpa [prefixWord, tailWord_140986, baseEnd_140986] using wordTrace_append hprefix tailTrace_140986
  have hstable : (prefixWord ++ tailWord_140986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_140986).length < 2 ^ (prefixWord ++ tailWord_140986).sum := by decide
  have hdescent : baseEnd_140986 < baseStart_140986 := by decide
  rcases family_descends (prefixWord ++ tailWord_140986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141023 : List Nat := [1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 3]
def baseStart_141023 : Nat := 118140960795 + 141023 * 2 ^ 59
def prefixEnd_141023 : Nat := 4983230072969 + 3 ^ 40 * 141023 * 2
def baseEnd_141023 : Nat := 72412582339106980563953

theorem tailTrace_141023 : CollatzResearch.WordTrace tailWord_141023 prefixEnd_141023 72412582339106980563953 := by
  unfold tailWord_141023
  simp only [CollatzResearch.WordTrace]
  refine ⟨5143531368105230656019723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3429020912070153770679815 5143531368105230656019723)
  ·
    refine ⟨7715297052157845984029585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5143531368105230656019723 7715297052157845984029585)
    ·
      refine ⟨5786472789118384488022189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7715297052157845984029585 5786472789118384488022189)
      ·
        refine ⟨2169927295919394183008321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5786472789118384488022189 2169927295919394183008321)
        ·
          refine ⟨1627445471939545637256241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2169927295919394183008321 1627445471939545637256241)
          ·
            refine ⟨1220584103954659227942181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1627445471939545637256241 1220584103954659227942181)
            ·
              refine ⟨228859519491498605239159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1220584103954659227942181 228859519491498605239159)
              ·
                refine ⟨343289279237247907858739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228859519491498605239159 343289279237247907858739)
                ·
                  refine ⟨514933918855871861788109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343289279237247907858739 514933918855871861788109)
                  ·
                    refine ⟨193100219570951948170541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 514933918855871861788109 193100219570951948170541)
                    ·
                      refine ⟨72412582339106980563953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193100219570951948170541 72412582339106980563953)
                      ·
                        rfl

theorem cell23_141023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_141023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141023 prefixEnd_141023 := by exact prefixLift 141023
  have htrace : WordTrace (prefixWord ++ tailWord_141023) baseStart_141023 baseEnd_141023 := by
    simpa [prefixWord, tailWord_141023, baseEnd_141023] using wordTrace_append hprefix tailTrace_141023
  have hstable : (prefixWord ++ tailWord_141023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141023).length < 2 ^ (prefixWord ++ tailWord_141023).sum := by decide
  have hdescent : baseEnd_141023 < baseStart_141023 := by decide
  rcases family_descends (prefixWord ++ tailWord_141023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141044 : List Nat := [2, 6, 1, 1, 1, 2, 1, 3, 1, 2, 3]
def baseStart_141044 : Nat := 118140960795 + 141044 * 2 ^ 59
def prefixEnd_141044 : Nat := 4983230072969 + 3 ^ 40 * 141044 * 2
def baseEnd_141044 : Nat := 72423365432851398401357

theorem tailTrace_141044 : CollatzResearch.WordTrace tailWord_141044 prefixEnd_141044 72423365432851398401357 := by
  unfold tailWord_141044
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572148650514575621267093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3429531534019434161689457 2572148650514575621267093)
  ·
    refine ⟨120569467992870732246895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2572148650514575621267093 120569467992870732246895)
    ·
      refine ⟨180854201989306098370343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120569467992870732246895 180854201989306098370343)
      ·
        refine ⟨271281302983959147555515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180854201989306098370343 271281302983959147555515)
        ·
          refine ⟨406921954475938721333273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271281302983959147555515 406921954475938721333273)
          ·
            refine ⟨305191465856954040999955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 406921954475938721333273 305191465856954040999955)
            ·
              refine ⟨457787198785431061499933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305191465856954040999955 457787198785431061499933)
              ·
                refine ⟨171670199544536648062475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 457787198785431061499933 171670199544536648062475)
                ·
                  refine ⟨257505299316804972093713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171670199544536648062475 257505299316804972093713)
                  ·
                    refine ⟨193128974487603729070285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257505299316804972093713 193128974487603729070285)
                    ·
                      refine ⟨72423365432851398401357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193128974487603729070285 72423365432851398401357)
                      ·
                        rfl

theorem cell23_141044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_141044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141044 prefixEnd_141044 := by exact prefixLift 141044
  have htrace : WordTrace (prefixWord ++ tailWord_141044) baseStart_141044 baseEnd_141044 := by
    simpa [prefixWord, tailWord_141044, baseEnd_141044] using wordTrace_append hprefix tailTrace_141044
  have hstable : (prefixWord ++ tailWord_141044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141044).length < 2 ^ (prefixWord ++ tailWord_141044).sum := by decide
  have hdescent : baseEnd_141044 < baseStart_141044 := by decide
  rcases family_descends (prefixWord ++ tailWord_141044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141080 : List Nat := [2, 1, 2, 3, 1, 1, 5, 1, 1, 4, 2]
def baseStart_141080 : Nat := 118140960795 + 141080 * 2 ^ 59
def prefixEnd_141080 : Nat := 4983230072969 + 3 ^ 40 * 141080 * 2
def baseEnd_141080 : Nat := 72441850736413257551191

theorem tailTrace_141080 : CollatzResearch.WordTrace tailWord_141080 prefixEnd_141080 72441850736413257551191 := by
  unfold tailWord_141080
  simp only [CollatzResearch.WordTrace]
  refine ⟨2572805164449364695422347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3430406885932486260563129 2572805164449364695422347)
  ·
    refine ⟨3859207746674047043133521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2572805164449364695422347 3859207746674047043133521)
    ·
      refine ⟨2894405810005535282350141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3859207746674047043133521 2894405810005535282350141)
      ·
        refine ⟨1085402178752075730881303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2894405810005535282350141 1085402178752075730881303)
        ·
          refine ⟨1628103268128113596321955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1085402178752075730881303 1628103268128113596321955)
          ·
            refine ⟨2442154902192170394482933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1628103268128113596321955 2442154902192170394482933)
            ·
              refine ⟨228952022080515974482775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2442154902192170394482933 228952022080515974482775)
              ·
                refine ⟨343428033120773961724163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 228952022080515974482775 343428033120773961724163)
                ·
                  refine ⟨515142049681160942586245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343428033120773961724163 515142049681160942586245)
                  ·
                    refine ⟨96589134315217676734921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 515142049681160942586245 96589134315217676734921)
                    ·
                      refine ⟨72441850736413257551191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96589134315217676734921 72441850736413257551191)
                      ·
                        rfl

theorem cell23_141080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_141080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141080 prefixEnd_141080 := by exact prefixLift 141080
  have htrace : WordTrace (prefixWord ++ tailWord_141080) baseStart_141080 baseEnd_141080 := by
    simpa [prefixWord, tailWord_141080, baseEnd_141080] using wordTrace_append hprefix tailTrace_141080
  have hstable : (prefixWord ++ tailWord_141080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141080).length < 2 ^ (prefixWord ++ tailWord_141080).sum := by decide
  have hdescent : baseEnd_141080 < baseStart_141080 := by decide
  rcases family_descends (prefixWord ++ tailWord_141080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141170 : List Nat := [3, 2, 1, 2, 1, 1, 1, 4, 2, 4, 2]
def baseStart_141170 : Nat := 118140960795 + 141170 * 2 ^ 59
def prefixEnd_141170 : Nat := 4983230072969 + 3 ^ 40 * 141170 * 2
def baseEnd_141170 : Nat := 72488063995317905425777

theorem tailTrace_141170 : CollatzResearch.WordTrace tailWord_141170 prefixEnd_141170 72488063995317905425777 := by
  unfold tailWord_141170
  simp only [CollatzResearch.WordTrace]
  refine ⟨1287223224643168690405241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3432595265715116507747309 1287223224643168690405241)
  ·
    refine ⟨965417418482376517803931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1287223224643168690405241 965417418482376517803931)
    ·
      refine ⟨1448126127723564776705897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 965417418482376517803931 1448126127723564776705897)
      ·
        refine ⟨1086094595792673582529423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1448126127723564776705897 1086094595792673582529423)
        ·
          refine ⟨1629141893689010373794135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086094595792673582529423 1629141893689010373794135)
          ·
            refine ⟨2443712840533515560691203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1629141893689010373794135 2443712840533515560691203)
            ·
              refine ⟨3665569260800273341036805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2443712840533515560691203 3665569260800273341036805)
              ·
                refine ⟨687294236400051251444401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3665569260800273341036805 687294236400051251444401)
                ·
                  refine ⟨515470677300038438583301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 687294236400051251444401 515470677300038438583301)
                  ·
                    refine ⟨96650751993757207234369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 515470677300038438583301 96650751993757207234369)
                    ·
                      refine ⟨72488063995317905425777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96650751993757207234369 72488063995317905425777)
                      ·
                        rfl

theorem cell23_141170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_141170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141170 prefixEnd_141170 := by exact prefixLift 141170
  have htrace : WordTrace (prefixWord ++ tailWord_141170) baseStart_141170 baseEnd_141170 := by
    simpa [prefixWord, tailWord_141170, baseEnd_141170] using wordTrace_append hprefix tailTrace_141170
  have hstable : (prefixWord ++ tailWord_141170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141170).length < 2 ^ (prefixWord ++ tailWord_141170).sum := by decide
  have hdescent : baseEnd_141170 < baseStart_141170 := by decide
  rcases family_descends (prefixWord ++ tailWord_141170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141173 : List Nat := [1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_141173 : Nat := 118140960795 + 141173 * 2 ^ 59
def prefixEnd_141173 : Nat := 4983230072969 + 3 ^ 40 * 141173 * 2
def baseEnd_141173 : Nat := 72489604437281393688263

theorem tailTrace_141173 : CollatzResearch.WordTrace tailWord_141173 prefixEnd_141173 72489604437281393688263 := by
  unfold tailWord_141173
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149002317561806273980173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3432668211707870849320115 5149002317561806273980173)
  ·
    refine ⟨1930875869085677352742565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5149002317561806273980173 1930875869085677352742565)
    ·
      refine ⟨362039225453564503639231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1930875869085677352742565 362039225453564503639231)
      ·
        refine ⟨543058838180346755458847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362039225453564503639231 543058838180346755458847)
        ·
          refine ⟨814588257270520133188271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543058838180346755458847 814588257270520133188271)
          ·
            refine ⟨1221882385905780199782407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814588257270520133188271 1221882385905780199782407)
            ·
              refine ⟨1832823578858670299673611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1221882385905780199782407 1832823578858670299673611)
              ·
                refine ⟨2749235368288005449510417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1832823578858670299673611 2749235368288005449510417)
                ·
                  refine ⟨2061926526216004087132813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2749235368288005449510417 2061926526216004087132813)
                  ·
                    refine ⟨773222447331001532674805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2061926526216004087132813 773222447331001532674805)
                    ·
                      refine ⟨72489604437281393688263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 773222447331001532674805 72489604437281393688263)
                      ·
                        rfl

theorem cell23_141173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_141173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141173 prefixEnd_141173 := by exact prefixLift 141173
  have htrace : WordTrace (prefixWord ++ tailWord_141173) baseStart_141173 baseEnd_141173 := by
    simpa [prefixWord, tailWord_141173, baseEnd_141173] using wordTrace_append hprefix tailTrace_141173
  have hstable : (prefixWord ++ tailWord_141173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141173).length < 2 ^ (prefixWord ++ tailWord_141173).sum := by decide
  have hdescent : baseEnd_141173 < baseStart_141173 := by decide
  rcases family_descends (prefixWord ++ tailWord_141173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141176 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 12]
def baseStart_141176 : Nat := 118140960795 + 141176 * 2 ^ 59
def prefixEnd_141176 : Nat := 4983230072969 + 3 ^ 40 * 141176 * 2
def baseEnd_141176 : Nat := 8054571653249431327861

theorem tailTrace_141176 : CollatzResearch.WordTrace tailWord_141176 prefixEnd_141176 8054571653249431327861 := by
  unfold tailWord_141176
  simp only [CollatzResearch.WordTrace]
  refine ⟨2574555868275468893169691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3432741157700625190892921 2574555868275468893169691)
  ·
    refine ⟨3861833802413203339754537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2574555868275468893169691 3861833802413203339754537)
    ·
      refine ⟨2896375351809902504815903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3861833802413203339754537 2896375351809902504815903)
      ·
        refine ⟨4344563027714853757223855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2896375351809902504815903 4344563027714853757223855)
        ·
          refine ⟨6516844541572280635835783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4344563027714853757223855 6516844541572280635835783)
          ·
            refine ⟨9775266812358420953753675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6516844541572280635835783 9775266812358420953753675)
            ·
              refine ⟨14662900218537631430630513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9775266812358420953753675 14662900218537631430630513)
              ·
                refine ⟨10997175163903223572972885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14662900218537631430630513 10997175163903223572972885)
                ·
                  refine ⟨8054571653249431327861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 10997175163903223572972885 8054571653249431327861)
                  ·
                    rfl

theorem cell23_141176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 12].length) (baseStart_141176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141176 prefixEnd_141176 := by exact prefixLift 141176
  have htrace : WordTrace (prefixWord ++ tailWord_141176) baseStart_141176 baseEnd_141176 := by
    simpa [prefixWord, tailWord_141176, baseEnd_141176] using wordTrace_append hprefix tailTrace_141176
  have hstable : (prefixWord ++ tailWord_141176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141176).length < 2 ^ (prefixWord ++ tailWord_141176).sum := by decide
  have hdescent : baseEnd_141176 < baseStart_141176 := by decide
  rcases family_descends (prefixWord ++ tailWord_141176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141193 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 6]
def baseStart_141193 : Nat := 118140960795 + 141193 * 2 ^ 59
def prefixEnd_141193 : Nat := 4983230072969 + 3 ^ 40 * 141193 * 2
def baseEnd_141193 : Nat := 8055541561152368382019

theorem tailTrace_141193 : CollatzResearch.WordTrace tailWord_141193 prefixEnd_141193 8055541561152368382019 := by
  unfold tailWord_141193
  simp only [CollatzResearch.WordTrace]
  refine ⟨5149731777489349689708233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3433154518326233126472155 5149731777489349689708233)
  ·
    refine ⟨3862298833117012267281175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5149731777489349689708233 3862298833117012267281175)
    ·
      refine ⟨5793448249675518400921763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3862298833117012267281175 5793448249675518400921763)
      ·
        refine ⟨8690172374513277601382645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5793448249675518400921763 8690172374513277601382645)
        ·
          refine ⟨814703660110619775129623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8690172374513277601382645 814703660110619775129623)
          ·
            refine ⟨1222055490165929662694435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 814703660110619775129623 1222055490165929662694435)
            ·
              refine ⟨1833083235248894494041653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222055490165929662694435 1833083235248894494041653)
              ·
                refine ⟨171851553304583858816405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1833083235248894494041653 171851553304583858816405)
                ·
                  refine ⟨8055541561152368382019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171851553304583858816405 8055541561152368382019)
                  ·
                    rfl

theorem cell23_141193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 6].length) (baseStart_141193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141193 prefixEnd_141193 := by exact prefixLift 141193
  have htrace : WordTrace (prefixWord ++ tailWord_141193) baseStart_141193 baseEnd_141193 := by
    simpa [prefixWord, tailWord_141193, baseEnd_141193] using wordTrace_append hprefix tailTrace_141193
  have hstable : (prefixWord ++ tailWord_141193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141193).length < 2 ^ (prefixWord ++ tailWord_141193).sum := by decide
  have hdescent : baseEnd_141193 < baseStart_141193 := by decide
  rcases family_descends (prefixWord ++ tailWord_141193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141207 : List Nat := [1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_141207 : Nat := 118140960795 + 141207 * 2 ^ 59
def prefixEnd_141207 : Nat := 4983230072969 + 3 ^ 40 * 141207 * 2
def baseEnd_141207 : Nat := 72507062779534260663107

theorem tailTrace_141207 : CollatzResearch.WordTrace tailWord_141207 prefixEnd_141207 72507062779534260663107 := by
  unfold tailWord_141207
  simp only [CollatzResearch.WordTrace]
  refine ⟨5150242399438630080717875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3433494932959086720478583 5150242399438630080717875)
  ·
    refine ⟨7725363599157945121076813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5150242399438630080717875 7725363599157945121076813)
    ·
      refine ⟨2897011349684229420403805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7725363599157945121076813 2897011349684229420403805)
      ·
        refine ⟨1086379256131586032651427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2897011349684229420403805 1086379256131586032651427)
        ·
          refine ⟨1629568884197379048977141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1086379256131586032651427 1629568884197379048977141)
          ·
            refine ⟨152772082893504285841607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1629568884197379048977141 152772082893504285841607)
            ·
              refine ⟨229158124340256428762411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152772082893504285841607 229158124340256428762411)
              ·
                refine ⟨343737186510384643143617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229158124340256428762411 343737186510384643143617)
                ·
                  refine ⟨257802889882788482357713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343737186510384643143617 257802889882788482357713)
                  ·
                    refine ⟨193352167412091361768285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257802889882788482357713 193352167412091361768285)
                    ·
                      refine ⟨72507062779534260663107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193352167412091361768285 72507062779534260663107)
                      ·
                        rfl

theorem cell23_141207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_141207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141207 prefixEnd_141207 := by exact prefixLift 141207
  have htrace : WordTrace (prefixWord ++ tailWord_141207) baseStart_141207 baseEnd_141207 := by
    simpa [prefixWord, tailWord_141207, baseEnd_141207] using wordTrace_append hprefix tailTrace_141207
  have hstable : (prefixWord ++ tailWord_141207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141207).length < 2 ^ (prefixWord ++ tailWord_141207).sum := by decide
  have hdescent : baseEnd_141207 < baseStart_141207 := by decide
  rcases family_descends (prefixWord ++ tailWord_141207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141237 : List Nat := [1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_141237 : Nat := 118140960795 + 141237 * 2 ^ 59
def prefixEnd_141237 : Nat := 4983230072969 + 3 ^ 40 * 141237 * 2
def baseEnd_141237 : Nat := 72522467199169143287969

theorem tailTrace_141237 : CollatzResearch.WordTrace tailWord_141237 prefixEnd_141237 72522467199169143287969 := by
  unfold tailWord_141237
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151336589329945204309965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3434224392886630136206643 5151336589329945204309965)
  ·
    refine ⟨1931751220998729451616237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5151336589329945204309965 1931751220998729451616237)
    ·
      refine ⟨724406707874523544356089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1931751220998729451616237 724406707874523544356089)
      ·
        refine ⟨543305030905892658267067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 724406707874523544356089 543305030905892658267067)
        ·
          refine ⟨814957546358838987400601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543305030905892658267067 814957546358838987400601)
          ·
            refine ⟨611218159769129240550451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 814957546358838987400601 611218159769129240550451)
            ·
              refine ⟨916827239653693860825677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611218159769129240550451 916827239653693860825677)
              ·
                refine ⟨343810214870135197809629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 916827239653693860825677 343810214870135197809629)
                ·
                  refine ⟨128928830576300699178611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343810214870135197809629 128928830576300699178611)
                  ·
                    refine ⟨193393245864451048767917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128928830576300699178611 193393245864451048767917)
                    ·
                      refine ⟨72522467199169143287969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193393245864451048767917 72522467199169143287969)
                      ·
                        rfl

theorem cell23_141237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_141237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141237 prefixEnd_141237 := by exact prefixLift 141237
  have htrace : WordTrace (prefixWord ++ tailWord_141237) baseStart_141237 baseEnd_141237 := by
    simpa [prefixWord, tailWord_141237, baseEnd_141237] using wordTrace_append hprefix tailTrace_141237
  have hstable : (prefixWord ++ tailWord_141237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141237).length < 2 ^ (prefixWord ++ tailWord_141237).sum := by decide
  have hdescent : baseEnd_141237 < baseStart_141237 := by decide
  rcases family_descends (prefixWord ++ tailWord_141237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141244 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 6]
def baseStart_141244 : Nat := 118140960795 + 141244 * 2 ^ 59
def prefixEnd_141244 : Nat := 4983230072969 + 3 ^ 40 * 141244 * 2
def baseEnd_141244 : Nat := 8058451284861179544493

theorem tailTrace_141244 : CollatzResearch.WordTrace tailWord_141244 prefixEnd_141244 8058451284861179544493 := by
  unfold tailWord_141244
  simp only [CollatzResearch.WordTrace]
  refine ⟨2575795950152292699907393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3434394600203056933209857 2575795950152292699907393)
  ·
    refine ⟨1931846962614219524930545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2575795950152292699907393 1931846962614219524930545)
    ·
      refine ⟨1448885221960664643697909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1931846962614219524930545 1448885221960664643697909)
      ·
        refine ⟨135832989558812310346679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1448885221960664643697909 135832989558812310346679)
        ·
          refine ⟨203749484338218465520019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135832989558812310346679 203749484338218465520019)
          ·
            refine ⟨305624226507327698280029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203749484338218465520019 305624226507327698280029)
            ·
              refine ⟨114609084940247886855011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305624226507327698280029 114609084940247886855011)
              ·
                refine ⟨171913627410371830282517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114609084940247886855011 171913627410371830282517)
                ·
                  refine ⟨8058451284861179544493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171913627410371830282517 8058451284861179544493)
                  ·
                    rfl

theorem cell23_141244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_141244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141244 prefixEnd_141244 := by exact prefixLift 141244
  have htrace : WordTrace (prefixWord ++ tailWord_141244) baseStart_141244 baseEnd_141244 := by
    simpa [prefixWord, tailWord_141244, baseEnd_141244] using wordTrace_append hprefix tailTrace_141244
  have hstable : (prefixWord ++ tailWord_141244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141244).length < 2 ^ (prefixWord ++ tailWord_141244).sum := by decide
  have hdescent : baseEnd_141244 < baseStart_141244 := by decide
  rcases family_descends (prefixWord ++ tailWord_141244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141253 : List Nat := [1, 3, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_141253 : Nat := 118140960795 + 141253 * 2 ^ 59
def prefixEnd_141253 : Nat := 4983230072969 + 3 ^ 40 * 141253 * 2
def baseEnd_141253 : Nat := 24176894296547026895965

theorem tailTrace_141253 : CollatzResearch.WordTrace tailWord_141253 prefixEnd_141253 24176894296547026895965 := by
  unfold tailWord_141253
  simp only [CollatzResearch.WordTrace]
  refine ⟨5151920157271979936892413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3434613438181319957928275 5151920157271979936892413)
  ·
    refine ⟨1931970058976992476334655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5151920157271979936892413 1931970058976992476334655)
    ·
      refine ⟨2897955088465488714501983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1931970058976992476334655 2897955088465488714501983)
      ·
        refine ⟨4346932632698233071752975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2897955088465488714501983 4346932632698233071752975)
        ·
          refine ⟨6520398949047349607629463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4346932632698233071752975 6520398949047349607629463)
          ·
            refine ⟨9780598423571024411444195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6520398949047349607629463 9780598423571024411444195)
            ·
              refine ⟨14670897635356536617166293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9780598423571024411444195 14670897635356536617166293)
              ·
                refine ⟨343849163328668826964835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 14670897635356536617166293 343849163328668826964835)
                ·
                  refine ⟨515773744993003240447253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343849163328668826964835 515773744993003240447253)
                  ·
                    refine ⟨24176894296547026895965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 515773744993003240447253 24176894296547026895965)
                    ·
                      rfl

theorem cell23_141253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_141253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141253 prefixEnd_141253 := by exact prefixLift 141253
  have htrace : WordTrace (prefixWord ++ tailWord_141253) baseStart_141253 baseEnd_141253 := by
    simpa [prefixWord, tailWord_141253, baseEnd_141253] using wordTrace_append hprefix tailTrace_141253
  have hstable : (prefixWord ++ tailWord_141253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141253).length < 2 ^ (prefixWord ++ tailWord_141253).sum := by decide
  have hdescent : baseEnd_141253 < baseStart_141253 := by decide
  rcases family_descends (prefixWord ++ tailWord_141253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141263 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_141263 : Nat := 118140960795 + 141263 * 2 ^ 59
def prefixEnd_141263 : Nat := 4983230072969 + 3 ^ 40 * 141263 * 2
def baseEnd_141263 : Nat := 72535817696186041562849

theorem tailTrace_141263 : CollatzResearch.WordTrace tailWord_141263 prefixEnd_141263 72535817696186041562849 := by
  unfold tailWord_141263
  simp only [CollatzResearch.WordTrace]
  refine ⟨5152284887235751644756443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3434856591490501096504295 5152284887235751644756443)
  ·
    refine ⟨7728427330853627467134665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5152284887235751644756443 7728427330853627467134665)
    ·
      refine ⟨5796320498140220600350999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7728427330853627467134665 5796320498140220600350999)
      ·
        refine ⟨8694480747210330900526499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5796320498140220600350999 8694480747210330900526499)
        ·
          refine ⟨13041721120815496350789749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8694480747210330900526499 13041721120815496350789749)
          ·
            refine ⟨1222661355076452782886539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13041721120815496350789749 1222661355076452782886539)
            ·
              refine ⟨1833992032614679174329809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1222661355076452782886539 1833992032614679174329809)
              ·
                refine ⟨1375494024461009380747357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1833992032614679174329809 1375494024461009380747357)
                ·
                  refine ⟨515810259172878517780259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1375494024461009380747357 515810259172878517780259)
                  ·
                    refine ⟨773715388759317776670389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 515810259172878517780259 773715388759317776670389)
                    ·
                      refine ⟨72535817696186041562849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 773715388759317776670389 72535817696186041562849)
                      ·
                        rfl

theorem cell23_141263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_141263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141263 prefixEnd_141263 := by exact prefixLift 141263
  have htrace : WordTrace (prefixWord ++ tailWord_141263) baseStart_141263 baseEnd_141263 := by
    simpa [prefixWord, tailWord_141263, baseEnd_141263] using wordTrace_append hprefix tailTrace_141263
  have hstable : (prefixWord ++ tailWord_141263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141263).length < 2 ^ (prefixWord ++ tailWord_141263).sum := by decide
  have hdescent : baseEnd_141263 < baseStart_141263 := by decide
  rcases family_descends (prefixWord ++ tailWord_141263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141283 : List Nat := [1, 1, 1, 6, 1, 2, 11]
def baseStart_141283 : Nat := 118140960795 + 141283 * 2 ^ 59
def prefixEnd_141283 : Nat := 4983230072969 + 3 ^ 40 * 141283 * 2
def baseEnd_141283 : Nat := 895630707521925472997

theorem tailTrace_141283 : CollatzResearch.WordTrace tailWord_141283 prefixEnd_141283 895630707521925472997 := by
  unfold tailWord_141283
  simp only [CollatzResearch.WordTrace]
  refine ⟨5153014347163295060484503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3435342898108863373656335 5153014347163295060484503)
  ·
    refine ⟨7729521520744942590726755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5153014347163295060484503 7729521520744942590726755)
    ·
      refine ⟨11594282281117413886090133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7729521520744942590726755 11594282281117413886090133)
      ·
        refine ⟨543481981927378775910475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 11594282281117413886090133 543481981927378775910475)
        ·
          refine ⟨815222972891068163865713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543481981927378775910475 815222972891068163865713)
          ·
            refine ⟨611417229668301122899285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 815222972891068163865713 611417229668301122899285)
            ·
              refine ⟨895630707521925472997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 611417229668301122899285 895630707521925472997)
              ·
                rfl

theorem cell23_141283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 11].length) (baseStart_141283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141283 prefixEnd_141283 := by exact prefixLift 141283
  have htrace : WordTrace (prefixWord ++ tailWord_141283) baseStart_141283 baseEnd_141283 := by
    simpa [prefixWord, tailWord_141283, baseEnd_141283] using wordTrace_append hprefix tailTrace_141283
  have hstable : (prefixWord ++ tailWord_141283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141283).length < 2 ^ (prefixWord ++ tailWord_141283).sum := by decide
  have hdescent : baseEnd_141283 < baseStart_141283 := by decide
  rcases family_descends (prefixWord ++ tailWord_141283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141345 : List Nat := [1, 2, 3, 2, 4, 2, 2, 2, 1, 2, 2]
def baseStart_141345 : Nat := 118140960795 + 141345 * 2 ^ 59
def prefixEnd_141345 : Nat := 4983230072969 + 3 ^ 40 * 141345 * 2
def baseEnd_141345 : Nat := 72577923109854720737473

theorem tailTrace_141345 : CollatzResearch.WordTrace tailWord_141345 prefixEnd_141345 72577923109854720737473 := by
  unfold tailWord_141345
  simp only [CollatzResearch.WordTrace]
  refine ⟨5155275672938679649241489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3436850448625786432827659 5155275672938679649241489)
  ·
    refine ⟨3866456754704009736931117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5155275672938679649241489 3866456754704009736931117)
    ·
      refine ⟨1449921283014003651349169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3866456754704009736931117 1449921283014003651349169)
      ·
        refine ⟨1087440962260502738511877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1449921283014003651349169 1087440962260502738511877)
        ·
          refine ⟨203895180423844263470977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1087440962260502738511877 203895180423844263470977)
          ·
            refine ⟨152921385317883197603233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203895180423844263470977 152921385317883197603233)
            ·
              refine ⟨114691038988412398202425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152921385317883197603233 114691038988412398202425)
              ·
                refine ⟨86018279241309298651819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114691038988412398202425 86018279241309298651819)
                ·
                  refine ⟨129027418861963947977729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86018279241309298651819 129027418861963947977729)
                  ·
                    refine ⟨96770564146472960983297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129027418861963947977729 96770564146472960983297)
                    ·
                      refine ⟨72577923109854720737473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96770564146472960983297 72577923109854720737473)
                      ·
                        rfl

theorem cell23_141345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 2, 2, 1, 2, 2].length) (baseStart_141345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141345 prefixEnd_141345 := by exact prefixLift 141345
  have htrace : WordTrace (prefixWord ++ tailWord_141345) baseStart_141345 baseEnd_141345 := by
    simpa [prefixWord, tailWord_141345, baseEnd_141345] using wordTrace_append hprefix tailTrace_141345
  have hstable : (prefixWord ++ tailWord_141345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141345).length < 2 ^ (prefixWord ++ tailWord_141345).sum := by decide
  have hdescent : baseEnd_141345 < baseStart_141345 := by decide
  rcases family_descends (prefixWord ++ tailWord_141345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141354 : List Nat := [3, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2]
def baseStart_141354 : Nat := 118140960795 + 141354 * 2 ^ 59
def prefixEnd_141354 : Nat := 4983230072969 + 3 ^ 40 * 141354 * 2
def baseEnd_141354 : Nat := 72582544435745185524931

theorem tailTrace_141354 : CollatzResearch.WordTrace tailWord_141354 prefixEnd_141354 72582544435745185524931 := by
  unfold tailWord_141354
  simp only [CollatzResearch.WordTrace]
  refine ⟨1288900982476518546579779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3437069286604049457546077 1288900982476518546579779)
  ·
    refine ⟨1933351473714777819869669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1288900982476518546579779 1933351473714777819869669)
    ·
      refine ⟨362503401321520841225563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1933351473714777819869669 362503401321520841225563)
      ·
        refine ⟨543755101982281261838345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362503401321520841225563 543755101982281261838345)
        ·
          refine ⟨407816326486710946378759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543755101982281261838345 407816326486710946378759)
          ·
            refine ⟨611724489730066419568139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407816326486710946378759 611724489730066419568139)
            ·
              refine ⟨917586734595099629352209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 611724489730066419568139 917586734595099629352209)
              ·
                refine ⟨688190050946324722014157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 917586734595099629352209 688190050946324722014157)
                ·
                  refine ⟨258071269104871770755309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 688190050946324722014157 258071269104871770755309)
                  ·
                    refine ⟨96776725914326914033241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258071269104871770755309 96776725914326914033241)
                    ·
                      refine ⟨72582544435745185524931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96776725914326914033241 72582544435745185524931)
                      ·
                        rfl

theorem cell23_141354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_141354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141354 prefixEnd_141354 := by exact prefixLift 141354
  have htrace : WordTrace (prefixWord ++ tailWord_141354) baseStart_141354 baseEnd_141354 := by
    simpa [prefixWord, tailWord_141354, baseEnd_141354] using wordTrace_append hprefix tailTrace_141354
  have hstable : (prefixWord ++ tailWord_141354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141354).length < 2 ^ (prefixWord ++ tailWord_141354).sum := by decide
  have hdescent : baseEnd_141354 < baseStart_141354 := by decide
  rcases family_descends (prefixWord ++ tailWord_141354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141360 : List Nat := [2, 1, 1, 1, 2, 6, 1, 1, 2, 6]
def baseStart_141360 : Nat := 118140960795 + 141360 * 2 ^ 59
def prefixEnd_141360 : Nat := 4983230072969 + 3 ^ 40 * 141360 * 2
def baseEnd_141360 : Nat := 24195208439890720683301

theorem tailTrace_141360 : CollatzResearch.WordTrace tailWord_141360 prefixEnd_141360 24195208439890720683301 := by
  unfold tailWord_141360
  simp only [CollatzResearch.WordTrace]
  refine ⟨2577911383942168605518767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3437215178589558140691689 2577911383942168605518767)
  ·
    refine ⟨3866867075913252908278151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2577911383942168605518767 3866867075913252908278151)
    ·
      refine ⟨5800300613869879362417227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3866867075913252908278151 5800300613869879362417227)
      ·
        refine ⟨8700450920804819043625841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5800300613869879362417227 8700450920804819043625841)
        ·
          refine ⟨6525338190603614282719381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8700450920804819043625841 6525338190603614282719381)
          ·
            refine ⟨305875227684544419502471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 6525338190603614282719381 305875227684544419502471)
            ·
              refine ⟨458812841526816629253707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305875227684544419502471 458812841526816629253707)
              ·
                refine ⟨688219262290224943880561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458812841526816629253707 688219262290224943880561)
                ·
                  refine ⟨516164446717668707910421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 688219262290224943880561 516164446717668707910421)
                  ·
                    refine ⟨24195208439890720683301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 516164446717668707910421 24195208439890720683301)
                    ·
                      rfl

theorem cell23_141360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_141360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141360 prefixEnd_141360 := by exact prefixLift 141360
  have htrace : WordTrace (prefixWord ++ tailWord_141360) baseStart_141360 baseEnd_141360 := by
    simpa [prefixWord, tailWord_141360, baseEnd_141360] using wordTrace_append hprefix tailTrace_141360
  have hstable : (prefixWord ++ tailWord_141360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141360).length < 2 ^ (prefixWord ++ tailWord_141360).sum := by decide
  have hdescent : baseEnd_141360 < baseStart_141360 := by decide
  rcases family_descends (prefixWord ++ tailWord_141360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141367 : List Nat := [1, 1, 3, 1, 2, 2, 3, 3, 1, 4, 2]
def baseStart_141367 : Nat := 118140960795 + 141367 * 2 ^ 59
def prefixEnd_141367 : Nat := 4983230072969 + 3 ^ 40 * 141367 * 2
def baseEnd_141367 : Nat := 72589219684253634662371

theorem tailTrace_141367 : CollatzResearch.WordTrace tailWord_141367 prefixEnd_141367 72589219684253634662371 := by
  unfold tailWord_141367
  simp only [CollatzResearch.WordTrace]
  refine ⟨5156078078858977406542355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3437385385905984937694903 5156078078858977406542355)
  ·
    refine ⟨7734117118288466109813533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5156078078858977406542355 7734117118288466109813533)
    ·
      refine ⟨2900293919358174791180075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7734117118288466109813533 2900293919358174791180075)
      ·
        refine ⟨4350440879037262186770113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900293919358174791180075 4350440879037262186770113)
        ·
          refine ⟨3262830659277946640077585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4350440879037262186770113 3262830659277946640077585)
          ·
            refine ⟨2447122994458459980058189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3262830659277946640077585 2447122994458459980058189)
            ·
              refine ⟨917671122921922492521821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2447122994458459980058189 917671122921922492521821)
              ·
                refine ⟨344126671095720934695683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 917671122921922492521821 344126671095720934695683)
                ·
                  refine ⟨516190006643581402043525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344126671095720934695683 516190006643581402043525)
                  ·
                    refine ⟨96785626245671512883161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516190006643581402043525 96785626245671512883161)
                    ·
                      refine ⟨72589219684253634662371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96785626245671512883161 72589219684253634662371)
                      ·
                        rfl

theorem cell23_141367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 3, 3, 1, 4, 2].length) (baseStart_141367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141367 prefixEnd_141367 := by exact prefixLift 141367
  have htrace : WordTrace (prefixWord ++ tailWord_141367) baseStart_141367 baseEnd_141367 := by
    simpa [prefixWord, tailWord_141367, baseEnd_141367] using wordTrace_append hprefix tailTrace_141367
  have hstable : (prefixWord ++ tailWord_141367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141367).length < 2 ^ (prefixWord ++ tailWord_141367).sum := by decide
  have hdescent : baseEnd_141367 < baseStart_141367 := by decide
  rcases family_descends (prefixWord ++ tailWord_141367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141370 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3]
def baseStart_141370 : Nat := 118140960795 + 141370 * 2 ^ 59
def prefixEnd_141370 : Nat := 4983230072969 + 3 ^ 40 * 141370 * 2
def baseEnd_141370 : Nat := 72590760126217122924857

theorem tailTrace_141370 : CollatzResearch.WordTrace tailWord_141370 prefixEnd_141370 72590760126217122924857 := by
  unfold tailWord_141370
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289046874462027229725391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3437458331898739279267709 1289046874462027229725391)
  ·
    refine ⟨1933570311693040844588087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289046874462027229725391 1933570311693040844588087)
    ·
      refine ⟨2900355467539561266882131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1933570311693040844588087 2900355467539561266882131)
      ·
        refine ⟨4350533201309341900323197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2900355467539561266882131 4350533201309341900323197)
        ·
          refine ⟨1631449950491003212621199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4350533201309341900323197 1631449950491003212621199)
          ·
            refine ⟨2447174925736504818931799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1631449950491003212621199 2447174925736504818931799)
            ·
              refine ⟨3670762388604757228397699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2447174925736504818931799 3670762388604757228397699)
              ·
                refine ⟨5506143582907135842596549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3670762388604757228397699 5506143582907135842596549)
                ·
                  refine ⟨1032401921795087970486853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5506143582907135842596549 1032401921795087970486853)
                  ·
                    refine ⟨193575360336578994466285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1032401921795087970486853 193575360336578994466285)
                    ·
                      refine ⟨72590760126217122924857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193575360336578994466285 72590760126217122924857)
                      ·
                        rfl

theorem cell23_141370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3].length) (baseStart_141370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141370 prefixEnd_141370 := by exact prefixLift 141370
  have htrace : WordTrace (prefixWord ++ tailWord_141370) baseStart_141370 baseEnd_141370 := by
    simpa [prefixWord, tailWord_141370, baseEnd_141370] using wordTrace_append hprefix tailTrace_141370
  have hstable : (prefixWord ++ tailWord_141370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141370).length < 2 ^ (prefixWord ++ tailWord_141370).sum := by decide
  have hdescent : baseEnd_141370 < baseStart_141370 := by decide
  rcases family_descends (prefixWord ++ tailWord_141370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141418 : List Nat := [3, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2]
def baseStart_141418 : Nat := 118140960795 + 141418 * 2 ^ 59
def prefixEnd_141418 : Nat := 4983230072969 + 3 ^ 40 * 141418 * 2
def baseEnd_141418 : Nat := 72615407197632935124637

theorem tailTrace_141418 : CollatzResearch.WordTrace tailWord_141418 prefixEnd_141418 72615407197632935124637 := by
  unfold tailWord_141418
  simp only [CollatzResearch.WordTrace]
  refine ⟨1289484550418553279162227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3438625467782808744432605 1289484550418553279162227)
  ·
    refine ⟨1934226825627829918743341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1289484550418553279162227 1934226825627829918743341)
    ·
      refine ⟨725335059610436219528753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1934226825627829918743341 725335059610436219528753)
      ·
        refine ⟨544001294707827164646565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725335059610436219528753 544001294707827164646565)
        ·
          refine ⟨102000242757717593371231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 544001294707827164646565 102000242757717593371231)
          ·
            refine ⟨153000364136576390056847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102000242757717593371231 153000364136576390056847)
            ·
              refine ⟨229500546204864585085271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153000364136576390056847 229500546204864585085271)
              ·
                refine ⟨344250819307296877627907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229500546204864585085271 344250819307296877627907)
                ·
                  refine ⟨516376228960945316441861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344250819307296877627907 516376228960945316441861)
                  ·
                    refine ⟨96820542930177246832849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 516376228960945316441861 96820542930177246832849)
                    ·
                      refine ⟨72615407197632935124637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96820542930177246832849 72615407197632935124637)
                      ·
                        rfl

theorem cell23_141418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2].length) (baseStart_141418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141418 prefixEnd_141418 := by exact prefixLift 141418
  have htrace : WordTrace (prefixWord ++ tailWord_141418) baseStart_141418 baseEnd_141418 := by
    simpa [prefixWord, tailWord_141418, baseEnd_141418] using wordTrace_append hprefix tailTrace_141418
  have hstable : (prefixWord ++ tailWord_141418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141418).length < 2 ^ (prefixWord ++ tailWord_141418).sum := by decide
  have hdescent : baseEnd_141418 < baseStart_141418 := by decide
  rcases family_descends (prefixWord ++ tailWord_141418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141420 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_141420 : Nat := 118140960795 + 141420 * 2 ^ 59
def prefixEnd_141420 : Nat := 4983230072969 + 3 ^ 40 * 141420 * 2
def baseEnd_141420 : Nat := 24205478052980642433209

theorem tailTrace_141420 : CollatzResearch.WordTrace tailWord_141420 prefixEnd_141420 24205478052980642433209 := by
  unfold tailWord_141420
  simp only [CollatzResearch.WordTrace]
  refine ⟨2579005573833483729110857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3438674098444644972147809 2579005573833483729110857)
  ·
    refine ⟨1934254180375112796833143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2579005573833483729110857 1934254180375112796833143)
    ·
      refine ⟨2901381270562669195249715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1934254180375112796833143 2901381270562669195249715)
      ·
        refine ⟨4352071905844003792874573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2901381270562669195249715 4352071905844003792874573)
        ·
          refine ⟨1632026964691501422327965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4352071905844003792874573 1632026964691501422327965)
          ·
            refine ⟨612010111759313033372987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1632026964691501422327965 612010111759313033372987)
            ·
              refine ⟨918015167638969550059481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612010111759313033372987 918015167638969550059481)
              ·
                refine ⟨688511375729227162544611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 918015167638969550059481 688511375729227162544611)
                ·
                  refine ⟨1032767063593840743816917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 688511375729227162544611 1032767063593840743816917)
                  ·
                    refine ⟨24205478052980642433209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 1032767063593840743816917 24205478052980642433209)
                    ·
                      rfl

theorem cell23_141420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_141420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141420 prefixEnd_141420 := by exact prefixLift 141420
  have htrace : WordTrace (prefixWord ++ tailWord_141420) baseStart_141420 baseEnd_141420 := by
    simpa [prefixWord, tailWord_141420, baseEnd_141420] using wordTrace_append hprefix tailTrace_141420
  have hstable : (prefixWord ++ tailWord_141420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141420).length < 2 ^ (prefixWord ++ tailWord_141420).sum := by decide
  have hdescent : baseEnd_141420 < baseStart_141420 := by decide
  rcases family_descends (prefixWord ++ tailWord_141420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141441 : List Nat := [1, 2, 4, 2, 3, 2, 1, 3, 5]
def baseStart_141441 : Nat := 118140960795 + 141441 * 2 ^ 59
def prefixEnd_141441 : Nat := 4983230072969 + 3 ^ 40 * 141441 * 2
def baseEnd_141441 : Nat := 8069690805854038348559

theorem tailTrace_141441 : CollatzResearch.WordTrace tailWord_141441 prefixEnd_141441 8069690805854038348559 := by
  unfold tailWord_141441
  simp only [CollatzResearch.WordTrace]
  refine ⟨5158777080590888044736177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3439184720393925363157451 5158777080590888044736177)
  ·
    refine ⟨3869082810443166033552133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5158777080590888044736177 3869082810443166033552133)
    ·
      refine ⟨725453026958093631291025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3869082810443166033552133 725453026958093631291025)
      ·
        refine ⟨544089770218570223468269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 725453026958093631291025 544089770218570223468269)
        ·
          refine ⟨204033663831963833800601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 544089770218570223468269 204033663831963833800601)
          ·
            refine ⟨153025247873972875350451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 204033663831963833800601 153025247873972875350451)
            ·
              refine ⟨229537871810959313025677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153025247873972875350451 229537871810959313025677)
              ·
                refine ⟨86076701929109742384629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229537871810959313025677 86076701929109742384629)
                ·
                  refine ⟨8069690805854038348559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 86076701929109742384629 8069690805854038348559)
                  ·
                    rfl

theorem cell23_141441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 3, 2, 1, 3, 5].length) (baseStart_141441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141441 prefixEnd_141441 := by exact prefixLift 141441
  have htrace : WordTrace (prefixWord ++ tailWord_141441) baseStart_141441 baseEnd_141441 := by
    simpa [prefixWord, tailWord_141441, baseEnd_141441] using wordTrace_append hprefix tailTrace_141441
  have hstable : (prefixWord ++ tailWord_141441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141441).length < 2 ^ (prefixWord ++ tailWord_141441).sum := by decide
  have hdescent : baseEnd_141441 < baseStart_141441 := by decide
  rcases family_descends (prefixWord ++ tailWord_141441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141454 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_141454 : Nat := 118140960795 + 141454 * 2 ^ 59
def prefixEnd_141454 : Nat := 4983230072969 + 3 ^ 40 * 141454 * 2
def baseEnd_141454 : Nat := 24211297500398264758157

theorem tailTrace_141454 : CollatzResearch.WordTrace tailWord_141454 prefixEnd_141454 24211297500398264758157 := by
  unfold tailWord_141454
  simp only [CollatzResearch.WordTrace]
  refine ⟨644906403692973908119927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3439500819695860843306277 644906403692973908119927)
  ·
    refine ⟨967359605539460862179891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 644906403692973908119927 967359605539460862179891)
    ·
      refine ⟨1451039408309191293269837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967359605539460862179891 1451039408309191293269837)
      ·
        refine ⟨544139778115946734976189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1451039408309191293269837 544139778115946734976189)
        ·
          refine ⟨204052416793480025616071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 544139778115946734976189 204052416793480025616071)
          ·
            refine ⟨306078625190220038424107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204052416793480025616071 306078625190220038424107)
            ·
              refine ⟨459117937785330057636161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306078625190220038424107 459117937785330057636161)
              ·
                refine ⟨344338453338997543227121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459117937785330057636161 344338453338997543227121)
                ·
                  refine ⟨258253840004248157420341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344338453338997543227121 258253840004248157420341)
                  ·
                    refine ⟨24211297500398264758157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 258253840004248157420341 24211297500398264758157)
                    ·
                      rfl

theorem cell23_141454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_141454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141454 prefixEnd_141454 := by exact prefixLift 141454
  have htrace : WordTrace (prefixWord ++ tailWord_141454) baseStart_141454 baseEnd_141454 := by
    simpa [prefixWord, tailWord_141454, baseEnd_141454] using wordTrace_append hprefix tailTrace_141454
  have hstable : (prefixWord ++ tailWord_141454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141454).length < 2 ^ (prefixWord ++ tailWord_141454).sum := by decide
  have hdescent : baseEnd_141454 < baseStart_141454 := by decide
  rcases family_descends (prefixWord ++ tailWord_141454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141477 : List Nat := [1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_141477 : Nat := 118140960795 + 141477 * 2 ^ 59
def prefixEnd_141477 : Nat := 4983230072969 + 3 ^ 40 * 141477 * 2
def baseEnd_141477 : Nat := 72645702556248204286865

theorem tailTrace_141477 : CollatzResearch.WordTrace tailWord_141477 prefixEnd_141477 72645702556248204286865 := by
  unfold tailWord_141477
  simp only [CollatzResearch.WordTrace]
  refine ⟨5160090108460466193046685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3440060072306977462031123 5160090108460466193046685)
  ·
    refine ⟨1935033790672674822392507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5160090108460466193046685 1935033790672674822392507)
    ·
      refine ⟨2902550686009012233588761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935033790672674822392507 2902550686009012233588761)
      ·
        refine ⟨2176913014506759175191571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2902550686009012233588761 2176913014506759175191571)
        ·
          refine ⟨3265369521760138762787357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2176913014506759175191571 3265369521760138762787357)
          ·
            refine ⟨1224513570660052036045259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3265369521760138762787357 1224513570660052036045259)
            ·
              refine ⟨1836770355990078054067889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1224513570660052036045259 1836770355990078054067889)
              ·
                refine ⟨1377577766992558540550917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1836770355990078054067889 1377577766992558540550917)
                ·
                  refine ⟨258295831311104726353297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1377577766992558540550917 258295831311104726353297)
                  ·
                    refine ⟨193721873483328544764973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 258295831311104726353297 193721873483328544764973)
                    ·
                      refine ⟨72645702556248204286865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193721873483328544764973 72645702556248204286865)
                      ·
                        rfl

theorem cell23_141477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_141477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141477 prefixEnd_141477 := by exact prefixLift 141477
  have htrace : WordTrace (prefixWord ++ tailWord_141477) baseStart_141477 baseEnd_141477 := by
    simpa [prefixWord, tailWord_141477, baseEnd_141477] using wordTrace_append hprefix tailTrace_141477
  have hstable : (prefixWord ++ tailWord_141477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141477).length < 2 ^ (prefixWord ++ tailWord_141477).sum := by decide
  have hdescent : baseEnd_141477 < baseStart_141477 := by decide
  rcases family_descends (prefixWord ++ tailWord_141477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141518 : List Nat := [4, 1, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_141518 : Nat := 118140960795 + 141518 * 2 ^ 59
def prefixEnd_141518 : Nat := 4983230072969 + 3 ^ 40 * 141518 * 2
def baseEnd_141518 : Nat := 24222251754360847958059

theorem tailTrace_141518 : CollatzResearch.WordTrace tailWord_141518 prefixEnd_141518 24222251754360847958059 := by
  unfold tailWord_141518
  simp only [CollatzResearch.WordTrace]
  refine ⟨645198187663991274411151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3441057000874620130192805 645198187663991274411151)
  ·
    refine ⟨967797281495986911616727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 645198187663991274411151 967797281495986911616727)
    ·
      refine ⟨1451695922243980367425091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 967797281495986911616727 1451695922243980367425091)
      ·
        refine ⟨2177543883365970551137637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1451695922243980367425091 2177543883365970551137637)
        ·
          refine ⟨408289478131119478338307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2177543883365970551137637 408289478131119478338307)
          ·
            refine ⟨612434217196679217507461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408289478131119478338307 612434217196679217507461)
            ·
              refine ⟨114831415724377353282649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 612434217196679217507461 114831415724377353282649)
              ·
                refine ⟨86123561793283014961987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114831415724377353282649 86123561793283014961987)
                ·
                  refine ⟨129185342689924522442981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86123561793283014961987 129185342689924522442981)
                  ·
                    refine ⟨24222251754360847958059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129185342689924522442981 24222251754360847958059)
                    ·
                      rfl

theorem cell23_141518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_141518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141518 prefixEnd_141518 := by exact prefixLift 141518
  have htrace : WordTrace (prefixWord ++ tailWord_141518) baseStart_141518 baseEnd_141518 := by
    simpa [prefixWord, tailWord_141518, baseEnd_141518] using wordTrace_append hprefix tailTrace_141518
  have hstable : (prefixWord ++ tailWord_141518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141518).length < 2 ^ (prefixWord ++ tailWord_141518).sum := by decide
  have hdescent : baseEnd_141518 < baseStart_141518 := by decide
  rcases family_descends (prefixWord ++ tailWord_141518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141520 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5]
def baseStart_141520 : Nat := 118140960795 + 141520 * 2 ^ 59
def prefixEnd_141520 : Nat := 4983230072969 + 3 ^ 40 * 141520 * 2
def baseEnd_141520 : Nat := 72667782224391536049167

theorem tailTrace_141520 : CollatzResearch.WordTrace tailWord_141520 prefixEnd_141520 72667782224391536049167 := by
  unfold tailWord_141520
  simp only [CollatzResearch.WordTrace]
  refine ⟨2580829223652342268431007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3441105631536456357908009 2580829223652342268431007)
  ·
    refine ⟨3871243835478513402646511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2580829223652342268431007 3871243835478513402646511)
    ·
      refine ⟨5806865753217770103969767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3871243835478513402646511 5806865753217770103969767)
      ·
        refine ⟨8710298629826655155954651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5806865753217770103969767 8710298629826655155954651)
        ·
          refine ⟨13065447944739982733931977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8710298629826655155954651 13065447944739982733931977)
          ·
            refine ⟨9799085958554987050448983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13065447944739982733931977 9799085958554987050448983)
            ·
              refine ⟨14698628937832480575673475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9799085958554987050448983 14698628937832480575673475)
              ·
                refine ⟨22047943406748720863510213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14698628937832480575673475 22047943406748720863510213)
                ·
                  refine ⟨4133989388765385161908165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22047943406748720863510213 4133989388765385161908165)
                  ·
                    refine ⟨775123010393509717857781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4133989388765385161908165 775123010393509717857781)
                    ·
                      refine ⟨72667782224391536049167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 775123010393509717857781 72667782224391536049167)
                      ·
                        rfl

theorem cell23_141520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 5].length) (baseStart_141520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141520 prefixEnd_141520 := by exact prefixLift 141520
  have htrace : WordTrace (prefixWord ++ tailWord_141520) baseStart_141520 baseEnd_141520 := by
    simpa [prefixWord, tailWord_141520, baseEnd_141520] using wordTrace_append hprefix tailTrace_141520
  have hstable : (prefixWord ++ tailWord_141520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141520).length < 2 ^ (prefixWord ++ tailWord_141520).sum := by decide
  have hdescent : baseEnd_141520 < baseStart_141520 := by decide
  rcases family_descends (prefixWord ++ tailWord_141520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141541 : List Nat := [1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_141541 : Nat := 118140960795 + 141541 * 2 ^ 59
def prefixEnd_141541 : Nat := 4983230072969 + 3 ^ 40 * 141541 * 2
def baseEnd_141541 : Nat := 72678565318135953886571

theorem tailTrace_141541 : CollatzResearch.WordTrace tailWord_141541 prefixEnd_141541 72678565318135953886571 := by
  unfold tailWord_141541
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162424380228605123376477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3441616253485736748917651 5162424380228605123376477)
  ·
    refine ⟨1935909142585726921266179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5162424380228605123376477 1935909142585726921266179)
    ·
      refine ⟨2903863713878590381899269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1935909142585726921266179 2903863713878590381899269)
      ·
        refine ⟨544474446352235696606113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2903863713878590381899269 544474446352235696606113)
        ·
          refine ⟨408355834764176772454585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 544474446352235696606113 408355834764176772454585)
          ·
            refine ⟨306266876073132579340939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 408355834764176772454585 306266876073132579340939)
            ·
              refine ⟨459400314109698869011409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306266876073132579340939 459400314109698869011409)
              ·
                refine ⟨344550235582274151758557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459400314109698869011409 344550235582274151758557)
                ·
                  refine ⟨129206338343352806909459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 344550235582274151758557 129206338343352806909459)
                  ·
                    refine ⟨193809507515029210364189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129206338343352806909459 193809507515029210364189)
                    ·
                      refine ⟨72678565318135953886571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193809507515029210364189 72678565318135953886571)
                      ·
                        rfl

theorem cell23_141541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_141541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141541 prefixEnd_141541 := by exact prefixLift 141541
  have htrace : WordTrace (prefixWord ++ tailWord_141541) baseStart_141541 baseEnd_141541 := by
    simpa [prefixWord, tailWord_141541, baseEnd_141541] using wordTrace_append hprefix tailTrace_141541
  have hstable : (prefixWord ++ tailWord_141541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141541).length < 2 ^ (prefixWord ++ tailWord_141541).sum := by decide
  have hdescent : baseEnd_141541 < baseStart_141541 := by decide
  rcases family_descends (prefixWord ++ tailWord_141541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141547 : List Nat := [1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 4]
def baseStart_141547 : Nat := 118140960795 + 141547 * 2 ^ 59
def prefixEnd_141547 : Nat := 4983230072969 + 3 ^ 40 * 141547 * 2
def baseEnd_141547 : Nat := 72681646202062930411543

theorem tailTrace_141547 : CollatzResearch.WordTrace tailWord_141547 prefixEnd_141547 72681646202062930411543 := by
  unfold tailWord_141547
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162643218206868148094895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3441762145471245432063263 5162643218206868148094895)
  ·
    refine ⟨7743964827310302222142343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162643218206868148094895 7743964827310302222142343)
    ·
      refine ⟨11615947240965453333213515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7743964827310302222142343 11615947240965453333213515)
      ·
        refine ⟨17423920861448179999820273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11615947240965453333213515 17423920861448179999820273)
        ·
          refine ⟨13067940646086134999865205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17423920861448179999820273 13067940646086134999865205)
          ·
            refine ⟨1225119435570575156237363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 13067940646086134999865205 1225119435570575156237363)
            ·
              refine ⟨1837679153355862734356045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1225119435570575156237363 1837679153355862734356045)
              ·
                refine ⟨689129682508448525383517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1837679153355862734356045 689129682508448525383517)
                ·
                  refine ⟨258423630940668197018819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 689129682508448525383517 258423630940668197018819)
                  ·
                    refine ⟨387635446411002295528229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 258423630940668197018819 387635446411002295528229)
                    ·
                      refine ⟨72681646202062930411543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 387635446411002295528229 72681646202062930411543)
                      ·
                        rfl

theorem cell23_141547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 4].length) (baseStart_141547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141547 prefixEnd_141547 := by exact prefixLift 141547
  have htrace : WordTrace (prefixWord ++ tailWord_141547) baseStart_141547 baseEnd_141547 := by
    simpa [prefixWord, tailWord_141547, baseEnd_141547] using wordTrace_append hprefix tailTrace_141547
  have hstable : (prefixWord ++ tailWord_141547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141547).length < 2 ^ (prefixWord ++ tailWord_141547).sum := by decide
  have hdescent : baseEnd_141547 < baseStart_141547 := by decide
  rcases family_descends (prefixWord ++ tailWord_141547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141551 : List Nat := [1, 1, 2, 1, 6, 1, 3, 1, 2, 3, 2]
def baseStart_141551 : Nat := 118140960795 + 141551 * 2 ^ 59
def prefixEnd_141551 : Nat := 4983230072969 + 3 ^ 40 * 141551 * 2
def baseEnd_141551 : Nat := 72683700124680914761525

theorem tailTrace_141551 : CollatzResearch.WordTrace tailWord_141551 prefixEnd_141551 72683700124680914761525 := by
  unfold tailWord_141551
  simp only [CollatzResearch.WordTrace]
  refine ⟨5162789110192376831240507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3441859406794917887493671 5162789110192376831240507)
  ·
    refine ⟨7744183665288565246860761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5162789110192376831240507 7744183665288565246860761)
    ·
      refine ⟨5808137748966423935145571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7744183665288565246860761 5808137748966423935145571)
      ·
        refine ⟨8712206623449635902718357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808137748966423935145571 8712206623449635902718357)
        ·
          refine ⟨408384685474201682939923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 8712206623449635902718357 408384685474201682939923)
          ·
            refine ⟨612577028211302524409885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408384685474201682939923 612577028211302524409885)
            ·
              refine ⟨229716385579238446653707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 612577028211302524409885 229716385579238446653707)
              ·
                refine ⟨344574578368857669980561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229716385579238446653707 344574578368857669980561)
                ·
                  refine ⟨258430933776643252485421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 344574578368857669980561 258430933776643252485421)
                  ·
                    refine ⟨96911600166241219682033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 258430933776643252485421 96911600166241219682033)
                    ·
                      refine ⟨72683700124680914761525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96911600166241219682033 72683700124680914761525)
                      ·
                        rfl

theorem cell23_141551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 1, 2, 3, 2].length) (baseStart_141551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141551 prefixEnd_141551 := by exact prefixLift 141551
  have htrace : WordTrace (prefixWord ++ tailWord_141551) baseStart_141551 baseEnd_141551 := by
    simpa [prefixWord, tailWord_141551, baseEnd_141551] using wordTrace_append hprefix tailTrace_141551
  have hstable : (prefixWord ++ tailWord_141551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141551).length < 2 ^ (prefixWord ++ tailWord_141551).sum := by decide
  have hdescent : baseEnd_141551 < baseStart_141551 := by decide
  rcases family_descends (prefixWord ++ tailWord_141551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141558 : List Nat := [5, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3]
def baseStart_141558 : Nat := 118140960795 + 141558 * 2 ^ 59
def prefixEnd_141558 : Nat := 4983230072969 + 3 ^ 40 * 141558 * 2
def baseEnd_141558 : Nat := 72687294489262387373993

theorem tailTrace_141558 : CollatzResearch.WordTrace tailWord_141558 prefixEnd_141558 72687294489262387373993 := by
  unfold tailWord_141558
  simp only [CollatzResearch.WordTrace]
  refine ⟨322690276322938564171583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3442029614111344684496885 322690276322938564171583)
  ·
    refine ⟨484035414484407846257375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 322690276322938564171583 484035414484407846257375)
    ·
      refine ⟨726053121726611769386063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484035414484407846257375 726053121726611769386063)
      ·
        refine ⟨1089079682589917654079095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726053121726611769386063 1089079682589917654079095)
        ·
          refine ⟨1633619523884876481118643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1089079682589917654079095 1633619523884876481118643)
          ·
            refine ⟨2450429285827314721677965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633619523884876481118643 2450429285827314721677965)
            ·
              refine ⟨918910982185243020629237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2450429285827314721677965 918910982185243020629237)
              ·
                refine ⟨86147904579866533183991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 918910982185243020629237 86147904579866533183991)
                ·
                  refine ⟨129221856869799799775987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86147904579866533183991 129221856869799799775987)
                  ·
                    refine ⟨193832785304699699663981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129221856869799799775987 193832785304699699663981)
                    ·
                      refine ⟨72687294489262387373993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193832785304699699663981 72687294489262387373993)
                      ·
                        rfl

theorem cell23_141558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 5, 1, 1, 3].length) (baseStart_141558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141558 prefixEnd_141558 := by exact prefixLift 141558
  have htrace : WordTrace (prefixWord ++ tailWord_141558) baseStart_141558 baseEnd_141558 := by
    simpa [prefixWord, tailWord_141558, baseEnd_141558] using wordTrace_append hprefix tailTrace_141558
  have hstable : (prefixWord ++ tailWord_141558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141558).length < 2 ^ (prefixWord ++ tailWord_141558).sum := by decide
  have hdescent : baseEnd_141558 < baseStart_141558 := by decide
  rcases family_descends (prefixWord ++ tailWord_141558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141567 : List Nat := [1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_141567 : Nat := 118140960795 + 141567 * 2 ^ 59
def prefixEnd_141567 : Nat := 4983230072969 + 3 ^ 40 * 141567 * 2
def baseEnd_141567 : Nat := 72691915815152852161451

theorem tailTrace_141567 : CollatzResearch.WordTrace tailWord_141567 prefixEnd_141567 72691915815152852161451 := by
  unfold tailWord_141567
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163372678134411563822955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3442248452089607709215303 5163372678134411563822955)
  ·
    refine ⟨7745059017201617345734433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5163372678134411563822955 7745059017201617345734433)
    ·
      refine ⟨5808794262901213009300825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7745059017201617345734433 5808794262901213009300825)
      ·
        refine ⟨4356595697175909756975619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5808794262901213009300825 4356595697175909756975619)
        ·
          refine ⟨6534893545763864635463429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4356595697175909756975619 6534893545763864635463429)
          ·
            refine ⟨1225292539830724619149393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6534893545763864635463429 1225292539830724619149393)
            ·
              refine ⟨918969404873043464362045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225292539830724619149393 918969404873043464362045)
              ·
                refine ⟨344613526827391299135767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 918969404873043464362045 344613526827391299135767)
                ·
                  refine ⟨516920290241086948703651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344613526827391299135767 516920290241086948703651)
                  ·
                    refine ⟨775380435361630423055477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 516920290241086948703651 775380435361630423055477)
                    ·
                      refine ⟨72691915815152852161451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 775380435361630423055477 72691915815152852161451)
                      ·
                        rfl

theorem cell23_141567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_141567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141567 prefixEnd_141567 := by exact prefixLift 141567
  have htrace : WordTrace (prefixWord ++ tailWord_141567) baseStart_141567 baseEnd_141567 := by
    simpa [prefixWord, tailWord_141567, baseEnd_141567] using wordTrace_append hprefix tailTrace_141567
  have hstable : (prefixWord ++ tailWord_141567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141567).length < 2 ^ (prefixWord ++ tailWord_141567).sum := by decide
  have hdescent : baseEnd_141567 < baseStart_141567 := by decide
  rcases family_descends (prefixWord ++ tailWord_141567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141594 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6]
def baseStart_141594 : Nat := 118140960795 + 141594 * 2 ^ 59
def prefixEnd_141594 : Nat := 4983230072969 + 3 ^ 40 * 141594 * 2
def baseEnd_141594 : Nat := 72705779792824246523827

theorem tailTrace_141594 : CollatzResearch.WordTrace tailWord_141594 prefixEnd_141594 72705779792824246523827 := by
  unfold tailWord_141594
  simp only [CollatzResearch.WordTrace]
  refine ⟨1291089362259148793763959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3442904966024396783370557 1291089362259148793763959)
  ·
    refine ⟨1936634043388723190645939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1291089362259148793763959 1936634043388723190645939)
    ·
      refine ⟨2904951065083084785968909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936634043388723190645939 2904951065083084785968909)
      ·
        refine ⟨1089356649406156794738341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2904951065083084785968909 1089356649406156794738341)
        ·
          refine ⟨204254371763654399013439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1089356649406156794738341 204254371763654399013439)
          ·
            refine ⟨306381557645481598520159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204254371763654399013439 306381557645481598520159)
            ·
              refine ⟨459572336468222397780239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306381557645481598520159 459572336468222397780239)
              ·
                refine ⟨689358504702333596670359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459572336468222397780239 689358504702333596670359)
                ·
                  refine ⟨1034037757053500395005539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 689358504702333596670359 1034037757053500395005539)
                  ·
                    refine ⟨1551056635580250592508309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1034037757053500395005539 1551056635580250592508309)
                    ·
                      refine ⟨72705779792824246523827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 1551056635580250592508309 72705779792824246523827)
                      ·
                        rfl

theorem cell23_141594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 1, 1, 6].length) (baseStart_141594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141594 prefixEnd_141594 := by exact prefixLift 141594
  have htrace : WordTrace (prefixWord ++ tailWord_141594) baseStart_141594 baseEnd_141594 := by
    simpa [prefixWord, tailWord_141594, baseEnd_141594] using wordTrace_append hprefix tailTrace_141594
  have hstable : (prefixWord ++ tailWord_141594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141594).length < 2 ^ (prefixWord ++ tailWord_141594).sum := by decide
  have hdescent : baseEnd_141594 < baseStart_141594 := by decide
  rcases family_descends (prefixWord ++ tailWord_141594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141598 : List Nat := [4, 3, 2, 1, 1, 1, 1, 4, 1, 1, 4]
def baseStart_141598 : Nat := 118140960795 + 141598 * 2 ^ 59
def prefixEnd_141598 : Nat := 4983230072969 + 3 ^ 40 * 141598 * 2
def baseEnd_141598 : Nat := 72707833715442230873809

theorem tailTrace_141598 : CollatzResearch.WordTrace tailWord_141598 prefixEnd_141598 72707833715442230873809 := by
  unfold tailWord_141598
  simp only [CollatzResearch.WordTrace]
  refine ⟨645562917627762982275181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3443002227348069238800965 645562917627762982275181)
  ·
    refine ⟨242086094110411118353193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 645562917627762982275181 242086094110411118353193)
    ·
      refine ⟨181564570582808338764895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242086094110411118353193 181564570582808338764895)
      ·
        refine ⟨272346855874212508147343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181564570582808338764895 272346855874212508147343)
        ·
          refine ⟨408520283811318762221015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272346855874212508147343 408520283811318762221015)
          ·
            refine ⟨612780425716978143331523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408520283811318762221015 612780425716978143331523)
            ·
              refine ⟨919170638575467214997285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 612780425716978143331523 919170638575467214997285)
              ·
                refine ⟨172344494732900102811991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 919170638575467214997285 172344494732900102811991)
                ·
                  refine ⟨258516742099350154217987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172344494732900102811991 258516742099350154217987)
                  ·
                    refine ⟨387775113149025231326981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 258516742099350154217987 387775113149025231326981)
                    ·
                      refine ⟨72707833715442230873809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 387775113149025231326981 72707833715442230873809)
                      ·
                        rfl

theorem cell23_141598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_141598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141598 prefixEnd_141598 := by exact prefixLift 141598
  have htrace : WordTrace (prefixWord ++ tailWord_141598) baseStart_141598 baseEnd_141598 := by
    simpa [prefixWord, tailWord_141598, baseEnd_141598] using wordTrace_append hprefix tailTrace_141598
  have hstable : (prefixWord ++ tailWord_141598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141598).length < 2 ^ (prefixWord ++ tailWord_141598).sum := by decide
  have hdescent : baseEnd_141598 < baseStart_141598 := by decide
  rcases family_descends (prefixWord ++ tailWord_141598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141604 : List Nat := [2, 3, 1, 3, 1, 2, 4, 7]
def baseStart_141604 : Nat := 118140960795 + 141604 * 2 ^ 59
def prefixEnd_141604 : Nat := 4983230072969 + 3 ^ 40 * 141604 * 2
def baseEnd_141604 : Nat := 2692996837013674348103

theorem tailTrace_141604 : CollatzResearch.WordTrace tailWord_141604 prefixEnd_141604 2692996837013674348103 := by
  unfold tailWord_141604
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582361089500183441459933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3443148119333577921946577 2582361089500183441459933)
  ·
    refine ⟨968385408562568790547475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2582361089500183441459933 968385408562568790547475)
    ·
      refine ⟨1452578112843853185821213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 968385408562568790547475 1452578112843853185821213)
      ·
        refine ⟨544716792316444944682955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1452578112843853185821213 544716792316444944682955)
        ·
          refine ⟨817075188474667417024433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 544716792316444944682955 817075188474667417024433)
          ·
            refine ⟨612806391356000562768325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 817075188474667417024433 612806391356000562768325)
            ·
              refine ⟨114901198379250105519061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 612806391356000562768325 114901198379250105519061)
              ·
                refine ⟨2692996837013674348103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114901198379250105519061 2692996837013674348103)
                ·
                  rfl

theorem cell23_141604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 4, 7].length) (baseStart_141604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141604 prefixEnd_141604 := by exact prefixLift 141604
  have htrace : WordTrace (prefixWord ++ tailWord_141604) baseStart_141604 baseEnd_141604 := by
    simpa [prefixWord, tailWord_141604, baseEnd_141604] using wordTrace_append hprefix tailTrace_141604
  have hstable : (prefixWord ++ tailWord_141604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141604).length < 2 ^ (prefixWord ++ tailWord_141604).sum := by decide
  have hdescent : baseEnd_141604 < baseStart_141604 := by decide
  rcases family_descends (prefixWord ++ tailWord_141604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141631 : List Nat := [1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 3]
def baseStart_141631 : Nat := 118140960795 + 141631 * 2 ^ 59
def prefixEnd_141631 : Nat := 4983230072969 + 3 ^ 40 * 141631 * 2
def baseEnd_141631 : Nat := 72724778577040601761157

theorem tailTrace_141631 : CollatzResearch.WordTrace tailWord_141631 prefixEnd_141631 72724778577040601761157 := by
  unfold tailWord_141631
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165706949902550494152747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3443804633268366996101831 5165706949902550494152747)
  ·
    refine ⟨7748560424853825741229121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165706949902550494152747 7748560424853825741229121)
    ·
      refine ⟨5811420318640369305921841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7748560424853825741229121 5811420318640369305921841)
      ·
        refine ⟨4358565238980276979441381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5811420318640369305921841 4358565238980276979441381)
        ·
          refine ⟨817230982308801933645259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4358565238980276979441381 817230982308801933645259)
          ·
            refine ⟨1225846473463202900467889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 817230982308801933645259 1225846473463202900467889)
            ·
              refine ⟨919384855097402175350917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1225846473463202900467889 919384855097402175350917)
              ·
                refine ⟨172384660330762907878297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 919384855097402175350917 172384660330762907878297)
                ·
                  refine ⟨129288495248072180908723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172384660330762907878297 129288495248072180908723)
                  ·
                    refine ⟨193932742872108271363085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129288495248072180908723 193932742872108271363085)
                    ·
                      refine ⟨72724778577040601761157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193932742872108271363085 72724778577040601761157)
                      ·
                        rfl

theorem cell23_141631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_141631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141631 prefixEnd_141631 := by exact prefixLift 141631
  have htrace : WordTrace (prefixWord ++ tailWord_141631) baseStart_141631 baseEnd_141631 := by
    simpa [prefixWord, tailWord_141631, baseEnd_141631] using wordTrace_append hprefix tailTrace_141631
  have hstable : (prefixWord ++ tailWord_141631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141631).length < 2 ^ (prefixWord ++ tailWord_141631).sum := by decide
  have hdescent : baseEnd_141631 < baseStart_141631 := by decide
  rcases family_descends (prefixWord ++ tailWord_141631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141648 : List Nat := [2, 1, 1, 1, 1, 6, 4, 1, 2, 1, 3]
def baseStart_141648 : Nat := 118140960795 + 141648 * 2 ^ 59
def prefixEnd_141648 : Nat := 4983230072969 + 3 ^ 40 * 141648 * 2
def baseEnd_141648 : Nat := 72733507748167035248579

theorem tailTrace_141648 : CollatzResearch.WordTrace tailWord_141648 prefixEnd_141648 72733507748167035248579 := by
  unfold tailWord_141648
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583163495420481198760799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3444217993893974931681065 2583163495420481198760799)
  ·
    refine ⟨3874745243130721798141199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2583163495420481198760799 3874745243130721798141199)
    ·
      refine ⟨5812117864696082697211799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3874745243130721798141199 5812117864696082697211799)
      ·
        refine ⟨8718176797044124045817699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5812117864696082697211799 8718176797044124045817699)
        ·
          refine ⟨13077265195566186068726549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8718176797044124045817699 13077265195566186068726549)
          ·
            refine ⟨612996806042164971971557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 13077265195566186068726549 612996806042164971971557)
            ·
              refine ⟨114936901132905932244667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 612996806042164971971557 114936901132905932244667)
              ·
                refine ⟨172405351699358898367001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114936901132905932244667 172405351699358898367001)
                ·
                  refine ⟨129304013774519173775251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 172405351699358898367001 129304013774519173775251)
                  ·
                    refine ⟨193956020661778760662877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129304013774519173775251 193956020661778760662877)
                    ·
                      refine ⟨72733507748167035248579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 193956020661778760662877 72733507748167035248579)
                      ·
                        rfl

theorem cell23_141648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 4, 1, 2, 1, 3].length) (baseStart_141648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141648 prefixEnd_141648 := by exact prefixLift 141648
  have htrace : WordTrace (prefixWord ++ tailWord_141648) baseStart_141648 baseEnd_141648 := by
    simpa [prefixWord, tailWord_141648, baseEnd_141648] using wordTrace_append hprefix tailTrace_141648
  have hstable : (prefixWord ++ tailWord_141648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141648).length < 2 ^ (prefixWord ++ tailWord_141648).sum := by decide
  have hdescent : baseEnd_141648 < baseStart_141648 := by decide
  rcases family_descends (prefixWord ++ tailWord_141648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141662 : List Nat := [4, 4, 2, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_141662 : Nat := 118140960795 + 141662 * 2 ^ 59
def prefixEnd_141662 : Nat := 4983230072969 + 3 ^ 40 * 141662 * 2
def baseEnd_141662 : Nat := 72740696477329980473515

theorem tailTrace_141662 : CollatzResearch.WordTrace tailWord_141662 prefixEnd_141662 72740696477329980473515 := by
  unfold tailWord_141662
  simp only [CollatzResearch.WordTrace]
  refine ⟨645854701598780348566405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3444558408526828525687493 645854701598780348566405)
  ·
    refine ⟨121097756549771315356201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 645854701598780348566405 121097756549771315356201)
    ·
      refine ⟨90823317412328486517151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 121097756549771315356201 90823317412328486517151)
      ·
        refine ⟨136234976118492729775727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90823317412328486517151 136234976118492729775727)
        ·
          refine ⟨204352464177739094663591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 136234976118492729775727 204352464177739094663591)
          ·
            refine ⟨306528696266608641995387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204352464177739094663591 306528696266608641995387)
            ·
              refine ⟨459793044399912962993081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306528696266608641995387 459793044399912962993081)
              ·
                refine ⟨344844783299934722244811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 459793044399912962993081 344844783299934722244811)
                ·
                  refine ⟨517267174949902083367217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 344844783299934722244811 517267174949902083367217)
                  ·
                    refine ⟨387950381212426562525413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 517267174949902083367217 387950381212426562525413)
                    ·
                      refine ⟨72740696477329980473515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 387950381212426562525413 72740696477329980473515)
                      ·
                        rfl

theorem cell23_141662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_141662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141662 prefixEnd_141662 := by exact prefixLift 141662
  have htrace : WordTrace (prefixWord ++ tailWord_141662) baseStart_141662 baseEnd_141662 := by
    simpa [prefixWord, tailWord_141662, baseEnd_141662] using wordTrace_append hprefix tailTrace_141662
  have hstable : (prefixWord ++ tailWord_141662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141662).length < 2 ^ (prefixWord ++ tailWord_141662).sum := by decide
  have hdescent : baseEnd_141662 < baseStart_141662 := by decide
  rcases family_descends (prefixWord ++ tailWord_141662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141671 : List Nat := [1, 1, 5, 1, 3, 1, 1, 1, 3, 4, 2]
def baseStart_141671 : Nat := 118140960795 + 141671 * 2 ^ 59
def prefixEnd_141671 : Nat := 4983230072969 + 3 ^ 40 * 141671 * 2
def baseEnd_141671 : Nat := 72745317803220445260973

theorem tailTrace_141671 : CollatzResearch.WordTrace tailWord_141671 prefixEnd_141671 72745317803220445260973 := by
  unfold tailWord_141671
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167165869757637325608867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3444777246505091550405911 5167165869757637325608867)
  ·
    refine ⟨7750748804636455988413301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5167165869757637325608867 7750748804636455988413301)
    ·
      refine ⟨726632700434667748913747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7750748804636455988413301 726632700434667748913747)
      ·
        refine ⟨1089949050652001623370621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 726632700434667748913747 1089949050652001623370621)
        ·
          refine ⟨408730893994500608763983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1089949050652001623370621 408730893994500608763983)
          ·
            refine ⟨613096340991750913145975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 408730893994500608763983 613096340991750913145975)
            ·
              refine ⟨919644511487626369718963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613096340991750913145975 919644511487626369718963)
              ·
                refine ⟨1379466767231439554578445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 919644511487626369718963 1379466767231439554578445)
                ·
                  refine ⟨517300037711789832966917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1379466767231439554578445 517300037711789832966917)
                  ·
                    refine ⟨96993757070960593681297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 517300037711789832966917 96993757070960593681297)
                    ·
                      refine ⟨72745317803220445260973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 96993757070960593681297 72745317803220445260973)
                      ·
                        rfl

theorem cell23_141671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 1, 1, 3, 4, 2].length) (baseStart_141671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141671 prefixEnd_141671 := by exact prefixLift 141671
  have htrace : WordTrace (prefixWord ++ tailWord_141671) baseStart_141671 baseEnd_141671 := by
    simpa [prefixWord, tailWord_141671, baseEnd_141671] using wordTrace_append hprefix tailTrace_141671
  have hstable : (prefixWord ++ tailWord_141671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141671).length < 2 ^ (prefixWord ++ tailWord_141671).sum := by decide
  have hdescent : baseEnd_141671 < baseStart_141671 := by decide
  rcases family_descends (prefixWord ++ tailWord_141671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141698 : List Nat := [3, 4, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_141698 : Nat := 118140960795 + 141698 * 2 ^ 59
def prefixEnd_141698 : Nat := 4983230072969 + 3 ^ 40 * 141698 * 2
def baseEnd_141698 : Nat := 24253060593630613207783

theorem tailTrace_141698 : CollatzResearch.WordTrace tailWord_141698 prefixEnd_141698 24253060593630613207783 := by
  unfold tailWord_141698
  simp only [CollatzResearch.WordTrace]
  refine ⟨1292037660164955234210437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3445433760439880624561165 1292037660164955234210437)
  ·
    refine ⟨242257061280929106414457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1292037660164955234210437 242257061280929106414457)
    ·
      refine ⟨181692795960696829810843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 242257061280929106414457 181692795960696829810843)
      ·
        refine ⟨272539193941045244716265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181692795960696829810843 272539193941045244716265)
        ·
          refine ⟨204404395455783933537199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 272539193941045244716265 204404395455783933537199)
          ·
            refine ⟨306606593183675900305799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 204404395455783933537199 306606593183675900305799)
            ·
              refine ⟨459909889775513850458699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 306606593183675900305799 459909889775513850458699)
              ·
                refine ⟨689864834663270775688049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 459909889775513850458699 689864834663270775688049)
                ·
                  refine ⟨517398625997453081766037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 689864834663270775688049 517398625997453081766037)
                  ·
                    refine ⟨24253060593630613207783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 517398625997453081766037 24253060593630613207783)
                    ·
                      rfl

theorem cell23_141698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_141698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141698 prefixEnd_141698 := by exact prefixLift 141698
  have htrace : WordTrace (prefixWord ++ tailWord_141698) baseStart_141698 baseEnd_141698 := by
    simpa [prefixWord, tailWord_141698, baseEnd_141698] using wordTrace_append hprefix tailTrace_141698
  have hstable : (prefixWord ++ tailWord_141698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141698).length < 2 ^ (prefixWord ++ tailWord_141698).sum := by decide
  have hdescent : baseEnd_141698 < baseStart_141698 := by decide
  rcases family_descends (prefixWord ++ tailWord_141698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141737 : List Nat := [1, 2, 1, 1, 1, 1, 3, 2, 1, 10]
def baseStart_141737 : Nat := 118140960795 + 141737 * 2 ^ 59
def prefixEnd_141737 : Nat := 4983230072969 + 3 ^ 40 * 141737 * 2
def baseEnd_141737 : Nat := 24259735842139062345223

theorem tailTrace_141737 : CollatzResearch.WordTrace tailWord_141737 prefixEnd_141737 24259735842139062345223 := by
  unfold tailWord_141737
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169573087518530597511465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3446382058345687065007643 5169573087518530597511465)
  ·
    refine ⟨3877179815638897948133599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5169573087518530597511465 3877179815638897948133599)
    ·
      refine ⟨5815769723458346922200399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3877179815638897948133599 5815769723458346922200399)
      ·
        refine ⟨8723654585187520383300599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815769723458346922200399 8723654585187520383300599)
        ·
          refine ⟨13085481877781280574950899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8723654585187520383300599 13085481877781280574950899)
          ·
            refine ⟨19628222816671920862426349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13085481877781280574950899 19628222816671920862426349)
            ·
              refine ⟨7360583556251970323409881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19628222816671920862426349 7360583556251970323409881)
              ·
                refine ⟨5520437667188977742557411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7360583556251970323409881 5520437667188977742557411)
                ·
                  refine ⟨8280656500783466613836117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520437667188977742557411 8280656500783466613836117)
                  ·
                    refine ⟨24259735842139062345223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 8280656500783466613836117 24259735842139062345223)
                    ·
                      rfl

theorem cell23_141737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_141737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141737 prefixEnd_141737 := by exact prefixLift 141737
  have htrace : WordTrace (prefixWord ++ tailWord_141737) baseStart_141737 baseEnd_141737 := by
    simpa [prefixWord, tailWord_141737, baseEnd_141737] using wordTrace_append hprefix tailTrace_141737
  have hstable : (prefixWord ++ tailWord_141737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141737).length < 2 ^ (prefixWord ++ tailWord_141737).sum := by decide
  have hdescent : baseEnd_141737 < baseStart_141737 := by decide
  rcases family_descends (prefixWord ++ tailWord_141737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141774 : List Nat := [4, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4]
def baseStart_141774 : Nat := 118140960795 + 141774 * 2 ^ 59
def prefixEnd_141774 : Nat := 4983230072969 + 3 ^ 40 * 141774 * 2
def baseEnd_141774 : Nat := 72798206310633542272999

theorem tailTrace_141774 : CollatzResearch.WordTrace tailWord_141774 prefixEnd_141774 72798206310633542272999 := by
  unfold tailWord_141774
  simp only [CollatzResearch.WordTrace]
  refine ⟨646365323548060739576047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3447281725589657277738917 646365323548060739576047)
  ·
    refine ⟨969547985322091109364071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646365323548060739576047 969547985322091109364071)
    ·
      refine ⟨1454321977983136664046107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 969547985322091109364071 1454321977983136664046107)
      ·
        refine ⟨2181482966974704996069161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1454321977983136664046107 2181482966974704996069161)
        ·
          refine ⟨1636112225231028747051871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2181482966974704996069161 1636112225231028747051871)
          ·
            refine ⟨2454168337846543120577807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1636112225231028747051871 2454168337846543120577807)
            ·
              refine ⟨3681252506769814680866711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454168337846543120577807 3681252506769814680866711)
              ·
                refine ⟨5521878760154722021300067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681252506769814680866711 5521878760154722021300067)
                ·
                  refine ⟨8282818140232083031950101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5521878760154722021300067 8282818140232083031950101)
                  ·
                    refine ⟨388257100323378892122661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8282818140232083031950101 388257100323378892122661)
                    ·
                      refine ⟨72798206310633542272999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 388257100323378892122661 72798206310633542272999)
                      ·
                        rfl

theorem cell23_141774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 1, 1, 6, 4].length) (baseStart_141774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141774 prefixEnd_141774 := by exact prefixLift 141774
  have htrace : WordTrace (prefixWord ++ tailWord_141774) baseStart_141774 baseEnd_141774 := by
    simpa [prefixWord, tailWord_141774, baseEnd_141774] using wordTrace_append hprefix tailTrace_141774
  have hstable : (prefixWord ++ tailWord_141774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141774).length < 2 ^ (prefixWord ++ tailWord_141774).sum := by decide
  have hdescent : baseEnd_141774 < baseStart_141774 := by decide
  rcases family_descends (prefixWord ++ tailWord_141774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141781 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_141781 : Nat := 118140960795 + 141781 * 2 ^ 59
def prefixEnd_141781 : Nat := 4983230072969 + 3 ^ 40 * 141781 * 2
def baseEnd_141781 : Nat := 72801800675215014885467

theorem tailTrace_141781 : CollatzResearch.WordTrace tailWord_141781 prefixEnd_141781 72801800675215014885467 := by
  unfold tailWord_141781
  simp only [CollatzResearch.WordTrace]
  refine ⟨5171177899359126112113197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3447451932906084074742131 5171177899359126112113197)
  ·
    refine ⟨1939191712259672292042449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5171177899359126112113197 1939191712259672292042449)
    ·
      refine ⟨1454393784194754219031837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1939191712259672292042449 1454393784194754219031837)
      ·
        refine ⟨545397669073032832136939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1454393784194754219031837 545397669073032832136939)
        ·
          refine ⟨818096503609549248205409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 545397669073032832136939 818096503609549248205409)
          ·
            refine ⟨613572377707161936154057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 818096503609549248205409 613572377707161936154057)
            ·
              refine ⟨460179283280371452115543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 613572377707161936154057 460179283280371452115543)
              ·
                refine ⟨690268924920557178173315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 460179283280371452115543 690268924920557178173315)
                ·
                  refine ⟨1035403387380835767259973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 690268924920557178173315 1035403387380835767259973)
                  ·
                    refine ⟨194138135133906706361245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1035403387380835767259973 194138135133906706361245)
                    ·
                      refine ⟨72801800675215014885467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 194138135133906706361245 72801800675215014885467)
                      ·
                        rfl

theorem cell23_141781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_141781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141781 prefixEnd_141781 := by exact prefixLift 141781
  have htrace : WordTrace (prefixWord ++ tailWord_141781) baseStart_141781 baseEnd_141781 := by
    simpa [prefixWord, tailWord_141781, baseEnd_141781] using wordTrace_append hprefix tailTrace_141781
  have hstable : (prefixWord ++ tailWord_141781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141781).length < 2 ^ (prefixWord ++ tailWord_141781).sum := by decide
  have hdescent : baseEnd_141781 < baseStart_141781 := by decide
  rcases family_descends (prefixWord ++ tailWord_141781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141805 : List Nat := [1, 5, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_141805 : Nat := 118140960795 + 141805 * 2 ^ 59
def prefixEnd_141805 : Nat := 4983230072969 + 3 ^ 40 * 141805 * 2
def baseEnd_141805 : Nat := 24271374736974306995119

theorem tailTrace_141805 : CollatzResearch.WordTrace tailWord_141805 prefixEnd_141805 24271374736974306995119 := by
  unfold tailWord_141805
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172053251272178210986869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3448035500848118807324579 5172053251272178210986869)
  ·
    refine ⟨484879992306766707280019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 5172053251272178210986869 484879992306766707280019)
    ·
      refine ⟨727319988460150060920029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 484879992306766707280019 727319988460150060920029)
      ·
        refine ⟨272744995672556272845011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 727319988460150060920029 272744995672556272845011)
        ·
          refine ⟨409117493508834409267517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 272744995672556272845011 409117493508834409267517)
          ·
            refine ⟨153419060065812903475319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 409117493508834409267517 153419060065812903475319)
            ·
              refine ⟨230128590098719355212979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153419060065812903475319 230128590098719355212979)
              ·
                refine ⟨345192885148079032819469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 230128590098719355212979 345192885148079032819469)
                ·
                  refine ⟨129447331930529637307301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 345192885148079032819469 129447331930529637307301)
                  ·
                    refine ⟨24271374736974306995119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129447331930529637307301 24271374736974306995119)
                    ·
                      rfl

theorem cell23_141805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_141805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141805 prefixEnd_141805 := by exact prefixLift 141805
  have htrace : WordTrace (prefixWord ++ tailWord_141805) baseStart_141805 baseEnd_141805 := by
    simpa [prefixWord, tailWord_141805, baseEnd_141805] using wordTrace_append hprefix tailTrace_141805
  have hstable : (prefixWord ++ tailWord_141805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141805).length < 2 ^ (prefixWord ++ tailWord_141805).sum := by decide
  have hdescent : baseEnd_141805 < baseStart_141805 := by decide
  rcases family_descends (prefixWord ++ tailWord_141805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141845 : List Nat := [1, 3, 2, 1, 3, 1, 2, 5, 1, 1, 3]
def baseStart_141845 : Nat := 118140960795 + 141845 * 2 ^ 59
def prefixEnd_141845 : Nat := 4983230072969 + 3 ^ 40 * 141845 * 2
def baseEnd_141845 : Nat := 72834663437102764485173

theorem tailTrace_141845 : CollatzResearch.WordTrace tailWord_141845 prefixEnd_141845 72834663437102764485173 := by
  unfold tailWord_141845
  simp only [CollatzResearch.WordTrace]
  refine ⟨5173512171127265042442989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3449008114084843361628659 5173512171127265042442989)
  ·
    refine ⟨1940067064172724390916121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5173512171127265042442989 1940067064172724390916121)
    ·
      refine ⟨1455050298129543293187091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1940067064172724390916121 1455050298129543293187091)
      ·
        refine ⟨2182575447194314939780637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455050298129543293187091 2182575447194314939780637)
        ·
          refine ⟨818465792697868102417739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2182575447194314939780637 818465792697868102417739)
          ·
            refine ⟨1227698689046802153626609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 818465792697868102417739 1227698689046802153626609)
            ·
              refine ⟨920774016785101615219957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1227698689046802153626609 920774016785101615219957)
              ·
                refine ⟨86322564073603276426871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 920774016785101615219957 86322564073603276426871)
                ·
                  refine ⟨129483846110404914640307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86322564073603276426871 129483846110404914640307)
                  ·
                    refine ⟨194225769165607371960461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 129483846110404914640307 194225769165607371960461)
                    ·
                      refine ⟨72834663437102764485173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 194225769165607371960461 72834663437102764485173)
                      ·
                        rfl

theorem cell23_141845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 5, 1, 1, 3].length) (baseStart_141845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141845 prefixEnd_141845 := by exact prefixLift 141845
  have htrace : WordTrace (prefixWord ++ tailWord_141845) baseStart_141845 baseEnd_141845 := by
    simpa [prefixWord, tailWord_141845, baseEnd_141845] using wordTrace_append hprefix tailTrace_141845
  have hstable : (prefixWord ++ tailWord_141845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141845).length < 2 ^ (prefixWord ++ tailWord_141845).sum := by decide
  have hdescent : baseEnd_141845 < baseStart_141845 := by decide
  rcases family_descends (prefixWord ++ tailWord_141845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141861 : List Nat := [1, 3, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_141861 : Nat := 118140960795 + 141861 * 2 ^ 59
def prefixEnd_141861 : Nat := 4983230072969 + 3 ^ 40 * 141861 * 2
def baseEnd_141861 : Nat := 24280959709191567295033

theorem tailTrace_141861 : CollatzResearch.WordTrace tailWord_141861 prefixEnd_141861 24280959709191567295033 := by
  unfold tailWord_141861
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174095739069299775025437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3449397159379533183350291 5174095739069299775025437)
  ·
    refine ⟨1940285902150987415634539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5174095739069299775025437 1940285902150987415634539)
    ·
      refine ⟨2910428853226481123451809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1940285902150987415634539 2910428853226481123451809)
      ·
        refine ⟨2182821639919860842588857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2910428853226481123451809 2182821639919860842588857)
        ·
          refine ⟨1637116229939895631941643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2182821639919860842588857 1637116229939895631941643)
          ·
            refine ⟨2455674344909843447912465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637116229939895631941643 2455674344909843447912465)
            ·
              refine ⟨1841755758682382585934349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2455674344909843447912465 1841755758682382585934349)
              ·
                refine ⟨690658409505893469725381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1841755758682382585934349 690658409505893469725381)
                ·
                  refine ⟨129498451782355025573509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 690658409505893469725381 129498451782355025573509)
                  ·
                    refine ⟨24280959709191567295033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 129498451782355025573509 24280959709191567295033)
                    ·
                      rfl

theorem cell23_141861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_141861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141861 prefixEnd_141861 := by exact prefixLift 141861
  have htrace : WordTrace (prefixWord ++ tailWord_141861) baseStart_141861 baseEnd_141861 := by
    simpa [prefixWord, tailWord_141861, baseEnd_141861] using wordTrace_append hprefix tailTrace_141861
  have hstable : (prefixWord ++ tailWord_141861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141861).length < 2 ^ (prefixWord ++ tailWord_141861).sum := by decide
  have hdescent : baseEnd_141861 < baseStart_141861 := by decide
  rcases family_descends (prefixWord ++ tailWord_141861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141868 : List Nat := [2, 2, 1, 1, 1, 2, 1, 2, 7, 2, 2]
def baseStart_141868 : Nat := 118140960795 + 141868 * 2 ^ 59
def prefixEnd_141868 : Nat := 4983230072969 + 3 ^ 40 * 141868 * 2
def baseEnd_141868 : Nat := 72846473492156174497567

theorem tailTrace_141868 : CollatzResearch.WordTrace tailWord_141868 prefixEnd_141868 72846473492156174497567 := by
  unfold tailWord_141868
  simp only [CollatzResearch.WordTrace]
  refine ⟨2587175525021969985265129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3449567366695959980353505 2587175525021969985265129)
  ·
    refine ⟨1940381643766477488948847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2587175525021969985265129 1940381643766477488948847)
    ·
      refine ⟨2910572465649716233423271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1940381643766477488948847 2910572465649716233423271)
      ·
        refine ⟨4365858698474574350134907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910572465649716233423271 4365858698474574350134907)
        ·
          refine ⟨6548788047711861525202361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365858698474574350134907 6548788047711861525202361)
          ·
            refine ⟨4911591035783896143901771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6548788047711861525202361 4911591035783896143901771)
            ·
              refine ⟨7367386553675844215852657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4911591035783896143901771 7367386553675844215852657)
              ·
                refine ⟨5525539915256883161889493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7367386553675844215852657 5525539915256883161889493)
                ·
                  refine ⟨129504841763833199106785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5525539915256883161889493 129504841763833199106785)
                  ·
                    refine ⟨97128631322874899330089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129504841763833199106785 97128631322874899330089)
                    ·
                      refine ⟨72846473492156174497567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97128631322874899330089 72846473492156174497567)
                      ·
                        rfl

theorem cell23_141868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 2, 2].length) (baseStart_141868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141868 prefixEnd_141868 := by exact prefixLift 141868
  have htrace : WordTrace (prefixWord ++ tailWord_141868) baseStart_141868 baseEnd_141868 := by
    simpa [prefixWord, tailWord_141868, baseEnd_141868] using wordTrace_append hprefix tailTrace_141868
  have hstable : (prefixWord ++ tailWord_141868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141868).length < 2 ^ (prefixWord ++ tailWord_141868).sum := by decide
  have hdescent : baseEnd_141868 < baseStart_141868 := by decide
  rcases family_descends (prefixWord ++ tailWord_141868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141878 : List Nat := [5, 1, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_141878 : Nat := 118140960795 + 141878 * 2 ^ 59
def prefixEnd_141878 : Nat := 4983230072969 + 3 ^ 40 * 141878 * 2
def baseEnd_141878 : Nat := 24283869432900378457507

theorem tailTrace_141878 : CollatzResearch.WordTrace tailWord_141878 prefixEnd_141878 24283869432900378457507 := by
  unfold tailWord_141878
  simp only [CollatzResearch.WordTrace]
  refine ⟨323419736250481979899643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3449810520005141118929525 323419736250481979899643)
  ·
    refine ⟨485129604375722969849465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 323419736250481979899643 485129604375722969849465)
    ·
      refine ⟨363847203281792227387099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 485129604375722969849465 363847203281792227387099)
      ·
        refine ⟨545770804922688341080649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 363847203281792227387099 545770804922688341080649)
        ·
          refine ⟨409328103692016255810487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545770804922688341080649 409328103692016255810487)
          ·
            refine ⟨613992155538024383715731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409328103692016255810487 613992155538024383715731)
            ·
              refine ⟨920988233307036575573597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 613992155538024383715731 920988233307036575573597)
              ·
                refine ⟨345370587490138715840099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 920988233307036575573597 345370587490138715840099)
                ·
                  refine ⟨518055881235208073760149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 345370587490138715840099 518055881235208073760149)
                  ·
                    refine ⟨24283869432900378457507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 518055881235208073760149 24283869432900378457507)
                    ·
                      rfl

theorem cell23_141878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_141878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141878 prefixEnd_141878 := by exact prefixLift 141878
  have htrace : WordTrace (prefixWord ++ tailWord_141878) baseStart_141878 baseEnd_141878 := by
    simpa [prefixWord, tailWord_141878, baseEnd_141878] using wordTrace_append hprefix tailTrace_141878
  have hstable : (prefixWord ++ tailWord_141878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141878).length < 2 ^ (prefixWord ++ tailWord_141878).sum := by decide
  have hdescent : baseEnd_141878 < baseStart_141878 := by decide
  rcases family_descends (prefixWord ++ tailWord_141878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141885 : List Nat := [1, 4, 1, 3, 2, 1, 1, 1, 5, 2, 2]
def baseStart_141885 : Nat := 118140960795 + 141885 * 2 ^ 59
def prefixEnd_141885 : Nat := 4983230072969 + 3 ^ 40 * 141885 * 2
def baseEnd_141885 : Nat := 72855202663282607984989

theorem tailTrace_141885 : CollatzResearch.WordTrace tailWord_141885 prefixEnd_141885 72855202663282607984989 := by
  unfold tailWord_141885
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174971090982351873899109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3449980727321567915932739 5174971090982351873899109)
  ·
    refine ⟨970307079559190976356083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 5174971090982351873899109 970307079559190976356083)
    ·
      refine ⟨1455460619338786464534125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970307079559190976356083 1455460619338786464534125)
      ·
        refine ⟨545797732252044924200297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1455460619338786464534125 545797732252044924200297)
        ·
          refine ⟨409348299189033693150223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 545797732252044924200297 409348299189033693150223)
          ·
            refine ⟨614022448783550539725335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 409348299189033693150223 614022448783550539725335)
            ·
              refine ⟨921033673175325809588003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614022448783550539725335 921033673175325809588003)
              ·
                refine ⟨1381550509762988714382005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 921033673175325809588003 1381550509762988714382005)
                ·
                  refine ⟨129520360290280191973313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1381550509762988714382005 129520360290280191973313)
                  ·
                    refine ⟨97140270217710143979985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129520360290280191973313 97140270217710143979985)
                    ·
                      refine ⟨72855202663282607984989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97140270217710143979985 72855202663282607984989)
                      ·
                        rfl

theorem cell23_141885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_141885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141885 prefixEnd_141885 := by exact prefixLift 141885
  have htrace : WordTrace (prefixWord ++ tailWord_141885) baseStart_141885 baseEnd_141885 := by
    simpa [prefixWord, tailWord_141885, baseEnd_141885] using wordTrace_append hprefix tailTrace_141885
  have hstable : (prefixWord ++ tailWord_141885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141885).length < 2 ^ (prefixWord ++ tailWord_141885).sum := by decide
  have hdescent : baseEnd_141885 < baseStart_141885 := by decide
  rcases family_descends (prefixWord ++ tailWord_141885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141902 : List Nat := [4, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2]
def baseStart_141902 : Nat := 118140960795 + 141902 * 2 ^ 59
def prefixEnd_141902 : Nat := 4983230072969 + 3 ^ 40 * 141902 * 2
def baseEnd_141902 : Nat := 72863931834409041472411

theorem tailTrace_141902 : CollatzResearch.WordTrace tailWord_141902 prefixEnd_141902 72863931834409041472411 := by
  unfold tailWord_141902
  simp only [CollatzResearch.WordTrace]
  refine ⟨646948891490095472158495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 3450394087947175851511973 646948891490095472158495)
  ·
    refine ⟨970423337235143208237743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 646948891490095472158495 970423337235143208237743)
    ·
      refine ⟨1455635005852714812356615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 970423337235143208237743 1455635005852714812356615)
      ·
        refine ⟨2183452508779072218534923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455635005852714812356615 2183452508779072218534923)
        ·
          refine ⟨3275178763168608327802385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183452508779072218534923 3275178763168608327802385)
          ·
            refine ⟨2456384072376456245851789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3275178763168608327802385 2456384072376456245851789)
            ·
              refine ⟨921144027141171092194421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2456384072376456245851789 921144027141171092194421)
              ·
                refine ⟨86357252544484789893227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 921144027141171092194421 86357252544484789893227)
                ·
                  refine ⟨129535878816727184839841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 86357252544484789893227 129535878816727184839841)
                  ·
                    refine ⟨97151909112545388629881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129535878816727184839841 97151909112545388629881)
                    ·
                      refine ⟨72863931834409041472411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97151909112545388629881 72863931834409041472411)
                      ·
                        rfl

theorem cell23_141902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 3, 5, 1, 2, 2].length) (baseStart_141902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141902 prefixEnd_141902 := by exact prefixLift 141902
  have htrace : WordTrace (prefixWord ++ tailWord_141902) baseStart_141902 baseEnd_141902 := by
    simpa [prefixWord, tailWord_141902, baseEnd_141902] using wordTrace_append hprefix tailTrace_141902
  have hstable : (prefixWord ++ tailWord_141902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141902).length < 2 ^ (prefixWord ++ tailWord_141902).sum := by decide
  have hdescent : baseEnd_141902 < baseStart_141902 := by decide
  rcases family_descends (prefixWord ++ tailWord_141902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141904 : List Nat := [2, 1, 1, 1, 1, 3, 2, 2, 1, 9]
def baseStart_141904 : Nat := 118140960795 + 141904 * 2 ^ 59
def prefixEnd_141904 : Nat := 4983230072969 + 3 ^ 40 * 141904 * 2
def baseEnd_141904 : Nat := 24288319598572677882467

theorem tailTrace_141904 : CollatzResearch.WordTrace tailWord_141904 prefixEnd_141904 24288319598572677882467 := by
  unfold tailWord_141904
  simp only [CollatzResearch.WordTrace]
  refine ⟨2587832038956759059420383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 3450442718609012079227177 2587832038956759059420383)
  ·
    refine ⟨3881748058435138589130575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2587832038956759059420383 3881748058435138589130575)
    ·
      refine ⟨5822622087652707883695863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3881748058435138589130575 5822622087652707883695863)
      ·
        refine ⟨8733933131479061825543795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5822622087652707883695863 8733933131479061825543795)
        ·
          refine ⟨13100899697218592738315693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8733933131479061825543795 13100899697218592738315693)
          ·
            refine ⟨4912837386456972276868385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13100899697218592738315693 4912837386456972276868385)
            ·
              refine ⟨3684628039842729207651289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4912837386456972276868385 3684628039842729207651289)
              ·
                refine ⟨2763471029882046905738467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3684628039842729207651289 2763471029882046905738467)
                ·
                  refine ⟨4145206544823070358607701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2763471029882046905738467 4145206544823070358607701)
                  ·
                    refine ⟨24288319598572677882467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 4145206544823070358607701 24288319598572677882467)
                    ·
                      rfl

theorem cell23_141904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_141904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141904 prefixEnd_141904 := by exact prefixLift 141904
  have htrace : WordTrace (prefixWord ++ tailWord_141904) baseStart_141904 baseEnd_141904 := by
    simpa [prefixWord, tailWord_141904, baseEnd_141904] using wordTrace_append hprefix tailTrace_141904
  have hstable : (prefixWord ++ tailWord_141904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141904).length < 2 ^ (prefixWord ++ tailWord_141904).sum := by decide
  have hdescent : baseEnd_141904 < baseStart_141904 := by decide
  rcases family_descends (prefixWord ++ tailWord_141904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141905 : List Nat := [1, 2, 2, 1, 3, 3, 4, 1, 1, 2, 3]
def baseStart_141905 : Nat := 118140960795 + 141905 * 2 ^ 59
def prefixEnd_141905 : Nat := 4983230072969 + 3 ^ 40 * 141905 * 2
def baseEnd_141905 : Nat := 72865472276372529734897

theorem tailTrace_141905 : CollatzResearch.WordTrace tailWord_141905 prefixEnd_141905 72865472276372529734897 := by
  unfold tailWord_141905
  simp only [CollatzResearch.WordTrace]
  refine ⟨5175700550909895289627169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3450467033939930193084779 5175700550909895289627169)
  ·
    refine ⟨3881775413182421467220377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5175700550909895289627169 3881775413182421467220377)
    ·
      refine ⟨2911331559886816100415283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3881775413182421467220377 2911331559886816100415283)
      ·
        refine ⟨4366997339830224150622925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2911331559886816100415283 4366997339830224150622925)
        ·
          refine ⟨1637624002436334056483597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4366997339830224150622925 1637624002436334056483597)
          ·
            refine ⟨614109000913625271181349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1637624002436334056483597 614109000913625271181349)
            ·
              refine ⟨115145437671304738346503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 614109000913625271181349 115145437671304738346503)
              ·
                refine ⟨172718156506957107519755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 115145437671304738346503 172718156506957107519755)
                ·
                  refine ⟨259077234760435661279633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172718156506957107519755 259077234760435661279633)
                  ·
                    refine ⟨194307926070326745959725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 259077234760435661279633 194307926070326745959725)
                    ·
                      refine ⟨72865472276372529734897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 194307926070326745959725 72865472276372529734897)
                      ·
                        rfl

theorem cell23_141905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 4, 1, 1, 2, 3].length) (baseStart_141905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141905 prefixEnd_141905 := by exact prefixLift 141905
  have htrace : WordTrace (prefixWord ++ tailWord_141905) baseStart_141905 baseEnd_141905 := by
    simpa [prefixWord, tailWord_141905, baseEnd_141905] using wordTrace_append hprefix tailTrace_141905
  have hstable : (prefixWord ++ tailWord_141905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141905).length < 2 ^ (prefixWord ++ tailWord_141905).sum := by decide
  have hdescent : baseEnd_141905 < baseStart_141905 := by decide
  rcases family_descends (prefixWord ++ tailWord_141905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141942 : List Nat := [5, 1, 1, 2, 4, 1, 2, 7]
def baseStart_141942 : Nat := 118140960795 + 141942 * 2 ^ 59
def prefixEnd_141942 : Nat := 4983230072969 + 3 ^ 40 * 141942 * 2
def baseEnd_141942 : Nat := 2699424854095884628601

theorem tailTrace_141942 : CollatzResearch.WordTrace tailWord_141942 prefixEnd_141942 2699424854095884628601 := by
  unfold tailWord_141942
  simp only [CollatzResearch.WordTrace]
  refine ⟨323565628235990663045255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 3451366701183900405816053 323565628235990663045255)
  ·
    refine ⟨485348442353985994567883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 323565628235990663045255 485348442353985994567883)
    ·
      refine ⟨728022663530978991851825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 485348442353985994567883 728022663530978991851825)
      ·
        refine ⟨546016997648234243888869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 728022663530978991851825 546016997648234243888869)
        ·
          refine ⟨102378187059043920729163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 546016997648234243888869 102378187059043920729163)
          ·
            refine ⟨153567280588565881093745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102378187059043920729163 153567280588565881093745)
            ·
              refine ⟨115175460441424410820309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 153567280588565881093745 115175460441424410820309)
              ·
                refine ⟨2699424854095884628601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 115175460441424410820309 2699424854095884628601)
                ·
                  rfl

theorem cell23_141942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_141942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141942 prefixEnd_141942 := by exact prefixLift 141942
  have htrace : WordTrace (prefixWord ++ tailWord_141942) baseStart_141942 baseEnd_141942 := by
    simpa [prefixWord, tailWord_141942, baseEnd_141942] using wordTrace_append hprefix tailTrace_141942
  have hstable : (prefixWord ++ tailWord_141942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141942).length < 2 ^ (prefixWord ++ tailWord_141942).sum := by decide
  have hdescent : baseEnd_141942 < baseStart_141942 := by decide
  rcases family_descends (prefixWord ++ tailWord_141942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141945 : List Nat := [1, 2, 1, 3, 3, 2, 1, 4, 1, 3, 2]
def baseStart_141945 : Nat := 118140960795 + 141945 * 2 ^ 59
def prefixEnd_141945 : Nat := 4983230072969 + 3 ^ 40 * 141945 * 2
def baseEnd_141945 : Nat := 72886011502552373234713

theorem tailTrace_141945 : CollatzResearch.WordTrace tailWord_141945 prefixEnd_141945 72886011502552373234713 := by
  unfold tailWord_141945
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177159470764982121083289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3451439647176654747388859 5177159470764982121083289)
  ·
    refine ⟨3882869603073736590812467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5177159470764982121083289 3882869603073736590812467)
    ·
      refine ⟨5824304404610604886218701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3882869603073736590812467 5824304404610604886218701)
      ·
        refine ⟨2184114151728976832332013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5824304404610604886218701 2184114151728976832332013)
        ·
          refine ⟨819042806898366312124505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2184114151728976832332013 819042806898366312124505)
          ·
            refine ⟨614282105173774734093379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819042806898366312124505 614282105173774734093379)
            ·
              refine ⟨921423157760662101140069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614282105173774734093379 921423157760662101140069)
              ·
                refine ⟨172766842080124143963763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 921423157760662101140069 172766842080124143963763)
                ·
                  refine ⟨259150263120186215945645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172766842080124143963763 259150263120186215945645)
                  ·
                    refine ⟨97181348670069830979617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 259150263120186215945645 97181348670069830979617)
                    ·
                      refine ⟨72886011502552373234713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97181348670069830979617 72886011502552373234713)
                      ·
                        rfl

theorem cell23_141945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 4, 1, 3, 2].length) (baseStart_141945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141945 prefixEnd_141945 := by exact prefixLift 141945
  have htrace : WordTrace (prefixWord ++ tailWord_141945) baseStart_141945 baseEnd_141945 := by
    simpa [prefixWord, tailWord_141945, baseEnd_141945] using wordTrace_append hprefix tailTrace_141945
  have hstable : (prefixWord ++ tailWord_141945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141945).length < 2 ^ (prefixWord ++ tailWord_141945).sum := by decide
  have hdescent : baseEnd_141945 < baseStart_141945 := by decide
  rcases family_descends (prefixWord ++ tailWord_141945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141961 : List Nat := [1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 3]
def baseStart_141961 : Nat := 118140960795 + 141961 * 2 ^ 59
def prefixEnd_141961 : Nat := 4983230072969 + 3 ^ 40 * 141961 * 2
def baseEnd_141961 : Nat := 72894227193024310634639

theorem tailTrace_141961 : CollatzResearch.WordTrace tailWord_141961 prefixEnd_141961 72894227193024310634639 := by
  unfold tailWord_141961
  simp only [CollatzResearch.WordTrace]
  refine ⟨5177743038707016853665737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3451828692471344569110491 5177743038707016853665737)
  ·
    refine ⟨3883307279030262640249303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5177743038707016853665737 3883307279030262640249303)
    ·
      refine ⟨5824960918545393960373955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3883307279030262640249303 5824960918545393960373955)
      ·
        refine ⟨8737441377818090940560933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5824960918545393960373955 8737441377818090940560933)
        ·
          refine ⟨1638270258340892051355175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8737441377818090940560933 1638270258340892051355175)
          ·
            refine ⟨2457405387511338077032763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1638270258340892051355175 2457405387511338077032763)
            ·
              refine ⟨3686108081267007115549145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2457405387511338077032763 3686108081267007115549145)
              ·
                refine ⟨2764581060950255336661859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3686108081267007115549145 2764581060950255336661859)
                ·
                  refine ⟨4146871591425383004992789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2764581060950255336661859 4146871591425383004992789)
                  ·
                    refine ⟨194384605848064828359037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4146871591425383004992789 194384605848064828359037)
                    ·
                      refine ⟨72894227193024310634639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 194384605848064828359037 72894227193024310634639)
                      ·
                        rfl

theorem cell23_141961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_141961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141961 prefixEnd_141961 := by exact prefixLift 141961
  have htrace : WordTrace (prefixWord ++ tailWord_141961) baseStart_141961 baseEnd_141961 := by
    simpa [prefixWord, tailWord_141961, baseEnd_141961] using wordTrace_append hprefix tailTrace_141961
  have hstable : (prefixWord ++ tailWord_141961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141961).length < 2 ^ (prefixWord ++ tailWord_141961).sum := by decide
  have hdescent : baseEnd_141961 < baseStart_141961 := by decide
  rcases family_descends (prefixWord ++ tailWord_141961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_141975 : List Nat := [1, 1, 3, 3, 2, 1, 1, 3, 4, 2, 2]
def baseStart_141975 : Nat := 118140960795 + 141975 * 2 ^ 59
def prefixEnd_141975 : Nat := 4983230072969 + 3 ^ 40 * 141975 * 2
def baseEnd_141975 : Nat := 72901415922187255859575

theorem tailTrace_141975 : CollatzResearch.WordTrace tailWord_141975 prefixEnd_141975 72901415922187255859575 := by
  unfold tailWord_141975
  simp only [CollatzResearch.WordTrace]
  refine ⟨5178253660656297244675379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3452169107104198163116919 5178253660656297244675379)
  ·
    refine ⟨7767380490984445867013069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5178253660656297244675379 7767380490984445867013069)
    ·
      refine ⟨2912767684119167200129901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7767380490984445867013069 2912767684119167200129901)
      ·
        refine ⟨1092287881544687700048713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2912767684119167200129901 1092287881544687700048713)
        ·
          refine ⟨819215911158515775036535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1092287881544687700048713 819215911158515775036535)
          ·
            refine ⟨1228823866737773662554803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 819215911158515775036535 1228823866737773662554803)
            ·
              refine ⟨1843235800106660493832205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1228823866737773662554803 1843235800106660493832205)
              ·
                refine ⟨691213425039997685187077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1843235800106660493832205 691213425039997685187077)
                ·
                  refine ⟨129602517194999565972577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 691213425039997685187077 129602517194999565972577)
                  ·
                    refine ⟨97201887896249674479433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 129602517194999565972577 97201887896249674479433)
                    ·
                      refine ⟨72901415922187255859575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97201887896249674479433 72901415922187255859575)
                      ·
                        rfl

theorem cell23_141975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_141975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_141975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_141975 prefixEnd_141975 := by exact prefixLift 141975
  have htrace : WordTrace (prefixWord ++ tailWord_141975) baseStart_141975 baseEnd_141975 := by
    simpa [prefixWord, tailWord_141975, baseEnd_141975] using wordTrace_append hprefix tailTrace_141975
  have hstable : (prefixWord ++ tailWord_141975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_141975).length < 2 ^ (prefixWord ++ tailWord_141975).sum := by decide
  have hdescent : baseEnd_141975 < baseStart_141975 := by decide
  rcases family_descends (prefixWord ++ tailWord_141975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142031 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_142031 : Nat := 118140960795 + 142031 * 2 ^ 59
def prefixEnd_142031 : Nat := 4983230072969 + 3 ^ 40 * 142031 * 2
def baseEnd_142031 : Nat := 72930170838839036759317

theorem tailTrace_142031 : CollatzResearch.WordTrace tailWord_142031 prefixEnd_142031 72930170838839036759317 := by
  unfold tailWord_142031
  simp only [CollatzResearch.WordTrace]
  refine ⟨5180296148453418808713947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3453530765635612539142631 5180296148453418808713947)
  ·
    refine ⟨7770444222680128213070921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5180296148453418808713947 7770444222680128213070921)
    ·
      refine ⟨5827833167010096159803191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7770444222680128213070921 5827833167010096159803191)
      ·
        refine ⟨8741749750515144239704787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5827833167010096159803191 8741749750515144239704787)
        ·
          refine ⟨13112624625772716359557181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8741749750515144239704787 13112624625772716359557181)
          ·
            refine ⟨4917234234664768634833943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13112624625772716359557181 4917234234664768634833943)
            ·
              refine ⟨7375851351997152952250915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4917234234664768634833943 7375851351997152952250915)
              ·
                refine ⟨11063777027995729428376373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7375851351997152952250915 11063777027995729428376373)
                ·
                  refine ⟨1037229096374599633910285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 11063777027995729428376373 1037229096374599633910285)
                  ·
                    refine ⟨388960911140474862716357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 1037229096374599633910285 388960911140474862716357)
                    ·
                      refine ⟨72930170838839036759317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 388960911140474862716357 72930170838839036759317)
                      ·
                        rfl

theorem cell23_142031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_142031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142031 prefixEnd_142031 := by exact prefixLift 142031
  have htrace : WordTrace (prefixWord ++ tailWord_142031) baseStart_142031 baseEnd_142031 := by
    simpa [prefixWord, tailWord_142031, baseEnd_142031] using wordTrace_append hprefix tailTrace_142031
  have hstable : (prefixWord ++ tailWord_142031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142031).length < 2 ^ (prefixWord ++ tailWord_142031).sum := by decide
  have hdescent : baseEnd_142031 < baseStart_142031 := by decide
  rcases family_descends (prefixWord ++ tailWord_142031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142071 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 8]
def baseStart_142071 : Nat := 118140960795 + 142071 * 2 ^ 59
def prefixEnd_142071 : Nat := 4983230072969 + 3 ^ 40 * 142071 * 2
def baseEnd_142071 : Nat := 8105634451668764473237

theorem tailTrace_142071 : CollatzResearch.WordTrace tailWord_142071 prefixEnd_142071 8105634451668764473237 := by
  unfold tailWord_142071
  simp only [CollatzResearch.WordTrace]
  refine ⟨5181755068308505640170067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 3454503378872337093446711 5181755068308505640170067)
  ·
    refine ⟨7772632602462758460255101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5181755068308505640170067 7772632602462758460255101)
    ·
      refine ⟨2914737225923534422595663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7772632602462758460255101 2914737225923534422595663)
      ·
        refine ⟨4372105838885301633893495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2914737225923534422595663 4372105838885301633893495)
        ·
          refine ⟨6558158758327952450840243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4372105838885301633893495 6558158758327952450840243)
          ·
            refine ⟨9837238137491928676260365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6558158758327952450840243 9837238137491928676260365)
            ·
              refine ⟨3688964301559473253597637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9837238137491928676260365 3688964301559473253597637)
              ·
                refine ⟨691680806542401235049557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3688964301559473253597637 691680806542401235049557)
                ·
                  refine ⟨8105634451668764473237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 691680806542401235049557 8105634451668764473237)
                  ·
                    rfl

theorem cell23_142071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 8].length) (baseStart_142071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142071 prefixEnd_142071 := by exact prefixLift 142071
  have htrace : WordTrace (prefixWord ++ tailWord_142071) baseStart_142071 baseEnd_142071 := by
    simpa [prefixWord, tailWord_142071, baseEnd_142071] using wordTrace_append hprefix tailTrace_142071
  have hstable : (prefixWord ++ tailWord_142071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142071).length < 2 ^ (prefixWord ++ tailWord_142071).sum := by decide
  have hdescent : baseEnd_142071 < baseStart_142071 := by decide
  rcases family_descends (prefixWord ++ tailWord_142071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_142082 : List Nat := [3, 4, 1, 1, 1, 2, 1, 2, 2, 4, 2]
def baseStart_142082 : Nat := 118140960795 + 142082 * 2 ^ 59
def prefixEnd_142082 : Nat := 4983230072969 + 3 ^ 40 * 142082 * 2
def baseEnd_142082 : Nat := 72956358352218337221583

theorem tailTrace_142082 : CollatzResearch.WordTrace tailWord_142082 prefixEnd_142082 72956358352218337221583 := by
  unfold tailWord_142082
  simp only [CollatzResearch.WordTrace]
  refine ⟨1295539067817163629705125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 3454770847512436345880333 1295539067817163629705125)
  ·
    refine ⟨242913575215718180569711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1295539067817163629705125 242913575215718180569711)
    ·
      refine ⟨364370362823577270854567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 242913575215718180569711 364370362823577270854567)
      ·
        refine ⟨546555544235365906281851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 364370362823577270854567 546555544235365906281851)
        ·
          refine ⟨819833316353048859422777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 546555544235365906281851 819833316353048859422777)
          ·
            refine ⟨614874987264786644567083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 819833316353048859422777 614874987264786644567083)
            ·
              refine ⟨922312480897179966850625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 614874987264786644567083 922312480897179966850625)
              ·
                refine ⟨691734360672884975137969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 922312480897179966850625 691734360672884975137969)
                ·
                  refine ⟨518800770504663731353477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 691734360672884975137969 518800770504663731353477)
                  ·
                    refine ⟨97275144469624449628777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 518800770504663731353477 97275144469624449628777)
                    ·
                      refine ⟨72956358352218337221583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 97275144469624449628777 72956358352218337221583)
                      ·
                        rfl

theorem cell23_142082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_142082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_142082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_142082 prefixEnd_142082 := by exact prefixLift 142082
  have htrace : WordTrace (prefixWord ++ tailWord_142082) baseStart_142082 baseEnd_142082 := by
    simpa [prefixWord, tailWord_142082, baseEnd_142082] using wordTrace_append hprefix tailTrace_142082
  have hstable : (prefixWord ++ tailWord_142082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_142082).length < 2 ^ (prefixWord ++ tailWord_142082).sum := by decide
  have hdescent : baseEnd_142082 < baseStart_142082 := by decide
  rcases family_descends (prefixWord ++ tailWord_142082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
