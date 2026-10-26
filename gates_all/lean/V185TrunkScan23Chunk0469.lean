import V185TrunkScan23Chunk0468

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2774202 : List Nat := [3, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3]
def baseStart_2774202 : Nat := 118140960795 + 2774202 * 2 ^ 59
def prefixEnd_2774202 : Nat := 4983230072969 + 3 ^ 40 * 2774202 * 2
def baseEnd_2774202 : Nat := 1424499058664460155616683

theorem tailTrace_2774202 : CollatzResearch.WordTrace tailWord_2774202 prefixEnd_2774202 1424499058664460155616683 := by
  unfold tailWord_2774202
  simp only [CollatzResearch.WordTrace]
  refine ⟨25295864873886856206471215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67455639663698283217256573 25295864873886856206471215)
  ·
    refine ⟨37943797310830284309706823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25295864873886856206471215 37943797310830284309706823)
    ·
      refine ⟨56915695966245426464560235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37943797310830284309706823 56915695966245426464560235)
      ·
        refine ⟨85373543949368139696840353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56915695966245426464560235 85373543949368139696840353)
        ·
          refine ⟨64030157962026104772630265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85373543949368139696840353 64030157962026104772630265)
          ·
            refine ⟨48022618471519578579472699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64030157962026104772630265 48022618471519578579472699)
            ·
              refine ⟨72033927707279367869209049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48022618471519578579472699 72033927707279367869209049)
              ·
                refine ⟨54025445780459525901906787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72033927707279367869209049 54025445780459525901906787)
                ·
                  refine ⟨81038168670689288852860181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54025445780459525901906787 81038168670689288852860181)
                  ·
                    refine ⟨3798664156438560414977821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81038168670689288852860181 3798664156438560414977821)
                    ·
                      refine ⟨1424499058664460155616683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3798664156438560414977821 1424499058664460155616683)
                      ·
                        rfl

theorem cell23_2774202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 1, 6, 3].length) (baseStart_2774202 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774202 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774202 prefixEnd_2774202 := by exact prefixLift 2774202
  have htrace : WordTrace (prefixWord ++ tailWord_2774202) baseStart_2774202 baseEnd_2774202 := by
    simpa [prefixWord, tailWord_2774202, baseEnd_2774202] using wordTrace_append hprefix tailTrace_2774202
  have hstable : (prefixWord ++ tailWord_2774202).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774202).length < 2 ^ (prefixWord ++ tailWord_2774202).sum := by decide
  have hdescent : baseEnd_2774202 < baseStart_2774202 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774216 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 4, 2, 2]
def baseStart_2774216 : Nat := 118140960795 + 2774216 * 2 ^ 59
def prefixEnd_2774216 : Nat := 4983230072969 + 3 ^ 40 * 2774216 * 2
def baseEnd_2774216 : Nat := 1424506247393623100841619

theorem tailTrace_2774216 : CollatzResearch.WordTrace tailWord_2774216 prefixEnd_2774216 1424506247393623100841619 := by
  unfold tailWord_2774216
  simp only [CollatzResearch.WordTrace]
  refine ⟨50591985058748352608447251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67455980078331136811263001 50591985058748352608447251)
  ·
    refine ⟨75887977588122528912670877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50591985058748352608447251 75887977588122528912670877)
    ·
      refine ⟨28457991595545948342251579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75887977588122528912670877 28457991595545948342251579)
      ·
        refine ⟨42686987393318922513377369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28457991595545948342251579 42686987393318922513377369)
        ·
          refine ⟨32015240544989191885033027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42686987393318922513377369 32015240544989191885033027)
          ·
            refine ⟨48022860817483787827549541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32015240544989191885033027 48022860817483787827549541)
            ·
              refine ⟨9004286403278210217665539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48022860817483787827549541 9004286403278210217665539)
              ·
                refine ⟨13506429604917315326498309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9004286403278210217665539 13506429604917315326498309)
                ·
                  refine ⟨2532455550921996623718433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13506429604917315326498309 2532455550921996623718433)
                  ·
                    refine ⟨1899341663191497467788825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2532455550921996623718433 1899341663191497467788825)
                    ·
                      refine ⟨1424506247393623100841619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899341663191497467788825 1424506247393623100841619)
                      ·
                        rfl

theorem cell23_2774216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 4, 2, 2].length) (baseStart_2774216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774216 prefixEnd_2774216 := by exact prefixLift 2774216
  have htrace : WordTrace (prefixWord ++ tailWord_2774216) baseStart_2774216 baseEnd_2774216 := by
    simpa [prefixWord, tailWord_2774216, baseEnd_2774216] using wordTrace_append hprefix tailTrace_2774216
  have hstable : (prefixWord ++ tailWord_2774216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774216).length < 2 ^ (prefixWord ++ tailWord_2774216).sum := by decide
  have hdescent : baseEnd_2774216 < baseStart_2774216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774237 : List Nat := [1, 4, 3, 2, 3, 1, 1, 2, 1, 3, 2]
def baseStart_2774237 : Nat := 118140960795 + 2774237 * 2 ^ 59
def prefixEnd_2774237 : Nat := 4983230072969 + 3 ^ 40 * 2774237 * 2
def baseEnd_2774237 : Nat := 1424517030487367518679023

theorem tailTrace_2774237 : CollatzResearch.WordTrace tailWord_2774237 prefixEnd_2774237 1424517030487367518679023 := by
  unfold tailWord_2774237
  simp only [CollatzResearch.WordTrace]
  refine ⟨101184736050420625803408965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67456490700280417202272643 101184736050420625803408965)
  ·
    refine ⟨18972138009453867338139181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101184736050420625803408965 18972138009453867338139181)
    ·
      refine ⟨7114551753545200251802193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18972138009453867338139181 7114551753545200251802193)
      ·
        refine ⟨5335913815158900188851645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7114551753545200251802193 5335913815158900188851645)
        ·
          refine ⟨2000967680684587570819367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5335913815158900188851645 2000967680684587570819367)
          ·
            refine ⟨3001451521026881356229051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2000967680684587570819367 3001451521026881356229051)
            ·
              refine ⟨4502177281540322034343577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001451521026881356229051 4502177281540322034343577)
              ·
                refine ⟨3376632961155241525757683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4502177281540322034343577 3376632961155241525757683)
                ·
                  refine ⟨5064949441732862288636525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376632961155241525757683 5064949441732862288636525)
                  ·
                    refine ⟨1899356040649823358238697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5064949441732862288636525 1899356040649823358238697)
                    ·
                      refine ⟨1424517030487367518679023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899356040649823358238697 1424517030487367518679023)
                      ·
                        rfl

theorem cell23_2774237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_2774237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774237 prefixEnd_2774237 := by exact prefixLift 2774237
  have htrace : WordTrace (prefixWord ++ tailWord_2774237) baseStart_2774237 baseEnd_2774237 := by
    simpa [prefixWord, tailWord_2774237, baseEnd_2774237] using wordTrace_append hprefix tailTrace_2774237
  have hstable : (prefixWord ++ tailWord_2774237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774237).length < 2 ^ (prefixWord ++ tailWord_2774237).sum := by decide
  have hdescent : baseEnd_2774237 < baseStart_2774237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774272 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4]
def baseStart_2774272 : Nat := 118140960795 + 2774272 * 2 ^ 59
def prefixEnd_2774272 : Nat := 4983230072969 + 3 ^ 40 * 2774272 * 2
def baseEnd_2774272 : Nat := 1424535002310274881741361

theorem tailTrace_2774272 : CollatzResearch.WordTrace tailWord_2774272 prefixEnd_2774272 1424535002310274881741361 := by
  unfold tailWord_2774272
  simp only [CollatzResearch.WordTrace]
  refine ⟨50593006302646913390466535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67457341736862551187288713 50593006302646913390466535)
  ·
    refine ⟨75889509453970370085699803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50593006302646913390466535 75889509453970370085699803)
    ·
      refine ⟨113834264180955555128549705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75889509453970370085699803 113834264180955555128549705)
      ·
        refine ⟨85375698135716666346412279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113834264180955555128549705 85375698135716666346412279)
        ·
          refine ⟨128063547203574999519618419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85375698135716666346412279 128063547203574999519618419)
          ·
            refine ⟨192095320805362499279427629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128063547203574999519618419 192095320805362499279427629)
            ·
              refine ⟨72035745302010937229785361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192095320805362499279427629 72035745302010937229785361)
              ·
                refine ⟨54026808976508202922339021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72035745302010937229785361 54026808976508202922339021)
                ·
                  refine ⟨20260053366190576095877133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54026808976508202922339021 20260053366190576095877133)
                  ·
                    refine ⟨7597520012321466035953925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20260053366190576095877133 7597520012321466035953925)
                    ·
                      refine ⟨1424535002310274881741361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7597520012321466035953925 1424535002310274881741361)
                      ·
                        rfl

theorem cell23_2774272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 3, 3, 4].length) (baseStart_2774272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774272 prefixEnd_2774272 := by exact prefixLift 2774272
  have htrace : WordTrace (prefixWord ++ tailWord_2774272) baseStart_2774272 baseEnd_2774272 := by
    simpa [prefixWord, tailWord_2774272, baseEnd_2774272] using wordTrace_append hprefix tailTrace_2774272
  have hstable : (prefixWord ++ tailWord_2774272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774272).length < 2 ^ (prefixWord ++ tailWord_2774272).sum := by decide
  have hdescent : baseEnd_2774272 < baseStart_2774272 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774273 : List Nat := [1, 2, 4, 1, 1, 5, 2, 2, 5]
def baseStart_2774273 : Nat := 118140960795 + 2774273 * 2 ^ 59
def prefixEnd_2774273 : Nat := 4983230072969 + 3 ^ 40 * 2774273 * 2
def baseEnd_2774273 : Nat := 158281723976769930869873

theorem tailTrace_2774273 : CollatzResearch.WordTrace tailWord_2774273 prefixEnd_2774273 158281723976769930869873 := by
  unfold tailWord_2774273
  simp only [CollatzResearch.WordTrace]
  refine ⟨101186049078290203951719473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67457366052193469301146315 101186049078290203951719473)
  ·
    refine ⟨75889536808717652963789605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101186049078290203951719473 75889536808717652963789605)
    ·
      refine ⟨14229288151634559930710551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75889536808717652963789605 14229288151634559930710551)
      ·
        refine ⟨21343932227451839896065827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14229288151634559930710551 21343932227451839896065827)
        ·
          refine ⟨32015898341177759844098741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21343932227451839896065827 32015898341177759844098741)
          ·
            refine ⟨3001490469485414985384257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32015898341177759844098741 3001490469485414985384257)
            ·
              refine ⟨2251117852114061239038193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001490469485414985384257 2251117852114061239038193)
              ·
                refine ⟨1688338389085545929278645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2251117852114061239038193 1688338389085545929278645)
                ·
                  refine ⟨158281723976769930869873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1688338389085545929278645 158281723976769930869873)
                  ·
                    rfl

theorem cell23_2774273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 2, 5].length) (baseStart_2774273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774273 prefixEnd_2774273 := by exact prefixLift 2774273
  have htrace : WordTrace (prefixWord ++ tailWord_2774273) baseStart_2774273 baseEnd_2774273 := by
    simpa [prefixWord, tailWord_2774273, baseEnd_2774273] using wordTrace_append hprefix tailTrace_2774273
  have hstable : (prefixWord ++ tailWord_2774273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774273).length < 2 ^ (prefixWord ++ tailWord_2774273).sum := by decide
  have hdescent : baseEnd_2774273 < baseStart_2774273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774276 : List Nat := [2, 3, 2, 2, 2, 1, 1, 1, 2, 5, 2]
def baseStart_2774276 : Nat := 118140960795 + 2774276 * 2 ^ 59
def prefixEnd_2774276 : Nat := 4983230072969 + 3 ^ 40 * 2774276 * 2
def baseEnd_2774276 : Nat := 1424537056232892866091343

theorem tailTrace_2774276 : CollatzResearch.WordTrace tailWord_2774276 prefixEnd_2774276 1424537056232892866091343 := by
  unfold tailWord_2774276
  simp only [CollatzResearch.WordTrace]
  refine ⟨50593079248639667732039341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67457438998186223642719121 50593079248639667732039341)
  ·
    refine ⟨18972404718239875399514753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50593079248639667732039341 18972404718239875399514753)
    ·
      refine ⟨14229303538679906549636065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18972404718239875399514753 14229303538679906549636065)
      ·
        refine ⟨10671977654009929912227049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14229303538679906549636065 10671977654009929912227049)
        ·
          refine ⟨8003983240507447434170287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10671977654009929912227049 8003983240507447434170287)
          ·
            refine ⟨12005974860761171151255431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8003983240507447434170287 12005974860761171151255431)
            ·
              refine ⟨18008962291141756726883147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12005974860761171151255431 18008962291141756726883147)
              ·
                refine ⟨27013443436712635090324721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18008962291141756726883147 27013443436712635090324721)
                ·
                  refine ⟨20260082577534476317743541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27013443436712635090324721 20260082577534476317743541)
                  ·
                    refine ⟨1899382741643857154788457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20260082577534476317743541 1899382741643857154788457)
                    ·
                      refine ⟨1424537056232892866091343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899382741643857154788457 1424537056232892866091343)
                      ·
                        rfl

theorem cell23_2774276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_2774276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774276 prefixEnd_2774276 := by exact prefixLift 2774276
  have htrace : WordTrace (prefixWord ++ tailWord_2774276) baseStart_2774276 baseEnd_2774276 := by
    simpa [prefixWord, tailWord_2774276, baseEnd_2774276] using wordTrace_append hprefix tailTrace_2774276
  have hstable : (prefixWord ++ tailWord_2774276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774276).length < 2 ^ (prefixWord ++ tailWord_2774276).sum := by decide
  have hdescent : baseEnd_2774276 < baseStart_2774276 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774282 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 2, 8]
def baseStart_2774282 : Nat := 118140960795 + 2774282 * 2 ^ 59
def prefixEnd_2774282 : Nat := 4983230072969 + 3 ^ 40 * 2774282 * 2
def baseEnd_2774282 : Nat := 474846712372273280872105

theorem tailTrace_2774282 : CollatzResearch.WordTrace tailWord_2774282 prefixEnd_2774282 474846712372273280872105 := by
  unfold tailWord_2774282
  simp only [CollatzResearch.WordTrace]
  refine ⟨25296594333814399622199275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67457584890171732325864733 25296594333814399622199275)
  ·
    refine ⟨37944891500721599433298913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25296594333814399622199275 37944891500721599433298913)
    ·
      refine ⟨28458668625541199574974185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37944891500721599433298913 28458668625541199574974185)
      ·
        refine ⟨21344001469155899681230639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28458668625541199574974185 21344001469155899681230639)
        ·
          refine ⟨32016002203733849521845959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21344001469155899681230639 32016002203733849521845959)
          ·
            refine ⟨48024003305600774282768939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32016002203733849521845959 48024003305600774282768939)
            ·
              refine ⟨72036004958401161424153409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48024003305600774282768939 72036004958401161424153409)
              ·
                refine ⟨54027003718800871068115057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72036004958401161424153409 54027003718800871068115057)
                ·
                  refine ⟨40520252789100653301086293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54027003718800871068115057 40520252789100653301086293)
                  ·
                    refine ⟨474846712372273280872105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40520252789100653301086293 474846712372273280872105)
                    ·
                      rfl

theorem cell23_2774282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 2, 8].length) (baseStart_2774282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774282 prefixEnd_2774282 := by exact prefixLift 2774282
  have htrace : WordTrace (prefixWord ++ tailWord_2774282) baseStart_2774282 baseEnd_2774282 := by
    simpa [prefixWord, tailWord_2774282, baseEnd_2774282] using wordTrace_append hprefix tailTrace_2774282
  have hstable : (prefixWord ++ tailWord_2774282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774282).length < 2 ^ (prefixWord ++ tailWord_2774282).sum := by decide
  have hdescent : baseEnd_2774282 < baseStart_2774282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774303 : List Nat := [1, 1, 2, 4, 5, 1, 1, 1, 2, 5]
def baseStart_2774303 : Nat := 118140960795 + 2774303 * 2 ^ 59
def prefixEnd_2774303 : Nat := 4983230072969 + 3 ^ 40 * 2774303 * 2
def baseEnd_2774303 : Nat := 474850306736854753484573

theorem tailTrace_2774303 : CollatzResearch.WordTrace tailWord_2774303 prefixEnd_2774303 474850306736854753484573 := by
  unfold tailWord_2774303
  simp only [CollatzResearch.WordTrace]
  refine ⟨101187143268181519075311563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67458095512121012716874375 101187143268181519075311563)
  ·
    refine ⟨151780714902272278612967345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101187143268181519075311563 151780714902272278612967345)
    ·
      refine ⟨113835536176704208959725509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151780714902272278612967345 113835536176704208959725509)
      ·
        refine ⟨21344163033132039179948533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113835536176704208959725509 21344163033132039179948533)
        ·
          refine ⟨2001015284356128673120175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21344163033132039179948533 2001015284356128673120175)
          ·
            refine ⟨3001522926534193009680263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001015284356128673120175 3001522926534193009680263)
            ·
              refine ⟨4502284389801289514520395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001522926534193009680263 4502284389801289514520395)
              ·
                refine ⟨6753426584701934271780593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502284389801289514520395 6753426584701934271780593)
                ·
                  refine ⟨5065069938526450703835445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6753426584701934271780593 5065069938526450703835445)
                  ·
                    refine ⟨474850306736854753484573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5065069938526450703835445 474850306736854753484573)
                    ·
                      rfl

theorem cell23_2774303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 1, 2, 5].length) (baseStart_2774303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774303 prefixEnd_2774303 := by exact prefixLift 2774303
  have htrace : WordTrace (prefixWord ++ tailWord_2774303) baseStart_2774303 baseEnd_2774303 := by
    simpa [prefixWord, tailWord_2774303, baseEnd_2774303] using wordTrace_append hprefix tailTrace_2774303
  have hstable : (prefixWord ++ tailWord_2774303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774303).length < 2 ^ (prefixWord ++ tailWord_2774303).sum := by decide
  have hdescent : baseEnd_2774303 < baseStart_2774303 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774306 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 1, 3, 4]
def baseStart_2774306 : Nat := 118140960795 + 2774306 * 2 ^ 59
def prefixEnd_2774306 : Nat := 4983230072969 + 3 ^ 40 * 2774306 * 2
def baseEnd_2774306 : Nat := 1424552460652527748716205

theorem tailTrace_2774306 : CollatzResearch.WordTrace tailWord_2774306 prefixEnd_2774306 1424552460652527748716205 := by
  unfold tailWord_2774306
  simp only [CollatzResearch.WordTrace]
  refine ⟨25296813171792662646917693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67458168458113767058447181 25296813171792662646917693)
  ·
    refine ⟨9486304939422248492594135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25296813171792662646917693 9486304939422248492594135)
    ·
      refine ⟨14229457409133372738891203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9486304939422248492594135 14229457409133372738891203)
      ·
        refine ⟨21344186113700059108336805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14229457409133372738891203 21344186113700059108336805)
        ·
          refine ⟨4002034896318761082813151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21344186113700059108336805 4002034896318761082813151)
          ·
            refine ⟨6003052344478141624219727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4002034896318761082813151 6003052344478141624219727)
            ·
              refine ⟨9004578516717212436329591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003052344478141624219727 9004578516717212436329591)
              ·
                refine ⟨13506867775075818654494387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9004578516717212436329591 13506867775075818654494387)
                ·
                  refine ⟨20260301662613727981741581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13506867775075818654494387 20260301662613727981741581)
                  ·
                    refine ⟨7597613123480147993153093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20260301662613727981741581 7597613123480147993153093)
                    ·
                      refine ⟨1424552460652527748716205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7597613123480147993153093 1424552460652527748716205)
                      ·
                        rfl

theorem cell23_2774306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 1, 3, 4].length) (baseStart_2774306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774306 prefixEnd_2774306 := by exact prefixLift 2774306
  have htrace : WordTrace (prefixWord ++ tailWord_2774306) baseStart_2774306 baseEnd_2774306 := by
    simpa [prefixWord, tailWord_2774306, baseEnd_2774306] using wordTrace_append hprefix tailTrace_2774306
  have hstable : (prefixWord ++ tailWord_2774306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774306).length < 2 ^ (prefixWord ++ tailWord_2774306).sum := by decide
  have hdescent : baseEnd_2774306 < baseStart_2774306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774426 : List Nat := [3, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4]
def baseStart_2774426 : Nat := 118140960795 + 2774426 * 2 ^ 59
def prefixEnd_2774426 : Nat := 4983230072969 + 3 ^ 40 * 2774426 * 2
def baseEnd_2774426 : Nat := 1424614078331067279215653

theorem tailTrace_2774426 : CollatzResearch.WordTrace tailWord_2774426 prefixEnd_2774426 1424614078331067279215653 := by
  unfold tailWord_2774426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25297907361683977770509783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67461086297823940721359421 25297907361683977770509783)
  ·
    refine ⟨37946861042525966655764675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25297907361683977770509783 37946861042525966655764675)
    ·
      refine ⟨56920291563788949983647013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37946861042525966655764675 56920291563788949983647013)
      ·
        refine ⟨10672554668210428121933815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56920291563788949983647013 10672554668210428121933815)
        ·
          refine ⟨16008832002315642182900723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10672554668210428121933815 16008832002315642182900723)
          ·
            refine ⟨24013248003473463274351085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16008832002315642182900723 24013248003473463274351085)
            ·
              refine ⟨9004968001302548727881657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24013248003473463274351085 9004968001302548727881657)
              ·
                refine ⟨6753726000976911545911243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9004968001302548727881657 6753726000976911545911243)
                ·
                  refine ⟨10130589001465367318866865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6753726000976911545911243 10130589001465367318866865)
                  ·
                    refine ⟨7597941751099025489150149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10130589001465367318866865 7597941751099025489150149)
                    ·
                      refine ⟨1424614078331067279215653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7597941751099025489150149 1424614078331067279215653)
                      ·
                        rfl

theorem cell23_2774426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_2774426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774426 prefixEnd_2774426 := by exact prefixLift 2774426
  have htrace : WordTrace (prefixWord ++ tailWord_2774426) baseStart_2774426 baseEnd_2774426 := by
    simpa [prefixWord, tailWord_2774426, baseEnd_2774426] using wordTrace_append hprefix tailTrace_2774426
  have hstable : (prefixWord ++ tailWord_2774426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774426).length < 2 ^ (prefixWord ++ tailWord_2774426).sum := by decide
  have hdescent : baseEnd_2774426 < baseStart_2774426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774449 : List Nat := [1, 2, 2, 4, 1, 1, 1, 1, 1, 9]
def baseStart_2774449 : Nat := 118140960795 + 2774449 * 2 ^ 59
def prefixEnd_2774449 : Nat := 4983230072969 + 3 ^ 40 * 2774449 * 2
def baseEnd_2774449 : Nat := 474875296128706896409349

theorem tailTrace_2774449 : CollatzResearch.WordTrace tailWord_2774449 prefixEnd_2774449 474875296128706896409349 := by
  unfold tailWord_2774449
  simp only [CollatzResearch.WordTrace]
  refine ⟨101192468325652586010126401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67461645550435057340084267 101192468325652586010126401)
  ·
    refine ⟨75894351244239439507594801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101192468325652586010126401 75894351244239439507594801)
    ·
      refine ⟨56920763433179579630696101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75894351244239439507594801 56920763433179579630696101)
      ·
        refine ⟨10672643143721171180755519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56920763433179579630696101 10672643143721171180755519)
        ·
          refine ⟨16008964715581756771133279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10672643143721171180755519 16008964715581756771133279)
          ·
            refine ⟨24013447073372635156699919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16008964715581756771133279 24013447073372635156699919)
            ·
              refine ⟨36020170610058952735049879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24013447073372635156699919 36020170610058952735049879)
              ·
                refine ⟨54030255915088429102574819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36020170610058952735049879 54030255915088429102574819)
                ·
                  refine ⟨81045383872632643653862229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54030255915088429102574819 81045383872632643653862229)
                  ·
                    refine ⟨474875296128706896409349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81045383872632643653862229 474875296128706896409349)
                    ·
                      rfl

theorem cell23_2774449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 1, 1, 1, 9].length) (baseStart_2774449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774449 prefixEnd_2774449 := by exact prefixLift 2774449
  have htrace : WordTrace (prefixWord ++ tailWord_2774449) baseStart_2774449 baseEnd_2774449 := by
    simpa [prefixWord, tailWord_2774449, baseEnd_2774449] using wordTrace_append hprefix tailTrace_2774449
  have hstable : (prefixWord ++ tailWord_2774449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774449).length < 2 ^ (prefixWord ++ tailWord_2774449).sum := by decide
  have hdescent : baseEnd_2774449 < baseStart_2774449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774473 : List Nat := [1, 2, 1, 1, 2, 1, 3, 6, 1, 3, 2]
def baseStart_2774473 : Nat := 118140960795 + 2774473 * 2 ^ 59
def prefixEnd_2774473 : Nat := 4983230072969 + 3 ^ 40 * 2774473 * 2
def baseEnd_2774473 : Nat := 1424638211921828595327937

theorem tailTrace_2774473 : CollatzResearch.WordTrace tailWord_2774473 prefixEnd_2774473 1424638211921828595327937 := by
  unfold tailWord_2774473
  simp only [CollatzResearch.WordTrace]
  refine ⟨101193343677565638109000073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67462229118377092072666715 101193343677565638109000073)
  ·
    refine ⟨75895007758174228581750055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101193343677565638109000073 75895007758174228581750055)
    ·
      refine ⟨113842511637261342872625083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75895007758174228581750055 113842511637261342872625083)
      ·
        refine ⟨170763767455892014308937625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113842511637261342872625083 170763767455892014308937625)
        ·
          refine ⟨128072825591919010731703219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170763767455892014308937625 128072825591919010731703219)
          ·
            refine ⟨192109238387878516097554829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128072825591919010731703219 192109238387878516097554829)
            ·
              refine ⟨72040964395454443536583061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192109238387878516097554829 72040964395454443536583061)
              ·
                refine ⟨3376920206036927040777331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72040964395454443536583061 3376920206036927040777331)
                ·
                  refine ⟨5065380309055390561165997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376920206036927040777331 5065380309055390561165997)
                  ·
                    refine ⟨1899517615895771460437249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5065380309055390561165997 1899517615895771460437249)
                    ·
                      refine ⟨1424638211921828595327937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899517615895771460437249 1424638211921828595327937)
                      ·
                        rfl

theorem cell23_2774473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 1, 3, 2].length) (baseStart_2774473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774473 prefixEnd_2774473 := by exact prefixLift 2774473
  have htrace : WordTrace (prefixWord ++ tailWord_2774473) baseStart_2774473 baseEnd_2774473 := by
    simpa [prefixWord, tailWord_2774473, baseEnd_2774473] using wordTrace_append hprefix tailTrace_2774473
  have hstable : (prefixWord ++ tailWord_2774473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774473).length < 2 ^ (prefixWord ++ tailWord_2774473).sum := by decide
  have hdescent : baseEnd_2774473 < baseStart_2774473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774484 : List Nat := [2, 4, 1, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_2774484 : Nat := 118140960795 + 2774484 * 2 ^ 59
def prefixEnd_2774484 : Nat := 4983230072969 + 3 ^ 40 * 2774484 * 2
def baseEnd_2774484 : Nat := 1424643860209028052290387

theorem tailTrace_2774484 : CollatzResearch.WordTrace tailWord_2774484 prefixEnd_2774484 1424643860209028052290387 := by
  unfold tailWord_2774484
  simp only [CollatzResearch.WordTrace]
  refine ⟨50596872440262893493825253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67462496587017191325100337 50596872440262893493825253)
  ·
    refine ⟨9486913582549292530092235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50596872440262893493825253 9486913582549292530092235)
    ·
      refine ⟨14230370373823938795138353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9486913582549292530092235 14230370373823938795138353)
      ·
        refine ⟨10672777780367954096353765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14230370373823938795138353 10672777780367954096353765)
        ·
          refine ⟨2001145833818991393066331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10672777780367954096353765 2001145833818991393066331)
          ·
            refine ⟨3001718750728487089599497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2001145833818991393066331 3001718750728487089599497)
            ·
              refine ⟨2251289063046365317199623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3001718750728487089599497 2251289063046365317199623)
              ·
                refine ⟨3376933594569547975799435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251289063046365317199623 3376933594569547975799435)
                ·
                  refine ⟨5065400391854321963699153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376933594569547975799435 5065400391854321963699153)
                  ·
                    refine ⟨3799050293890741472774365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5065400391854321963699153 3799050293890741472774365)
                    ·
                      refine ⟨1424643860209028052290387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3799050293890741472774365 1424643860209028052290387)
                      ·
                        rfl

theorem cell23_2774484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_2774484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774484 prefixEnd_2774484 := by exact prefixLift 2774484
  have htrace : WordTrace (prefixWord ++ tailWord_2774484) baseStart_2774484 baseEnd_2774484 := by
    simpa [prefixWord, tailWord_2774484, baseEnd_2774484] using wordTrace_append hprefix tailTrace_2774484
  have hstable : (prefixWord ++ tailWord_2774484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774484).length < 2 ^ (prefixWord ++ tailWord_2774484).sum := by decide
  have hdescent : baseEnd_2774484 < baseStart_2774484 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774490 : List Nat := [3, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2]
def baseStart_2774490 : Nat := 118140960795 + 2774490 * 2 ^ 59
def prefixEnd_2774490 : Nat := 4983230072969 + 3 ^ 40 * 2774490 * 2
def baseEnd_2774490 : Nat := 1424646941092955028815359

theorem tailTrace_2774490 : CollatzResearch.WordTrace tailWord_2774490 prefixEnd_2774490 1424646941092955028815359 := by
  unfold tailWord_2774490
  simp only [CollatzResearch.WordTrace]
  refine ⟨25298490929626012503092231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67462642479002700008245949 25298490929626012503092231)
  ·
    refine ⟨37947736394439018754638347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25298490929626012503092231 37947736394439018754638347)
    ·
      refine ⟨56921604591658528131957521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37947736394439018754638347 56921604591658528131957521)
      ·
        refine ⟨42691203443743896098968141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56921604591658528131957521 42691203443743896098968141)
        ·
          refine ⟨16009201291403961037113053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42691203443743896098968141 16009201291403961037113053)
          ·
            refine ⟨6003450484276485388917395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16009201291403961037113053 6003450484276485388917395)
            ·
              refine ⟨9005175726414728083376093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6003450484276485388917395 9005175726414728083376093)
              ·
                refine ⟨3376940897405523031266035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9005175726414728083376093 3376940897405523031266035)
                ·
                  refine ⟨5065411346108284546899053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3376940897405523031266035 5065411346108284546899053)
                  ·
                    refine ⟨1899529254790606705087145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5065411346108284546899053 1899529254790606705087145)
                    ·
                      refine ⟨1424646941092955028815359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899529254790606705087145 1424646941092955028815359)
                      ·
                        rfl

theorem cell23_2774490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_2774490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774490 prefixEnd_2774490 := by exact prefixLift 2774490
  have htrace : WordTrace (prefixWord ++ tailWord_2774490) baseStart_2774490 baseEnd_2774490 := by
    simpa [prefixWord, tailWord_2774490, baseEnd_2774490] using wordTrace_append hprefix tailTrace_2774490
  have hstable : (prefixWord ++ tailWord_2774490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774490).length < 2 ^ (prefixWord ++ tailWord_2774490).sum := by decide
  have hdescent : baseEnd_2774490 < baseStart_2774490 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774520 : List Nat := [2, 1, 2, 1, 1, 7, 1, 1, 1, 4, 2]
def baseStart_2774520 : Nat := 118140960795 + 2774520 * 2 ^ 59
def prefixEnd_2774520 : Nat := 4983230072969 + 3 ^ 40 * 2774520 * 2
def baseEnd_2774520 : Nat := 1424662345512589911440221

theorem tailTrace_2774520 : CollatzResearch.WordTrace tailWord_2774520 prefixEnd_2774520 1424662345512589911440221 := by
  unfold tailWord_2774520
  simp only [CollatzResearch.WordTrace]
  refine ⟨50597528954197682567980507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67463371938930243423974009 50597528954197682567980507)
  ·
    refine ⟨75896293431296523851970761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50597528954197682567980507 75896293431296523851970761)
    ·
      refine ⟨56922220073472392888978071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75896293431296523851970761 56922220073472392888978071)
      ·
        refine ⟨85383330110208589333467107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56922220073472392888978071 85383330110208589333467107)
        ·
          refine ⟨128074995165312884000200661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85383330110208589333467107 128074995165312884000200661)
          ·
            refine ⟨3001757699187020718754703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128074995165312884000200661 3001757699187020718754703)
            ·
              refine ⟨4502636548780531078132055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3001757699187020718754703 4502636548780531078132055)
              ·
                refine ⟨6753954823170796617198083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502636548780531078132055 6753954823170796617198083)
                ·
                  refine ⟨10130932234756194925797125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6753954823170796617198083 10130932234756194925797125)
                  ·
                    refine ⟨1899549794016786548586961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10130932234756194925797125 1899549794016786548586961)
                    ·
                      refine ⟨1424662345512589911440221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899549794016786548586961 1424662345512589911440221)
                      ·
                        rfl

theorem cell23_2774520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 1, 1, 1, 4, 2].length) (baseStart_2774520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774520 prefixEnd_2774520 := by exact prefixLift 2774520
  have htrace : WordTrace (prefixWord ++ tailWord_2774520) baseStart_2774520 baseEnd_2774520 := by
    simpa [prefixWord, tailWord_2774520, baseEnd_2774520] using wordTrace_append hprefix tailTrace_2774520
  have hstable : (prefixWord ++ tailWord_2774520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774520).length < 2 ^ (prefixWord ++ tailWord_2774520).sum := by decide
  have hdescent : baseEnd_2774520 < baseStart_2774520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774536 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 1, 5, 3]
def baseStart_2774536 : Nat := 118140960795 + 2774536 * 2 ^ 59
def prefixEnd_2774536 : Nat := 4983230072969 + 3 ^ 40 * 2774536 * 2
def baseEnd_2774536 : Nat := 1424670561203061848840147

theorem tailTrace_2774536 : CollatzResearch.WordTrace tailWord_2774536 prefixEnd_2774536 1424670561203061848840147 := by
  unfold tailWord_2774536
  simp only [CollatzResearch.WordTrace]
  refine ⟨50597820738168699934271731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67463760984224933245695641 50597820738168699934271731)
  ·
    refine ⟨75896731107253049901407597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50597820738168699934271731 75896731107253049901407597)
    ·
      refine ⟨28461274165219893713027849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75896731107253049901407597 28461274165219893713027849)
      ·
        refine ⟨21345955623914920284770887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28461274165219893713027849 21345955623914920284770887)
        ·
          refine ⟨32018933435872380427156331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21345955623914920284770887 32018933435872380427156331)
          ·
            refine ⟨48028400153808570640734497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32018933435872380427156331 48028400153808570640734497)
            ·
              refine ⟨36021300115356427980550873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48028400153808570640734497 36021300115356427980550873)
              ·
                refine ⟨27015975086517320985413155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36021300115356427980550873 27015975086517320985413155)
                ·
                  refine ⟨40523962629775981478119733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27015975086517320985413155 40523962629775981478119733)
                  ·
                    refine ⟨3799121496541498263573725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40523962629775981478119733 3799121496541498263573725)
                    ·
                      refine ⟨1424670561203061848840147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3799121496541498263573725 1424670561203061848840147)
                      ·
                        rfl

theorem cell23_2774536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 1, 5, 3].length) (baseStart_2774536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774536 prefixEnd_2774536 := by exact prefixLift 2774536
  have htrace : WordTrace (prefixWord ++ tailWord_2774536) baseStart_2774536 baseEnd_2774536 := by
    simpa [prefixWord, tailWord_2774536, baseEnd_2774536] using wordTrace_append hprefix tailTrace_2774536
  have hstable : (prefixWord ++ tailWord_2774536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774536).length < 2 ^ (prefixWord ++ tailWord_2774536).sum := by decide
  have hdescent : baseEnd_2774536 < baseStart_2774536 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774576 : List Nat := [2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4]
def baseStart_2774576 : Nat := 118140960795 + 2774576 * 2 ^ 59
def prefixEnd_2774576 : Nat := 4983230072969 + 3 ^ 40 * 2774576 * 2
def baseEnd_2774576 : Nat := 1424691100429241692339963

theorem tailTrace_2774576 : CollatzResearch.WordTrace tailWord_2774576 prefixEnd_2774576 1424691100429241692339963 := by
  unfold tailWord_2774576
  simp only [CollatzResearch.WordTrace]
  refine ⟨50598550198096243349999791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67464733597461657799999721 50598550198096243349999791)
  ·
    refine ⟨75897825297144365024999687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50598550198096243349999791 75897825297144365024999687)
    ·
      refine ⟨113846737945716547537499531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75897825297144365024999687 113846737945716547537499531)
      ·
        refine ⟨170770106918574821306249297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113846737945716547537499531 170770106918574821306249297)
        ·
          refine ⟨128077580188931115979686973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170770106918574821306249297 128077580188931115979686973)
          ·
            refine ⟨48029092570849168492382615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128077580188931115979686973 48029092570849168492382615)
            ·
              refine ⟨72043638856273752738573923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48029092570849168492382615 72043638856273752738573923)
              ·
                refine ⟨108065458284410629107860885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72043638856273752738573923 108065458284410629107860885)
                ·
                  refine ⟨5065568357081748239430979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 108065458284410629107860885 5065568357081748239430979)
                  ·
                    refine ⟨7598352535622622359146469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5065568357081748239430979 7598352535622622359146469)
                    ·
                      refine ⟨1424691100429241692339963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7598352535622622359146469 1424691100429241692339963)
                      ·
                        rfl

theorem cell23_2774576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 1, 1, 6, 1, 4].length) (baseStart_2774576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774576 prefixEnd_2774576 := by exact prefixLift 2774576
  have htrace : WordTrace (prefixWord ++ tailWord_2774576) baseStart_2774576 baseEnd_2774576 := by
    simpa [prefixWord, tailWord_2774576, baseEnd_2774576] using wordTrace_append hprefix tailTrace_2774576
  have hstable : (prefixWord ++ tailWord_2774576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774576).length < 2 ^ (prefixWord ++ tailWord_2774576).sum := by decide
  have hdescent : baseEnd_2774576 < baseStart_2774576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774606 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6]
def baseStart_2774606 : Nat := 118140960795 + 2774606 * 2 ^ 59
def prefixEnd_2774606 : Nat := 4983230072969 + 3 ^ 40 * 2774606 * 2
def baseEnd_2774606 : Nat := 1424706504848876574964825

theorem tailTrace_2774606 : CollatzResearch.WordTrace tailWord_2774606 prefixEnd_2774606 1424706504848876574964825 := by
  unfold tailWord_2774606
  simp only [CollatzResearch.WordTrace]
  refine ⟨12649774323260475227948959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67465463057389201215727781 12649774323260475227948959)
  ·
    refine ⟨18974661484890712841923439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12649774323260475227948959 18974661484890712841923439)
    ·
      refine ⟨28461992227336069262885159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18974661484890712841923439 28461992227336069262885159)
      ·
        refine ⟨42692988341004103894327739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28461992227336069262885159 42692988341004103894327739)
        ·
          refine ⟨64039482511506155841491609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42692988341004103894327739 64039482511506155841491609)
          ·
            refine ⟨48029611883629616881118707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64039482511506155841491609 48029611883629616881118707)
            ·
              refine ⟨72044417825444425321678061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48029611883629616881118707 72044417825444425321678061)
              ·
                refine ⟨27016656684541659495629273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72044417825444425321678061 27016656684541659495629273)
                ·
                  refine ⟨20262492513406244621721955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27016656684541659495629273 20262492513406244621721955)
                  ·
                    refine ⟨30393738770109366932582933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20262492513406244621721955 30393738770109366932582933)
                    ·
                      refine ⟨1424706504848876574964825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30393738770109366932582933 1424706504848876574964825)
                      ·
                        rfl

theorem cell23_2774606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 2, 1, 6].length) (baseStart_2774606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774606 prefixEnd_2774606 := by exact prefixLift 2774606
  have htrace : WordTrace (prefixWord ++ tailWord_2774606) baseStart_2774606 baseEnd_2774606 := by
    simpa [prefixWord, tailWord_2774606, baseEnd_2774606] using wordTrace_append hprefix tailTrace_2774606
  have hstable : (prefixWord ++ tailWord_2774606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774606).length < 2 ^ (prefixWord ++ tailWord_2774606).sum := by decide
  have hdescent : baseEnd_2774606 < baseStart_2774606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774693 : List Nat := [1, 3, 1, 2, 1, 2, 5, 1, 1, 6]
def baseStart_2774693 : Nat := 118140960795 + 2774693 * 2 ^ 59
def prefixEnd_2774693 : Nat := 4983230072969 + 3 ^ 40 * 2774693 * 2
def baseEnd_2774693 : Nat := 474917059221939244858975

theorem tailTrace_2774693 : CollatzResearch.WordTrace tailWord_2774693 prefixEnd_2774693 474917059221939244858975 := by
  unfold tailWord_2774693
  simp only [CollatzResearch.WordTrace]
  refine ⟨101201367736768615682008733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67467578491179077121339155 101201367736768615682008733)
  ·
    refine ⟨37950512901288230880753275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101201367736768615682008733 37950512901288230880753275)
    ·
      refine ⟨56925769351932346321129913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37950512901288230880753275 56925769351932346321129913)
      ·
        refine ⟨42694327013949259740847435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56925769351932346321129913 42694327013949259740847435)
        ·
          refine ⟨64041490520923889611271153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42694327013949259740847435 64041490520923889611271153)
          ·
            refine ⟨48031117890692917208453365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64041490520923889611271153 48031117890692917208453365)
            ·
              refine ⟨4502917302252460988292503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48031117890692917208453365 4502917302252460988292503)
              ·
                refine ⟨6754375953378691482438755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4502917302252460988292503 6754375953378691482438755)
                ·
                  refine ⟨10131563930068037223658133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754375953378691482438755 10131563930068037223658133)
                  ·
                    refine ⟨474917059221939244858975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10131563930068037223658133 474917059221939244858975)
                    ·
                      rfl

theorem cell23_2774693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_2774693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774693 prefixEnd_2774693 := by exact prefixLift 2774693
  have htrace : WordTrace (prefixWord ++ tailWord_2774693) baseStart_2774693 baseEnd_2774693 := by
    simpa [prefixWord, tailWord_2774693, baseEnd_2774693] using wordTrace_append hprefix tailTrace_2774693
  have hstable : (prefixWord ++ tailWord_2774693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774693).length < 2 ^ (prefixWord ++ tailWord_2774693).sum := by decide
  have hdescent : baseEnd_2774693 < baseStart_2774693 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774713 : List Nat := [1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 4]
def baseStart_2774713 : Nat := 118140960795 + 2774713 * 2 ^ 59
def prefixEnd_2774713 : Nat := 4983230072969 + 3 ^ 40 * 2774713 * 2
def baseEnd_2774713 : Nat := 1424761447278907656326833

theorem tailTrace_2774713 : CollatzResearch.WordTrace tailWord_2774713 prefixEnd_2774713 1424761447278907656326833 := by
  unfold tailWord_2774713
  simp only [CollatzResearch.WordTrace]
  refine ⟨101202097196696159097736793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67468064797797439398491195 101202097196696159097736793)
  ·
    refine ⟨75901572897522119323302595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101202097196696159097736793 75901572897522119323302595)
    ·
      refine ⟨113852359346283178984953893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75901572897522119323302595 113852359346283178984953893)
      ·
        refine ⟨21347317377428096059678855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113852359346283178984953893 21347317377428096059678855)
        ·
          refine ⟨32020976066142144089518283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21347317377428096059678855 32020976066142144089518283)
          ·
            refine ⟨48031464099213216134277425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32020976066142144089518283 48031464099213216134277425)
            ·
              refine ⟨36023598074409912100708069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48031464099213216134277425 36023598074409912100708069)
              ·
                refine ⟨6754424638951858518882763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36023598074409912100708069 6754424638951858518882763)
                ·
                  refine ⟨10131636958427787778324145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754424638951858518882763 10131636958427787778324145)
                  ·
                    refine ⟨7598727718820840833743109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10131636958427787778324145 7598727718820840833743109)
                    ·
                      refine ⟨1424761447278907656326833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7598727718820840833743109 1424761447278907656326833)
                      ·
                        rfl

theorem cell23_2774713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 2, 4, 1, 2, 4].length) (baseStart_2774713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774713 prefixEnd_2774713 := by exact prefixLift 2774713
  have htrace : WordTrace (prefixWord ++ tailWord_2774713) baseStart_2774713 baseEnd_2774713 := by
    simpa [prefixWord, tailWord_2774713, baseEnd_2774713] using wordTrace_append hprefix tailTrace_2774713
  have hstable : (prefixWord ++ tailWord_2774713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774713).length < 2 ^ (prefixWord ++ tailWord_2774713).sum := by decide
  have hdescent : baseEnd_2774713 < baseStart_2774713 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774720 : List Nat := [2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3]
def baseStart_2774720 : Nat := 118140960795 + 2774720 * 2 ^ 59
def prefixEnd_2774720 : Nat := 4983230072969 + 3 ^ 40 * 2774720 * 2
def baseEnd_2774720 : Nat := 1424765041643489128939301

theorem tailTrace_2774720 : CollatzResearch.WordTrace tailWord_2774720 prefixEnd_2774720 1424765041643489128939301 := by
  unfold tailWord_2774720
  simp only [CollatzResearch.WordTrace]
  refine ⟨50601176253835399646620807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67468235005113866195494409 50601176253835399646620807)
  ·
    refine ⟨75901764380753099469931211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50601176253835399646620807 75901764380753099469931211)
    ·
      refine ⟨113852646571129649204896817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75901764380753099469931211 113852646571129649204896817)
      ·
        refine ⟨85389484928347236903672613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113852646571129649204896817 85389484928347236903672613)
        ·
          refine ⟨16010528424065106919438615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85389484928347236903672613 16010528424065106919438615)
          ·
            refine ⟨24015792636097660379157923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16010528424065106919438615 24015792636097660379157923)
            ·
              refine ⟨36023688954146490568736885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24015792636097660379157923 36023688954146490568736885)
              ·
                refine ⟨3377220839451233490819083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36023688954146490568736885 3377220839451233490819083)
                ·
                  refine ⟨5065831259176850236228625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377220839451233490819083 5065831259176850236228625)
                  ·
                    refine ⟨3799373444382637677171469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5065831259176850236228625 3799373444382637677171469)
                    ·
                      refine ⟨1424765041643489128939301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3799373444382637677171469 1424765041643489128939301)
                      ·
                        rfl

theorem cell23_2774720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 5, 1, 2, 3].length) (baseStart_2774720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774720 prefixEnd_2774720 := by exact prefixLift 2774720
  have htrace : WordTrace (prefixWord ++ tailWord_2774720) baseStart_2774720 baseEnd_2774720 := by
    simpa [prefixWord, tailWord_2774720, baseEnd_2774720] using wordTrace_append hprefix tailTrace_2774720
  have hstable : (prefixWord ++ tailWord_2774720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774720).length < 2 ^ (prefixWord ++ tailWord_2774720).sum := by decide
  have hdescent : baseEnd_2774720 < baseStart_2774720 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774740 : List Nat := [2, 4, 1, 3, 1, 2, 2, 8]
def baseStart_2774740 : Nat := 118140960795 + 2774740 * 2 ^ 59
def prefixEnd_2774740 : Nat := 4983230072969 + 3 ^ 40 * 2774740 * 2
def baseEnd_2774740 : Nat := 52769455972465890766267

theorem tailTrace_2774740 : CollatzResearch.WordTrace tailWord_2774740 prefixEnd_2774740 52769455972465890766267 := by
  unfold tailWord_2774740
  simp only [CollatzResearch.WordTrace]
  refine ⟨50601540983799171354484837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67468721311732228472646449 50601540983799171354484837)
  ·
    refine ⟨9487788934462344628965907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50601540983799171354484837 9487788934462344628965907)
    ·
      refine ⟨14231683401693516943448861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9487788934462344628965907 14231683401693516943448861)
      ·
        refine ⟨5336881275635068853793323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14231683401693516943448861 5336881275635068853793323)
        ·
          refine ⟨8005321913452603280689985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5336881275635068853793323 8005321913452603280689985)
          ·
            refine ⟨6003991435089452460517489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8005321913452603280689985 6003991435089452460517489)
            ·
              refine ⟨4502993576317089345388117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6003991435089452460517489 4502993576317089345388117)
              ·
                refine ⟨52769455972465890766267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4502993576317089345388117 52769455972465890766267)
                ·
                  rfl

theorem cell23_2774740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 8].length) (baseStart_2774740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774740 prefixEnd_2774740 := by exact prefixLift 2774740
  have htrace : WordTrace (prefixWord ++ tailWord_2774740) baseStart_2774740 baseEnd_2774740 := by
    simpa [prefixWord, tailWord_2774740, baseEnd_2774740] using wordTrace_append hprefix tailTrace_2774740
  have hstable : (prefixWord ++ tailWord_2774740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774740).length < 2 ^ (prefixWord ++ tailWord_2774740).sum := by decide
  have hdescent : baseEnd_2774740 < baseStart_2774740 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774807 : List Nat := [1, 1, 3, 4, 2, 1, 1, 3, 1, 4, 2]
def baseStart_2774807 : Nat := 118140960795 + 2774807 * 2 ^ 59
def prefixEnd_2774807 : Nat := 4983230072969 + 3 ^ 40 * 2774807 * 2
def baseEnd_2774807 : Nat := 1424809714460430288551401

theorem tailTrace_2774807 : CollatzResearch.WordTrace tailWord_2774807 prefixEnd_2774807 1424809714460430288551401 := by
  unfold tailWord_2774807
  simp only [CollatzResearch.WordTrace]
  refine ⟨101205525658355613151658675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67470350438903742101105783 101205525658355613151658675)
  ·
    refine ⟨151808288487533419727488013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101205525658355613151658675 151808288487533419727488013)
    ·
      refine ⟨56928108182825032397808005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151808288487533419727488013 56928108182825032397808005)
      ·
        refine ⟨10674020284279693574589001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56928108182825032397808005 10674020284279693574589001)
        ·
          refine ⟨8005515213209770180941751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10674020284279693574589001 8005515213209770180941751)
          ·
            refine ⟨12008272819814655271412627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8005515213209770180941751 12008272819814655271412627)
            ·
              refine ⟨18012409229721982907118941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12008272819814655271412627 18012409229721982907118941)
              ·
                refine ⟨6754653461145743590169603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18012409229721982907118941 6754653461145743590169603)
                ·
                  refine ⟨10131980191718615385254405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6754653461145743590169603 10131980191718615385254405)
                  ·
                    refine ⟨1899746285947240384735201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10131980191718615385254405 1899746285947240384735201)
                    ·
                      refine ⟨1424809714460430288551401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899746285947240384735201 1424809714460430288551401)
                      ·
                        rfl

theorem cell23_2774807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 1, 1, 3, 1, 4, 2].length) (baseStart_2774807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774807 prefixEnd_2774807 := by exact prefixLift 2774807
  have htrace : WordTrace (prefixWord ++ tailWord_2774807) baseStart_2774807 baseEnd_2774807 := by
    simpa [prefixWord, tailWord_2774807, baseEnd_2774807] using wordTrace_append hprefix tailTrace_2774807
  have hstable : (prefixWord ++ tailWord_2774807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774807).length < 2 ^ (prefixWord ++ tailWord_2774807).sum := by decide
  have hdescent : baseEnd_2774807 < baseStart_2774807 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774840 : List Nat := [2, 1, 2, 1, 3, 3, 1, 2, 2, 3, 3]
def baseStart_2774840 : Nat := 118140960795 + 2774840 * 2 ^ 59
def prefixEnd_2774840 : Nat := 4983230072969 + 3 ^ 40 * 2774840 * 2
def baseEnd_2774840 : Nat := 1424826659322028659438749

theorem tailTrace_2774840 : CollatzResearch.WordTrace tailWord_2774840 prefixEnd_2774840 1424826659322028659438749 := by
  unfold tailWord_2774840
  simp only [CollatzResearch.WordTrace]
  refine ⟨50603364633618029893804987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67471152844824039858406649 50603364633618029893804987)
  ·
    refine ⟨75905046950427044840707481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50603364633618029893804987 75905046950427044840707481)
    ·
      refine ⟨56928785212820283630530611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75905046950427044840707481 56928785212820283630530611)
      ·
        refine ⟨85393177819230425445795917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56928785212820283630530611 85393177819230425445795917)
        ·
          refine ⟨32022441682211409542173469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85393177819230425445795917 32022441682211409542173469)
          ·
            refine ⟨12008415630829278578315051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32022441682211409542173469 12008415630829278578315051)
            ·
              refine ⟨18012623446243917867472577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12008415630829278578315051 18012623446243917867472577)
              ·
                refine ⟨13509467584682938400604433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18012623446243917867472577 13509467584682938400604433)
                ·
                  refine ⟨10132100688512203800453325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13509467584682938400604433 10132100688512203800453325)
                  ·
                    refine ⟨3799537758192076425169997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10132100688512203800453325 3799537758192076425169997)
                    ·
                      refine ⟨1424826659322028659438749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3799537758192076425169997 1424826659322028659438749)
                      ·
                        rfl

theorem cell23_2774840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 2, 3, 3].length) (baseStart_2774840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774840 prefixEnd_2774840 := by exact prefixLift 2774840
  have htrace : WordTrace (prefixWord ++ tailWord_2774840) baseStart_2774840 baseEnd_2774840 := by
    simpa [prefixWord, tailWord_2774840, baseEnd_2774840] using wordTrace_append hprefix tailTrace_2774840
  have hstable : (prefixWord ++ tailWord_2774840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774840).length < 2 ^ (prefixWord ++ tailWord_2774840).sum := by decide
  have hdescent : baseEnd_2774840 < baseStart_2774840 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774841 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2774841 : Nat := 118140960795 + 2774841 * 2 ^ 59
def prefixEnd_2774841 : Nat := 4983230072969 + 3 ^ 40 * 2774841 * 2
def baseEnd_2774841 : Nat := 1424827172802683155526245

theorem tailTrace_2774841 : CollatzResearch.WordTrace tailWord_2774841 prefixEnd_2774841 1424827172802683155526245 := by
  unfold tailWord_2774841
  simp only [CollatzResearch.WordTrace]
  refine ⟨101206765740232436958396377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67471177160154957972264251 101206765740232436958396377)
  ·
    refine ⟨75905074305174327718797283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101206765740232436958396377 75905074305174327718797283)
    ·
      refine ⟨113857611457761491578195925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75905074305174327718797283 113857611457761491578195925)
      ·
        refine ⟨2668537768541284958863967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 113857611457761491578195925 2668537768541284958863967)
        ·
          refine ⟨4002806652811927438295951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668537768541284958863967 4002806652811927438295951)
          ·
            refine ⟨6004209979217891157443927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4002806652811927438295951 6004209979217891157443927)
            ·
              refine ⟨9006314968826836736165891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004209979217891157443927 9006314968826836736165891)
              ·
                refine ⟨13509472453240255104248837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9006314968826836736165891 13509472453240255104248837)
                ·
                  refine ⟨2533026084982547832046657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13509472453240255104248837 2533026084982547832046657)
                  ·
                    refine ⟨1899769563736910874034993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2533026084982547832046657 1899769563736910874034993)
                    ·
                      refine ⟨1424827172802683155526245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899769563736910874034993 1424827172802683155526245)
                      ·
                        rfl

theorem cell23_2774841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2774841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774841 prefixEnd_2774841 := by exact prefixLift 2774841
  have htrace : WordTrace (prefixWord ++ tailWord_2774841) baseStart_2774841 baseEnd_2774841 := by
    simpa [prefixWord, tailWord_2774841, baseEnd_2774841] using wordTrace_append hprefix tailTrace_2774841
  have hstable : (prefixWord ++ tailWord_2774841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774841).length < 2 ^ (prefixWord ++ tailWord_2774841).sum := by decide
  have hdescent : baseEnd_2774841 < baseStart_2774841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774853 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_2774853 : Nat := 118140960795 + 2774853 * 2 ^ 59
def prefixEnd_2774853 : Nat := 4983230072969 + 3 ^ 40 * 2774853 * 2
def baseEnd_2774853 : Nat := 1424833334570537108576189

theorem tailTrace_2774853 : CollatzResearch.WordTrace tailWord_2774853 prefixEnd_2774853 1424833334570537108576189 := by
  unfold tailWord_2774853
  simp only [CollatzResearch.WordTrace]
  refine ⟨101207203416188963007833213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67471468944125975338555475 101207203416188963007833213)
  ·
    refine ⟨37952701281070861127937455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101207203416188963007833213 37952701281070861127937455)
    ·
      refine ⟨56929051921606291691906183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37952701281070861127937455 56929051921606291691906183)
      ·
        refine ⟨85393577882409437537859275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56929051921606291691906183 85393577882409437537859275)
        ·
          refine ⟨128090366823614156306788913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85393577882409437537859275 128090366823614156306788913)
          ·
            refine ⟨96067775117710617230091685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128090366823614156306788913 96067775117710617230091685)
            ·
              refine ⟨18012707834570740730642191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 96067775117710617230091685 18012707834570740730642191)
              ·
                refine ⟨27019061751856111095963287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18012707834570740730642191 27019061751856111095963287)
                ·
                  refine ⟨40528592627784166643944931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27019061751856111095963287 40528592627784166643944931)
                  ·
                    refine ⟨60792888941676249965917397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40528592627784166643944931 60792888941676249965917397)
                    ·
                      refine ⟨1424833334570537108576189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60792888941676249965917397 1424833334570537108576189)
                      ·
                        rfl

theorem cell23_2774853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_2774853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774853 prefixEnd_2774853 := by exact prefixLift 2774853
  have htrace : WordTrace (prefixWord ++ tailWord_2774853) baseStart_2774853 baseEnd_2774853 := by
    simpa [prefixWord, tailWord_2774853, baseEnd_2774853] using wordTrace_append hprefix tailTrace_2774853
  have hstable : (prefixWord ++ tailWord_2774853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774853).length < 2 ^ (prefixWord ++ tailWord_2774853).sum := by decide
  have hdescent : baseEnd_2774853 < baseStart_2774853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774854 : List Nat := [6, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4]
def baseStart_2774854 : Nat := 118140960795 + 2774854 * 2 ^ 59
def prefixEnd_2774854 : Nat := 4983230072969 + 3 ^ 40 * 2774854 * 2
def baseEnd_2774854 : Nat := 1424833848051191604663685

theorem tailTrace_2774854 : CollatzResearch.WordTrace tailWord_2774854 prefixEnd_2774854 1424833848051191604663685 := by
  unfold tailWord_2774854
  simp only [CollatzResearch.WordTrace]
  refine ⟨3162726246537041880581863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67471493259456893452413077 3162726246537041880581863)
  ·
    refine ⟨4744089369805562820872795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3162726246537041880581863 4744089369805562820872795)
    ·
      refine ⟨7116134054708344231309193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4744089369805562820872795 7116134054708344231309193)
      ·
        refine ⟨5337100541031258173481895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7116134054708344231309193 5337100541031258173481895)
        ·
          refine ⟨8005650811546887260222843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337100541031258173481895 8005650811546887260222843)
          ·
            refine ⟨12008476217320330890334265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8005650811546887260222843 12008476217320330890334265)
            ·
              refine ⟨9006357162990248167750699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12008476217320330890334265 9006357162990248167750699)
              ·
                refine ⟨13509535744485372251626049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9006357162990248167750699 13509535744485372251626049)
                ·
                  refine ⟨10132151808364029188719537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13509535744485372251626049 10132151808364029188719537)
                  ·
                    refine ⟨7599113856273021891539653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10132151808364029188719537 7599113856273021891539653)
                    ·
                      refine ⟨1424833848051191604663685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7599113856273021891539653 1424833848051191604663685)
                      ·
                        rfl

theorem cell23_2774854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 1, 2, 2, 4].length) (baseStart_2774854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774854 prefixEnd_2774854 := by exact prefixLift 2774854
  have htrace : WordTrace (prefixWord ++ tailWord_2774854) baseStart_2774854 baseEnd_2774854 := by
    simpa [prefixWord, tailWord_2774854, baseEnd_2774854] using wordTrace_append hprefix tailTrace_2774854
  have hstable : (prefixWord ++ tailWord_2774854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774854).length < 2 ^ (prefixWord ++ tailWord_2774854).sum := by decide
  have hdescent : baseEnd_2774854 < baseStart_2774854 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774873 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 2, 8]
def baseStart_2774873 : Nat := 118140960795 + 2774873 * 2 ^ 59
def prefixEnd_2774873 : Nat := 4983230072969 + 3 ^ 40 * 2774873 * 2
def baseEnd_2774873 : Nat := 474947868061209010108699

theorem tailTrace_2774873 : CollatzResearch.WordTrace tailWord_2774873 prefixEnd_2774873 474947868061209010108699 := by
  unfold tailWord_2774873
  simp only [CollatzResearch.WordTrace]
  refine ⟨101207932876116506423561273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67471955250744337615707515 101207932876116506423561273)
  ·
    refine ⟨75905949657087379817670955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101207932876116506423561273 75905949657087379817670955)
    ·
      refine ⟨113858924485631069726506433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75905949657087379817670955 113858924485631069726506433)
      ·
        refine ⟨85394193364223302294879825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113858924485631069726506433 85394193364223302294879825)
        ·
          refine ⟨64045645023167476721159869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85394193364223302294879825 64045645023167476721159869)
          ·
            refine ⟨24017116883687803770434951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64045645023167476721159869 24017116883687803770434951)
            ·
              refine ⟨36025675325531705655652427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24017116883687803770434951 36025675325531705655652427)
              ·
                refine ⟨54038512988297558483478641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36025675325531705655652427 54038512988297558483478641)
                ·
                  refine ⟨40528884741223168862608981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54038512988297558483478641 40528884741223168862608981)
                  ·
                    refine ⟨474947868061209010108699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40528884741223168862608981 474947868061209010108699)
                    ·
                      rfl

theorem cell23_2774873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 2, 8].length) (baseStart_2774873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774873 prefixEnd_2774873 := by exact prefixLift 2774873
  have htrace : WordTrace (prefixWord ++ tailWord_2774873) baseStart_2774873 baseEnd_2774873 := by
    simpa [prefixWord, tailWord_2774873, baseEnd_2774873] using wordTrace_append hprefix tailTrace_2774873
  have hstable : (prefixWord ++ tailWord_2774873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774873).length < 2 ^ (prefixWord ++ tailWord_2774873).sum := by decide
  have hdescent : baseEnd_2774873 < baseStart_2774873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774880 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4]
def baseStart_2774880 : Nat := 118140960795 + 2774880 * 2 ^ 59
def prefixEnd_2774880 : Nat := 4983230072969 + 3 ^ 40 * 2774880 * 2
def baseEnd_2774880 : Nat := 1424847198548208502938565

theorem tailTrace_2774880 : CollatzResearch.WordTrace tailWord_2774880 prefixEnd_2774880 1424847198548208502938565 := by
  unfold tailWord_2774880
  simp only [CollatzResearch.WordTrace]
  refine ⟨50604094093545573309533047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67472125458060764412710729 50604094093545573309533047)
  ·
    refine ⟨75906141140318359964299571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50604094093545573309533047 75906141140318359964299571)
    ·
      refine ⟨113859211710477539946449357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75906141140318359964299571 113859211710477539946449357)
      ·
        refine ⟨42697204391429077479918509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 113859211710477539946449357 42697204391429077479918509)
        ·
          refine ⟨16011451646785904054969441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42697204391429077479918509 16011451646785904054969441)
          ·
            refine ⟨12008588735089428041227081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16011451646785904054969441 12008588735089428041227081)
            ·
              refine ⟨9006441551317071030920311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12008588735089428041227081 9006441551317071030920311)
              ·
                refine ⟨13509662326975606546380467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9006441551317071030920311 13509662326975606546380467)
                ·
                  refine ⟨20264493490463409819570701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13509662326975606546380467 20264493490463409819570701)
                  ·
                    refine ⟨7599185058923778682339013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20264493490463409819570701 7599185058923778682339013)
                    ·
                      refine ⟨1424847198548208502938565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7599185058923778682339013 1424847198548208502938565)
                      ·
                        rfl

theorem cell23_2774880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 1, 3, 4].length) (baseStart_2774880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774880 prefixEnd_2774880 := by exact prefixLift 2774880
  have htrace : WordTrace (prefixWord ++ tailWord_2774880) baseStart_2774880 baseEnd_2774880 := by
    simpa [prefixWord, tailWord_2774880, baseEnd_2774880] using wordTrace_append hprefix tailTrace_2774880
  have hstable : (prefixWord ++ tailWord_2774880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774880).length < 2 ^ (prefixWord ++ tailWord_2774880).sum := by decide
  have hdescent : baseEnd_2774880 < baseStart_2774880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774987 : List Nat := [1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 4]
def baseStart_2774987 : Nat := 118140960795 + 2774987 * 2 ^ 59
def prefixEnd_2774987 : Nat := 4983230072969 + 3 ^ 40 * 2774987 * 2
def baseEnd_2774987 : Nat := 1424902140978239584300573

theorem tailTrace_2774987 : CollatzResearch.WordTrace tailWord_2774987 prefixEnd_2774987 1424902140978239584300573 := by
  unfold tailWord_2774987
  simp only [CollatzResearch.WordTrace]
  refine ⟨101212090797703503893211215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67474727198469002595474143 101212090797703503893211215)
  ·
    refine ⟨151818136196555255839816823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101212090797703503893211215 151818136196555255839816823)
    ·
      refine ⟨227727204294832883759725235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151818136196555255839816823 227727204294832883759725235)
      ·
        refine ⟨341590806442249325639587853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227727204294832883759725235 341590806442249325639587853)
        ·
          refine ⟨128096552415843497114845445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341590806442249325639587853 128096552415843497114845445)
          ·
            refine ⟨24018103577970655709033521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128096552415843497114845445 24018103577970655709033521)
            ·
              refine ⟨18013577683477991781775141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24018103577970655709033521 18013577683477991781775141)
              ·
                refine ⟨3377545815652123459082839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18013577683477991781775141 3377545815652123459082839)
                ·
                  refine ⟨5066318723478185188624259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377545815652123459082839 5066318723478185188624259)
                  ·
                    refine ⟨7599478085217277782936389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5066318723478185188624259 7599478085217277782936389)
                    ·
                      refine ⟨1424902140978239584300573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7599478085217277782936389 1424902140978239584300573)
                      ·
                        rfl

theorem cell23_2774987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 2, 4, 1, 1, 4].length) (baseStart_2774987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774987 prefixEnd_2774987 := by exact prefixLift 2774987
  have htrace : WordTrace (prefixWord ++ tailWord_2774987) baseStart_2774987 baseEnd_2774987 := by
    simpa [prefixWord, tailWord_2774987, baseEnd_2774987] using wordTrace_append hprefix tailTrace_2774987
  have hstable : (prefixWord ++ tailWord_2774987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774987).length < 2 ^ (prefixWord ++ tailWord_2774987).sum := by decide
  have hdescent : baseEnd_2774987 < baseStart_2774987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2774997 : List Nat := [1, 3, 2, 3, 2, 1, 2, 2, 1, 6]
def baseStart_2774997 : Nat := 118140960795 + 2774997 * 2 ^ 59
def prefixEnd_2774997 : Nat := 4983230072969 + 3 ^ 40 * 2774997 * 2
def baseEnd_2774997 : Nat := 474969091928261515058509

theorem tailTrace_2774997 : CollatzResearch.WordTrace tailWord_2774997 prefixEnd_2774997 474969091928261515058509 := by
  unfold tailWord_2774997
  simp only [CollatzResearch.WordTrace]
  refine ⟨101212455527667275601075245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67474970351778183734050163 101212455527667275601075245)
  ·
    refine ⟨37954670822875228350403217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101212455527667275601075245 37954670822875228350403217)
    ·
      refine ⟨28466003117156421262802413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37954670822875228350403217 28466003117156421262802413)
      ·
        refine ⟨10674751168933657973550905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28466003117156421262802413 10674751168933657973550905)
        ·
          refine ⟨8006063376700243480163179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10674751168933657973550905 8006063376700243480163179)
          ·
            refine ⟨12009095065050365220244769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8006063376700243480163179 12009095065050365220244769)
            ·
              refine ⟨9006821298787773915183577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12009095065050365220244769 9006821298787773915183577)
              ·
                refine ⟨6755115974090830436387683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9006821298787773915183577 6755115974090830436387683)
                ·
                  refine ⟨10132673961136245654581525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6755115974090830436387683 10132673961136245654581525)
                  ·
                    refine ⟨474969091928261515058509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10132673961136245654581525 474969091928261515058509)
                    ·
                      rfl

theorem cell23_2774997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_2774997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2774997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2774997 prefixEnd_2774997 := by exact prefixLift 2774997
  have htrace : WordTrace (prefixWord ++ tailWord_2774997) baseStart_2774997 baseEnd_2774997 := by
    simpa [prefixWord, tailWord_2774997, baseEnd_2774997] using wordTrace_append hprefix tailTrace_2774997
  have hstable : (prefixWord ++ tailWord_2774997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2774997).length < 2 ^ (prefixWord ++ tailWord_2774997).sum := by decide
  have hdescent : baseEnd_2774997 < baseStart_2774997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2774997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775001 : List Nat := [1, 2, 1, 2, 6, 2, 2, 1, 1, 5]
def baseStart_2775001 : Nat := 118140960795 + 2775001 * 2 ^ 59
def prefixEnd_2775001 : Nat := 4983230072969 + 3 ^ 40 * 2775001 * 2
def baseEnd_2775001 : Nat := 474969776569134176508503

theorem tailTrace_2775001 : CollatzResearch.WordTrace tailWord_2775001 prefixEnd_2775001 474969776569134176508503 := by
  unfold tailWord_2775001
  simp only [CollatzResearch.WordTrace]
  refine ⟨101212601419652784284220857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67475067613101856189480571 101212601419652784284220857)
  ·
    refine ⟨75909451064739588213165643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101212601419652784284220857 75909451064739588213165643)
    ·
      refine ⟨113864176597109382319748465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75909451064739588213165643 113864176597109382319748465)
      ·
        refine ⟨85398132447832036739811349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113864176597109382319748465 85398132447832036739811349)
        ·
          refine ⟨4003037458492126722178657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 85398132447832036739811349 4003037458492126722178657)
          ·
            refine ⟨3002278093869095041633993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4003037458492126722178657 3002278093869095041633993)
            ·
              refine ⟨2251708570401821281225495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002278093869095041633993 2251708570401821281225495)
              ·
                refine ⟨3377562855602731921838243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251708570401821281225495 3377562855602731921838243)
                ·
                  refine ⟨5066344283404097882757365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3377562855602731921838243 5066344283404097882757365)
                  ·
                    refine ⟨474969776569134176508503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5066344283404097882757365 474969776569134176508503)
                    ·
                      rfl

theorem cell23_2775001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 1, 5].length) (baseStart_2775001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775001 prefixEnd_2775001 := by exact prefixLift 2775001
  have htrace : WordTrace (prefixWord ++ tailWord_2775001) baseStart_2775001 baseEnd_2775001 := by
    simpa [prefixWord, tailWord_2775001, baseEnd_2775001] using wordTrace_append hprefix tailTrace_2775001
  have hstable : (prefixWord ++ tailWord_2775001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775001).length < 2 ^ (prefixWord ++ tailWord_2775001).sum := by decide
  have hdescent : baseEnd_2775001 < baseStart_2775001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775038 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_2775038 : Nat := 118140960795 + 2775038 * 2 ^ 59
def prefixEnd_2775038 : Nat := 4983230072969 + 3 ^ 40 * 2775038 * 2
def baseEnd_2775038 : Nat := 1424928328491618884762839

theorem tailTrace_2775038 : CollatzResearch.WordTrace tailWord_2775038 prefixEnd_2775038 1424928328491618884762839 := by
  unfold tailWord_2775038
  simp only [CollatzResearch.WordTrace]
  refine ⟨12651743865064842450414721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67475967280345826402211845 12651743865064842450414721)
  ·
    refine ⟨9488807898798631837811041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12651743865064842450414721 9488807898798631837811041)
    ·
      refine ⟨7116605924098973878358281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9488807898798631837811041 7116605924098973878358281)
      ·
        refine ⟨5337454443074230408768711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7116605924098973878358281 5337454443074230408768711)
        ·
          refine ⟨8006181664611345613153067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337454443074230408768711 8006181664611345613153067)
          ·
            refine ⟨12009272496917018419729601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8006181664611345613153067 12009272496917018419729601)
            ·
              refine ⟨9006954372687763814797201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12009272496917018419729601 9006954372687763814797201)
              ·
                refine ⟨6755215779515822861097901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9006954372687763814797201 6755215779515822861097901)
                ·
                  refine ⟨2533205917318433572911713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6755215779515822861097901 2533205917318433572911713)
                  ·
                    refine ⟨1899904437988825179683785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2533205917318433572911713 1899904437988825179683785)
                    ·
                      refine ⟨1424928328491618884762839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899904437988825179683785 1424928328491618884762839)
                      ·
                        rfl

theorem cell23_2775038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_2775038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775038 prefixEnd_2775038 := by exact prefixLift 2775038
  have htrace : WordTrace (prefixWord ++ tailWord_2775038) baseStart_2775038 baseEnd_2775038 := by
    simpa [prefixWord, tailWord_2775038, baseEnd_2775038] using wordTrace_append hprefix tailTrace_2775038
  have hstable : (prefixWord ++ tailWord_2775038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775038).length < 2 ^ (prefixWord ++ tailWord_2775038).sum := by decide
  have hdescent : baseEnd_2775038 < baseStart_2775038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775044 : List Nat := [2, 3, 2, 4, 1, 1, 1, 9]
def baseStart_2775044 : Nat := 118140960795 + 2775044 * 2 ^ 59
def prefixEnd_2775044 : Nat := 4983230072969 + 3 ^ 40 * 2775044 * 2
def baseEnd_2775044 : Nat := 52775237384279476343993

theorem tailTrace_2775044 : CollatzResearch.WordTrace tailWord_2775044 prefixEnd_2775044 52775237384279476343993 := by
  unfold tailWord_2775044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50607084879248501314018093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67476113172331335085357457 50607084879248501314018093)
  ·
    refine ⟨18977656829718187992756785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50607084879248501314018093 18977656829718187992756785)
    ·
      refine ⟨14233242622288640994567589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18977656829718187992756785 14233242622288640994567589)
      ·
        refine ⟨2668732991679120186481423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14233242622288640994567589 2668732991679120186481423)
        ·
          refine ⟨4003099487518680279722135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2668732991679120186481423 4003099487518680279722135)
          ·
            refine ⟨6004649231278020419583203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4003099487518680279722135 6004649231278020419583203)
            ·
              refine ⟨9006973846917030629374805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6004649231278020419583203 9006973846917030629374805)
              ·
                refine ⟨52775237384279476343993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 9006973846917030629374805 52775237384279476343993)
                ·
                  rfl

theorem cell23_2775044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 9].length) (baseStart_2775044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775044 prefixEnd_2775044 := by exact prefixLift 2775044
  have htrace : WordTrace (prefixWord ++ tailWord_2775044) baseStart_2775044 baseEnd_2775044 := by
    simpa [prefixWord, tailWord_2775044, baseEnd_2775044] using wordTrace_append hprefix tailTrace_2775044
  have hstable : (prefixWord ++ tailWord_2775044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775044).length < 2 ^ (prefixWord ++ tailWord_2775044).sum := by decide
  have hdescent : baseEnd_2775044 < baseStart_2775044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775054 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3]
def baseStart_2775054 : Nat := 118140960795 + 2775054 * 2 ^ 59
def prefixEnd_2775054 : Nat := 4983230072969 + 3 ^ 40 * 2775054 * 2
def baseEnd_2775054 : Nat := 1424936544182090822162765

theorem tailTrace_2775054 : CollatzResearch.WordTrace tailWord_2775054 prefixEnd_2775054 1424936544182090822162765 := by
  unfold tailWord_2775054
  simp only [CollatzResearch.WordTrace]
  refine ⟨12651816811057596791987527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67476356325640516223933477 12651816811057596791987527)
  ·
    refine ⟨18977725216586395187981291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12651816811057596791987527 18977725216586395187981291)
    ·
      refine ⟨28466587824879592781971937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18977725216586395187981291 28466587824879592781971937)
      ·
        refine ⟨21349940868659694586478953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28466587824879592781971937 21349940868659694586478953)
        ·
          refine ⟨16012455651494770939859215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21349940868659694586478953 16012455651494770939859215)
          ·
            refine ⟨24018683477242156409788823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16012455651494770939859215 24018683477242156409788823)
            ·
              refine ⟨36028025215863234614683235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24018683477242156409788823 36028025215863234614683235)
              ·
                refine ⟨54042037823794851922024853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36028025215863234614683235 54042037823794851922024853)
                ·
                  refine ⟨2533220522990383683844915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54042037823794851922024853 2533220522990383683844915)
                  ·
                    refine ⟨3799830784485575525767373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2533220522990383683844915 3799830784485575525767373)
                    ·
                      refine ⟨1424936544182090822162765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3799830784485575525767373 1424936544182090822162765)
                      ·
                        rfl

theorem cell23_2775054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3].length) (baseStart_2775054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775054 prefixEnd_2775054 := by exact prefixLift 2775054
  have htrace : WordTrace (prefixWord ++ tailWord_2775054) baseStart_2775054 baseEnd_2775054 := by
    simpa [prefixWord, tailWord_2775054, baseEnd_2775054] using wordTrace_append hprefix tailTrace_2775054
  have hstable : (prefixWord ++ tailWord_2775054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775054).length < 2 ^ (prefixWord ++ tailWord_2775054).sum := by decide
  have hdescent : baseEnd_2775054 < baseStart_2775054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775088 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 2, 1, 3]
def baseStart_2775088 : Nat := 118140960795 + 2775088 * 2 ^ 59
def prefixEnd_2775088 : Nat := 4983230072969 + 3 ^ 40 * 2775088 * 2
def baseEnd_2775088 : Nat := 1424954002524343689137609

theorem tailTrace_2775088 : CollatzResearch.WordTrace tailWord_2775088 prefixEnd_2775088 1424954002524343689137609 := by
  unfold tailWord_2775088
  simp only [CollatzResearch.WordTrace]
  refine ⟨50607887285168799071318959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67477183046891732095091945 50607887285168799071318959)
  ·
    refine ⟨75911830927753198606978439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50607887285168799071318959 75911830927753198606978439)
    ·
      refine ⟨113867746391629797910467659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75911830927753198606978439 113867746391629797910467659)
      ·
        refine ⟨170801619587444696865701489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113867746391629797910467659 170801619587444696865701489)
        ·
          refine ⟨128101214690583522649276117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170801619587444696865701489 128101214690583522649276117)
          ·
            refine ⟨3002372219310551312092409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 128101214690583522649276117 3002372219310551312092409)
            ·
              refine ⟨2251779164482913484069307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002372219310551312092409 2251779164482913484069307)
              ·
                refine ⟨3377668746724370226103961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2251779164482913484069307 3377668746724370226103961)
                ·
                  refine ⟨2533251560043277669577971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3377668746724370226103961 2533251560043277669577971)
                  ·
                    refine ⟨3799877340064916504366957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2533251560043277669577971 3799877340064916504366957)
                    ·
                      refine ⟨1424954002524343689137609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3799877340064916504366957 1424954002524343689137609)
                      ·
                        rfl

theorem cell23_2775088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 2, 1, 3].length) (baseStart_2775088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775088 prefixEnd_2775088 := by exact prefixLift 2775088
  have htrace : WordTrace (prefixWord ++ tailWord_2775088) baseStart_2775088 baseEnd_2775088 := by
    simpa [prefixWord, tailWord_2775088, baseEnd_2775088] using wordTrace_append hprefix tailTrace_2775088
  have hstable : (prefixWord ++ tailWord_2775088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775088).length < 2 ^ (prefixWord ++ tailWord_2775088).sum := by decide
  have hdescent : baseEnd_2775088 < baseStart_2775088 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775128 : List Nat := [2, 1, 2, 2, 1, 5, 2, 2, 2, 2, 2]
def baseStart_2775128 : Nat := 118140960795 + 2775128 * 2 ^ 59
def prefixEnd_2775128 : Nat := 4983230072969 + 3 ^ 40 * 2775128 * 2
def baseEnd_2775128 : Nat := 1424974541750523532637425

theorem tailTrace_2775128 : CollatzResearch.WordTrace tailWord_2775128 prefixEnd_2775128 1424974541750523532637425 := by
  unfold tailWord_2775128
  simp only [CollatzResearch.WordTrace]
  refine ⟨50608616745096342487047019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67478155660128456649396025 50608616745096342487047019)
  ·
    refine ⟨75912925117644513730570529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50608616745096342487047019 75912925117644513730570529)
    ·
      refine ⟨56934693838233385297927897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75912925117644513730570529 56934693838233385297927897)
      ·
        refine ⟨42701020378675038973445923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56934693838233385297927897 42701020378675038973445923)
        ·
          refine ⟨64051530568012558460168885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42701020378675038973445923 64051530568012558460168885)
          ·
            refine ⟨6004830990751177355640833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 64051530568012558460168885 6004830990751177355640833)
            ·
              refine ⟨4503623243063383016730625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6004830990751177355640833 4503623243063383016730625)
              ·
                refine ⟨3377717432297537262547969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4503623243063383016730625 3377717432297537262547969)
                ·
                  refine ⟨2533288074223152946910977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3377717432297537262547969 2533288074223152946910977)
                  ·
                    refine ⟨1899966055667364710183233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2533288074223152946910977 1899966055667364710183233)
                    ·
                      refine ⟨1424974541750523532637425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1899966055667364710183233 1424974541750523532637425)
                      ·
                        rfl

theorem cell23_2775128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_2775128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775128 prefixEnd_2775128 := by exact prefixLift 2775128
  have htrace : WordTrace (prefixWord ++ tailWord_2775128) baseStart_2775128 baseEnd_2775128 := by
    simpa [prefixWord, tailWord_2775128, baseEnd_2775128] using wordTrace_append hprefix tailTrace_2775128
  have hstable : (prefixWord ++ tailWord_2775128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775128).length < 2 ^ (prefixWord ++ tailWord_2775128).sum := by decide
  have hdescent : baseEnd_2775128 < baseStart_2775128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775164 : List Nat := [2, 2, 2, 1, 1, 4, 3, 1, 2, 5]
def baseStart_2775164 : Nat := 118140960795 + 2775164 * 2 ^ 59
def prefixEnd_2775164 : Nat := 4983230072969 + 3 ^ 40 * 2775164 * 2
def baseEnd_2775164 : Nat := 474997675684695130595753

theorem tailTrace_2775164 : CollatzResearch.WordTrace tailWord_2775164 prefixEnd_2775164 474997675684695130595753 := by
  unfold tailWord_2775164
  simp only [CollatzResearch.WordTrace]
  refine ⟨50609273259031131561202273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67479031012041508748269697 50609273259031131561202273)
  ·
    refine ⟨37956954944273348670901705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50609273259031131561202273 37956954944273348670901705)
    ·
      refine ⟨28467716208205011503176279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37956954944273348670901705 28467716208205011503176279)
      ·
        refine ⟨42701574312307517254764419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28467716208205011503176279 42701574312307517254764419)
        ·
          refine ⟨64052361468461275882146629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42701574312307517254764419 64052361468461275882146629)
          ·
            refine ⟨12009817775336489227902493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64052361468461275882146629 12009817775336489227902493)
            ·
              refine ⟨4503681665751183460463435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12009817775336489227902493 4503681665751183460463435)
              ·
                refine ⟨6755522498626775190695153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4503681665751183460463435 6755522498626775190695153)
                ·
                  refine ⟨5066641873970081393021365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6755522498626775190695153 5066641873970081393021365)
                  ·
                    refine ⟨474997675684695130595753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5066641873970081393021365 474997675684695130595753)
                    ·
                      rfl

theorem cell23_2775164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 1, 2, 5].length) (baseStart_2775164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775164 prefixEnd_2775164 := by exact prefixLift 2775164
  have htrace : WordTrace (prefixWord ++ tailWord_2775164) baseStart_2775164 baseEnd_2775164 := by
    simpa [prefixWord, tailWord_2775164, baseEnd_2775164] using wordTrace_append hprefix tailTrace_2775164
  have hstable : (prefixWord ++ tailWord_2775164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775164).length < 2 ^ (prefixWord ++ tailWord_2775164).sum := by decide
  have hdescent : baseEnd_2775164 < baseStart_2775164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775184 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 4, 4, 2]
def baseStart_2775184 : Nat := 118140960795 + 2775184 * 2 ^ 59
def prefixEnd_2775184 : Nat := 4983230072969 + 3 ^ 40 * 2775184 * 2
def baseEnd_2775184 : Nat := 1425003296667175313537167

theorem tailTrace_2775184 : CollatzResearch.WordTrace tailWord_2775184 prefixEnd_2775184 1425003296667175313537167 := by
  unfold tailWord_2775184
  simp only [CollatzResearch.WordTrace]
  refine ⟨50609637988994903269066303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67479517318659871025421737 50609637988994903269066303)
  ·
    refine ⟨75914456983492354903599455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50609637988994903269066303 75914456983492354903599455)
    ·
      refine ⟨113871685475238532355399183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75914456983492354903599455 113871685475238532355399183)
      ·
        refine ⟨170807528212857798533098775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113871685475238532355399183 170807528212857798533098775)
        ·
          refine ⟨256211292319286697799648163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170807528212857798533098775 256211292319286697799648163)
          ·
            refine ⟨384316938478930046699472245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 256211292319286697799648163 384316938478930046699472245)
            ·
              refine ⟨36029712982399691878075523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 384316938478930046699472245 36029712982399691878075523)
              ·
                refine ⟨54044569473599537817113285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36029712982399691878075523 54044569473599537817113285)
                ·
                  refine ⟨10133356776299913340708741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54044569473599537817113285 10133356776299913340708741)
                  ·
                    refine ⟨1900004395556233751382889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10133356776299913340708741 1900004395556233751382889)
                    ·
                      refine ⟨1425003296667175313537167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900004395556233751382889 1425003296667175313537167)
                      ·
                        rfl

theorem cell23_2775184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 4, 4, 2].length) (baseStart_2775184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775184 prefixEnd_2775184 := by exact prefixLift 2775184
  have htrace : WordTrace (prefixWord ++ tailWord_2775184) baseStart_2775184 baseEnd_2775184 := by
    simpa [prefixWord, tailWord_2775184, baseEnd_2775184] using wordTrace_append hprefix tailTrace_2775184
  have hstable : (prefixWord ++ tailWord_2775184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775184).length < 2 ^ (prefixWord ++ tailWord_2775184).sum := by decide
  have hdescent : baseEnd_2775184 < baseStart_2775184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775201 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 2, 4, 2]
def baseStart_2775201 : Nat := 118140960795 + 2775201 * 2 ^ 59
def prefixEnd_2775201 : Nat := 4983230072969 + 3 ^ 40 * 2775201 * 2
def baseEnd_2775201 : Nat := 1425012025838301747024589

theorem tailTrace_2775201 : CollatzResearch.WordTrace tailWord_2775201 prefixEnd_2775201 1425012025838301747024589 := by
  unfold tailWord_2775201
  simp only [CollatzResearch.WordTrace]
  refine ⟨101219896018928218441501457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67479930679285478961000971 101219896018928218441501457)
  ·
    refine ⟨75914922014196163831126093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101219896018928218441501457 75914922014196163831126093)
    ·
      refine ⟨28468095755323561436672285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75914922014196163831126093 28468095755323561436672285)
      ·
        refine ⟨10675535908246335538752107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28468095755323561436672285 10675535908246335538752107)
        ·
          refine ⟨16013303862369503308128161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10675535908246335538752107 16013303862369503308128161)
          ·
            refine ⟨12009977896777127481096121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16013303862369503308128161 12009977896777127481096121)
            ·
              refine ⟨9007483422582845610822091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12009977896777127481096121 9007483422582845610822091)
              ·
                refine ⟨13511225133874268416233137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9007483422582845610822091 13511225133874268416233137)
                ·
                  refine ⟨10133418850405701312174853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13511225133874268416233137 10133418850405701312174853)
                  ·
                    refine ⟨1900016034451068996032785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10133418850405701312174853 1900016034451068996032785)
                    ·
                      refine ⟨1425012025838301747024589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900016034451068996032785 1425012025838301747024589)
                      ·
                        rfl

theorem cell23_2775201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 2, 4, 2].length) (baseStart_2775201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775201 prefixEnd_2775201 := by exact prefixLift 2775201
  have htrace : WordTrace (prefixWord ++ tailWord_2775201) baseStart_2775201 baseEnd_2775201 := by
    simpa [prefixWord, tailWord_2775201, baseEnd_2775201] using wordTrace_append hprefix tailTrace_2775201
  have hstable : (prefixWord ++ tailWord_2775201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775201).length < 2 ^ (prefixWord ++ tailWord_2775201).sum := by decide
  have hdescent : baseEnd_2775201 < baseStart_2775201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775271 : List Nat := [1, 1, 5, 3, 1, 2, 1, 1, 3, 5]
def baseStart_2775271 : Nat := 118140960795 + 2775271 * 2 ^ 59
def prefixEnd_2775271 : Nat := 4983230072969 + 3 ^ 40 * 2775271 * 2
def baseEnd_2775271 : Nat := 475015989828038824383089

theorem tailTrace_2775271 : CollatzResearch.WordTrace tailWord_2775271 prefixEnd_2775271 475015989828038824383089 := by
  unfold tailWord_2775271
  simp only [CollatzResearch.WordTrace]
  refine ⟨101222449128674620396549667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67481632752449746931033111 101222449128674620396549667)
  ·
    refine ⟨151833673693011930594824501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101222449128674620396549667 151833673693011930594824501)
    ·
      refine ⟨14234406908719868493264797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151833673693011930594824501 14234406908719868493264797)
      ·
        refine ⟨5337902590769950684974299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14234406908719868493264797 5337902590769950684974299)
        ·
          refine ⟨8006853886154926027461449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5337902590769950684974299 8006853886154926027461449)
          ·
            refine ⟨6005140414616194520596087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8006853886154926027461449 6005140414616194520596087)
            ·
              refine ⟨9007710621924291780894131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005140414616194520596087 9007710621924291780894131)
              ·
                refine ⟨13511565932886437671341197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9007710621924291780894131 13511565932886437671341197)
                ·
                  refine ⟨5066837224832414126752949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13511565932886437671341197 5066837224832414126752949)
                  ·
                    refine ⟨475015989828038824383089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5066837224832414126752949 475015989828038824383089)
                    ·
                      rfl

theorem cell23_2775271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 3, 5].length) (baseStart_2775271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775271 prefixEnd_2775271 := by exact prefixLift 2775271
  have htrace : WordTrace (prefixWord ++ tailWord_2775271) baseStart_2775271 baseEnd_2775271 := by
    simpa [prefixWord, tailWord_2775271, baseEnd_2775271] using wordTrace_append hprefix tailTrace_2775271
  have hstable : (prefixWord ++ tailWord_2775271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775271).length < 2 ^ (prefixWord ++ tailWord_2775271).sum := by decide
  have hdescent : baseEnd_2775271 < baseStart_2775271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775308 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 3, 2, 2]
def baseStart_2775308 : Nat := 118140960795 + 2775308 * 2 ^ 59
def prefixEnd_2775308 : Nat := 4983230072969 + 3 ^ 40 * 2775308 * 2
def baseEnd_2775308 : Nat := 1425066968268332828386597

theorem tailTrace_2775308 : CollatzResearch.WordTrace tailWord_2775308 prefixEnd_2775308 1425066968268332828386597 := by
  unfold tailWord_2775308
  simp only [CollatzResearch.WordTrace]
  refine ⟨50611899314770287857823289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67482532419693717143764385 50611899314770287857823289)
  ·
    refine ⟨37958924486077715893367467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50611899314770287857823289 37958924486077715893367467)
    ·
      refine ⟨56938386729116573840051201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37958924486077715893367467 56938386729116573840051201)
      ·
        refine ⟨42703790046837430380038401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56938386729116573840051201 42703790046837430380038401)
        ·
          refine ⟨32027842535128072785028801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42703790046837430380038401 32027842535128072785028801)
          ·
            refine ⟨24020881901346054588771601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32027842535128072785028801 24020881901346054588771601)
            ·
              refine ⟨18015661426009540941578701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24020881901346054588771601 18015661426009540941578701)
              ·
                refine ⟨6755873034753577853092013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18015661426009540941578701 6755873034753577853092013)
                ·
                  refine ⟨2533452388032591694909505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6755873034753577853092013 2533452388032591694909505)
                  ·
                    refine ⟨1900089291024443771182129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2533452388032591694909505 1900089291024443771182129)
                    ·
                      refine ⟨1425066968268332828386597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900089291024443771182129 1425066968268332828386597)
                      ·
                        rfl

theorem cell23_2775308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_2775308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775308 prefixEnd_2775308 := by exact prefixLift 2775308
  have htrace : WordTrace (prefixWord ++ tailWord_2775308) baseStart_2775308 baseEnd_2775308 := by
    simpa [prefixWord, tailWord_2775308, baseEnd_2775308] using wordTrace_append hprefix tailTrace_2775308
  have hstable : (prefixWord ++ tailWord_2775308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775308).length < 2 ^ (prefixWord ++ tailWord_2775308).sum := by decide
  have hdescent : baseEnd_2775308 < baseStart_2775308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775374 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 1, 8]
def baseStart_2775374 : Nat := 118140960795 + 2775374 * 2 ^ 59
def prefixEnd_2775374 : Nat := 4983230072969 + 3 ^ 40 * 2775374 * 2
def baseEnd_2775374 : Nat := 475033619330509856720431

theorem tailTrace_2775374 : CollatzResearch.WordTrace tailWord_2775374 prefixEnd_2775374 475033619330509856720431 := by
  unfold tailWord_2775374
  simp only [CollatzResearch.WordTrace]
  refine ⟨12653275730912683623443647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67484137231534312658366117 12653275730912683623443647)
  ·
    refine ⟨18979913596369025435165471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12653275730912683623443647 18979913596369025435165471)
    ·
      refine ⟨28469870394553538152748207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18979913596369025435165471 28469870394553538152748207)
      ·
        refine ⟨42704805591830307229122311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28469870394553538152748207 42704805591830307229122311)
        ·
          refine ⟨64057208387745460843683467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42704805591830307229122311 64057208387745460843683467)
          ·
            refine ⟨96085812581618191265525201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64057208387745460843683467 96085812581618191265525201)
            ·
              refine ⟨72064359436213643449143901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96085812581618191265525201 72064359436213643449143901)
              ·
                refine ⟨27024134788580116293428963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72064359436213643449143901 27024134788580116293428963)
                ·
                  refine ⟨40536202182870174440143445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27024134788580116293428963 40536202182870174440143445)
                  ·
                    refine ⟨475033619330509856720431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 40536202182870174440143445 475033619330509856720431)
                    ·
                      rfl

theorem cell23_2775374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 1, 8].length) (baseStart_2775374 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775374 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775374 prefixEnd_2775374 := by exact prefixLift 2775374
  have htrace : WordTrace (prefixWord ++ tailWord_2775374) baseStart_2775374 baseEnd_2775374 := by
    simpa [prefixWord, tailWord_2775374, baseEnd_2775374] using wordTrace_append hprefix tailTrace_2775374
  have hstable : (prefixWord ++ tailWord_2775374).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775374).length < 2 ^ (prefixWord ++ tailWord_2775374).sum := by decide
  have hdescent : baseEnd_2775374 < baseStart_2775374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775421 : List Nat := [1, 4, 1, 1, 2, 3, 3, 1, 7]
def baseStart_2775421 : Nat := 118140960795 + 2775421 * 2 ^ 59
def prefixEnd_2775421 : Nat := 4983230072969 + 3 ^ 40 * 2775421 * 2
def baseEnd_2775421 : Nat := 158347221286921209585953

theorem tailTrace_2775421 : CollatzResearch.WordTrace tailWord_2775421 prefixEnd_2775421 158347221286921209585953 := by
  unfold tailWord_2775421
  simp only [CollatzResearch.WordTrace]
  refine ⟨101227920078131196014510117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67485280052087464009673411 101227920078131196014510117)
  ·
    refine ⟨18980235014649599252720647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101227920078131196014510117 18980235014649599252720647)
    ·
      refine ⟨28470352521974398879080971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18980235014649599252720647 28470352521974398879080971)
      ·
        refine ⟨42705528782961598318621457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28470352521974398879080971 42705528782961598318621457)
        ·
          refine ⟨32029146587221198738966093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42705528782961598318621457 32029146587221198738966093)
          ·
            refine ⟨12010929970207949527112285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32029146587221198738966093 12010929970207949527112285)
            ·
              refine ⟨4504098738827981072667107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12010929970207949527112285 4504098738827981072667107)
              ·
                refine ⟨6756148108241971609000661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504098738827981072667107 6756148108241971609000661)
                ·
                  refine ⟨158347221286921209585953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6756148108241971609000661 158347221286921209585953)
                  ·
                    rfl

theorem cell23_2775421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 1, 7].length) (baseStart_2775421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775421 prefixEnd_2775421 := by exact prefixLift 2775421
  have htrace : WordTrace (prefixWord ++ tailWord_2775421) baseStart_2775421 baseEnd_2775421 := by
    simpa [prefixWord, tailWord_2775421, baseEnd_2775421] using wordTrace_append hprefix tailTrace_2775421
  have hstable : (prefixWord ++ tailWord_2775421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775421).length < 2 ^ (prefixWord ++ tailWord_2775421).sum := by decide
  have hdescent : baseEnd_2775421 < baseStart_2775421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775426 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 2, 1, 3]
def baseStart_2775426 : Nat := 118140960795 + 2775426 * 2 ^ 59
def prefixEnd_2775426 : Nat := 4983230072969 + 3 ^ 40 * 2775426 * 2
def baseEnd_2775426 : Nat := 1425127558985563366711055

theorem tailTrace_2775426 : CollatzResearch.WordTrace tailWord_2775426 prefixEnd_2775426 1425127558985563366711055 := by
  unfold tailWord_2775426
  simp only [CollatzResearch.WordTrace]
  refine ⟨25307025610778270467110533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67485401628742054578961421 25307025610778270467110533)
  ·
    refine ⟨4745067302020925712583225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 25307025610778270467110533 4745067302020925712583225)
    ·
      refine ⟨3558800476515694284437419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4745067302020925712583225 3558800476515694284437419)
      ·
        refine ⟨5338200714773541426656129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3558800476515694284437419 5338200714773541426656129)
        ·
          refine ⟨4003650536080156069992097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5338200714773541426656129 4003650536080156069992097)
          ·
            refine ⟨3002737902060117052494073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4003650536080156069992097 3002737902060117052494073)
            ·
              refine ⟨2252053426545087789370555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3002737902060117052494073 2252053426545087789370555)
              ·
                refine ⟨3378080139817631684055833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252053426545087789370555 3378080139817631684055833)
                ·
                  refine ⟨2533560104863223763041875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3378080139817631684055833 2533560104863223763041875)
                  ·
                    refine ⟨3800340157294835644562813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2533560104863223763041875 3800340157294835644562813)
                    ·
                      refine ⟨1425127558985563366711055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3800340157294835644562813 1425127558985563366711055)
                      ·
                        rfl

theorem cell23_2775426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 2, 1, 3].length) (baseStart_2775426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775426 prefixEnd_2775426 := by exact prefixLift 2775426
  have htrace : WordTrace (prefixWord ++ tailWord_2775426) baseStart_2775426 baseEnd_2775426 := by
    simpa [prefixWord, tailWord_2775426, baseEnd_2775426] using wordTrace_append hprefix tailTrace_2775426
  have hstable : (prefixWord ++ tailWord_2775426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775426).length < 2 ^ (prefixWord ++ tailWord_2775426).sum := by decide
  have hdescent : baseEnd_2775426 < baseStart_2775426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775431 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 3]
def baseStart_2775431 : Nat := 118140960795 + 2775431 * 2 ^ 59
def prefixEnd_2775431 : Nat := 4983230072969 + 3 ^ 40 * 2775431 * 2
def baseEnd_2775431 : Nat := 1425130126388835847148531

theorem tailTrace_2775431 : CollatzResearch.WordTrace tailWord_2775431 prefixEnd_2775431 1425130126388835847148531 := by
  unfold tailWord_2775431
  simp only [CollatzResearch.WordTrace]
  refine ⟨101228284808094967722374147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67485523205396645148249431 101228284808094967722374147)
  ·
    refine ⟨151842427212142451583561221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101228284808094967722374147 151842427212142451583561221)
    ·
      refine ⟨28470455102276709671917729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151842427212142451583561221 28470455102276709671917729)
      ·
        refine ⟨21352841326707532253938297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28470455102276709671917729 21352841326707532253938297)
        ·
          refine ⟨16014630995030649190453723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21352841326707532253938297 16014630995030649190453723)
          ·
            refine ⟨24021946492545973785680585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16014630995030649190453723 24021946492545973785680585)
            ·
              refine ⟨18016459869409480339260439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24021946492545973785680585 18016459869409480339260439)
              ·
                refine ⟨27024689804114220508890659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18016459869409480339260439 27024689804114220508890659)
                ·
                  refine ⟨40537034706171330763335989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27024689804114220508890659 40537034706171330763335989)
                  ·
                    refine ⟨3800347003703562259062749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40537034706171330763335989 3800347003703562259062749)
                    ·
                      refine ⟨1425130126388835847148531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3800347003703562259062749 1425130126388835847148531)
                      ·
                        rfl

theorem cell23_2775431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_2775431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775431 prefixEnd_2775431 := by exact prefixLift 2775431
  have htrace : WordTrace (prefixWord ++ tailWord_2775431) baseStart_2775431 baseEnd_2775431 := by
    simpa [prefixWord, tailWord_2775431, baseEnd_2775431] using wordTrace_append hprefix tailTrace_2775431
  have hstable : (prefixWord ++ tailWord_2775431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775431).length < 2 ^ (prefixWord ++ tailWord_2775431).sum := by decide
  have hdescent : baseEnd_2775431 < baseStart_2775431 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775491 : List Nat := [1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 3]
def baseStart_2775491 : Nat := 118140960795 + 2775491 * 2 ^ 59
def prefixEnd_2775491 : Nat := 4983230072969 + 3 ^ 40 * 2775491 * 2
def baseEnd_2775491 : Nat := 1425160935228105612398255

theorem tailTrace_2775491 : CollatzResearch.WordTrace tailWord_2775491 prefixEnd_2775491 1425160935228105612398255 := by
  unfold tailWord_2775491
  simp only [CollatzResearch.WordTrace]
  refine ⟨101230473187877597969558327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67486982125251731979705551 101230473187877597969558327)
  ·
    refine ⟨151845709781816396954337491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101230473187877597969558327 151845709781816396954337491)
    ·
      refine ⟨227768564672724595431506237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151845709781816396954337491 227768564672724595431506237)
      ·
        refine ⟨85413211752271723286814839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 227768564672724595431506237 85413211752271723286814839)
        ·
          refine ⟨128119817628407584930222259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85413211752271723286814839 128119817628407584930222259)
          ·
            refine ⟨192179726442611377395333389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128119817628407584930222259 192179726442611377395333389)
            ·
              refine ⟨72067397415979266523250021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192179726442611377395333389 72067397415979266523250021)
              ·
                refine ⟨13512637015496112473109379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72067397415979266523250021 13512637015496112473109379)
                ·
                  refine ⟨20268955523244168709664069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13512637015496112473109379 20268955523244168709664069)
                  ·
                    refine ⟨3800429160608281633062013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20268955523244168709664069 3800429160608281633062013)
                    ·
                      refine ⟨1425160935228105612398255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3800429160608281633062013 1425160935228105612398255)
                      ·
                        rfl

theorem cell23_2775491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 4, 1, 4, 3].length) (baseStart_2775491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775491 prefixEnd_2775491 := by exact prefixLift 2775491
  have htrace : WordTrace (prefixWord ++ tailWord_2775491) baseStart_2775491 baseEnd_2775491 := by
    simpa [prefixWord, tailWord_2775491, baseEnd_2775491] using wordTrace_append hprefix tailTrace_2775491
  have hstable : (prefixWord ++ tailWord_2775491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775491).length < 2 ^ (prefixWord ++ tailWord_2775491).sum := by decide
  have hdescent : baseEnd_2775491 < baseStart_2775491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775498 : List Nat := [3, 1, 2, 1, 2, 2, 3, 2, 3, 4]
def baseStart_2775498 : Nat := 118140960795 + 2775498 * 2 ^ 59
def prefixEnd_2775498 : Nat := 4983230072969 + 3 ^ 40 * 2775498 * 2
def baseEnd_2775498 : Nat := 475054843197562361670241

theorem tailTrace_2775498 : CollatzResearch.WordTrace tailWord_2775498 prefixEnd_2775498 475054843197562361670241 := by
  unfold tailWord_2775498
  simp only [CollatzResearch.WordTrace]
  refine ⟨25307682124713059541265787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67487152332568158776708765 25307682124713059541265787)
  ·
    refine ⟨37961523187069589311898681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25307682124713059541265787 37961523187069589311898681)
    ·
      refine ⟨28471142390302191983924011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37961523187069589311898681 28471142390302191983924011)
      ·
        refine ⟨42706713585453287975886017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28471142390302191983924011 42706713585453287975886017)
        ·
          refine ⟨32030035189089965981914513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42706713585453287975886017 32030035189089965981914513)
          ·
            refine ⟨24022526391817474486435885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32030035189089965981914513 24022526391817474486435885)
            ·
              refine ⟨9008447396931552932413457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24022526391817474486435885 9008447396931552932413457)
              ·
                refine ⟨6756335547698664699310093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9008447396931552932413457 6756335547698664699310093)
                ·
                  refine ⟨2533625830386999262241285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6756335547698664699310093 2533625830386999262241285)
                  ·
                    refine ⟨475054843197562361670241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2533625830386999262241285 475054843197562361670241)
                    ·
                      rfl

theorem cell23_2775498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 3, 4].length) (baseStart_2775498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775498 prefixEnd_2775498 := by exact prefixLift 2775498
  have htrace : WordTrace (prefixWord ++ tailWord_2775498) baseStart_2775498 baseEnd_2775498 := by
    simpa [prefixWord, tailWord_2775498, baseEnd_2775498] using wordTrace_append hprefix tailTrace_2775498
  have hstable : (prefixWord ++ tailWord_2775498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775498).length < 2 ^ (prefixWord ++ tailWord_2775498).sum := by decide
  have hdescent : baseEnd_2775498 < baseStart_2775498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775528 : List Nat := [2, 1, 4, 1, 1, 3, 3, 2, 6]
def baseStart_2775528 : Nat := 118140960795 + 2775528 * 2 ^ 59
def prefixEnd_2775528 : Nat := 4983230072969 + 3 ^ 40 * 2775528 * 2
def baseEnd_2775528 : Nat := 158353326001369107515065

theorem tailTrace_2775528 : CollatzResearch.WordTrace tailWord_2775528 prefixEnd_2775528 158353326001369107515065 := by
  unfold tailWord_2775528
  simp only [CollatzResearch.WordTrace]
  refine ⟨50615911344371776644327619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67487881792495702192436825 50615911344371776644327619)
  ·
    refine ⟨75923867016557664966491429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50615911344371776644327619 75923867016557664966491429)
    ·
      refine ⟨14235725065604562181217143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75923867016557664966491429 14235725065604562181217143)
      ·
        refine ⟨21353587598406843271825715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14235725065604562181217143 21353587598406843271825715)
        ·
          refine ⟨32030381397610264907738573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21353587598406843271825715 32030381397610264907738573)
          ·
            refine ⟨12011393024103849340401965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32030381397610264907738573 12011393024103849340401965)
            ·
              refine ⟨4504272384038943502650737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12011393024103849340401965 4504272384038943502650737)
              ·
                refine ⟨3378204288029207626988053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4504272384038943502650737 3378204288029207626988053)
                ·
                  refine ⟨158353326001369107515065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3378204288029207626988053 158353326001369107515065)
                  ·
                    rfl

theorem cell23_2775528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 2, 6].length) (baseStart_2775528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775528 prefixEnd_2775528 := by exact prefixLift 2775528
  have htrace : WordTrace (prefixWord ++ tailWord_2775528) baseStart_2775528 baseEnd_2775528 := by
    simpa [prefixWord, tailWord_2775528, baseEnd_2775528] using wordTrace_append hprefix tailTrace_2775528
  have hstable : (prefixWord ++ tailWord_2775528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775528).length < 2 ^ (prefixWord ++ tailWord_2775528).sum := by decide
  have hdescent : baseEnd_2775528 < baseStart_2775528 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775571 : List Nat := [1, 1, 1, 2, 1, 5, 2, 1, 3, 6]
def baseStart_2775571 : Nat := 118140960795 + 2775571 * 2 ^ 59
def prefixEnd_2775571 : Nat := 4983230072969 + 3 ^ 40 * 2775571 * 2
def baseEnd_2775571 : Nat := 475067337893488433132629

theorem tailTrace_2775571 : CollatzResearch.WordTrace tailWord_2775571 prefixEnd_2775571 475067337893488433132629 := by
  unfold tailWord_2775571
  simp only [CollatzResearch.WordTrace]
  refine ⟨101233391027587771632470567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67488927351725181088313711 101233391027587771632470567)
  ·
    refine ⟨151850086541381657448705851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101233391027587771632470567 151850086541381657448705851)
    ·
      refine ⟨227775129812072486173058777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151850086541381657448705851 227775129812072486173058777)
      ·
        refine ⟨170831347359054364629794083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227775129812072486173058777 170831347359054364629794083)
        ·
          refine ⟨256247021038581546944691125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170831347359054364629794083 256247021038581546944691125)
          ·
            refine ⟨24023158222367020026064793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256247021038581546944691125 24023158222367020026064793)
            ·
              refine ⟨18017368666775265019548595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24023158222367020026064793 18017368666775265019548595)
              ·
                refine ⟨27026053000162897529322893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18017368666775265019548595 27026053000162897529322893)
                ·
                  refine ⟨10134769875061086573496085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27026053000162897529322893 10134769875061086573496085)
                  ·
                    refine ⟨475067337893488433132629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10134769875061086573496085 475067337893488433132629)
                    ·
                      rfl

theorem cell23_2775571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 1, 3, 6].length) (baseStart_2775571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775571 prefixEnd_2775571 := by exact prefixLift 2775571
  have htrace : WordTrace (prefixWord ++ tailWord_2775571) baseStart_2775571 baseEnd_2775571 := by
    simpa [prefixWord, tailWord_2775571, baseEnd_2775571] using wordTrace_append hprefix tailTrace_2775571
  have hstable : (prefixWord ++ tailWord_2775571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775571).length < 2 ^ (prefixWord ++ tailWord_2775571).sum := by decide
  have hdescent : baseEnd_2775571 < baseStart_2775571 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775601 : List Nat := [1, 2, 2, 3, 1, 1, 3, 10]
def baseStart_2775601 : Nat := 118140960795 + 2775601 * 2 ^ 59
def prefixEnd_2775601 : Nat := 4983230072969 + 3 ^ 40 * 2775601 * 2
def baseEnd_2775601 : Nat := 52785830300003710445287

theorem tailTrace_2775601 : CollatzResearch.WordTrace tailWord_2775601 prefixEnd_2775601 52785830300003710445287 := by
  unfold tailWord_2775601
  simp only [CollatzResearch.WordTrace]
  refine ⟨101234485217479086756062657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67489656811652724504041771 101234485217479086756062657)
  ·
    refine ⟨75925863913109315067046993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101234485217479086756062657 75925863913109315067046993)
    ·
      refine ⟨56944397934831986300285245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75925863913109315067046993 56944397934831986300285245)
      ·
        refine ⟨21354149225561994862606967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56944397934831986300285245 21354149225561994862606967)
        ·
          refine ⟨32031223838342992293910451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21354149225561994862606967 32031223838342992293910451)
          ·
            refine ⟨48046835757514488440865677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32031223838342992293910451 48046835757514488440865677)
            ·
              refine ⟨18017563409067933165324629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48046835757514488440865677 18017563409067933165324629)
              ·
                refine ⟨52785830300003710445287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 18017563409067933165324629 52785830300003710445287)
                ·
                  rfl

theorem cell23_2775601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 10].length) (baseStart_2775601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775601 prefixEnd_2775601 := by exact prefixLift 2775601
  have htrace : WordTrace (prefixWord ++ tailWord_2775601) baseStart_2775601 baseEnd_2775601 := by
    simpa [prefixWord, tailWord_2775601, baseEnd_2775601] using wordTrace_append hprefix tailTrace_2775601
  have hstable : (prefixWord ++ tailWord_2775601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775601).length < 2 ^ (prefixWord ++ tailWord_2775601).sum := by decide
  have hdescent : baseEnd_2775601 < baseStart_2775601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775605 : List Nat := [1, 3, 3, 1, 1, 2, 3, 3, 2, 4]
def baseStart_2775605 : Nat := 118140960795 + 2775605 * 2 ^ 59
def prefixEnd_2775605 : Nat := 4983230072969 + 3 ^ 40 * 2775605 * 2
def baseEnd_2775605 : Nat := 475073157340906055457577

theorem tailTrace_2775605 : CollatzResearch.WordTrace tailWord_2775605 prefixEnd_2775605 475073157340906055457577 := by
  unfold tailWord_2775605
  simp only [CollatzResearch.WordTrace]
  refine ⟨101234631109464595439208269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67489754072976396959472179 101234631109464595439208269)
  ·
    refine ⟨37962986666049223289703101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101234631109464595439208269 37962986666049223289703101)
    ·
      refine ⟨14236119999768458733638663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37962986666049223289703101 14236119999768458733638663)
      ·
        refine ⟨21354179999652688100457995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14236119999768458733638663 21354179999652688100457995)
        ·
          refine ⟨32031269999479032150686993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21354179999652688100457995 32031269999479032150686993)
          ·
            refine ⟨24023452499609274113015245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32031269999479032150686993 24023452499609274113015245)
            ·
              refine ⟨9008794687353477792380717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24023452499609274113015245 9008794687353477792380717)
              ·
                refine ⟨3378298007757554172142769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9008794687353477792380717 3378298007757554172142769)
                ·
                  refine ⟨2533723505818165629107077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3378298007757554172142769 2533723505818165629107077)
                  ·
                    refine ⟨475073157340906055457577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2533723505818165629107077 475073157340906055457577)
                    ·
                      rfl

theorem cell23_2775605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_2775605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775605 prefixEnd_2775605 := by exact prefixLift 2775605
  have htrace : WordTrace (prefixWord ++ tailWord_2775605) baseStart_2775605 baseEnd_2775605 := by
    simpa [prefixWord, tailWord_2775605, baseEnd_2775605] using wordTrace_append hprefix tailTrace_2775605
  have hstable : (prefixWord ++ tailWord_2775605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775605).length < 2 ^ (prefixWord ++ tailWord_2775605).sum := by decide
  have hdescent : baseEnd_2775605 < baseStart_2775605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775608 : List Nat := [2, 1, 2, 1, 4, 1, 2, 3, 1, 2, 4]
def baseStart_2775608 : Nat := 118140960795 + 2775608 * 2 ^ 59
def prefixEnd_2775608 : Nat := 4983230072969 + 3 ^ 40 * 2775608 * 2
def baseEnd_2775608 : Nat := 1425221012464681654635217

theorem tailTrace_2775608 : CollatzResearch.WordTrace tailWord_2775608 prefixEnd_2775608 1425221012464681654635217 := by
  unfold tailWord_2775608
  simp only [CollatzResearch.WordTrace]
  refine ⟨50617370264226863475783739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67489827018969151301044985 50617370264226863475783739)
  ·
    refine ⟨75926055396340295213675609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50617370264226863475783739 75926055396340295213675609)
    ·
      refine ⟨56944541547255221410256707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75926055396340295213675609 56944541547255221410256707)
      ·
        refine ⟨85416812320882832115385061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56944541547255221410256707 85416812320882832115385061)
        ·
          refine ⟨16015652310165531021634699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85416812320882832115385061 16015652310165531021634699)
          ·
            refine ⟨24023478465248296532452049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16015652310165531021634699 24023478465248296532452049)
            ·
              refine ⟨18017608848936222399339037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24023478465248296532452049 18017608848936222399339037)
              ·
                refine ⟨6756603318351083399752139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18017608848936222399339037 6756603318351083399752139)
                ·
                  refine ⟨10134904977526625099628209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6756603318351083399752139 10134904977526625099628209)
                  ·
                    refine ⟨7601178733144968824721157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10134904977526625099628209 7601178733144968824721157)
                    ·
                      refine ⟨1425221012464681654635217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7601178733144968824721157 1425221012464681654635217)
                      ·
                        rfl

theorem cell23_2775608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 2, 3, 1, 2, 4].length) (baseStart_2775608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775608 prefixEnd_2775608 := by exact prefixLift 2775608
  have htrace : WordTrace (prefixWord ++ tailWord_2775608) baseStart_2775608 baseEnd_2775608 := by
    simpa [prefixWord, tailWord_2775608, baseEnd_2775608] using wordTrace_append hprefix tailTrace_2775608
  have hstable : (prefixWord ++ tailWord_2775608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775608).length < 2 ^ (prefixWord ++ tailWord_2775608).sum := by decide
  have hdescent : baseEnd_2775608 < baseStart_2775608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775612 : List Nat := [2, 2, 2, 2, 3, 3, 1, 2, 1, 1, 4]
def baseStart_2775612 : Nat := 118140960795 + 2775612 * 2 ^ 59
def prefixEnd_2775612 : Nat := 4983230072969 + 3 ^ 40 * 2775612 * 2
def baseEnd_2775612 : Nat := 1425223066387299638985199

theorem tailTrace_2775612 : CollatzResearch.WordTrace tailWord_2775612 prefixEnd_2775612 1425223066387299638985199 := by
  unfold tailWord_2775612
  simp only [CollatzResearch.WordTrace]
  refine ⟨50617443210219617817356545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67489924280292823756475393 50617443210219617817356545)
  ·
    refine ⟨37963082407664713363017409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50617443210219617817356545 37963082407664713363017409)
    ·
      refine ⟨28472311805748535022263057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37963082407664713363017409 28472311805748535022263057)
      ·
        refine ⟨21354233854311401266697293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28472311805748535022263057 21354233854311401266697293)
        ·
          refine ⟨8007837695366775475011485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21354233854311401266697293 8007837695366775475011485)
          ·
            refine ⟨3002939135762540803129307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8007837695366775475011485 3002939135762540803129307)
            ·
              refine ⟨4504408703643811204693961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3002939135762540803129307 4504408703643811204693961)
              ·
                refine ⟨3378306527732858403520471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4504408703643811204693961 3378306527732858403520471)
                ·
                  refine ⟨5067459791599287605280707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3378306527732858403520471 5067459791599287605280707)
                  ·
                    refine ⟨7601189687398931407921061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5067459791599287605280707 7601189687398931407921061)
                    ·
                      refine ⟨1425223066387299638985199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7601189687398931407921061 1425223066387299638985199)
                      ·
                        rfl

theorem cell23_2775612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 3, 1, 2, 1, 1, 4].length) (baseStart_2775612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775612 prefixEnd_2775612 := by exact prefixLift 2775612
  have htrace : WordTrace (prefixWord ++ tailWord_2775612) baseStart_2775612 baseEnd_2775612 := by
    simpa [prefixWord, tailWord_2775612, baseEnd_2775612] using wordTrace_append hprefix tailTrace_2775612
  have hstable : (prefixWord ++ tailWord_2775612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775612).length < 2 ^ (prefixWord ++ tailWord_2775612).sum := by decide
  have hdescent : baseEnd_2775612 < baseStart_2775612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775622 : List Nat := [6, 1, 1, 1, 2, 2, 1, 2, 1, 6]
def baseStart_2775622 : Nat := 118140960795 + 2775622 * 2 ^ 59
def prefixEnd_2775622 : Nat := 4983230072969 + 3 ^ 40 * 2775622 * 2
def baseEnd_2775622 : Nat := 475076067064614866620051

theorem tailTrace_2775622 : CollatzResearch.WordTrace tailWord_2775622 prefixEnd_2775622 475076067064614866620051 := by
  unfold tailWord_2775622
  simp only [CollatzResearch.WordTrace]
  refine ⟨3163601598450093979455535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67490167433602004895051413 3163601598450093979455535)
  ·
    refine ⟨4745402397675140969183303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3163601598450093979455535 4745402397675140969183303)
    ·
      refine ⟨7118103596512711453774955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4745402397675140969183303 7118103596512711453774955)
      ·
        refine ⟨10677155394769067180662433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7118103596512711453774955 10677155394769067180662433)
        ·
          refine ⟨8007866546076800385496825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10677155394769067180662433 8007866546076800385496825)
          ·
            refine ⟨6005899909557600289122619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8007866546076800385496825 6005899909557600289122619)
            ·
              refine ⟨9008849864336400433683929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6005899909557600289122619 9008849864336400433683929)
              ·
                refine ⟨6756637398252300325262947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9008849864336400433683929 6756637398252300325262947)
                ·
                  refine ⟨10134956097378450487894421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6756637398252300325262947 10134956097378450487894421)
                  ·
                    refine ⟨475076067064614866620051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10134956097378450487894421 475076067064614866620051)
                    ·
                      rfl

theorem cell23_2775622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_2775622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775622 prefixEnd_2775622 := by exact prefixLift 2775622
  have htrace : WordTrace (prefixWord ++ tailWord_2775622) baseStart_2775622 baseEnd_2775622 := by
    simpa [prefixWord, tailWord_2775622, baseEnd_2775622] using wordTrace_append hprefix tailTrace_2775622
  have hstable : (prefixWord ++ tailWord_2775622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775622).length < 2 ^ (prefixWord ++ tailWord_2775622).sum := by decide
  have hdescent : baseEnd_2775622 < baseStart_2775622 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775629 : List Nat := [1, 6, 1, 1, 2, 2, 3, 1, 1, 1, 4]
def baseStart_2775629 : Nat := 118140960795 + 2775629 * 2 ^ 59
def prefixEnd_2775629 : Nat := 4983230072969 + 3 ^ 40 * 2775629 * 2
def baseEnd_2775629 : Nat := 1425231795558426072472621

theorem tailTrace_2775629 : CollatzResearch.WordTrace tailWord_2775629 prefixEnd_2775629 1425231795558426072472621 := by
  unfold tailWord_2775629
  simp only [CollatzResearch.WordTrace]
  refine ⟨101235506461377647538081941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67490337640918431692054627 101235506461377647538081941)
  ·
    refine ⟨4745414365377077228347591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101235506461377647538081941 4745414365377077228347591)
    ·
      refine ⟨7118121548065615842521387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4745414365377077228347591 7118121548065615842521387)
      ·
        refine ⟨10677182322098423763782081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7118121548065615842521387 10677182322098423763782081)
        ·
          refine ⟨8007886741573817822836561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10677182322098423763782081 8007886741573817822836561)
          ·
            refine ⟨6005915056180363367127421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8007886741573817822836561 6005915056180363367127421)
            ·
              refine ⟨2252218146067636262672783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6005915056180363367127421 2252218146067636262672783)
              ·
                refine ⟨3378327219101454394009175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252218146067636262672783 3378327219101454394009175)
                ·
                  refine ⟨5067490828652181591013763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3378327219101454394009175 5067490828652181591013763)
                  ·
                    refine ⟨7601236242978272386520645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5067490828652181591013763 7601236242978272386520645)
                    ·
                      refine ⟨1425231795558426072472621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7601236242978272386520645 1425231795558426072472621)
                      ·
                        rfl

theorem cell23_2775629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 3, 1, 1, 1, 4].length) (baseStart_2775629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775629 prefixEnd_2775629 := by exact prefixLift 2775629
  have htrace : WordTrace (prefixWord ++ tailWord_2775629) baseStart_2775629 baseEnd_2775629 := by
    simpa [prefixWord, tailWord_2775629, baseEnd_2775629] using wordTrace_append hprefix tailTrace_2775629
  have hstable : (prefixWord ++ tailWord_2775629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775629).length < 2 ^ (prefixWord ++ tailWord_2775629).sum := by decide
  have hdescent : baseEnd_2775629 < baseStart_2775629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775641 : List Nat := [1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 7]
def baseStart_2775641 : Nat := 118140960795 + 2775641 * 2 ^ 59
def prefixEnd_2775641 : Nat := 4983230072969 + 3 ^ 40 * 2775641 * 2
def baseEnd_2775641 : Nat := 1425237957326280025522565

theorem tailTrace_2775641 : CollatzResearch.WordTrace tailWord_2775641 prefixEnd_2775641 1425237957326280025522565 := by
  unfold tailWord_2775641
  simp only [CollatzResearch.WordTrace]
  refine ⟨101235944137334173587518777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67490629424889449058345851 101235944137334173587518777)
  ·
    refine ⟨75926958103000630190639083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101235944137334173587518777 75926958103000630190639083)
    ·
      refine ⟨113890437154500945285958625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75926958103000630190639083 113890437154500945285958625)
      ·
        refine ⟨85417827865875708964468969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113890437154500945285958625 85417827865875708964468969)
        ·
          refine ⟨64063370899406781723351727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85417827865875708964468969 64063370899406781723351727)
          ·
            refine ⟨96095056349110172585027591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64063370899406781723351727 96095056349110172585027591)
            ·
              refine ⟨144142584523665258877541387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96095056349110172585027591 144142584523665258877541387)
              ·
                refine ⟨216213876785497888316312081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 144142584523665258877541387 216213876785497888316312081)
                ·
                  refine ⟨162160407589123416237234061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216213876785497888316312081 162160407589123416237234061)
                  ·
                    refine ⟨60810152845921281088962773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 162160407589123416237234061 60810152845921281088962773)
                    ·
                      refine ⟨1425237957326280025522565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60810152845921281088962773 1425237957326280025522565)
                      ·
                        rfl

theorem cell23_2775641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 1, 1, 2, 3, 7].length) (baseStart_2775641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775641 prefixEnd_2775641 := by exact prefixLift 2775641
  have htrace : WordTrace (prefixWord ++ tailWord_2775641) baseStart_2775641 baseEnd_2775641 := by
    simpa [prefixWord, tailWord_2775641, baseEnd_2775641] using wordTrace_append hprefix tailTrace_2775641
  have hstable : (prefixWord ++ tailWord_2775641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775641).length < 2 ^ (prefixWord ++ tailWord_2775641).sum := by decide
  have hdescent : baseEnd_2775641 < baseStart_2775641 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775662 : List Nat := [4, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3]
def baseStart_2775662 : Nat := 118140960795 + 2775662 * 2 ^ 59
def prefixEnd_2775662 : Nat := 4983230072969 + 3 ^ 40 * 2775662 * 2
def baseEnd_2775662 : Nat := 1425248740420024443359969

theorem tailTrace_2775662 : CollatzResearch.WordTrace tailWord_2775662 prefixEnd_2775662 1425248740420024443359969 := by
  unfold tailWord_2775662
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654588758782261771754155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67491140046838729449355493 12654588758782261771754155)
  ·
    refine ⟨18981883138173392657631233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12654588758782261771754155 18981883138173392657631233)
    ·
      refine ⟨14236412353630044493223425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18981883138173392657631233 14236412353630044493223425)
      ·
        refine ⟨10677309265222533369917569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14236412353630044493223425 10677309265222533369917569)
        ·
          refine ⟨8007981948916900027438177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10677309265222533369917569 8007981948916900027438177)
          ·
            refine ⟨6005986461687675020578633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8007981948916900027438177 6005986461687675020578633)
            ·
              refine ⟨4504489846265756265433975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6005986461687675020578633 4504489846265756265433975)
              ·
                refine ⟨6756734769398634398150963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4504489846265756265433975 6756734769398634398150963)
                ·
                  refine ⟨10135102154097951597226445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6756734769398634398150963 10135102154097951597226445)
                  ·
                    refine ⟨3800663307786731848959917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10135102154097951597226445 3800663307786731848959917)
                    ·
                      refine ⟨1425248740420024443359969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3800663307786731848959917 1425248740420024443359969)
                      ·
                        rfl

theorem cell23_2775662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 1, 3, 3].length) (baseStart_2775662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775662 prefixEnd_2775662 := by exact prefixLift 2775662
  have htrace : WordTrace (prefixWord ++ tailWord_2775662) baseStart_2775662 baseEnd_2775662 := by
    simpa [prefixWord, tailWord_2775662, baseEnd_2775662] using wordTrace_append hprefix tailTrace_2775662
  have hstable : (prefixWord ++ tailWord_2775662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775662).length < 2 ^ (prefixWord ++ tailWord_2775662).sum := by decide
  have hdescent : baseEnd_2775662 < baseStart_2775662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775725 : List Nat := [1, 5, 2, 1, 1, 2, 2, 2, 7]
def baseStart_2775725 : Nat := 118140960795 + 2775725 * 2 ^ 59
def prefixEnd_2775725 : Nat := 4983230072969 + 3 ^ 40 * 2775725 * 2
def baseEnd_2775725 : Nat := 158364565522361966319131

theorem tailTrace_2775725 : CollatzResearch.WordTrace tailWord_2775725 prefixEnd_2775725 158364565522361966319131 := by
  unfold tailWord_2775725
  simp only [CollatzResearch.WordTrace]
  refine ⟨101239007869029855933576629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67492671912686570622384419 101239007869029855933576629)
  ·
    refine ⟨9491156987721548993772809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101239007869029855933576629 9491156987721548993772809)
    ·
      refine ⟨7118367740791161745329607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9491156987721548993772809 7118367740791161745329607)
      ·
        refine ⟨10677551611186742617994411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7118367740791161745329607 10677551611186742617994411)
        ·
          refine ⟨16016327416780113926991617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10677551611186742617994411 16016327416780113926991617)
          ·
            refine ⟨12012245562585085445243713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16016327416780113926991617 12012245562585085445243713)
            ·
              refine ⟨9009184171938814083932785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12012245562585085445243713 9009184171938814083932785)
              ·
                refine ⟨6756888128954110562949589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9009184171938814083932785 6756888128954110562949589)
                ·
                  refine ⟨158364565522361966319131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6756888128954110562949589 158364565522361966319131)
                  ·
                    rfl

theorem cell23_2775725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_2775725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775725 prefixEnd_2775725 := by exact prefixLift 2775725
  have htrace : WordTrace (prefixWord ++ tailWord_2775725) baseStart_2775725 baseEnd_2775725 := by
    simpa [prefixWord, tailWord_2775725, baseEnd_2775725] using wordTrace_append hprefix tailTrace_2775725
  have hstable : (prefixWord ++ tailWord_2775725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775725).length < 2 ^ (prefixWord ++ tailWord_2775725).sum := by decide
  have hdescent : baseEnd_2775725 < baseStart_2775725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775738 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 1, 7]
def baseStart_2775738 : Nat := 118140960795 + 2775738 * 2 ^ 59
def prefixEnd_2775738 : Nat := 4983230072969 + 3 ^ 40 * 2775738 * 2
def baseEnd_2775738 : Nat := 475095921649922048669873

theorem tailTrace_2775738 : CollatzResearch.WordTrace tailWord_2775738 prefixEnd_2775738 475095921649922048669873 := by
  unfold tailWord_2775738
  simp only [CollatzResearch.WordTrace]
  refine ⟨25309870504495689788449967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67492988011988506102533245 25309870504495689788449967)
  ·
    refine ⟨37964805756743534682674951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25309870504495689788449967 37964805756743534682674951)
    ·
      refine ⟨56947208635115302024012427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37964805756743534682674951 56947208635115302024012427)
      ·
        refine ⟨85420812952672953036018641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56947208635115302024012427 85420812952672953036018641)
        ·
          refine ⟨64065609714504714777013981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85420812952672953036018641 64065609714504714777013981)
          ·
            refine ⟨24024603642939268041380243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64065609714504714777013981 24024603642939268041380243)
            ·
              refine ⟨36036905464408902062070365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24024603642939268041380243 36036905464408902062070365)
              ·
                refine ⟨13513839549153338273276387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36036905464408902062070365 13513839549153338273276387)
                ·
                  refine ⟨20270759323730007409914581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13513839549153338273276387 20270759323730007409914581)
                  ·
                    refine ⟨475095921649922048669873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20270759323730007409914581 475095921649922048669873)
                    ·
                      rfl

theorem cell23_2775738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 1, 7].length) (baseStart_2775738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775738 prefixEnd_2775738 := by exact prefixLift 2775738
  have htrace : WordTrace (prefixWord ++ tailWord_2775738) baseStart_2775738 baseEnd_2775738 := by
    simpa [prefixWord, tailWord_2775738, baseEnd_2775738] using wordTrace_append hprefix tailTrace_2775738
  have hstable : (prefixWord ++ tailWord_2775738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775738).length < 2 ^ (prefixWord ++ tailWord_2775738).sum := by decide
  have hdescent : baseEnd_2775738 < baseStart_2775738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775785 : List Nat := [1, 2, 1, 1, 1, 2, 4, 4, 3, 4]
def baseStart_2775785 : Nat := 118140960795 + 2775785 * 2 ^ 59
def prefixEnd_2775785 : Nat := 4983230072969 + 3 ^ 40 * 2775785 * 2
def baseEnd_2775785 : Nat := 475103966180175820707301

theorem tailTrace_2775785 : CollatzResearch.WordTrace tailWord_2775785 prefixEnd_2775785 475103966180175820707301 := by
  unfold tailWord_2775785
  simp only [CollatzResearch.WordTrace]
  refine ⟨101241196248812486180760809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67494130832541657453840539 101241196248812486180760809)
  ·
    refine ⟨75930897186609364635570607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101241196248812486180760809 75930897186609364635570607)
    ·
      refine ⟨113896345779914046953355911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75930897186609364635570607 113896345779914046953355911)
      ·
        refine ⟨170844518669871070430033867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113896345779914046953355911 170844518669871070430033867)
        ·
          refine ⟨256266778004806605645050801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170844518669871070430033867 256266778004806605645050801)
          ·
            refine ⟨192200083503604954233788101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256266778004806605645050801 192200083503604954233788101)
            ·
              refine ⟨36037515656925928918835269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192200083503604954233788101 36037515656925928918835269)
              ·
                refine ⟨6757034185673611672281613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36037515656925928918835269 6757034185673611672281613)
                ·
                  refine ⟨2533887819627604377105605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6757034185673611672281613 2533887819627604377105605)
                  ·
                    refine ⟨475103966180175820707301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2533887819627604377105605 475103966180175820707301)
                    ·
                      rfl

theorem cell23_2775785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 4, 3, 4].length) (baseStart_2775785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775785 prefixEnd_2775785 := by exact prefixLift 2775785
  have htrace : WordTrace (prefixWord ++ tailWord_2775785) baseStart_2775785 baseEnd_2775785 := by
    simpa [prefixWord, tailWord_2775785, baseEnd_2775785] using wordTrace_append hprefix tailTrace_2775785
  have hstable : (prefixWord ++ tailWord_2775785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775785).length < 2 ^ (prefixWord ++ tailWord_2775785).sum := by decide
  have hdescent : baseEnd_2775785 < baseStart_2775785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775788 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 6]
def baseStart_2775788 : Nat := 118140960795 + 2775788 * 2 ^ 59
def prefixEnd_2775788 : Nat := 4983230072969 + 3 ^ 40 * 2775788 * 2
def baseEnd_2775788 : Nat := 1425313438982490950384389

theorem tailTrace_2775788 : CollatzResearch.WordTrace tailWord_2775788 prefixEnd_2775788 1425313438982490950384389 := by
  unfold tailWord_2775788
  simp only [CollatzResearch.WordTrace]
  refine ⟨50620652833900808846560009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67494203778534411795413345 50620652833900808846560009)
  ·
    refine ⟨37965489625425606634920007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50620652833900808846560009 37965489625425606634920007)
    ·
      refine ⟨56948234438138409952380011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37965489625425606634920007 56948234438138409952380011)
      ·
        refine ⟨85422351657207614928570017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56948234438138409952380011 85422351657207614928570017)
        ·
          refine ⟨64066763742905711196427513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85422351657207614928570017 64066763742905711196427513)
          ·
            refine ⟨48050072807179283397320635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64066763742905711196427513 48050072807179283397320635)
            ·
              refine ⟨72075109210768925095980953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48050072807179283397320635 72075109210768925095980953)
              ·
                refine ⟨54056331908076693821985715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72075109210768925095980953 54056331908076693821985715)
                ·
                  refine ⟨81084497862115040732978573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54056331908076693821985715 81084497862115040732978573)
                  ·
                    refine ⟨30406686698293140274866965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 81084497862115040732978573 30406686698293140274866965)
                    ·
                      refine ⟨1425313438982490950384389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30406686698293140274866965 1425313438982490950384389)
                      ·
                        rfl

theorem cell23_2775788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 6].length) (baseStart_2775788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775788 prefixEnd_2775788 := by exact prefixLift 2775788
  have htrace : WordTrace (prefixWord ++ tailWord_2775788) baseStart_2775788 baseEnd_2775788 := by
    simpa [prefixWord, tailWord_2775788, baseEnd_2775788] using wordTrace_append hprefix tailTrace_2775788
  have hstable : (prefixWord ++ tailWord_2775788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775788).length < 2 ^ (prefixWord ++ tailWord_2775788).sum := by decide
  have hdescent : baseEnd_2775788 < baseStart_2775788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775812 : List Nat := [2, 3, 2, 2, 1, 1, 1, 4, 2, 2, 3]
def baseStart_2775812 : Nat := 118140960795 + 2775812 * 2 ^ 59
def prefixEnd_2775812 : Nat := 4983230072969 + 3 ^ 40 * 2775812 * 2
def baseEnd_2775812 : Nat := 1425325762518198856484279

theorem tailTrace_2775812 : CollatzResearch.WordTrace tailWord_2775812 prefixEnd_2775812 1425325762518198856484279 := by
  unfold tailWord_2775812
  simp only [CollatzResearch.WordTrace]
  refine ⟨50621090509857334895996845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67494787346476446527995793 50621090509857334895996845)
  ·
    refine ⟨18982908941196500585998817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50621090509857334895996845 18982908941196500585998817)
    ·
      refine ⟨14237181705897375439499113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18982908941196500585998817 14237181705897375439499113)
      ·
        refine ⟨10677886279423031579624335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14237181705897375439499113 10677886279423031579624335)
        ·
          refine ⟨16016829419134547369436503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10677886279423031579624335 16016829419134547369436503)
          ·
            refine ⟨24025244128701821054154755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16016829419134547369436503 24025244128701821054154755)
            ·
              refine ⟨36037866193052731581232133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24025244128701821054154755 36037866193052731581232133)
              ·
                refine ⟨6757099911197387171481025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36037866193052731581232133 6757099911197387171481025)
                ·
                  refine ⟨5067824933398040378610769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6757099911197387171481025 5067824933398040378610769)
                  ·
                    refine ⟨3800868700048530283958077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5067824933398040378610769 3800868700048530283958077)
                    ·
                      refine ⟨1425325762518198856484279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3800868700048530283958077 1425325762518198856484279)
                      ·
                        rfl

theorem cell23_2775812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_2775812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775812 prefixEnd_2775812 := by exact prefixLift 2775812
  have htrace : WordTrace (prefixWord ++ tailWord_2775812) baseStart_2775812 baseEnd_2775812 := by
    simpa [prefixWord, tailWord_2775812, baseEnd_2775812] using wordTrace_append hprefix tailTrace_2775812
  have hstable : (prefixWord ++ tailWord_2775812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775812).length < 2 ^ (prefixWord ++ tailWord_2775812).sum := by decide
  have hdescent : baseEnd_2775812 < baseStart_2775812 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775826 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 2, 4, 2]
def baseStart_2775826 : Nat := 118140960795 + 2775826 * 2 ^ 59
def prefixEnd_2775826 : Nat := 4983230072969 + 3 ^ 40 * 2775826 * 2
def baseEnd_2775826 : Nat := 1425332951247361801709215

theorem tailTrace_2775826 : CollatzResearch.WordTrace tailWord_2775826 prefixEnd_2775826 1425332951247361801709215 := by
  unfold tailWord_2775826
  simp only [CollatzResearch.WordTrace]
  refine ⟨25310672910415987545750833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67495127761109300122002221 25310672910415987545750833)
  ·
    refine ⟨18983004682811990659313125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25310672910415987545750833 18983004682811990659313125)
    ·
      refine ⟨3559313378027248248621211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18983004682811990659313125 3559313378027248248621211)
      ·
        refine ⟨5338970067040872372931817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3559313378027248248621211 5338970067040872372931817)
        ·
          refine ⟨4004227550280654279698863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5338970067040872372931817 4004227550280654279698863)
          ·
            refine ⟨6006341325420981419548295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4004227550280654279698863 6006341325420981419548295)
            ·
              refine ⟨9009511988131472129322443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6006341325420981419548295 9009511988131472129322443)
              ·
                refine ⟨13514267982197208193983665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009511988131472129322443 13514267982197208193983665)
                ·
                  refine ⟨10135700986647906145487749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13514267982197208193983665 10135700986647906145487749)
                  ·
                    refine ⟨1900443934996482402278953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10135700986647906145487749 1900443934996482402278953)
                    ·
                      refine ⟨1425332951247361801709215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900443934996482402278953 1425332951247361801709215)
                      ·
                        rfl

theorem cell23_2775826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_2775826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775826 prefixEnd_2775826 := by exact prefixLift 2775826
  have htrace : WordTrace (prefixWord ++ tailWord_2775826) baseStart_2775826 baseEnd_2775826 := by
    simpa [prefixWord, tailWord_2775826, baseEnd_2775826] using wordTrace_append hprefix tailTrace_2775826
  have hstable : (prefixWord ++ tailWord_2775826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775826).length < 2 ^ (prefixWord ++ tailWord_2775826).sum := by decide
  have hdescent : baseEnd_2775826 < baseStart_2775826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775845 : List Nat := [1, 3, 1, 2, 3, 1, 1, 3, 3, 5]
def baseStart_2775845 : Nat := 118140960795 + 2775845 * 2 ^ 59
def prefixEnd_2775845 : Nat := 4983230072969 + 3 ^ 40 * 2775845 * 2
def baseEnd_2775845 : Nat := 475114235793265742457209

theorem tailTrace_2775845 : CollatzResearch.WordTrace tailWord_2775845 prefixEnd_2775845 475114235793265742457209 := by
  unfold tailWord_2775845
  simp only [CollatzResearch.WordTrace]
  refine ⟨101243384628595116427944989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67495589752396744285296659 101243384628595116427944989)
  ·
    refine ⟨37966269235723168660479371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101243384628595116427944989 37966269235723168660479371)
    ·
      refine ⟨56949403853584752990719057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37966269235723168660479371 56949403853584752990719057)
      ·
        refine ⟨42712052890188564743039293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56949403853584752990719057 42712052890188564743039293)
        ·
          refine ⟨16017019833820711778639735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42712052890188564743039293 16017019833820711778639735)
          ·
            refine ⟨24025529750731067667959603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16017019833820711778639735 24025529750731067667959603)
            ·
              refine ⟨36038294626096601501939405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24025529750731067667959603 36038294626096601501939405)
              ·
                refine ⟨13514360484786225563227277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36038294626096601501939405 13514360484786225563227277)
                ·
                  refine ⟨5067885181794834586210229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13514360484786225563227277 5067885181794834586210229)
                  ·
                    refine ⟨475114235793265742457209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5067885181794834586210229 475114235793265742457209)
                    ·
                      rfl

theorem cell23_2775845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_2775845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775845 prefixEnd_2775845 := by exact prefixLift 2775845
  have htrace : WordTrace (prefixWord ++ tailWord_2775845) baseStart_2775845 baseEnd_2775845 := by
    simpa [prefixWord, tailWord_2775845, baseEnd_2775845] using wordTrace_append hprefix tailTrace_2775845
  have hstable : (prefixWord ++ tailWord_2775845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775845).length < 2 ^ (prefixWord ++ tailWord_2775845).sum := by decide
  have hdescent : baseEnd_2775845 < baseStart_2775845 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775852 : List Nat := [2, 2, 1, 1, 1, 4, 3, 1, 1, 5, 2]
def baseStart_2775852 : Nat := 118140960795 + 2775852 * 2 ^ 59
def prefixEnd_2775852 : Nat := 4983230072969 + 3 ^ 40 * 2775852 * 2
def baseEnd_2775852 : Nat := 1425346301744378699984095

theorem tailTrace_2775852 : CollatzResearch.WordTrace tailWord_2775852 prefixEnd_2775852 1425346301744378699984095 := by
  unfold tailWord_2775852
  simp only [CollatzResearch.WordTrace]
  refine ⟨50621819969784878311724905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67495759959713171082299873 50621819969784878311724905)
  ·
    refine ⟨37966364977338658733793679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50621819969784878311724905 37966364977338658733793679)
    ·
      refine ⟨56949547466007988100690519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37966364977338658733793679 56949547466007988100690519)
      ·
        refine ⟨85424321199011982151035779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56949547466007988100690519 85424321199011982151035779)
        ·
          refine ⟨128136481798517973226553669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85424321199011982151035779 128136481798517973226553669)
          ·
            refine ⟨24025590337222119979978813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128136481798517973226553669 24025590337222119979978813)
            ·
              refine ⟨9009596376458294992492055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24025590337222119979978813 9009596376458294992492055)
              ·
                refine ⟨13514394564687442488738083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009596376458294992492055 13514394564687442488738083)
                ·
                  refine ⟨20271591847031163733107125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13514394564687442488738083 20271591847031163733107125)
                  ·
                    refine ⟨1900461735659171599978793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20271591847031163733107125 1900461735659171599978793)
                    ·
                      refine ⟨1425346301744378699984095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900461735659171599978793 1425346301744378699984095)
                      ·
                        rfl

theorem cell23_2775852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 5, 2].length) (baseStart_2775852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775852 prefixEnd_2775852 := by exact prefixLift 2775852
  have htrace : WordTrace (prefixWord ++ tailWord_2775852) baseStart_2775852 baseEnd_2775852 := by
    simpa [prefixWord, tailWord_2775852, baseEnd_2775852] using wordTrace_append hprefix tailTrace_2775852
  have hstable : (prefixWord ++ tailWord_2775852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775852).length < 2 ^ (prefixWord ++ tailWord_2775852).sum := by decide
  have hdescent : baseEnd_2775852 < baseStart_2775852 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775955 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4]
def baseStart_2775955 : Nat := 118140960795 + 2775955 * 2 ^ 59
def prefixEnd_2775955 : Nat := 4983230072969 + 3 ^ 40 * 2775955 * 2
def baseEnd_2775955 : Nat := 1425399190251791796996121

theorem tailTrace_2775955 : CollatzResearch.WordTrace tailWord_2775955 prefixEnd_2775955 1425399190251791796996121 := by
  unfold tailWord_2775955
  simp only [CollatzResearch.WordTrace]
  refine ⟨101247396658196605214449319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67498264438797736809632879 101247396658196605214449319)
  ·
    refine ⟨151871094987294907821673979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101247396658196605214449319 151871094987294907821673979)
    ·
      refine ⟨227806642480942361732510969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151871094987294907821673979 227806642480942361732510969)
      ·
        refine ⟨170854981860706771299383227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227806642480942361732510969 170854981860706771299383227)
        ·
          refine ⟨256282472791060156949074841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170854981860706771299383227 256282472791060156949074841)
          ·
            refine ⟨192211854593295117711806131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256282472791060156949074841 192211854593295117711806131)
            ·
              refine ⟨288317781889942676567709197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192211854593295117711806131 288317781889942676567709197)
              ·
                refine ⟨108119168208728503712890949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 288317781889942676567709197 108119168208728503712890949)
                ·
                  refine ⟨20272344039136594446167053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 108119168208728503712890949 20272344039136594446167053)
                  ·
                    refine ⟨7602129014676222917312645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20272344039136594446167053 7602129014676222917312645)
                    ·
                      refine ⟨1425399190251791796996121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7602129014676222917312645 1425399190251791796996121)
                      ·
                        rfl

theorem cell23_2775955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 4, 3, 4].length) (baseStart_2775955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775955 prefixEnd_2775955 := by exact prefixLift 2775955
  have htrace : WordTrace (prefixWord ++ tailWord_2775955) baseStart_2775955 baseEnd_2775955 := by
    simpa [prefixWord, tailWord_2775955, baseEnd_2775955] using wordTrace_append hprefix tailTrace_2775955
  have hstable : (prefixWord ++ tailWord_2775955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775955).length < 2 ^ (prefixWord ++ tailWord_2775955).sum := by decide
  have hdescent : baseEnd_2775955 < baseStart_2775955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775959 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 3, 3, 2]
def baseStart_2775959 : Nat := 118140960795 + 2775959 * 2 ^ 59
def prefixEnd_2775959 : Nat := 4983230072969 + 3 ^ 40 * 2775959 * 2
def baseEnd_2775959 : Nat := 1425401244174409781346103

theorem tailTrace_2775959 : CollatzResearch.WordTrace tailWord_2775959 prefixEnd_2775959 1425401244174409781346103 := by
  unfold tailWord_2775959
  simp only [CollatzResearch.WordTrace]
  refine ⟨101247542550182113897594931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67498361700121409265063287 101247542550182113897594931)
  ·
    refine ⟨151871313825273170846392397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101247542550182113897594931 151871313825273170846392397)
    ·
      refine ⟨56951742684477439067397149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151871313825273170846392397 56951742684477439067397149)
      ·
        refine ⟨21356903506679039650273931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56951742684477439067397149 21356903506679039650273931)
        ·
          refine ⟨32035355260018559475410897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21356903506679039650273931 32035355260018559475410897)
          ·
            refine ⟨24026516445013919606558173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32035355260018559475410897 24026516445013919606558173)
            ·
              refine ⟨9009943666880219852459315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24026516445013919606558173 9009943666880219852459315)
              ·
                refine ⟨13514915500320329778688973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9009943666880219852459315 13514915500320329778688973)
                ·
                  refine ⟨5068093312620123667008365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13514915500320329778688973 5068093312620123667008365)
                  ·
                    refine ⟨1900534992232546375128137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5068093312620123667008365 1900534992232546375128137)
                    ·
                      refine ⟨1425401244174409781346103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900534992232546375128137 1425401244174409781346103)
                      ·
                        rfl

theorem cell23_2775959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_2775959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775959 prefixEnd_2775959 := by exact prefixLift 2775959
  have htrace : WordTrace (prefixWord ++ tailWord_2775959) baseStart_2775959 baseEnd_2775959 := by
    simpa [prefixWord, tailWord_2775959, baseEnd_2775959] using wordTrace_append hprefix tailTrace_2775959
  have hstable : (prefixWord ++ tailWord_2775959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775959).length < 2 ^ (prefixWord ++ tailWord_2775959).sum := by decide
  have hdescent : baseEnd_2775959 < baseStart_2775959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775989 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 3, 4, 2]
def baseStart_2775989 : Nat := 118140960795 + 2775989 * 2 ^ 59
def prefixEnd_2775989 : Nat := 4983230072969 + 3 ^ 40 * 2775989 * 2
def baseEnd_2775989 : Nat := 1425416648594044663970965

theorem tailTrace_2775989 : CollatzResearch.WordTrace tailWord_2775989 prefixEnd_2775989 1425416648594044663970965 := by
  unfold tailWord_2775989
  simp only [CollatzResearch.WordTrace]
  refine ⟨101248636740073429021187021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67499091160048952680791347 101248636740073429021187021)
  ·
    refine ⟨37968238777527535882945133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101248636740073429021187021 37968238777527535882945133)
    ·
      refine ⟨14238089541572825956104425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37968238777527535882945133 14238089541572825956104425)
      ·
        refine ⟨10678567156179619467078319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14238089541572825956104425 10678567156179619467078319)
        ·
          refine ⟨16017850734269429200617479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10678567156179619467078319 16017850734269429200617479)
          ·
            refine ⟨24026776101404143800926219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16017850734269429200617479 24026776101404143800926219)
            ·
              refine ⟨36040164152106215701389329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24026776101404143800926219 36040164152106215701389329)
              ·
                refine ⟨27030123114079661776041997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36040164152106215701389329 27030123114079661776041997)
                ·
                  refine ⟨10136296167779873166015749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27030123114079661776041997 10136296167779873166015749)
                  ·
                    refine ⟨1900555531458726218627953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10136296167779873166015749 1900555531458726218627953)
                    ·
                      refine ⟨1425416648594044663970965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900555531458726218627953 1425416648594044663970965)
                      ·
                        rfl

theorem cell23_2775989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 3, 4, 2].length) (baseStart_2775989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775989 prefixEnd_2775989 := by exact prefixLift 2775989
  have htrace : WordTrace (prefixWord ++ tailWord_2775989) baseStart_2775989 baseEnd_2775989 := by
    simpa [prefixWord, tailWord_2775989, baseEnd_2775989] using wordTrace_append hprefix tailTrace_2775989
  have hstable : (prefixWord ++ tailWord_2775989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775989).length < 2 ^ (prefixWord ++ tailWord_2775989).sum := by decide
  have hdescent : baseEnd_2775989 < baseStart_2775989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775990 : List Nat := [5, 1, 4, 1, 2, 1, 1, 8]
def baseStart_2775990 : Nat := 118140960795 + 2775990 * 2 ^ 59
def prefixEnd_2775990 : Nat := 4983230072969 + 3 ^ 40 * 2775990 * 2
def baseEnd_2775990 : Nat := 52793228224988857779943

theorem tailTrace_2775990 : CollatzResearch.WordTrace tailWord_2775990 prefixEnd_2775990 52793228224988857779943 := by
  unfold tailWord_2775990
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328042075816862886998339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67499115475379870794648949 6328042075816862886998339)
  ·
    refine ⟨9492063113725294330497509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6328042075816862886998339 9492063113725294330497509)
    ·
      refine ⟨1779761833823492686968283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9492063113725294330497509 1779761833823492686968283)
      ·
        refine ⟨2669642750735239030452425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1779761833823492686968283 2669642750735239030452425)
        ·
          refine ⟨2002232063051429272839319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2669642750735239030452425 2002232063051429272839319)
          ·
            refine ⟨3003348094577143909258979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002232063051429272839319 3003348094577143909258979)
            ·
              refine ⟨4505022141865715863888469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003348094577143909258979 4505022141865715863888469)
              ·
                refine ⟨52793228224988857779943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4505022141865715863888469 52793228224988857779943)
                ·
                  rfl

theorem cell23_2775990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 8].length) (baseStart_2775990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775990 prefixEnd_2775990 := by exact prefixLift 2775990
  have htrace : WordTrace (prefixWord ++ tailWord_2775990) baseStart_2775990 baseEnd_2775990 := by
    simpa [prefixWord, tailWord_2775990, baseEnd_2775990] using wordTrace_append hprefix tailTrace_2775990
  have hstable : (prefixWord ++ tailWord_2775990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775990).length < 2 ^ (prefixWord ++ tailWord_2775990).sum := by decide
  have hdescent : baseEnd_2775990 < baseStart_2775990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2775992 : List Nat := [2, 1, 2, 1, 2, 4, 1, 1, 2, 4, 3]
def baseStart_2775992 : Nat := 118140960795 + 2775992 * 2 ^ 59
def prefixEnd_2775992 : Nat := 4983230072969 + 3 ^ 40 * 2775992 * 2
def baseEnd_2775992 : Nat := 1425418189036008152233451

theorem tailTrace_2775992 : CollatzResearch.WordTrace tailWord_2775992 prefixEnd_2775992 1425418189036008152233451 := by
  unfold tailWord_2775992
  simp only [CollatzResearch.WordTrace]
  refine ⟨50624373079531280266773115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67499164106041707022364153 50624373079531280266773115)
  ·
    refine ⟨75936559619296920400159673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50624373079531280266773115 75936559619296920400159673)
    ·
      refine ⟨56952419714472690300119755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75936559619296920400159673 56952419714472690300119755)
      ·
        refine ⟨85428629571709035450179633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56952419714472690300119755 85428629571709035450179633)
        ·
          refine ⟨64071472178781776587634725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85428629571709035450179633 64071472178781776587634725)
          ·
            refine ⟨12013401033521583110181511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64071472178781776587634725 12013401033521583110181511)
            ·
              refine ⟨18020101550282374665272267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12013401033521583110181511 18020101550282374665272267)
              ·
                refine ⟨27030152325423561997908401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18020101550282374665272267 27030152325423561997908401)
                ·
                  refine ⟨20272614244067671498431301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27030152325423561997908401 20272614244067671498431301)
                  ·
                    refine ⟨3801115170762688405955869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20272614244067671498431301 3801115170762688405955869)
                    ·
                      refine ⟨1425418189036008152233451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3801115170762688405955869 1425418189036008152233451)
                      ·
                        rfl

theorem cell23_2775992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 1, 2, 4, 3].length) (baseStart_2775992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2775992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2775992 prefixEnd_2775992 := by exact prefixLift 2775992
  have htrace : WordTrace (prefixWord ++ tailWord_2775992) baseStart_2775992 baseEnd_2775992 := by
    simpa [prefixWord, tailWord_2775992, baseEnd_2775992] using wordTrace_append hprefix tailTrace_2775992
  have hstable : (prefixWord ++ tailWord_2775992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2775992).length < 2 ^ (prefixWord ++ tailWord_2775992).sum := by decide
  have hdescent : baseEnd_2775992 < baseStart_2775992 := by decide
  rcases family_descends (prefixWord ++ tailWord_2775992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776005 : List Nat := [1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_2776005 : Nat := 118140960795 + 2776005 * 2 ^ 59
def prefixEnd_2776005 : Nat := 4983230072969 + 3 ^ 40 * 2776005 * 2
def baseEnd_2776005 : Nat := 1425424864284516601370891

theorem tailTrace_2776005 : CollatzResearch.WordTrace tailWord_2776005 prefixEnd_2776005 1425424864284516601370891 := by
  unfold tailWord_2776005
  simp only [CollatzResearch.WordTrace]
  refine ⟨101249220308015463753769469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67499480205343642502512979 101249220308015463753769469)
  ·
    refine ⟨37968457615505798907663551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101249220308015463753769469 37968457615505798907663551)
    ·
      refine ⟨56952686423258698361495327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37968457615505798907663551 56952686423258698361495327)
      ·
        refine ⟨85429029634888047542242991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56952686423258698361495327 85429029634888047542242991)
        ·
          refine ⟨128143544452332071313364487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85429029634888047542242991 128143544452332071313364487)
          ·
            refine ⟨192215316678498106970046731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128143544452332071313364487 192215316678498106970046731)
            ·
              refine ⟨288322975017747160455070097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192215316678498106970046731 288322975017747160455070097)
              ·
                refine ⟨216242231263310370341302573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288322975017747160455070097 216242231263310370341302573)
                ·
                  refine ⟨81090836723741388877988465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 216242231263310370341302573 81090836723741388877988465)
                  ·
                    refine ⟨60818127542806041658491349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81090836723741388877988465 60818127542806041658491349)
                    ·
                      refine ⟨1425424864284516601370891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60818127542806041658491349 1425424864284516601370891)
                      ·
                        rfl

theorem cell23_2776005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_2776005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776005 prefixEnd_2776005 := by exact prefixLift 2776005
  have htrace : WordTrace (prefixWord ++ tailWord_2776005) baseStart_2776005 baseEnd_2776005 := by
    simpa [prefixWord, tailWord_2776005, baseEnd_2776005] using wordTrace_append hprefix tailTrace_2776005
  have hstable : (prefixWord ++ tailWord_2776005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776005).length < 2 ^ (prefixWord ++ tailWord_2776005).sum := by decide
  have hdescent : baseEnd_2776005 < baseStart_2776005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776012 : List Nat := [2, 2, 1, 4, 1, 1, 3, 2, 7]
def baseStart_2776012 : Nat := 118140960795 + 2776012 * 2 ^ 59
def prefixEnd_2776012 : Nat := 4983230072969 + 3 ^ 40 * 2776012 * 2
def baseEnd_2776012 : Nat := 158380939849899785998151

theorem tailTrace_2776012 : CollatzResearch.WordTrace tailWord_2776012 prefixEnd_2776012 158380939849899785998151 := by
  unfold tailWord_2776012
  simp only [CollatzResearch.WordTrace]
  refine ⟨50624737809495051974637145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67499650412660069299516193 50624737809495051974637145)
  ·
    refine ⟨37968553357121288980977859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50624737809495051974637145 37968553357121288980977859)
    ·
      refine ⟨56952830035681933471466789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37968553357121288980977859 56952830035681933471466789)
      ·
        refine ⟨10678655631690362525900023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56952830035681933471466789 10678655631690362525900023)
        ·
          refine ⟨16017983447535543788850035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10678655631690362525900023 16017983447535543788850035)
          ·
            refine ⟨24026975171303315683275053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16017983447535543788850035 24026975171303315683275053)
            ·
              refine ⟨9010115689238743381228145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24026975171303315683275053 9010115689238743381228145)
              ·
                refine ⟨6757586766929057535921109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9010115689238743381228145 6757586766929057535921109)
                ·
                  refine ⟨158380939849899785998151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6757586766929057535921109 158380939849899785998151)
                  ·
                    rfl

theorem cell23_2776012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 2, 7].length) (baseStart_2776012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776012 prefixEnd_2776012 := by exact prefixLift 2776012
  have htrace : WordTrace (prefixWord ++ tailWord_2776012) baseStart_2776012 baseEnd_2776012 := by
    simpa [prefixWord, tailWord_2776012, baseEnd_2776012] using wordTrace_append hprefix tailTrace_2776012
  have hstable : (prefixWord ++ tailWord_2776012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776012).length < 2 ^ (prefixWord ++ tailWord_2776012).sum := by decide
  have hdescent : baseEnd_2776012 < baseStart_2776012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776039 : List Nat := [1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 3]
def baseStart_2776039 : Nat := 118140960795 + 2776039 * 2 ^ 59
def prefixEnd_2776039 : Nat := 4983230072969 + 3 ^ 40 * 2776039 * 2
def baseEnd_2776039 : Nat := 1425442322626769468345735

theorem tailTrace_2776039 : CollatzResearch.WordTrace tailWord_2776039 prefixEnd_2776039 1425442322626769468345735 := by
  unfold tailWord_2776039
  simp only [CollatzResearch.WordTrace]
  refine ⟨101250460389892287560507171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67500306926594858373671447 101250460389892287560507171)
  ·
    refine ⟨151875690584838431340760757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101250460389892287560507171 151875690584838431340760757)
    ·
      refine ⟨14238345992328602938196321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151875690584838431340760757 14238345992328602938196321)
      ·
        refine ⟨10678759494246452203647241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14238345992328602938196321 10678759494246452203647241)
        ·
          refine ⟨8009069620684839152735431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10678759494246452203647241 8009069620684839152735431)
          ·
            refine ⟨12013604431027258729103147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8009069620684839152735431 12013604431027258729103147)
            ·
              refine ⟨18020406646540888093654721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12013604431027258729103147 18020406646540888093654721)
              ·
                refine ⟨13515304984905666070241041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18020406646540888093654721 13515304984905666070241041)
                ·
                  refine ⟨10136478738679249552680781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13515304984905666070241041 10136478738679249552680781)
                  ·
                    refine ⟨3801179527004718582255293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10136478738679249552680781 3801179527004718582255293)
                    ·
                      refine ⟨1425442322626769468345735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3801179527004718582255293 1425442322626769468345735)
                      ·
                        rfl

theorem cell23_2776039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_2776039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776039 prefixEnd_2776039 := by exact prefixLift 2776039
  have htrace : WordTrace (prefixWord ++ tailWord_2776039) baseStart_2776039 baseEnd_2776039 := by
    simpa [prefixWord, tailWord_2776039, baseEnd_2776039] using wordTrace_append hprefix tailTrace_2776039
  have hstable : (prefixWord ++ tailWord_2776039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776039).length < 2 ^ (prefixWord ++ tailWord_2776039).sum := by decide
  have hdescent : baseEnd_2776039 < baseStart_2776039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776099 : List Nat := [1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 3]
def baseStart_2776099 : Nat := 118140960795 + 2776099 * 2 ^ 59
def prefixEnd_2776099 : Nat := 4983230072969 + 3 ^ 40 * 2776099 * 2
def baseEnd_2776099 : Nat := 1425473131466039233595459

theorem tailTrace_2776099 : CollatzResearch.WordTrace tailWord_2776099 prefixEnd_2776099 1425473131466039233595459 := by
  unfold tailWord_2776099
  simp only [CollatzResearch.WordTrace]
  refine ⟨101252648769674917807691351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67501765846449945205127567 101252648769674917807691351)
  ·
    refine ⟨151878973154512376711537027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101252648769674917807691351 151878973154512376711537027)
    ·
      refine ⟨227818459731768565067305541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151878973154512376711537027 227818459731768565067305541)
      ·
        refine ⟨42715961199706605950119789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 227818459731768565067305541 42715961199706605950119789)
        ·
          refine ⟨16018485449889977231294921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42715961199706605950119789 16018485449889977231294921)
          ·
            refine ⟨12013864087417482923471191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16018485449889977231294921 12013864087417482923471191)
            ·
              refine ⟨18020796131126224385206787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12013864087417482923471191 18020796131126224385206787)
              ·
                refine ⟨27031194196689336577810181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18020796131126224385206787 27031194196689336577810181)
                ·
                  refine ⟨5068348911879250608339409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27031194196689336577810181 5068348911879250608339409)
                  ·
                    refine ⟨3801261683909437956254557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5068348911879250608339409 3801261683909437956254557)
                    ·
                      refine ⟨1425473131466039233595459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3801261683909437956254557 1425473131466039233595459)
                      ·
                        rfl

theorem cell23_2776099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_2776099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776099 prefixEnd_2776099 := by exact prefixLift 2776099
  have htrace : WordTrace (prefixWord ++ tailWord_2776099) baseStart_2776099 baseEnd_2776099 := by
    simpa [prefixWord, tailWord_2776099, baseEnd_2776099] using wordTrace_append hprefix tailTrace_2776099
  have hstable : (prefixWord ++ tailWord_2776099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776099).length < 2 ^ (prefixWord ++ tailWord_2776099).sum := by decide
  have hdescent : baseEnd_2776099 < baseStart_2776099 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776122 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6]
def baseStart_2776122 : Nat := 118140960795 + 2776122 * 2 ^ 59
def prefixEnd_2776122 : Nat := 4983230072969 + 3 ^ 40 * 2776122 * 2
def baseEnd_2776122 : Nat := 1425484941521092643607853

theorem tailTrace_2776122 : CollatzResearch.WordTrace tailWord_2776122 prefixEnd_2776122 1425484941521092643607853 := by
  unfold tailWord_2776122
  simp only [CollatzResearch.WordTrace]
  refine ⟨25313371912147898183944655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67502325099061061823852413 25313371912147898183944655)
  ·
    refine ⟨37970057868221847275916983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25313371912147898183944655 37970057868221847275916983)
    ·
      refine ⟨56955086802332770913875475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37970057868221847275916983 56955086802332770913875475)
      ·
        refine ⟨85432630203499156370813213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56955086802332770913875475 85432630203499156370813213)
        ·
          refine ⟨32037236326312183639054955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85432630203499156370813213 32037236326312183639054955)
          ·
            refine ⟨48055854489468275458582433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32037236326312183639054955 48055854489468275458582433)
            ·
              refine ⟨36041890867101206593936825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48055854489468275458582433 36041890867101206593936825)
              ·
                refine ⟨27031418150325904945452619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36041890867101206593936825 27031418150325904945452619)
                ·
                  refine ⟨40547127225488857418178929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27031418150325904945452619 40547127225488857418178929)
                  ·
                    refine ⟨30410345419116643063634197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40547127225488857418178929 30410345419116643063634197)
                    ·
                      refine ⟨1425484941521092643607853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30410345419116643063634197 1425484941521092643607853)
                      ·
                        rfl

theorem cell23_2776122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 1, 2, 6].length) (baseStart_2776122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776122 prefixEnd_2776122 := by exact prefixLift 2776122
  have htrace : WordTrace (prefixWord ++ tailWord_2776122) baseStart_2776122 baseEnd_2776122 := by
    simpa [prefixWord, tailWord_2776122, baseEnd_2776122] using wordTrace_append hprefix tailTrace_2776122
  have hstable : (prefixWord ++ tailWord_2776122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776122).length < 2 ^ (prefixWord ++ tailWord_2776122).sum := by decide
  have hdescent : baseEnd_2776122 < baseStart_2776122 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776169 : List Nat := [1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 4]
def baseStart_2776169 : Nat := 118140960795 + 2776169 * 2 ^ 59
def prefixEnd_2776169 : Nat := 4983230072969 + 3 ^ 40 * 2776169 * 2
def baseEnd_2776169 : Nat := 1425509075111853959720137

theorem tailTrace_2776169 : CollatzResearch.WordTrace tailWord_2776169 prefixEnd_2776169 1425509075111853959720137 := by
  unfold tailWord_2776169
  simp only [CollatzResearch.WordTrace]
  refine ⟨101255201879421319762739561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67503467919614213175159707 101255201879421319762739561)
  ·
    refine ⟨75941401409565989822054671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101255201879421319762739561 75941401409565989822054671)
    ·
      refine ⟨113912102114348984733082007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75941401409565989822054671 113912102114348984733082007)
      ·
        refine ⟨170868153171523477099623011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113912102114348984733082007 170868153171523477099623011)
        ·
          refine ⟨256302229757285215649434517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170868153171523477099623011 256302229757285215649434517)
          ·
            refine ⟨12014167019872744483567243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 256302229757285215649434517 12014167019872744483567243)
            ·
              refine ⟨18021250529809116725350865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12014167019872744483567243 18021250529809116725350865)
              ·
                refine ⟨13515937897356837544013149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18021250529809116725350865 13515937897356837544013149)
                ·
                  refine ⟨5068476711508814079004931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13515937897356837544013149 5068476711508814079004931)
                  ·
                    refine ⟨7602715067263221118507397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5068476711508814079004931 7602715067263221118507397)
                    ·
                      refine ⟨1425509075111853959720137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7602715067263221118507397 1425509075111853959720137)
                      ·
                        rfl

theorem cell23_2776169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 6, 1, 2, 3, 1, 4].length) (baseStart_2776169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776169 prefixEnd_2776169 := by exact prefixLift 2776169
  have htrace : WordTrace (prefixWord ++ tailWord_2776169) baseStart_2776169 baseEnd_2776169 := by
    simpa [prefixWord, tailWord_2776169, baseEnd_2776169] using wordTrace_append hprefix tailTrace_2776169
  have hstable : (prefixWord ++ tailWord_2776169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776169).length < 2 ^ (prefixWord ++ tailWord_2776169).sum := by decide
  have hdescent : baseEnd_2776169 < baseStart_2776169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776192 : List Nat := [2, 1, 1, 2, 1, 3, 2, 11]
def baseStart_2776192 : Nat := 118140960795 + 2776192 * 2 ^ 59
def prefixEnd_2776192 : Nat := 4983230072969 + 3 ^ 40 * 2776192 * 2
def baseEnd_2776192 : Nat := 52797069820996569249353

theorem tailTrace_2776192 : CollatzResearch.WordTrace tailWord_2776192 prefixEnd_2776192 52797069820996569249353 := by
  unfold tailWord_2776192
  simp only [CollatzResearch.WordTrace]
  refine ⟨50628020379168997345413415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67504027172225329793884553 50628020379168997345413415)
  ·
    refine ⟨75942030568753496018120123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50628020379168997345413415 75942030568753496018120123)
    ·
      refine ⟨113913045853130244027180185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75942030568753496018120123 113913045853130244027180185)
      ·
        refine ⟨85434784389847683020385139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113913045853130244027180185 85434784389847683020385139)
        ·
          refine ⟨128152176584771524530577709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85434784389847683020385139 128152176584771524530577709)
          ·
            refine ⟨48057066219289321698966641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128152176584771524530577709 48057066219289321698966641)
            ·
              refine ⟨36042799664466991274224981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48057066219289321698966641 36042799664466991274224981)
              ·
                refine ⟨52797069820996569249353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 36042799664466991274224981 52797069820996569249353)
                ·
                  rfl

theorem cell23_2776192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 11].length) (baseStart_2776192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776192 prefixEnd_2776192 := by exact prefixLift 2776192
  have htrace : WordTrace (prefixWord ++ tailWord_2776192) baseStart_2776192 baseEnd_2776192 := by
    simpa [prefixWord, tailWord_2776192, baseEnd_2776192] using wordTrace_append hprefix tailTrace_2776192
  have hstable : (prefixWord ++ tailWord_2776192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776192).length < 2 ^ (prefixWord ++ tailWord_2776192).sum := by decide
  have hdescent : baseEnd_2776192 < baseStart_2776192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776200 : List Nat := [2, 1, 3, 4, 2, 2, 2, 1, 1, 5]
def baseStart_2776200 : Nat := 118140960795 + 2776200 * 2 ^ 59
def prefixEnd_2776200 : Nat := 4983230072969 + 3 ^ 40 * 2776200 * 2
def baseEnd_2776200 : Nat := 475174997670714446144165

theorem tailTrace_2776200 : CollatzResearch.WordTrace tailWord_2776200 prefixEnd_2776200 475174997670714446144165 := by
  unfold tailWord_2776200
  simp only [CollatzResearch.WordTrace]
  refine ⟨50628166271154506028559027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67504221694872674704745369 50628166271154506028559027)
  ·
    refine ⟨75942249406731759042838541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50628166271154506028559027 75942249406731759042838541)
    ·
      refine ⟨28478343527524409641064453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75942249406731759042838541 28478343527524409641064453)
      ·
        refine ⟨5339689411410826807699585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28478343527524409641064453 5339689411410826807699585)
        ·
          refine ⟨4004767058558120105774689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5339689411410826807699585 4004767058558120105774689)
          ·
            refine ⟨3003575293918590079331017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4004767058558120105774689 3003575293918590079331017)
            ·
              refine ⟨2252681470438942559498263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3003575293918590079331017 2252681470438942559498263)
              ·
                refine ⟨3379022205658413839247395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252681470438942559498263 3379022205658413839247395)
                ·
                  refine ⟨5068533308487620758871093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379022205658413839247395 5068533308487620758871093)
                  ·
                    refine ⟨475174997670714446144165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5068533308487620758871093 475174997670714446144165)
                    ·
                      rfl

theorem cell23_2776200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 2, 1, 1, 5].length) (baseStart_2776200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776200 prefixEnd_2776200 := by exact prefixLift 2776200
  have htrace : WordTrace (prefixWord ++ tailWord_2776200) baseStart_2776200 baseEnd_2776200 := by
    simpa [prefixWord, tailWord_2776200, baseEnd_2776200] using wordTrace_append hprefix tailTrace_2776200
  have hstable : (prefixWord ++ tailWord_2776200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776200).length < 2 ^ (prefixWord ++ tailWord_2776200).sum := by decide
  have hdescent : baseEnd_2776200 < baseStart_2776200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776220 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 3, 2, 2]
def baseStart_2776220 : Nat := 118140960795 + 2776220 * 2 ^ 59
def prefixEnd_2776220 : Nat := 4983230072969 + 3 ^ 40 * 2776220 * 2
def baseEnd_2776220 : Nat := 1425535262625233260182403

theorem tailTrace_2776220 : CollatzResearch.WordTrace tailWord_2776220 prefixEnd_2776220 1425535262625233260182403 := by
  unfold tailWord_2776220
  simp only [CollatzResearch.WordTrace]
  refine ⟨50628531001118277736423057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67504708001491036981897409 50628531001118277736423057)
  ·
    refine ⟨37971398250838708302317293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50628531001118277736423057 37971398250838708302317293)
    ·
      refine ⟨14239274344064515613368985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37971398250838708302317293 14239274344064515613368985)
      ·
        refine ⟨10679455758048386710026739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14239274344064515613368985 10679455758048386710026739)
        ·
          refine ⟨16019183637072580065040109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10679455758048386710026739 16019183637072580065040109)
          ·
            refine ⟨6007193863902217524390041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16019183637072580065040109 6007193863902217524390041)
            ·
              refine ⟨4505395397926663143292531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6007193863902217524390041 4505395397926663143292531)
              ·
                refine ⟨6758093096889994714938797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4505395397926663143292531 6758093096889994714938797)
                ·
                  refine ⟨2534284911333748018102049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6758093096889994714938797 2534284911333748018102049)
                  ·
                    refine ⟨1900713683500311013576537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2534284911333748018102049 1900713683500311013576537)
                    ·
                      refine ⟨1425535262625233260182403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900713683500311013576537 1425535262625233260182403)
                      ·
                        rfl

theorem cell23_2776220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_2776220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776220 prefixEnd_2776220 := by exact prefixLift 2776220
  have htrace : WordTrace (prefixWord ++ tailWord_2776220) baseStart_2776220 baseEnd_2776220 := by
    simpa [prefixWord, tailWord_2776220, baseEnd_2776220] using wordTrace_append hprefix tailTrace_2776220
  have hstable : (prefixWord ++ tailWord_2776220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776220).length < 2 ^ (prefixWord ++ tailWord_2776220).sum := by decide
  have hdescent : baseEnd_2776220 < baseStart_2776220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776249 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 5]
def baseStart_2776249 : Nat := 118140960795 + 2776249 * 2 ^ 59
def prefixEnd_2776249 : Nat := 4983230072969 + 3 ^ 40 * 2776249 * 2
def baseEnd_2776249 : Nat := 1425550153564213646719769

theorem tailTrace_2776249 : CollatzResearch.WordTrace tailWord_2776249 prefixEnd_2776249 1425550153564213646719769 := by
  unfold tailWord_2776249
  simp only [CollatzResearch.WordTrace]
  refine ⟨101258119719131493425651801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67505413146087662283767867 101258119719131493425651801)
  ·
    refine ⟨75943589789348620069238851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101258119719131493425651801 75943589789348620069238851)
    ·
      refine ⟨113915384684022930103858277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75943589789348620069238851 113915384684022930103858277)
      ·
        refine ⟨21359134628254299394473427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113915384684022930103858277 21359134628254299394473427)
        ·
          refine ⟨32038701942381449091710141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21359134628254299394473427 32038701942381449091710141)
          ·
            refine ⟨12014513228393043409391303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32038701942381449091710141 12014513228393043409391303)
            ·
              refine ⟨18021769842589565114086955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12014513228393043409391303 18021769842589565114086955)
              ·
                refine ⟨27032654763884347671130433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18021769842589565114086955 27032654763884347671130433)
                ·
                  refine ⟨20274491072913260753347825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27032654763884347671130433 20274491072913260753347825)
                  ·
                    refine ⟨15205868304684945565010869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20274491072913260753347825 15205868304684945565010869)
                    ·
                      refine ⟨1425550153564213646719769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15205868304684945565010869 1425550153564213646719769)
                      ·
                        rfl

theorem cell23_2776249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 2, 2, 5].length) (baseStart_2776249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776249 prefixEnd_2776249 := by exact prefixLift 2776249
  have htrace : WordTrace (prefixWord ++ tailWord_2776249) baseStart_2776249 baseEnd_2776249 := by
    simpa [prefixWord, tailWord_2776249, baseEnd_2776249] using wordTrace_append hprefix tailTrace_2776249
  have hstable : (prefixWord ++ tailWord_2776249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776249).length < 2 ^ (prefixWord ++ tailWord_2776249).sum := by decide
  have hdescent : baseEnd_2776249 < baseStart_2776249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776254 : List Nat := [4, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2]
def baseStart_2776254 : Nat := 118140960795 + 2776254 * 2 ^ 59
def prefixEnd_2776254 : Nat := 4983230072969 + 3 ^ 40 * 2776254 * 2
def baseEnd_2776254 : Nat := 1425552720967486127157247

theorem tailTrace_2776254 : CollatzResearch.WordTrace tailWord_2776254 prefixEnd_2776254 1425552720967486127157247 := by
  unfold tailWord_2776254
  simp only [CollatzResearch.WordTrace]
  refine ⟨12657287760514172409947977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67505534722742252853055877 12657287760514172409947977)
  ·
    refine ⟨9492965820385629307460983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12657287760514172409947977 9492965820385629307460983)
    ·
      refine ⟨14239448730578443961191475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9492965820385629307460983 14239448730578443961191475)
      ·
        refine ⟨21359173095867665941787213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14239448730578443961191475 21359173095867665941787213)
        ·
          refine ⟨8009689910950374728170205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21359173095867665941787213 8009689910950374728170205)
          ·
            refine ⟨3003633716606390523063827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8009689910950374728170205 3003633716606390523063827)
            ·
              refine ⟨4505450574909585784595741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3003633716606390523063827 4505450574909585784595741)
              ·
                refine ⟨1689543965591094669223403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4505450574909585784595741 1689543965591094669223403)
                ·
                  refine ⟨2534315948386642003835105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689543965591094669223403 2534315948386642003835105)
                  ·
                    refine ⟨1900736961289981502876329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2534315948386642003835105 1900736961289981502876329)
                    ·
                      refine ⟨1425552720967486127157247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900736961289981502876329 1425552720967486127157247)
                      ·
                        rfl

theorem cell23_2776254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2].length) (baseStart_2776254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776254 prefixEnd_2776254 := by exact prefixLift 2776254
  have htrace : WordTrace (prefixWord ++ tailWord_2776254) baseStart_2776254 baseEnd_2776254 := by
    simpa [prefixWord, tailWord_2776254, baseEnd_2776254] using wordTrace_append hprefix tailTrace_2776254
  have hstable : (prefixWord ++ tailWord_2776254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776254).length < 2 ^ (prefixWord ++ tailWord_2776254).sum := by decide
  have hdescent : baseEnd_2776254 < baseStart_2776254 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776350 : List Nat := [4, 3, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2776350 : Nat := 118140960795 + 2776350 * 2 ^ 59
def prefixEnd_2776350 : Nat := 4983230072969 + 3 ^ 40 * 2776350 * 2
def baseEnd_2776350 : Nat := 158400223901146416839645

theorem tailTrace_2776350 : CollatzResearch.WordTrace tailWord_2776350 prefixEnd_2776350 158400223901146416839645 := by
  unfold tailWord_2776350
  simp only [CollatzResearch.WordTrace]
  refine ⟨12657725436470698459384813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67507868994510391783385669 12657725436470698459384813)
  ·
    refine ⟨4746647038676511922269305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12657725436470698459384813 4746647038676511922269305)
    ·
      refine ⟨3559985279007383941701979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4746647038676511922269305 3559985279007383941701979)
      ·
        refine ⟨5339977918511075912552969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3559985279007383941701979 5339977918511075912552969)
        ·
          refine ⟨4004983438883306934414727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5339977918511075912552969 4004983438883306934414727)
          ·
            refine ⟨6007475158324960401622091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4004983438883306934414727 6007475158324960401622091)
            ·
              refine ⟨9011212737487440602433137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007475158324960401622091 9011212737487440602433137)
              ·
                refine ⟨6758409553115580451824853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9011212737487440602433137 6758409553115580451824853)
                ·
                  refine ⟨158400223901146416839645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6758409553115580451824853 158400223901146416839645)
                  ·
                    rfl

theorem cell23_2776350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2776350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776350 prefixEnd_2776350 := by exact prefixLift 2776350
  have htrace : WordTrace (prefixWord ++ tailWord_2776350) baseStart_2776350 baseEnd_2776350 := by
    simpa [prefixWord, tailWord_2776350, baseEnd_2776350] using wordTrace_append hprefix tailTrace_2776350
  have hstable : (prefixWord ++ tailWord_2776350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776350).length < 2 ^ (prefixWord ++ tailWord_2776350).sum := by decide
  have hdescent : baseEnd_2776350 < baseStart_2776350 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776376 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 7, 4]
def baseStart_2776376 : Nat := 118140960795 + 2776376 * 2 ^ 59
def prefixEnd_2776376 : Nat := 4983230072969 + 3 ^ 40 * 2776376 * 2
def baseEnd_2776376 : Nat := 475205121869111549943895

theorem tailTrace_2776376 : CollatzResearch.WordTrace tailWord_2776376 prefixEnd_2776376 475205121869111549943895 := by
  unfold tailWord_2776376
  simp only [CollatzResearch.WordTrace]
  refine ⟨50631375894835697057762491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67508501193114262743683321 50631375894835697057762491)
  ·
    refine ⟨75947063842253545586643737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50631375894835697057762491 75947063842253545586643737)
    ·
      refine ⟨56960297881690159189982803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75947063842253545586643737 56960297881690159189982803)
      ·
        refine ⟨85440446822535238784974205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56960297881690159189982803 85440446822535238784974205)
        ·
          refine ⟨32040167558450714544365327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85440446822535238784974205 32040167558450714544365327)
          ·
            refine ⟨48060251337676071816547991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32040167558450714544365327 48060251337676071816547991)
            ·
              refine ⟨72090377006514107724821987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48060251337676071816547991 72090377006514107724821987)
              ·
                refine ⟨108135565509771161587232981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72090377006514107724821987 108135565509771161587232981)
                ·
                  refine ⟨2534427316635261599700773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 108135565509771161587232981 2534427316635261599700773)
                  ·
                    refine ⟨475205121869111549943895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2534427316635261599700773 475205121869111549943895)
                    ·
                      rfl

theorem cell23_2776376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 7, 4].length) (baseStart_2776376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776376 prefixEnd_2776376 := by exact prefixLift 2776376
  have htrace : WordTrace (prefixWord ++ tailWord_2776376) baseStart_2776376 baseEnd_2776376 := by
    simpa [prefixWord, tailWord_2776376, baseEnd_2776376] using wordTrace_append hprefix tailTrace_2776376
  have hstable : (prefixWord ++ tailWord_2776376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776376).length < 2 ^ (prefixWord ++ tailWord_2776376).sum := by decide
  have hdescent : baseEnd_2776376 < baseStart_2776376 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776383 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 2, 4, 2]
def baseStart_2776383 : Nat := 118140960795 + 2776383 * 2 ^ 59
def prefixEnd_2776383 : Nat := 4983230072969 + 3 ^ 40 * 2776383 * 2
def baseEnd_2776383 : Nat := 1425618959971916122444153

theorem tailTrace_2776383 : CollatzResearch.WordTrace tailWord_2776383 prefixEnd_2776383 1425618959971916122444153 := by
  unfold tailWord_2776383
  simp only [CollatzResearch.WordTrace]
  refine ⟨101263007100646034311029803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67508671400430689540686535 101263007100646034311029803)
  ·
    refine ⟨151894510650969051466544705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101263007100646034311029803 151894510650969051466544705)
    ·
      refine ⟨113920882988226788599908529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151894510650969051466544705 113920882988226788599908529)
      ·
        refine ⟨85440662241170091449931397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113920882988226788599908529 85440662241170091449931397)
        ·
          refine ⟨16020124170219392146862137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85440662241170091449931397 16020124170219392146862137)
          ·
            refine ⟨12015093127664544110146603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16020124170219392146862137 12015093127664544110146603)
            ·
              refine ⟨18022639691496816165219905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12015093127664544110146603 18022639691496816165219905)
              ·
                refine ⟨13516979768622612123914929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18022639691496816165219905 13516979768622612123914929)
                ·
                  refine ⟨10137734826466959092936197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13516979768622612123914929 10137734826466959092936197)
                  ·
                    refine ⟨1900825279962554829925537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10137734826466959092936197 1900825279962554829925537)
                    ·
                      refine ⟨1425618959971916122444153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900825279962554829925537 1425618959971916122444153)
                      ·
                        rfl

theorem cell23_2776383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 2, 4, 2].length) (baseStart_2776383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776383 prefixEnd_2776383 := by exact prefixLift 2776383
  have htrace : WordTrace (prefixWord ++ tailWord_2776383) baseStart_2776383 baseEnd_2776383 := by
    simpa [prefixWord, tailWord_2776383, baseEnd_2776383] using wordTrace_append hprefix tailTrace_2776383
  have hstable : (prefixWord ++ tailWord_2776383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776383).length < 2 ^ (prefixWord ++ tailWord_2776383).sum := by decide
  have hdescent : baseEnd_2776383 < baseStart_2776383 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776399 : List Nat := [1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 9]
def baseStart_2776399 : Nat := 118140960795 + 2776399 * 2 ^ 59
def prefixEnd_2776399 : Nat := 4983230072969 + 3 ^ 40 * 2776399 * 2
def baseEnd_2776399 : Nat := 1425627175662388059844079

theorem tailTrace_2776399 : CollatzResearch.WordTrace tailWord_2776399 prefixEnd_2776399 1425627175662388059844079 := by
  unfold tailWord_2776399
  simp only [CollatzResearch.WordTrace]
  refine ⟨101263590668588069043612251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67509060445725379362408167 101263590668588069043612251)
  ·
    refine ⟨151895386002882103565418377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101263590668588069043612251 151895386002882103565418377)
    ·
      refine ⟨113921539502161577674063783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151895386002882103565418377 113921539502161577674063783)
      ·
        refine ⟨170882309253242366511095675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113921539502161577674063783 170882309253242366511095675)
        ·
          refine ⟨256323463879863549766643513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170882309253242366511095675 256323463879863549766643513)
          ·
            refine ⟨192242597909897662324982635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256323463879863549766643513 192242597909897662324982635)
            ·
              refine ⟨288363896864846493487473953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192242597909897662324982635 288363896864846493487473953)
              ·
                refine ⟨216272922648634870115605465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 288363896864846493487473953 216272922648634870115605465)
                ·
                  refine ⟨162204691986476152586704099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 216272922648634870115605465 162204691986476152586704099)
                  ·
                    refine ⟨243307037979714228880056149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162204691986476152586704099 243307037979714228880056149)
                    ·
                      refine ⟨1425627175662388059844079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 243307037979714228880056149 1425627175662388059844079)
                      ·
                        rfl

theorem cell23_2776399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_2776399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776399 prefixEnd_2776399 := by exact prefixLift 2776399
  have htrace : WordTrace (prefixWord ++ tailWord_2776399) baseStart_2776399 baseEnd_2776399 := by
    simpa [prefixWord, tailWord_2776399, baseEnd_2776399] using wordTrace_append hprefix tailTrace_2776399
  have hstable : (prefixWord ++ tailWord_2776399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776399).length < 2 ^ (prefixWord ++ tailWord_2776399).sum := by decide
  have hdescent : baseEnd_2776399 < baseStart_2776399 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776433 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 3]
def baseStart_2776433 : Nat := 118140960795 + 2776433 * 2 ^ 59
def prefixEnd_2776433 : Nat := 4983230072969 + 3 ^ 40 * 2776433 * 2
def baseEnd_2776433 : Nat := 1425644634004640926818923

theorem tailTrace_2776433 : CollatzResearch.WordTrace tailWord_2776433 prefixEnd_2776433 1425644634004640926818923 := by
  unfold tailWord_2776433
  simp only [CollatzResearch.WordTrace]
  refine ⟨101264830750464892850349953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67509887166976595233566635 101264830750464892850349953)
  ·
    refine ⟨75948623062848669637762465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101264830750464892850349953 75948623062848669637762465)
    ·
      refine ⟨56961467297136502228321849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75948623062848669637762465 56961467297136502228321849)
      ·
        refine ⟨42721100472852376671241387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56961467297136502228321849 42721100472852376671241387)
        ·
          refine ⟨64081650709278565006862081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42721100472852376671241387 64081650709278565006862081)
          ·
            refine ⟨48061238031958923755146561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64081650709278565006862081 48061238031958923755146561)
            ·
              refine ⟨36045928523969192816359921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48061238031958923755146561 36045928523969192816359921)
              ·
                refine ⟨27034446392976894612269941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36045928523969192816359921 27034446392976894612269941)
                ·
                  refine ⟨2534479349341583869900307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27034446392976894612269941 2534479349341583869900307)
                  ·
                    refine ⟨3801719024012375804850461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2534479349341583869900307 3801719024012375804850461)
                    ·
                      refine ⟨1425644634004640926818923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3801719024012375804850461 1425644634004640926818923)
                      ·
                        rfl

theorem cell23_2776433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_2776433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776433 prefixEnd_2776433 := by exact prefixLift 2776433
  have htrace : WordTrace (prefixWord ++ tailWord_2776433) baseStart_2776433 baseEnd_2776433 := by
    simpa [prefixWord, tailWord_2776433, baseEnd_2776433] using wordTrace_append hprefix tailTrace_2776433
  have hstable : (prefixWord ++ tailWord_2776433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776433).length < 2 ^ (prefixWord ++ tailWord_2776433).sum := by decide
  have hdescent : baseEnd_2776433 < baseStart_2776433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776457 : List Nat := [1, 2, 1, 1, 8, 1, 2, 1, 6]
def baseStart_2776457 : Nat := 118140960795 + 2776457 * 2 ^ 59
def prefixEnd_2776457 : Nat := 4983230072969 + 3 ^ 40 * 2776457 * 2
def baseEnd_2776457 : Nat := 158406328615594314768757

theorem tailTrace_2776457 : CollatzResearch.WordTrace tailWord_2776457 prefixEnd_2776457 158406328615594314768757 := by
  unfold tailWord_2776457
  simp only [CollatzResearch.WordTrace]
  refine ⟨101265706102377944949223625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67510470734918629966149083 101265706102377944949223625)
  ·
    refine ⟨75949279576783458711917719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101265706102377944949223625 75949279576783458711917719)
    ·
      refine ⟨113923919365175188067876579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75949279576783458711917719 113923919365175188067876579)
      ·
        refine ⟨170885879047762782101814869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113923919365175188067876579 170885879047762782101814869)
        ·
          refine ⟨2002568895090970102755643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 170885879047762782101814869 2002568895090970102755643)
          ·
            refine ⟨3003853342636455154133465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2002568895090970102755643 3003853342636455154133465)
            ·
              refine ⟨2252890006977341365600099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3003853342636455154133465 2252890006977341365600099)
              ·
                refine ⟨3379335010466012048400149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2252890006977341365600099 3379335010466012048400149)
                ·
                  refine ⟨158406328615594314768757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3379335010466012048400149 158406328615594314768757)
                  ·
                    rfl

theorem cell23_2776457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 1, 6].length) (baseStart_2776457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776457 prefixEnd_2776457 := by exact prefixLift 2776457
  have htrace : WordTrace (prefixWord ++ tailWord_2776457) baseStart_2776457 baseEnd_2776457 := by
    simpa [prefixWord, tailWord_2776457, baseEnd_2776457] using wordTrace_append hprefix tailTrace_2776457
  have hstable : (prefixWord ++ tailWord_2776457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776457).length < 2 ^ (prefixWord ++ tailWord_2776457).sum := by decide
  have hdescent : baseEnd_2776457 < baseStart_2776457 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776473 : List Nat := [1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 4]
def baseStart_2776473 : Nat := 118140960795 + 2776473 * 2 ^ 59
def prefixEnd_2776473 : Nat := 4983230072969 + 3 ^ 40 * 2776473 * 2
def baseEnd_2776473 : Nat := 1425665173230820770318739

theorem tailTrace_2776473 : CollatzResearch.WordTrace tailWord_2776473 prefixEnd_2776473 1425665173230820770318739 := by
  unfold tailWord_2776473
  simp only [CollatzResearch.WordTrace]
  refine ⟨101266289670319979681806073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67510859780213319787870715 101266289670319979681806073)
  ·
    refine ⟨75949717252739984761354555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101266289670319979681806073 75949717252739984761354555)
    ·
      refine ⟨113924575879109977142031833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75949717252739984761354555 113924575879109977142031833)
      ·
        refine ⟨85443431909332482856523875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113924575879109977142031833 85443431909332482856523875)
        ·
          refine ⟨128165147863998724284785813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85443431909332482856523875 128165147863998724284785813)
          ·
            refine ⟨6007741306124940200849335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128165147863998724284785813 6007741306124940200849335)
            ·
              refine ⟨9011611959187410301274003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6007741306124940200849335 9011611959187410301274003)
              ·
                refine ⟨13517417938781115451911005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011611959187410301274003 13517417938781115451911005)
                ·
                  refine ⟨5069031727042918294466627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13517417938781115451911005 5069031727042918294466627)
                  ·
                    refine ⟨7603547590564377441699941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069031727042918294466627 7603547590564377441699941)
                    ·
                      refine ⟨1425665173230820770318739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7603547590564377441699941 1425665173230820770318739)
                      ·
                        rfl

theorem cell23_2776473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 6, 1, 1, 3, 1, 4].length) (baseStart_2776473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776473 prefixEnd_2776473 := by exact prefixLift 2776473
  have htrace : WordTrace (prefixWord ++ tailWord_2776473) baseStart_2776473 baseEnd_2776473 := by
    simpa [prefixWord, tailWord_2776473, baseEnd_2776473] using wordTrace_append hprefix tailTrace_2776473
  have hstable : (prefixWord ++ tailWord_2776473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776473).length < 2 ^ (prefixWord ++ tailWord_2776473).sum := by decide
  have hdescent : baseEnd_2776473 < baseStart_2776473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776477 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 2, 3, 2]
def baseStart_2776477 : Nat := 118140960795 + 2776477 * 2 ^ 59
def prefixEnd_2776477 : Nat := 4983230072969 + 3 ^ 40 * 2776477 * 2
def baseEnd_2776477 : Nat := 1425667227153438754668721

theorem tailTrace_2776477 : CollatzResearch.WordTrace tailWord_2776477 prefixEnd_2776477 1425667227153438754668721 := by
  unfold tailWord_2776477
  simp only [CollatzResearch.WordTrace]
  refine ⟨101266435562305488364951685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67510957041536992243301123 101266435562305488364951685)
  ·
    refine ⟨18987456667932279068428441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101266435562305488364951685 18987456667932279068428441)
    ·
      refine ⟨14240592500949209301321331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18987456667932279068428441 14240592500949209301321331)
      ·
        refine ⟨21360888751423813951981997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14240592500949209301321331 21360888751423813951981997)
        ·
          refine ⟨8010333281783930231993249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21360888751423813951981997 8010333281783930231993249)
          ·
            refine ⟨6007749961337947673994937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8010333281783930231993249 6007749961337947673994937)
            ·
              refine ⟨4505812471003460755496203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6007749961337947673994937 4505812471003460755496203)
              ·
                refine ⟨6758718706505191133244305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4505812471003460755496203 6758718706505191133244305)
                ·
                  refine ⟨5069039029878893349933229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6758718706505191133244305 5069039029878893349933229)
                  ·
                    refine ⟨1900889636204585006224961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5069039029878893349933229 1900889636204585006224961)
                    ·
                      refine ⟨1425667227153438754668721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900889636204585006224961 1425667227153438754668721)
                      ·
                        rfl

theorem cell23_2776477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 2, 3, 2].length) (baseStart_2776477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776477 prefixEnd_2776477 := by exact prefixLift 2776477
  have htrace : WordTrace (prefixWord ++ tailWord_2776477) baseStart_2776477 baseEnd_2776477 := by
    simpa [prefixWord, tailWord_2776477, baseEnd_2776477] using wordTrace_append hprefix tailTrace_2776477
  have hstable : (prefixWord ++ tailWord_2776477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776477).length < 2 ^ (prefixWord ++ tailWord_2776477).sum := by decide
  have hdescent : baseEnd_2776477 < baseStart_2776477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776501 : List Nat := [1, 3, 3, 2, 2, 3, 2, 2, 1, 1, 3]
def baseStart_2776501 : Nat := 118140960795 + 2776501 * 2 ^ 59
def prefixEnd_2776501 : Nat := 4983230072969 + 3 ^ 40 * 2776501 * 2
def baseEnd_2776501 : Nat := 1425679550689146660768611

theorem tailTrace_2776501 : CollatzResearch.WordTrace tailWord_2776501 prefixEnd_2776501 1425679550689146660768611 := by
  unfold tailWord_2776501
  simp only [CollatzResearch.WordTrace]
  refine ⟨101267310914218540463825357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67511540609479026975883571 101267310914218540463825357)
  ·
    refine ⟨37975241592831952673934509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101267310914218540463825357 37975241592831952673934509)
    ·
      refine ⟨14240715597311982252725441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37975241592831952673934509 14240715597311982252725441)
      ·
        refine ⟨10680536697983986689544081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14240715597311982252725441 10680536697983986689544081)
        ·
          refine ⟨8010402523487990017158061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10680536697983986689544081 8010402523487990017158061)
          ·
            refine ⟨3003900946307996256434273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8010402523487990017158061 3003900946307996256434273)
            ·
              refine ⟨2252925709730997192325705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3003900946307996256434273 2252925709730997192325705)
              ·
                refine ⟨1689694282298247894244279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2252925709730997192325705 1689694282298247894244279)
                ·
                  refine ⟨2534541423447371841366419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689694282298247894244279 2534541423447371841366419)
                  ·
                    refine ⟨3801812135171057762049629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2534541423447371841366419 3801812135171057762049629)
                    ·
                      refine ⟨1425679550689146660768611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3801812135171057762049629 1425679550689146660768611)
                      ·
                        rfl

theorem cell23_2776501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 1, 1, 3].length) (baseStart_2776501 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776501 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776501 prefixEnd_2776501 := by exact prefixLift 2776501
  have htrace : WordTrace (prefixWord ++ tailWord_2776501) baseStart_2776501 baseEnd_2776501 := by
    simpa [prefixWord, tailWord_2776501, baseEnd_2776501] using wordTrace_append hprefix tailTrace_2776501
  have hstable : (prefixWord ++ tailWord_2776501).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776501).length < 2 ^ (prefixWord ++ tailWord_2776501).sum := by decide
  have hdescent : baseEnd_2776501 < baseStart_2776501 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776523 : List Nat := [1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3]
def baseStart_2776523 : Nat := 118140960795 + 2776523 * 2 ^ 59
def prefixEnd_2776523 : Nat := 4983230072969 + 3 ^ 40 * 2776523 * 2
def baseEnd_2776523 : Nat := 1425690847263545574693509

theorem tailTrace_2776523 : CollatzResearch.WordTrace tailWord_2776523 prefixEnd_2776523 1425690847263545574693509 := by
  unfold tailWord_2776523
  simp only [CollatzResearch.WordTrace]
  refine ⟨101268113320138838221126223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67512075546759225480750815 101268113320138838221126223)
  ·
    refine ⟨151902169980208257331689335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101268113320138838221126223 151902169980208257331689335)
    ·
      refine ⟨227853254970312385997534003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151902169980208257331689335 227853254970312385997534003)
      ·
        refine ⟨341779882455468578996301005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227853254970312385997534003 341779882455468578996301005)
        ·
          refine ⟨128167455920800717123612877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341779882455468578996301005 128167455920800717123612877)
          ·
            refine ⟨48062795970300268921354829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128167455920800717123612877 48062795970300268921354829)
            ·
              refine ⟨18023548488862600845508061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48062795970300268921354829 18023548488862600845508061)
              ·
                refine ⟨6758830683323475317065523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18023548488862600845508061 6758830683323475317065523)
                ·
                  refine ⟨10138246024985212975598285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6758830683323475317065523 10138246024985212975598285)
                  ·
                    refine ⟨3801842259369454865849357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10138246024985212975598285 3801842259369454865849357)
                    ·
                      refine ⟨1425690847263545574693509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3801842259369454865849357 1425690847263545574693509)
                      ·
                        rfl

theorem cell23_2776523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 1, 3, 3].length) (baseStart_2776523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776523 prefixEnd_2776523 := by exact prefixLift 2776523
  have htrace : WordTrace (prefixWord ++ tailWord_2776523) baseStart_2776523 baseEnd_2776523 := by
    simpa [prefixWord, tailWord_2776523, baseEnd_2776523] using wordTrace_append hprefix tailTrace_2776523
  have hstable : (prefixWord ++ tailWord_2776523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776523).length < 2 ^ (prefixWord ++ tailWord_2776523).sum := by decide
  have hdescent : baseEnd_2776523 < baseStart_2776523 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776541 : List Nat := [1, 4, 3, 1, 1, 3, 2, 3, 1, 2, 2]
def baseStart_2776541 : Nat := 118140960795 + 2776541 * 2 ^ 59
def prefixEnd_2776541 : Nat := 4983230072969 + 3 ^ 40 * 2776541 * 2
def baseEnd_2776541 : Nat := 1425700089915326504268427

theorem tailTrace_2776541 : CollatzResearch.WordTrace tailWord_2776541 prefixEnd_2776541 1425700089915326504268427 := by
  unfold tailWord_2776541
  simp only [CollatzResearch.WordTrace]
  refine ⟨101268769834073627295281477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67512513222715751530187651 101268769834073627295281477)
  ·
    refine ⟨18987894343888805117865277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101268769834073627295281477 18987894343888805117865277)
    ·
      refine ⟨7120460378958301919199479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18987894343888805117865277 7120460378958301919199479)
      ·
        refine ⟨10680690568437452878799219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7120460378958301919199479 10680690568437452878799219)
        ·
          refine ⟨16021035852656179318198829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10680690568437452878799219 16021035852656179318198829)
          ·
            refine ⟨6007888444746067244324561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16021035852656179318198829 6007888444746067244324561)
            ·
              refine ⟨4505916333559550433243421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6007888444746067244324561 4505916333559550433243421)
              ·
                refine ⟨1689718625084831412466283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4505916333559550433243421 1689718625084831412466283)
                ·
                  refine ⟨2534577937627247118699425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689718625084831412466283 2534577937627247118699425)
                  ·
                    refine ⟨1900933453220435339024569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2534577937627247118699425 1900933453220435339024569)
                    ·
                      refine ⟨1425700089915326504268427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900933453220435339024569 1425700089915326504268427)
                      ·
                        rfl

theorem cell23_2776541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 3, 1, 2, 2].length) (baseStart_2776541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776541 prefixEnd_2776541 := by exact prefixLift 2776541
  have htrace : WordTrace (prefixWord ++ tailWord_2776541) baseStart_2776541 baseEnd_2776541 := by
    simpa [prefixWord, tailWord_2776541, baseEnd_2776541] using wordTrace_append hprefix tailTrace_2776541
  have hstable : (prefixWord ++ tailWord_2776541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776541).length < 2 ^ (prefixWord ++ tailWord_2776541).sum := by decide
  have hdescent : baseEnd_2776541 < baseStart_2776541 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776573 : List Nat := [1, 4, 1, 1, 1, 4, 2, 1, 2, 6]
def baseStart_2776573 : Nat := 118140960795 + 2776573 * 2 ^ 59
def prefixEnd_2776573 : Nat := 4983230072969 + 3 ^ 40 * 2776573 * 2
def baseEnd_2776573 : Nat := 475238840432090126356093

theorem tailTrace_2776573 : CollatzResearch.WordTrace tailWord_2776573 prefixEnd_2776573 475238840432090126356093 := by
  unfold tailWord_2776573
  simp only [CollatzResearch.WordTrace]
  refine ⟨101269936969957696760446373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67513291313305131173630915 101269936969957696760446373)
  ·
    refine ⟨18988113181867068142583695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101269936969957696760446373 18988113181867068142583695)
    ·
      refine ⟨28482169772800602213875543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18988113181867068142583695 28482169772800602213875543)
      ·
        refine ⟨42723254659200903320813315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28482169772800602213875543 42723254659200903320813315)
        ·
          refine ⟨64084881988801354981219973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42723254659200903320813315 64084881988801354981219973)
          ·
            refine ⟨12015915372900254058978745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64084881988801354981219973 12015915372900254058978745)
            ·
              refine ⟨9011936529675190544234059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12015915372900254058978745 9011936529675190544234059)
              ·
                refine ⟨13517904794512785816351089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9011936529675190544234059 13517904794512785816351089)
                ·
                  refine ⟨10138428595884589362263317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13517904794512785816351089 10138428595884589362263317)
                  ·
                    refine ⟨475238840432090126356093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10138428595884589362263317 475238840432090126356093)
                    ·
                      rfl

theorem cell23_2776573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 1, 2, 6].length) (baseStart_2776573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776573 prefixEnd_2776573 := by exact prefixLift 2776573
  have htrace : WordTrace (prefixWord ++ tailWord_2776573) baseStart_2776573 baseEnd_2776573 := by
    simpa [prefixWord, tailWord_2776573, baseEnd_2776573] using wordTrace_append hprefix tailTrace_2776573
  have hstable : (prefixWord ++ tailWord_2776573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776573).length < 2 ^ (prefixWord ++ tailWord_2776573).sum := by decide
  have hdescent : baseEnd_2776573 < baseStart_2776573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776576 : List Nat := [2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10]
def baseStart_2776576 : Nat := 118140960795 + 2776576 * 2 ^ 59
def prefixEnd_2776576 : Nat := 4983230072969 + 3 ^ 40 * 2776576 * 2
def baseEnd_2776576 : Nat := 1425718061738233867330765

theorem tailTrace_2776576 : CollatzResearch.WordTrace tailWord_2776576 prefixEnd_2776576 1425718061738233867330765 := by
  unfold tailWord_2776576
  simp only [CollatzResearch.WordTrace]
  refine ⟨50635023194473414136402791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67513364259297885515203721 50635023194473414136402791)
  ·
    refine ⟨75952534791710121204604187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50635023194473414136402791 75952534791710121204604187)
    ·
      refine ⟨113928802187565181806906281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75952534791710121204604187 113928802187565181806906281)
      ·
        refine ⟨85446601640673886355179711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113928802187565181806906281 85446601640673886355179711)
        ·
          refine ⟨128169902461010829532769567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85446601640673886355179711 128169902461010829532769567)
          ·
            refine ⟨192254853691516244299154351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128169902461010829532769567 192254853691516244299154351)
            ·
              refine ⟨288382280537274366448731527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192254853691516244299154351 288382280537274366448731527)
              ·
                refine ⟨432573420805911549673097291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288382280537274366448731527 432573420805911549673097291)
                ·
                  refine ⟨648860131208867324509645937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 432573420805911549673097291 648860131208867324509645937)
                  ·
                    refine ⟨486645098406650493382234453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 648860131208867324509645937 486645098406650493382234453)
                    ·
                      refine ⟨1425718061738233867330765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 486645098406650493382234453 1425718061738233867330765)
                      ·
                        rfl

theorem cell23_2776576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 10].length) (baseStart_2776576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776576 prefixEnd_2776576 := by exact prefixLift 2776576
  have htrace : WordTrace (prefixWord ++ tailWord_2776576) baseStart_2776576 baseEnd_2776576 := by
    simpa [prefixWord, tailWord_2776576, baseEnd_2776576] using wordTrace_append hprefix tailTrace_2776576
  have hstable : (prefixWord ++ tailWord_2776576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776576).length < 2 ^ (prefixWord ++ tailWord_2776576).sum := by decide
  have hdescent : baseEnd_2776576 < baseStart_2776576 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776597 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 4, 2, 2]
def baseStart_2776597 : Nat := 118140960795 + 2776597 * 2 ^ 59
def prefixEnd_2776597 : Nat := 4983230072969 + 3 ^ 40 * 2776597 * 2
def baseEnd_2776597 : Nat := 1425728844831978285168169

theorem tailTrace_2776597 : CollatzResearch.WordTrace tailWord_2776597 prefixEnd_2776597 1425728844831978285168169 := by
  unfold tailWord_2776597
  simp only [CollatzResearch.WordTrace]
  refine ⟨101270812321870748859320045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67513874881247165906213363 101270812321870748859320045)
  ·
    refine ⟨37976554620701530822245017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101270812321870748859320045 37976554620701530822245017)
    ·
      refine ⟨28482415965526148116683763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37976554620701530822245017 28482415965526148116683763)
      ·
        refine ⟨42723623948289222175025645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28482415965526148116683763 42723623948289222175025645)
        ·
          refine ⟨16021358980608458315634617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42723623948289222175025645 16021358980608458315634617)
          ·
            refine ⟨12016019235456343736725963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16021358980608458315634617 12016019235456343736725963)
            ·
              refine ⟨18024028853184515605088945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12016019235456343736725963 18024028853184515605088945)
              ·
                refine ⟨13518021639888386703816709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18024028853184515605088945 13518021639888386703816709)
                ·
                  refine ⟨2534629057479072506965633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13518021639888386703816709 2534629057479072506965633)
                  ·
                    refine ⟨1900971793109304380224225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2534629057479072506965633 1900971793109304380224225)
                    ·
                      refine ⟨1425728844831978285168169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900971793109304380224225 1425728844831978285168169)
                      ·
                        rfl

theorem cell23_2776597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 4, 2, 2].length) (baseStart_2776597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776597 prefixEnd_2776597 := by exact prefixLift 2776597
  have htrace : WordTrace (prefixWord ++ tailWord_2776597) baseStart_2776597 baseEnd_2776597 := by
    simpa [prefixWord, tailWord_2776597, baseEnd_2776597] using wordTrace_append hprefix tailTrace_2776597
  have hstable : (prefixWord ++ tailWord_2776597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776597).length < 2 ^ (prefixWord ++ tailWord_2776597).sum := by decide
  have hdescent : baseEnd_2776597 < baseStart_2776597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776600 : List Nat := [2, 1, 2, 3, 4, 1, 1, 1, 2, 1, 5]
def baseStart_2776600 : Nat := 118140960795 + 2776600 * 2 ^ 59
def prefixEnd_2776600 : Nat := 4983230072969 + 3 ^ 40 * 2776600 * 2
def baseEnd_2776600 : Nat := 1425730385273941773430655

theorem tailTrace_2776600 : CollatzResearch.WordTrace tailWord_2776600 prefixEnd_2776600 1425730385273941773430655 := by
  unfold tailWord_2776600
  simp only [CollatzResearch.WordTrace]
  refine ⟨50635460870429940185839627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67513947827239920247786169 50635460870429940185839627)
  ·
    refine ⟨75953191305644910278759441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50635460870429940185839627 75953191305644910278759441)
    ·
      refine ⟨56964893479233682709069581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75953191305644910278759441 56964893479233682709069581)
      ·
        refine ⟨21361835054712631015901093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56964893479233682709069581 21361835054712631015901093)
        ·
          refine ⟨4005344072758618315481455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21361835054712631015901093 4005344072758618315481455)
          ·
            refine ⟨6008016109137927473222183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005344072758618315481455 6008016109137927473222183)
            ·
              refine ⟨9012024163706891209833275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6008016109137927473222183 9012024163706891209833275)
              ·
                refine ⟨13518036245560336814749913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9012024163706891209833275 13518036245560336814749913)
                ·
                  refine ⟨10138527184170252611062435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13518036245560336814749913 10138527184170252611062435)
                  ·
                    refine ⟨15207790776255378916593653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10138527184170252611062435 15207790776255378916593653)
                    ·
                      refine ⟨1425730385273941773430655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15207790776255378916593653 1425730385273941773430655)
                      ·
                        rfl

theorem cell23_2776600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_2776600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776600 prefixEnd_2776600 := by exact prefixLift 2776600
  have htrace : WordTrace (prefixWord ++ tailWord_2776600) baseStart_2776600 baseEnd_2776600 := by
    simpa [prefixWord, tailWord_2776600, baseEnd_2776600] using wordTrace_append hprefix tailTrace_2776600
  have hstable : (prefixWord ++ tailWord_2776600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776600).length < 2 ^ (prefixWord ++ tailWord_2776600).sum := by decide
  have hdescent : baseEnd_2776600 < baseStart_2776600 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776631 : List Nat := [1, 1, 3, 1, 2, 6, 2, 1, 2, 2, 2]
def baseStart_2776631 : Nat := 118140960795 + 2776631 * 2 ^ 59
def prefixEnd_2776631 : Nat := 4983230072969 + 3 ^ 40 * 2776631 * 2
def baseEnd_2776631 : Nat := 1425746303174231152143013

theorem tailTrace_2776631 : CollatzResearch.WordTrace tailWord_2776631 prefixEnd_2776631 1425746303174231152143013 := by
  unfold tailWord_2776631
  simp only [CollatzResearch.WordTrace]
  refine ⟨101272052403747572666057747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67514701602498381777371831 101272052403747572666057747)
  ·
    refine ⟨151908078605621358999086621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101272052403747572666057747 151908078605621358999086621)
    ·
      refine ⟨56965529477108009624657483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151908078605621358999086621 56965529477108009624657483)
      ·
        refine ⟨85448294215662014436986225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56965529477108009624657483 85448294215662014436986225)
        ·
          refine ⟨64086220661746510827739669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85448294215662014436986225 64086220661746510827739669)
          ·
            refine ⟨3004041593519367695050297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 64086220661746510827739669 3004041593519367695050297)
            ·
              refine ⟨2253031195139525771287723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3004041593519367695050297 2253031195139525771287723)
              ·
                refine ⟨3379546792709288656931585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253031195139525771287723 3379546792709288656931585)
                ·
                  refine ⟨2534660094531966492698689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3379546792709288656931585 2534660094531966492698689)
                  ·
                    refine ⟨1900995070898974869524017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2534660094531966492698689 1900995070898974869524017)
                    ·
                      refine ⟨1425746303174231152143013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1900995070898974869524017 1425746303174231152143013)
                      ·
                        rfl

theorem cell23_2776631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 6, 2, 1, 2, 2, 2].length) (baseStart_2776631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776631 prefixEnd_2776631 := by exact prefixLift 2776631
  have htrace : WordTrace (prefixWord ++ tailWord_2776631) baseStart_2776631 baseEnd_2776631 := by
    simpa [prefixWord, tailWord_2776631, baseEnd_2776631] using wordTrace_append hprefix tailTrace_2776631
  have hstable : (prefixWord ++ tailWord_2776631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776631).length < 2 ^ (prefixWord ++ tailWord_2776631).sum := by decide
  have hdescent : baseEnd_2776631 < baseStart_2776631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776650 : List Nat := [3, 1, 2, 1, 1, 3, 4, 1, 2, 5]
def baseStart_2776650 : Nat := 118140960795 + 2776650 * 2 ^ 59
def prefixEnd_2776650 : Nat := 4983230072969 + 3 ^ 40 * 2776650 * 2
def baseEnd_2776650 : Nat := 475252019768888859268475

theorem tailTrace_2776650 : CollatzResearch.WordTrace tailWord_2776650 prefixEnd_2776650 475252019768888859268475 := by
  unfold tailWord_2776650
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318186347669684727749851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67515163593785825940666269 25318186347669684727749851)
  ·
    refine ⟨37977279521504527091624777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25318186347669684727749851 37977279521504527091624777)
    ·
      refine ⟨28482959641128395318718583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37977279521504527091624777 28482959641128395318718583)
      ·
        refine ⟨42724439461692592978077875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28482959641128395318718583 42724439461692592978077875)
        ·
          refine ⟨64086659192538889467116813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42724439461692592978077875 64086659192538889467116813)
          ·
            refine ⟨24032497197202083550168805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64086659192538889467116813 24032497197202083550168805)
            ·
              refine ⟨4506093224475390665656651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24032497197202083550168805 4506093224475390665656651)
              ·
                refine ⟨6759139836713085998484977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506093224475390665656651 6759139836713085998484977)
                ·
                  refine ⟨5069354877534814498863733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6759139836713085998484977 5069354877534814498863733)
                  ·
                    refine ⟨475252019768888859268475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5069354877534814498863733 475252019768888859268475)
                    ·
                      rfl

theorem cell23_2776650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 1, 2, 5].length) (baseStart_2776650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776650 prefixEnd_2776650 := by exact prefixLift 2776650
  have htrace : WordTrace (prefixWord ++ tailWord_2776650) baseStart_2776650 baseEnd_2776650 := by
    simpa [prefixWord, tailWord_2776650, baseEnd_2776650] using wordTrace_append hprefix tailTrace_2776650
  have hstable : (prefixWord ++ tailWord_2776650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776650).length < 2 ^ (prefixWord ++ tailWord_2776650).sum := by decide
  have hdescent : baseEnd_2776650 < baseStart_2776650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776673 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 5]
def baseStart_2776673 : Nat := 118140960795 + 2776673 * 2 ^ 59
def prefixEnd_2776673 : Nat := 4983230072969 + 3 ^ 40 * 2776673 * 2
def baseEnd_2776673 : Nat := 1425767869361719987817819

theorem tailTrace_2776673 : CollatzResearch.WordTrace tailWord_2776673 prefixEnd_2776673 1425767869361719987817819 := by
  unfold tailWord_2776673
  simp only [CollatzResearch.WordTrace]
  refine ⟨101273584269595413839086673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67515722846396942559391115 101273584269595413839086673)
  ·
    refine ⟨75955188202196560379315005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101273584269595413839086673 75955188202196560379315005)
    ·
      refine ⟨28483195575823710142243127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75955188202196560379315005 28483195575823710142243127)
      ·
        refine ⟨42724793363735565213364691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28483195575823710142243127 42724793363735565213364691)
        ·
          refine ⟨64087190045603347820047037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42724793363735565213364691 64087190045603347820047037)
          ·
            refine ⟨24032696267101255432517639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64087190045603347820047037 24032696267101255432517639)
            ·
              refine ⟨36049044400651883148776459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24032696267101255432517639 36049044400651883148776459)
              ·
                refine ⟨54073566600977824723164689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36049044400651883148776459 54073566600977824723164689)
                ·
                  refine ⟨40555174950733368542373517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 54073566600977824723164689 40555174950733368542373517)
                  ·
                    refine ⟨15208190606525013203390069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 40555174950733368542373517 15208190606525013203390069)
                    ·
                      refine ⟨1425767869361719987817819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15208190606525013203390069 1425767869361719987817819)
                      ·
                        rfl

theorem cell23_2776673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 3, 5].length) (baseStart_2776673 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776673 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776673 prefixEnd_2776673 := by exact prefixLift 2776673
  have htrace : WordTrace (prefixWord ++ tailWord_2776673) baseStart_2776673 baseEnd_2776673 := by
    simpa [prefixWord, tailWord_2776673, baseEnd_2776673] using wordTrace_append hprefix tailTrace_2776673
  have hstable : (prefixWord ++ tailWord_2776673).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776673).length < 2 ^ (prefixWord ++ tailWord_2776673).sum := by decide
  have hdescent : baseEnd_2776673 < baseStart_2776673 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776714 : List Nat := [3, 1, 2, 3, 2, 1, 1, 5, 1, 4]
def baseStart_2776714 : Nat := 118140960795 + 2776714 * 2 ^ 59
def prefixEnd_2776714 : Nat := 4983230072969 + 3 ^ 40 * 2776714 * 2
def baseEnd_2776714 : Nat := 475262974022851442468377

theorem tailTrace_2776714 : CollatzResearch.WordTrace tailWord_2776714 prefixEnd_2776714 475262974022851442468377 := by
  unfold tailWord_2776714
  simp only [CollatzResearch.WordTrace]
  refine ⟨25318769915611719460332299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67516719774964585227552797 25318769915611719460332299)
  ·
    refine ⟨37978154873417579190498449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25318769915611719460332299 37978154873417579190498449)
    ·
      refine ⟨28483616155063184392873837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37978154873417579190498449 28483616155063184392873837)
      ·
        refine ⟨10681356058148694147327689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28483616155063184392873837 10681356058148694147327689)
        ·
          refine ⟨8011017043611520610495767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10681356058148694147327689 8011017043611520610495767)
          ·
            refine ⟨12016525565417280915743651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8011017043611520610495767 12016525565417280915743651)
            ·
              refine ⟨18024788348125921373615477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12016525565417280915743651 18024788348125921373615477)
              ·
                refine ⟨1689823907636805128776451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18024788348125921373615477 1689823907636805128776451)
                ·
                  refine ⟨2534735861455207693164677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1689823907636805128776451 2534735861455207693164677)
                  ·
                    refine ⟨475262974022851442468377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2534735861455207693164677 475262974022851442468377)
                    ·
                      rfl

theorem cell23_2776714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 5, 1, 4].length) (baseStart_2776714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776714 prefixEnd_2776714 := by exact prefixLift 2776714
  have htrace : WordTrace (prefixWord ++ tailWord_2776714) baseStart_2776714 baseEnd_2776714 := by
    simpa [prefixWord, tailWord_2776714, baseEnd_2776714] using wordTrace_append hprefix tailTrace_2776714
  have hstable : (prefixWord ++ tailWord_2776714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776714).length < 2 ^ (prefixWord ++ tailWord_2776714).sum := by decide
  have hdescent : baseEnd_2776714 < baseStart_2776714 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776727 : List Nat := [1, 1, 3, 3, 2, 4, 1, 2, 6]
def baseStart_2776727 : Nat := 118140960795 + 2776727 * 2 ^ 59
def prefixEnd_2776727 : Nat := 4983230072969 + 3 ^ 40 * 2776727 * 2
def baseEnd_2776727 : Nat := 158421733035229197393619

theorem tailTrace_2776727 : CollatzResearch.WordTrace tailWord_2776727 prefixEnd_2776727 158421733035229197393619 := by
  unfold tailWord_2776727
  simp only [CollatzResearch.WordTrace]
  refine ⟨101275553811399781061552435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67517035874266520707701623 101275553811399781061552435)
  ·
    refine ⟨151913330717099671592328653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101275553811399781061552435 151913330717099671592328653)
    ·
      refine ⟨56967499018912376847123245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151913330717099671592328653 56967499018912376847123245)
      ·
        refine ⟨21362812132092141317671217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56967499018912376847123245 21362812132092141317671217)
        ·
          refine ⟨16022109099069105988253413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21362812132092141317671217 16022109099069105988253413)
          ·
            refine ⟨3004145456075457372797515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16022109099069105988253413 3004145456075457372797515)
            ·
              refine ⟨4506218184113186059196273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3004145456075457372797515 4506218184113186059196273)
              ·
                refine ⟨3379663638084889544397205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4506218184113186059196273 3379663638084889544397205)
                ·
                  refine ⟨158421733035229197393619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3379663638084889544397205 158421733035229197393619)
                  ·
                    rfl

theorem cell23_2776727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 2, 6].length) (baseStart_2776727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776727 prefixEnd_2776727 := by exact prefixLift 2776727
  have htrace : WordTrace (prefixWord ++ tailWord_2776727) baseStart_2776727 baseEnd_2776727 := by
    simpa [prefixWord, tailWord_2776727, baseEnd_2776727] using wordTrace_append hprefix tailTrace_2776727
  have hstable : (prefixWord ++ tailWord_2776727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776727).length < 2 ^ (prefixWord ++ tailWord_2776727).sum := by decide
  have hdescent : baseEnd_2776727 < baseStart_2776727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776760 : List Nat := [2, 1, 2, 1, 2, 1, 1, 5, 3, 1, 4]
def baseStart_2776760 : Nat := 118140960795 + 2776760 * 2 ^ 59
def prefixEnd_2776760 : Nat := 4983230072969 + 3 ^ 40 * 2776760 * 2
def baseEnd_2776760 : Nat := 1425812542178661147429919

theorem tailTrace_2776760 : CollatzResearch.WordTrace tailWord_2776760 prefixEnd_2776760 1425812542178661147429919 := by
  unfold tailWord_2776760
  simp only [CollatzResearch.WordTrace]
  refine ⟨50638378710140113848751867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67517838280186818465002489 50638378710140113848751867)
  ·
    refine ⟨75957568065210170773127801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50638378710140113848751867 75957568065210170773127801)
    ·
      refine ⟨56968176048907628079845851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75957568065210170773127801 56968176048907628079845851)
      ·
        refine ⟨85452264073361442119768777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56968176048907628079845851 85452264073361442119768777)
        ·
          refine ⟨64089198055021081589826583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85452264073361442119768777 64089198055021081589826583)
          ·
            refine ⟨96133797082531622384739875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64089198055021081589826583 96133797082531622384739875)
            ·
              refine ⟨144200695623797433577109813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96133797082531622384739875 144200695623797433577109813)
              ·
                refine ⟨13518815214731009397854045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 144200695623797433577109813 13518815214731009397854045)
                ·
                  refine ⟨5069555705524128524195267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13518815214731009397854045 5069555705524128524195267)
                  ·
                    refine ⟨7604333558286192786292901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069555705524128524195267 7604333558286192786292901)
                    ·
                      refine ⟨1425812542178661147429919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7604333558286192786292901 1425812542178661147429919)
                      ·
                        rfl

theorem cell23_2776760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 5, 3, 1, 4].length) (baseStart_2776760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776760 prefixEnd_2776760 := by exact prefixLift 2776760
  have htrace : WordTrace (prefixWord ++ tailWord_2776760) baseStart_2776760 baseEnd_2776760 := by
    simpa [prefixWord, tailWord_2776760, baseEnd_2776760] using wordTrace_append hprefix tailTrace_2776760
  have hstable : (prefixWord ++ tailWord_2776760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776760).length < 2 ^ (prefixWord ++ tailWord_2776760).sum := by decide
  have hdescent : baseEnd_2776760 < baseStart_2776760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776781 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 4, 3, 2]
def baseStart_2776781 : Nat := 118140960795 + 2776781 * 2 ^ 59
def prefixEnd_2776781 : Nat := 4983230072969 + 3 ^ 40 * 2776781 * 2
def baseEnd_2776781 : Nat := 1425823325272405565267323

theorem tailTrace_2776781 : CollatzResearch.WordTrace tailWord_2776781 prefixEnd_2776781 1425823325272405565267323 := by
  unfold tailWord_2776781
  simp only [CollatzResearch.WordTrace]
  refine ⟨101277523353204148284018197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67518348902136098856012131 101277523353204148284018197)
  ·
    refine ⟨4747383907181444450813353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 101277523353204148284018197 4747383907181444450813353)
    ·
      refine ⟨3560537930386083338110015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4747383907181444450813353 3560537930386083338110015)
      ·
        refine ⟨5340806895579125007165023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3560537930386083338110015 5340806895579125007165023)
        ·
          refine ⟨8011210343368687510747535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5340806895579125007165023 8011210343368687510747535)
          ·
            refine ⟨12016815515053031266121303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8011210343368687510747535 12016815515053031266121303)
            ·
              refine ⟨18025223272579546899181955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12016815515053031266121303 18025223272579546899181955)
              ·
                refine ⟨27037834908869320348772933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18025223272579546899181955 27037834908869320348772933)
                ·
                  refine ⟨5069594045412997565394925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27037834908869320348772933 5069594045412997565394925)
                  ·
                    refine ⟨1901097767029874087023097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5069594045412997565394925 1901097767029874087023097)
                    ·
                      refine ⟨1425823325272405565267323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901097767029874087023097 1425823325272405565267323)
                      ·
                        rfl

theorem cell23_2776781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 4, 3, 2].length) (baseStart_2776781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776781 prefixEnd_2776781 := by exact prefixLift 2776781
  have htrace : WordTrace (prefixWord ++ tailWord_2776781) baseStart_2776781 baseEnd_2776781 := by
    simpa [prefixWord, tailWord_2776781, baseEnd_2776781] using wordTrace_append hprefix tailTrace_2776781
  have hstable : (prefixWord ++ tailWord_2776781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776781).length < 2 ^ (prefixWord ++ tailWord_2776781).sum := by decide
  have hdescent : baseEnd_2776781 < baseStart_2776781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776827 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 3]
def baseStart_2776827 : Nat := 118140960795 + 2776827 * 2 ^ 59
def prefixEnd_2776827 : Nat := 4983230072969 + 3 ^ 40 * 2776827 * 2
def baseEnd_2776827 : Nat := 1425846945382512385292111

theorem tailTrace_2776827 : CollatzResearch.WordTrace tailWord_2776827 prefixEnd_2776827 1425846945382512385292111 := by
  unfold tailWord_2776827
  simp only [CollatzResearch.WordTrace]
  refine ⟨101279201111037498140192735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67519467407358332093461823 101279201111037498140192735)
  ·
    refine ⟨151918801666556247210289103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101279201111037498140192735 151918801666556247210289103)
    ·
      refine ⟨227878202499834370815433655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151918801666556247210289103 227878202499834370815433655)
      ·
        refine ⟨341817303749751556223150483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227878202499834370815433655 341817303749751556223150483)
        ·
          refine ⟨512725955624627334334725725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341817303749751556223150483 512725955624627334334725725)
          ·
            refine ⟨192272233359235250375522147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 512725955624627334334725725 192272233359235250375522147)
            ·
              refine ⟨288408350038852875563283221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192272233359235250375522147 288408350038852875563283221)
              ·
                refine ⟨13519141408071228542028901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 288408350038852875563283221 13519141408071228542028901)
                ·
                  refine ⟨2534839014013355351630419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13519141408071228542028901 2534839014013355351630419)
                  ·
                    refine ⟨3802258521020033027445629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2534839014013355351630419 3802258521020033027445629)
                    ·
                      refine ⟨1425846945382512385292111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3802258521020033027445629 1425846945382512385292111)
                      ·
                        rfl

theorem cell23_2776827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 4, 1, 3].length) (baseStart_2776827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776827 prefixEnd_2776827 := by exact prefixLift 2776827
  have htrace : WordTrace (prefixWord ++ tailWord_2776827) baseStart_2776827 baseEnd_2776827 := by
    simpa [prefixWord, tailWord_2776827, baseEnd_2776827] using wordTrace_append hprefix tailTrace_2776827
  have hstable : (prefixWord ++ tailWord_2776827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776827).length < 2 ^ (prefixWord ++ tailWord_2776827).sum := by decide
  have hdescent : baseEnd_2776827 < baseStart_2776827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776844 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 2, 1, 3]
def baseStart_2776844 : Nat := 118140960795 + 2776844 * 2 ^ 59
def prefixEnd_2776844 : Nat := 4983230072969 + 3 ^ 40 * 2776844 * 2
def baseEnd_2776844 : Nat := 1425855674553638818779533

theorem tailTrace_2776844 : CollatzResearch.WordTrace tailWord_2776844 prefixEnd_2776844 1425855674553638818779533 := by
  unfold tailWord_2776844
  simp only [CollatzResearch.WordTrace]
  refine ⟨50639910575987955021780793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67519880767983940029041057 50639910575987955021780793)
  ·
    refine ⟨37979932931990966266335595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50639910575987955021780793 37979932931990966266335595)
    ·
      refine ⟨56969899397986449399503393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37979932931990966266335595 56969899397986449399503393)
      ·
        refine ⟨42727424548489837049627545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56969899397986449399503393 42727424548489837049627545)
        ·
          refine ⟨32045568411367377787220659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42727424548489837049627545 32045568411367377787220659)
          ·
            refine ⟨48068352617051066680830989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32045568411367377787220659 48068352617051066680830989)
            ·
              refine ⟨18025632231394150005311621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48068352617051066680830989 18025632231394150005311621)
              ·
                refine ⟨3379806043386403125995929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18025632231394150005311621 3379806043386403125995929)
                ·
                  refine ⟨2534854532539802344496947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3379806043386403125995929 2534854532539802344496947)
                  ·
                    refine ⟨3802281798809703516745421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2534854532539802344496947 3802281798809703516745421)
                    ·
                      refine ⟨1425855674553638818779533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3802281798809703516745421 1425855674553638818779533)
                      ·
                        rfl

theorem cell23_2776844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_2776844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776844 prefixEnd_2776844 := by exact prefixLift 2776844
  have htrace : WordTrace (prefixWord ++ tailWord_2776844) baseStart_2776844 baseEnd_2776844 := by
    simpa [prefixWord, tailWord_2776844, baseEnd_2776844] using wordTrace_append hprefix tailTrace_2776844
  have hstable : (prefixWord ++ tailWord_2776844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776844).length < 2 ^ (prefixWord ++ tailWord_2776844).sum := by decide
  have hdescent : baseEnd_2776844 < baseStart_2776844 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776888 : List Nat := [2, 1, 2, 1, 3, 5, 2, 1, 1, 3, 2]
def baseStart_2776888 : Nat := 118140960795 + 2776888 * 2 ^ 59
def prefixEnd_2776888 : Nat := 4983230072969 + 3 ^ 40 * 2776888 * 2
def baseEnd_2776888 : Nat := 1425878267702436646629331

theorem tailTrace_2776888 : CollatzResearch.WordTrace tailWord_2776888 prefixEnd_2776888 1425878267702436646629331 := by
  unfold tailWord_2776888
  simp only [CollatzResearch.WordTrace]
  refine ⟨50640712981908252779081659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67520950642544337038775545 50640712981908252779081659)
  ·
    refine ⟨75961069472862379168622489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50640712981908252779081659 75961069472862379168622489)
    ·
      refine ⟨56970802104646784376466867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75961069472862379168622489 56970802104646784376466867)
      ·
        refine ⟨85456203156970176564700301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56970802104646784376466867 85456203156970176564700301)
        ·
          refine ⟨32046076183863816211762613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85456203156970176564700301 32046076183863816211762613)
          ·
            refine ⟨3004319642237232769852745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 32046076183863816211762613 3004319642237232769852745)
            ·
              refine ⟨2253239731677924577389559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3004319642237232769852745 2253239731677924577389559)
              ·
                refine ⟨3379859597516886866084339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253239731677924577389559 3379859597516886866084339)
                ·
                  refine ⟨5069789396275330299126509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3379859597516886866084339 5069789396275330299126509)
                  ·
                    refine ⟨1901171023603248862172441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5069789396275330299126509 1901171023603248862172441)
                    ·
                      refine ⟨1425878267702436646629331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901171023603248862172441 1425878267702436646629331)
                      ·
                        rfl

theorem cell23_2776888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 1, 3, 2].length) (baseStart_2776888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776888 prefixEnd_2776888 := by exact prefixLift 2776888
  have htrace : WordTrace (prefixWord ++ tailWord_2776888) baseStart_2776888 baseEnd_2776888 := by
    simpa [prefixWord, tailWord_2776888, baseEnd_2776888] using wordTrace_append hprefix tailTrace_2776888
  have hstable : (prefixWord ++ tailWord_2776888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776888).length < 2 ^ (prefixWord ++ tailWord_2776888).sum := by decide
  have hdescent : baseEnd_2776888 < baseStart_2776888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776977 : List Nat := [1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 3]
def baseStart_2776977 : Nat := 118140960795 + 2776977 * 2 ^ 59
def prefixEnd_2776977 : Nat := 4983230072969 + 3 ^ 40 * 2776977 * 2
def baseEnd_2776977 : Nat := 1425923967480686798416421

theorem tailTrace_2776977 : CollatzResearch.WordTrace tailWord_2776977 prefixEnd_2776977 1425923967480686798416421 := by
  unfold tailWord_2776977
  simp only [CollatzResearch.WordTrace]
  refine ⟨101284672060494073758153185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67523114706996049172102123 101284672060494073758153185)
  ·
    refine ⟨75963504045370555318614889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101284672060494073758153185 75963504045370555318614889)
    ·
      refine ⟨56972628034027916488961167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75963504045370555318614889 56972628034027916488961167)
      ·
        refine ⟨85458942051041874733441751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56972628034027916488961167 85458942051041874733441751)
        ·
          refine ⟨128188413076562812100162627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85458942051041874733441751 128188413076562812100162627)
          ·
            refine ⟨192282619614844218150243941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128188413076562812100162627 192282619614844218150243941)
            ·
              refine ⟨36052991177783290903170739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192282619614844218150243941 36052991177783290903170739)
              ·
                refine ⟨54079486766674936354756109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36052991177783290903170739 54079486766674936354756109)
                ·
                  refine ⟨20279807537503101133033541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54079486766674936354756109 20279807537503101133033541)
                  ·
                    refine ⟨3802463913281831462443789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20279807537503101133033541 3802463913281831462443789)
                    ·
                      refine ⟨1425923967480686798416421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3802463913281831462443789 1425923967480686798416421)
                      ·
                        rfl

theorem cell23_2776977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 3].length) (baseStart_2776977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776977 prefixEnd_2776977 := by exact prefixLift 2776977
  have htrace : WordTrace (prefixWord ++ tailWord_2776977) baseStart_2776977 baseEnd_2776977 := by
    simpa [prefixWord, tailWord_2776977, baseEnd_2776977] using wordTrace_append hprefix tailTrace_2776977
  have hstable : (prefixWord ++ tailWord_2776977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776977).length < 2 ^ (prefixWord ++ tailWord_2776977).sum := by decide
  have hdescent : baseEnd_2776977 < baseStart_2776977 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2776991 : List Nat := [1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 4]
def baseStart_2776991 : Nat := 118140960795 + 2776991 * 2 ^ 59
def prefixEnd_2776991 : Nat := 4983230072969 + 3 ^ 40 * 2776991 * 2
def baseEnd_2776991 : Nat := 1425931156209849743641357

theorem tailTrace_2776991 : CollatzResearch.WordTrace tailWord_2776991 prefixEnd_2776991 1425931156209849743641357 := by
  unfold tailWord_2776991
  simp only [CollatzResearch.WordTrace]
  refine ⟨101285182682443354149162827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67523455121628902766108551 101285182682443354149162827)
  ·
    refine ⟨151927774023665031223744241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101285182682443354149162827 151927774023665031223744241)
    ·
      refine ⟨113945830517748773417808181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151927774023665031223744241 113945830517748773417808181)
      ·
        refine ⟨10682421611038947507919517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 113945830517748773417808181 10682421611038947507919517)
        ·
          refine ⟨4005908104139605315469819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10682421611038947507919517 4005908104139605315469819)
          ·
            refine ⟨6008862156209407973204729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4005908104139605315469819 6008862156209407973204729)
            ·
              refine ⟨4506646617157055979903547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6008862156209407973204729 4506646617157055979903547)
              ·
                refine ⟨6759969925735583969855321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4506646617157055979903547 6759969925735583969855321)
                ·
                  refine ⟨5069977444301687977391491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6759969925735583969855321 5069977444301687977391491)
                  ·
                    refine ⟨7604966166452531966087237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5069977444301687977391491 7604966166452531966087237)
                    ·
                      refine ⟨1425931156209849743641357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7604966166452531966087237 1425931156209849743641357)
                      ·
                        rfl

theorem cell23_2776991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_2776991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2776991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2776991 prefixEnd_2776991 := by exact prefixLift 2776991
  have htrace : WordTrace (prefixWord ++ tailWord_2776991) baseStart_2776991 baseEnd_2776991 := by
    simpa [prefixWord, tailWord_2776991, baseEnd_2776991] using wordTrace_append hprefix tailTrace_2776991
  have hstable : (prefixWord ++ tailWord_2776991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2776991).length < 2 ^ (prefixWord ++ tailWord_2776991).sum := by decide
  have hdescent : baseEnd_2776991 < baseStart_2776991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2776991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777017 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 6]
def baseStart_2777017 : Nat := 118140960795 + 2777017 * 2 ^ 59
def prefixEnd_2777017 : Nat := 4983230072969 + 3 ^ 40 * 2777017 * 2
def baseEnd_2777017 : Nat := 1425944506706866641916237

theorem tailTrace_2777017 : CollatzResearch.WordTrace tailWord_2777017 prefixEnd_2777017 1425944506706866641916237 := by
  unfold tailWord_2777017
  simp only [CollatzResearch.WordTrace]
  refine ⟨101286130980349160589609305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67524087320232773726406203 101286130980349160589609305)
  ·
    refine ⟨75964598235261870442206979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101286130980349160589609305 75964598235261870442206979)
    ·
      refine ⟨113946897352892805663310469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75964598235261870442206979 113946897352892805663310469)
      ·
        refine ⟨21365043253667401061870713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 113946897352892805663310469 21365043253667401061870713)
        ·
          refine ⟨16023782440250550796403035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21365043253667401061870713 16023782440250550796403035)
          ·
            refine ⟨24035673660375826194604553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16023782440250550796403035 24035673660375826194604553)
            ·
              refine ⟨18026755245281869645953415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24035673660375826194604553 18026755245281869645953415)
              ·
                refine ⟨27040132867922804468930123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18026755245281869645953415 27040132867922804468930123)
                ·
                  refine ⟨40560199301884206703395185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27040132867922804468930123 40560199301884206703395185)
                  ·
                    refine ⟨30420149476413155027546389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40560199301884206703395185 30420149476413155027546389)
                    ·
                      refine ⟨1425944506706866641916237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30420149476413155027546389 1425944506706866641916237)
                      ·
                        rfl

theorem cell23_2777017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 1, 2, 6].length) (baseStart_2777017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777017 prefixEnd_2777017 := by exact prefixLift 2777017
  have htrace : WordTrace (prefixWord ++ tailWord_2777017) baseStart_2777017 baseEnd_2777017 := by
    simpa [prefixWord, tailWord_2777017, baseEnd_2777017] using wordTrace_append hprefix tailTrace_2777017
  have hstable : (prefixWord ++ tailWord_2777017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777017).length < 2 ^ (prefixWord ++ tailWord_2777017).sum := by decide
  have hdescent : baseEnd_2777017 < baseStart_2777017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777044 : List Nat := [2, 4, 1, 2, 1, 1, 1, 3, 3, 5]
def baseStart_2777044 : Nat := 118140960795 + 2777044 * 2 ^ 59
def prefixEnd_2777044 : Nat := 4983230072969 + 3 ^ 40 * 2777044 * 2
def baseEnd_2777044 : Nat := 475319456894846012092871

theorem tailTrace_2777044 : CollatzResearch.WordTrace tailWord_2777044 prefixEnd_2777044 475319456894846012092871 := by
  unfold tailWord_2777044
  simp only [CollatzResearch.WordTrace]
  refine ⟨50643557875625672100421093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67524743834167562800561457 50643557875625672100421093)
  ·
    refine ⟨9495667101679813518828955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50643557875625672100421093 9495667101679813518828955)
    ·
      refine ⟨14243500652519720278243433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9495667101679813518828955 14243500652519720278243433)
      ·
        refine ⟨10682625489389790208682575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14243500652519720278243433 10682625489389790208682575)
        ·
          refine ⟨16023938234084685313023863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10682625489389790208682575 16023938234084685313023863)
          ·
            refine ⟨24035907351127027969535795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16023938234084685313023863 24035907351127027969535795)
            ·
              refine ⟨36053861026690541954303693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24035907351127027969535795 36053861026690541954303693)
              ·
                refine ⟨13520197885008953232863885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36053861026690541954303693 13520197885008953232863885)
                ·
                  refine ⟨5070074206878357462323957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13520197885008953232863885 5070074206878357462323957)
                  ·
                    refine ⟨475319456894846012092871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5070074206878357462323957 475319456894846012092871)
                    ·
                      rfl

theorem cell23_2777044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 3, 5].length) (baseStart_2777044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777044 prefixEnd_2777044 := by exact prefixLift 2777044
  have htrace : WordTrace (prefixWord ++ tailWord_2777044) baseStart_2777044 baseEnd_2777044 := by
    simpa [prefixWord, tailWord_2777044, baseEnd_2777044] using wordTrace_append hprefix tailTrace_2777044
  have hstable : (prefixWord ++ tailWord_2777044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777044).length < 2 ^ (prefixWord ++ tailWord_2777044).sum := by decide
  have hdescent : baseEnd_2777044 < baseStart_2777044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777067 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5]
def baseStart_2777067 : Nat := 118140960795 + 2777067 * 2 ^ 59
def prefixEnd_2777067 : Nat := 4983230072969 + 3 ^ 40 * 2777067 * 2
def baseEnd_2777067 : Nat := 1425970180739591446291007

theorem tailTrace_2777067 : CollatzResearch.WordTrace tailWord_2777067 prefixEnd_2777067 1425970180739591446291007 := by
  unfold tailWord_2777067
  simp only [CollatzResearch.WordTrace]
  refine ⟨101287954630168019128929455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67525303086778679419286303 101287954630168019128929455)
  ·
    refine ⟨151931931945252028693394183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101287954630168019128929455 151931931945252028693394183)
    ·
      refine ⟨227897897917878043040091275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151931931945252028693394183 227897897917878043040091275)
      ·
        refine ⟨341846846876817064560136913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227897897917878043040091275 341846846876817064560136913)
        ·
          refine ⟨256385135157612798420102685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341846846876817064560136913 256385135157612798420102685)
          ·
            refine ⟨96144425684104799407538507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256385135157612798420102685 96144425684104799407538507)
            ·
              refine ⟨144216638526157199111307761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96144425684104799407538507 144216638526157199111307761)
              ·
                refine ⟨108162478894617899333480821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144216638526157199111307761 108162478894617899333480821)
                ·
                  refine ⟨10140232396370428062513827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108162478894617899333480821 10140232396370428062513827)
                  ·
                    refine ⟨15210348594555642093770741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10140232396370428062513827 15210348594555642093770741)
                    ·
                      refine ⟨1425970180739591446291007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15210348594555642093770741 1425970180739591446291007)
                      ·
                        rfl

theorem cell23_2777067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 1, 5].length) (baseStart_2777067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777067 prefixEnd_2777067 := by exact prefixLift 2777067
  have htrace : WordTrace (prefixWord ++ tailWord_2777067) baseStart_2777067 baseEnd_2777067 := by
    simpa [prefixWord, tailWord_2777067, baseEnd_2777067] using wordTrace_append hprefix tailTrace_2777067
  have hstable : (prefixWord ++ tailWord_2777067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777067).length < 2 ^ (prefixWord ++ tailWord_2777067).sum := by decide
  have hdescent : baseEnd_2777067 < baseStart_2777067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777084 : List Nat := [2, 2, 2, 1, 2, 2, 3, 2, 1, 1, 5]
def baseStart_2777084 : Nat := 118140960795 + 2777084 * 2 ^ 59
def prefixEnd_2777084 : Nat := 4983230072969 + 3 ^ 40 * 2777084 * 2
def baseEnd_2777084 : Nat := 1425978909910717879778429

theorem tailTrace_2777084 : CollatzResearch.WordTrace tailWord_2777084 prefixEnd_2777084 1425978909910717879778429 := by
  unfold tailWord_2777084
  simp only [CollatzResearch.WordTrace]
  refine ⟨50644287335553215516149153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67525716447404287354865537 50644287335553215516149153)
  ·
    refine ⟨37983215501664911637111865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50644287335553215516149153 37983215501664911637111865)
    ·
      refine ⟨28487411626248683727833899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37983215501664911637111865 28487411626248683727833899)
      ·
        refine ⟨42731117439373025591750849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28487411626248683727833899 42731117439373025591750849)
        ·
          refine ⟨32048338079529769193813137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42731117439373025591750849 32048338079529769193813137)
          ·
            refine ⟨24036253559647326895359853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32048338079529769193813137 24036253559647326895359853)
            ·
              refine ⟨9013595084867747585759945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24036253559647326895359853 9013595084867747585759945)
              ·
                refine ⟨6760196313650810689319959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9013595084867747585759945 6760196313650810689319959)
                ·
                  refine ⟨10140294470476216033979939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760196313650810689319959 10140294470476216033979939)
                  ·
                    refine ⟨15210441705714324050969909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10140294470476216033979939 15210441705714324050969909)
                    ·
                      refine ⟨1425978909910717879778429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15210441705714324050969909 1425978909910717879778429)
                      ·
                        rfl

theorem cell23_2777084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 1, 1, 5].length) (baseStart_2777084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777084 prefixEnd_2777084 := by exact prefixLift 2777084
  have htrace : WordTrace (prefixWord ++ tailWord_2777084) baseStart_2777084 baseEnd_2777084 := by
    simpa [prefixWord, tailWord_2777084, baseEnd_2777084] using wordTrace_append hprefix tailTrace_2777084
  have hstable : (prefixWord ++ tailWord_2777084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777084).length < 2 ^ (prefixWord ++ tailWord_2777084).sum := by decide
  have hdescent : baseEnd_2777084 < baseStart_2777084 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777098 : List Nat := [3, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4]
def baseStart_2777098 : Nat := 118140960795 + 2777098 * 2 ^ 59
def prefixEnd_2777098 : Nat := 4983230072969 + 3 ^ 40 * 2777098 * 2
def baseEnd_2777098 : Nat := 1425986098639880825003365

theorem tailTrace_2777098 : CollatzResearch.WordTrace tailWord_2777098 prefixEnd_2777098 1425986098639880825003365 := by
  unfold tailWord_2777098
  simp only [CollatzResearch.WordTrace]
  refine ⟨25322271323263927855826987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67526056862037140948871965 25322271323263927855826987)
  ·
    refine ⟨37983406984895891783740481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25322271323263927855826987 37983406984895891783740481)
    ·
      refine ⟨28487555238671918837805361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37983406984895891783740481 28487555238671918837805361)
      ·
        refine ⟨21365666429003939128354021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28487555238671918837805361 21365666429003939128354021)
        ·
          refine ⟨4006062455438238586566379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21365666429003939128354021 4006062455438238586566379)
          ·
            refine ⟨6009093683157357879849569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006062455438238586566379 6009093683157357879849569)
            ·
              refine ⟨4506820262368018409887177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6009093683157357879849569 4506820262368018409887177)
              ·
                refine ⟨3380115196776013807415383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4506820262368018409887177 3380115196776013807415383)
                ·
                  refine ⟨5070172795164020711123075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380115196776013807415383 5070172795164020711123075)
                  ·
                    refine ⟨7605259192746031066684613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5070172795164020711123075 7605259192746031066684613)
                    ·
                      refine ⟨1425986098639880825003365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7605259192746031066684613 1425986098639880825003365)
                      ·
                        rfl

theorem cell23_2777098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 1, 2, 2, 1, 1, 4].length) (baseStart_2777098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777098 prefixEnd_2777098 := by exact prefixLift 2777098
  have htrace : WordTrace (prefixWord ++ tailWord_2777098) baseStart_2777098 baseEnd_2777098 := by
    simpa [prefixWord, tailWord_2777098, baseEnd_2777098] using wordTrace_append hprefix tailTrace_2777098
  have hstable : (prefixWord ++ tailWord_2777098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777098).length < 2 ^ (prefixWord ++ tailWord_2777098).sum := by decide
  have hdescent : baseEnd_2777098 < baseStart_2777098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777121 : List Nat := [1, 2, 3, 2, 5, 1, 9]
def baseStart_2777121 : Nat := 118140960795 + 2777121 * 2 ^ 59
def prefixEnd_2777121 : Nat := 4983230072969 + 3 ^ 40 * 2777121 * 2
def baseEnd_2777121 : Nat := 17604912453023879444639

theorem tailTrace_2777121 : CollatzResearch.WordTrace tailWord_2777121 prefixEnd_2777121 17604912453023879444639 := by
  unfold tailWord_2777121
  simp only [CollatzResearch.WordTrace]
  refine ⟨101289924171972386351395217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67526616114648257567596811 101289924171972386351395217)
  ·
    refine ⟨75967443128979289763546413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101289924171972386351395217 75967443128979289763546413)
    ·
      refine ⟨28487791173367233661329905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75967443128979289763546413 28487791173367233661329905)
      ·
        refine ⟨21365843380025425245997429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28487791173367233661329905 21365843380025425245997429)
        ·
          refine ⟨2003047816877383616812259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21365843380025425245997429 2003047816877383616812259)
          ·
            refine ⟨3004571725316075425218389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003047816877383616812259 3004571725316075425218389)
            ·
              refine ⟨17604912453023879444639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3004571725316075425218389 17604912453023879444639)
              ·
                rfl

theorem cell23_2777121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 9].length) (baseStart_2777121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777121 prefixEnd_2777121 := by exact prefixLift 2777121
  have htrace : WordTrace (prefixWord ++ tailWord_2777121) baseStart_2777121 baseEnd_2777121 := by
    simpa [prefixWord, tailWord_2777121, baseEnd_2777121] using wordTrace_append hprefix tailTrace_2777121
  have hstable : (prefixWord ++ tailWord_2777121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777121).length < 2 ^ (prefixWord ++ tailWord_2777121).sum := by decide
  have hdescent : baseEnd_2777121 < baseStart_2777121 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777148 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 2, 1, 3]
def baseStart_2777148 : Nat := 118140960795 + 2777148 * 2 ^ 59
def prefixEnd_2777148 : Nat := 4983230072969 + 3 ^ 40 * 2777148 * 2
def baseEnd_2777148 : Nat := 1426011772672605629378135

theorem tailTrace_2777148 : CollatzResearch.WordTrace tailWord_2777148 prefixEnd_2777148 1426011772672605629378135 := by
  unfold tailWord_2777148
  simp only [CollatzResearch.WordTrace]
  refine ⟨50645454471437284981314049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67527272628583046641752065 50645454471437284981314049)
  ·
    refine ⟨37984090853577963735985537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50645454471437284981314049 37984090853577963735985537)
    ·
      refine ⟨28488068140183472801989153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37984090853577963735985537 28488068140183472801989153)
      ·
        refine ⟨21366051105137604601491865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28488068140183472801989153 21366051105137604601491865)
        ·
          refine ⟨16024538328853203451118899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21366051105137604601491865 16024538328853203451118899)
          ·
            refine ⟨24036807493279805176678349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16024538328853203451118899 24036807493279805176678349)
            ·
              refine ⟨9013802809979926941254381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24036807493279805176678349 9013802809979926941254381)
              ·
                refine ⟨3380176053742472602970393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9013802809979926941254381 3380176053742472602970393)
                ·
                  refine ⟨2535132040306854452227795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380176053742472602970393 2535132040306854452227795)
                  ·
                    refine ⟨3802698060460281678341693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535132040306854452227795 3802698060460281678341693)
                    ·
                      refine ⟨1426011772672605629378135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3802698060460281678341693 1426011772672605629378135)
                      ·
                        rfl

theorem cell23_2777148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 2, 1, 3].length) (baseStart_2777148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777148 prefixEnd_2777148 := by exact prefixLift 2777148
  have htrace : WordTrace (prefixWord ++ tailWord_2777148) baseStart_2777148 baseEnd_2777148 := by
    simpa [prefixWord, tailWord_2777148, baseEnd_2777148] using wordTrace_append hprefix tailTrace_2777148
  have hstable : (prefixWord ++ tailWord_2777148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777148).length < 2 ^ (prefixWord ++ tailWord_2777148).sum := by decide
  have hdescent : baseEnd_2777148 < baseStart_2777148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777188 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 4, 2, 2]
def baseStart_2777188 : Nat := 118140960795 + 2777188 * 2 ^ 59
def prefixEnd_2777188 : Nat := 4983230072969 + 3 ^ 40 * 2777188 * 2
def baseEnd_2777188 : Nat := 1426032311898785472877951

theorem tailTrace_2777188 : CollatzResearch.WordTrace tailWord_2777188 prefixEnd_2777188 1426032311898785472877951 := by
  unfold tailWord_2777188
  simp only [CollatzResearch.WordTrace]
  refine ⟨50646183931364828397042109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67528245241819771196056145 50646183931364828397042109)
  ·
    refine ⟨18992318974261810648890791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50646183931364828397042109 18992318974261810648890791)
    ·
      refine ⟨28488478461392715973336187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18992318974261810648890791 28488478461392715973336187)
      ·
        refine ⟨42732717692089073960004281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28488478461392715973336187 42732717692089073960004281)
        ·
          refine ⟨32049538269066805470003211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42732717692089073960004281 32049538269066805470003211)
          ·
            refine ⟨48074307403600208205004817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32049538269066805470003211 48074307403600208205004817)
            ·
              refine ⟨36055730552700156153753613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48074307403600208205004817 36055730552700156153753613)
              ·
                refine ⟨13520898957262558557657605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36055730552700156153753613 13520898957262558557657605)
                ·
                  refine ⟨2535168554486729729560801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13520898957262558557657605 2535168554486729729560801)
                  ·
                    refine ⟨1901376415865047297170601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535168554486729729560801 1901376415865047297170601)
                    ·
                      refine ⟨1426032311898785472877951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901376415865047297170601 1426032311898785472877951)
                      ·
                        rfl

theorem cell23_2777188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 4, 2, 2].length) (baseStart_2777188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777188 prefixEnd_2777188 := by exact prefixLift 2777188
  have htrace : WordTrace (prefixWord ++ tailWord_2777188) baseStart_2777188 baseEnd_2777188 := by
    simpa [prefixWord, tailWord_2777188, baseEnd_2777188] using wordTrace_append hprefix tailTrace_2777188
  have hstable : (prefixWord ++ tailWord_2777188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777188).length < 2 ^ (prefixWord ++ tailWord_2777188).sum := by decide
  have hdescent : baseEnd_2777188 < baseStart_2777188 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777239 : List Nat := [1, 1, 3, 3, 5, 1, 1, 2, 2, 2, 2]
def baseStart_2777239 : Nat := 118140960795 + 2777239 * 2 ^ 59
def prefixEnd_2777239 : Nat := 4983230072969 + 3 ^ 40 * 2777239 * 2
def baseEnd_2777239 : Nat := 1426058499412164773340217

theorem tailTrace_2777239 : CollatzResearch.WordTrace tailWord_2777239 prefixEnd_2777239 1426058499412164773340217 := by
  unfold tailWord_2777239
  simp only [CollatzResearch.WordTrace]
  refine ⟨101294227985544892504190771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67529485323696595002793847 101294227985544892504190771)
  ·
    refine ⟨151941341978317338756286157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101294227985544892504190771 151941341978317338756286157)
    ·
      refine ⟨56978003241869002033607309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151941341978317338756286157 56978003241869002033607309)
      ·
        refine ⟨21366751215700875762602741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56978003241869002033607309 21366751215700875762602741)
        ·
          refine ⟨2003132926471957102744007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21366751215700875762602741 2003132926471957102744007)
          ·
            refine ⟨3004699389707935654116011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003132926471957102744007 3004699389707935654116011)
            ·
              refine ⟨4507049084561903481174017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3004699389707935654116011 4507049084561903481174017)
              ·
                refine ⟨3380286813421427610880513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507049084561903481174017 3380286813421427610880513)
                ·
                  refine ⟨2535215110066070708160385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380286813421427610880513 2535215110066070708160385)
                  ·
                    refine ⟨1901411332549553031120289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535215110066070708160385 1901411332549553031120289)
                    ·
                      refine ⟨1426058499412164773340217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901411332549553031120289 1426058499412164773340217)
                      ·
                        rfl

theorem cell23_2777239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_2777239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777239 prefixEnd_2777239 := by exact prefixLift 2777239
  have htrace : WordTrace (prefixWord ++ tailWord_2777239) baseStart_2777239 baseEnd_2777239 := by
    simpa [prefixWord, tailWord_2777239, baseEnd_2777239] using wordTrace_append hprefix tailTrace_2777239
  have hstable : (prefixWord ++ tailWord_2777239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777239).length < 2 ^ (prefixWord ++ tailWord_2777239).sum := by decide
  have hdescent : baseEnd_2777239 < baseStart_2777239 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777298 : List Nat := [3, 2, 2, 2, 1, 2, 1, 1, 4, 2, 3]
def baseStart_2777298 : Nat := 118140960795 + 2777298 * 2 ^ 59
def prefixEnd_2777298 : Nat := 4983230072969 + 3 ^ 40 * 2777298 * 2
def baseEnd_2777298 : Nat := 1426088794770780042502445

theorem tailTrace_2777298 : CollatzResearch.WordTrace tailWord_2777298 prefixEnd_2777298 1426088794770780042502445 := by
  unfold tailWord_2777298
  simp only [CollatzResearch.WordTrace]
  refine ⟨25324094973082786395147137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67530919928220763720392365 25324094973082786395147137)
  ·
    refine ⟨18993071229812089796360353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25324094973082786395147137 18993071229812089796360353)
    ·
      refine ⟨14244803422359067347270265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18993071229812089796360353 14244803422359067347270265)
      ·
        refine ⟨10683602566769300510452699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14244803422359067347270265 10683602566769300510452699)
        ·
          refine ⟨16025403850153950765679049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10683602566769300510452699 16025403850153950765679049)
          ·
            refine ⟨12019052887615463074259287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16025403850153950765679049 12019052887615463074259287)
            ·
              refine ⟨18028579331423194611388931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12019052887615463074259287 18028579331423194611388931)
              ·
                refine ⟨27042868997134791917083397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18028579331423194611388931 27042868997134791917083397)
                ·
                  refine ⟨5070537936962773484453137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27042868997134791917083397 5070537936962773484453137)
                  ·
                    refine ⟨3802903452722080113339853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5070537936962773484453137 3802903452722080113339853)
                    ·
                      refine ⟨1426088794770780042502445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3802903452722080113339853 1426088794770780042502445)
                      ·
                        rfl

theorem cell23_2777298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 2, 1, 1, 4, 2, 3].length) (baseStart_2777298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777298 prefixEnd_2777298 := by exact prefixLift 2777298
  have htrace : WordTrace (prefixWord ++ tailWord_2777298) baseStart_2777298 baseEnd_2777298 := by
    simpa [prefixWord, tailWord_2777298, baseEnd_2777298] using wordTrace_append hprefix tailTrace_2777298
  have hstable : (prefixWord ++ tailWord_2777298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777298).length < 2 ^ (prefixWord ++ tailWord_2777298).sum := by decide
  have hdescent : baseEnd_2777298 < baseStart_2777298 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777328 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 3, 1, 3]
def baseStart_2777328 : Nat := 118140960795 + 2777328 * 2 ^ 59
def prefixEnd_2777328 : Nat := 4983230072969 + 3 ^ 40 * 2777328 * 2
def baseEnd_2777328 : Nat := 1426104199190414925127307

theorem tailTrace_2777328 : CollatzResearch.WordTrace tailWord_2777328 prefixEnd_2777328 1426104199190414925127307 := by
  unfold tailWord_2777328
  simp only [CollatzResearch.WordTrace]
  refine ⟨50648737041111230352090319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67531649388148307136120425 50648737041111230352090319)
  ·
    refine ⟨75973105561666845528135479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50648737041111230352090319 75973105561666845528135479)
    ·
      refine ⟨113959658342500268292203219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75973105561666845528135479 113959658342500268292203219)
      ·
        refine ⟨170939487513750402438304829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113959658342500268292203219 170939487513750402438304829)
        ·
          refine ⟨64102307817656400914364311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170939487513750402438304829 64102307817656400914364311)
          ·
            refine ⟨96153461726484601371546467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64102307817656400914364311 96153461726484601371546467)
            ·
              refine ⟨144230192589726902057319701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96153461726484601371546467 144230192589726902057319701)
              ·
                refine ⟨6760790277643448533936861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 144230192589726902057319701 6760790277643448533936861)
                ·
                  refine ⟨2535296354116293200226323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6760790277643448533936861 2535296354116293200226323)
                  ·
                    refine ⟨3802944531174439800339485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535296354116293200226323 3802944531174439800339485)
                    ·
                      refine ⟨1426104199190414925127307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3802944531174439800339485 1426104199190414925127307)
                      ·
                        rfl

theorem cell23_2777328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 3, 1, 3].length) (baseStart_2777328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777328 prefixEnd_2777328 := by exact prefixLift 2777328
  have htrace : WordTrace (prefixWord ++ tailWord_2777328) baseStart_2777328 baseEnd_2777328 := by
    simpa [prefixWord, tailWord_2777328, baseEnd_2777328] using wordTrace_append hprefix tailTrace_2777328
  have hstable : (prefixWord ++ tailWord_2777328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777328).length < 2 ^ (prefixWord ++ tailWord_2777328).sum := by decide
  have hdescent : baseEnd_2777328 < baseStart_2777328 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777331 : List Nat := [1, 1, 1, 2, 2, 4, 3, 1, 3, 5]
def baseStart_2777331 : Nat := 118140960795 + 2777331 * 2 ^ 59
def prefixEnd_2777331 : Nat := 4983230072969 + 3 ^ 40 * 2777331 * 2
def baseEnd_2777331 : Nat := 475368579877459471129931

theorem tailTrace_2777331 : CollatzResearch.WordTrace tailWord_2777331 prefixEnd_2777331 475368579877459471129931 := by
  unfold tailWord_2777331
  simp only [CollatzResearch.WordTrace]
  refine ⟨101297583501211592216539847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67531722334141061477693231 101297583501211592216539847)
  ·
    refine ⟨151946375251817388324809771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101297583501211592216539847 151946375251817388324809771)
    ·
      refine ⟨227919562877726082487214657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151946375251817388324809771 227919562877726082487214657)
      ·
        refine ⟨170939672158294561865410993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227919562877726082487214657 170939672158294561865410993)
        ·
          refine ⟨128204754118720921399058245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 170939672158294561865410993 128204754118720921399058245)
          ·
            refine ⟨24038391397260172762323421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128204754118720921399058245 24038391397260172762323421)
            ·
              refine ⟨9014396773972564785871283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24038391397260172762323421 9014396773972564785871283)
              ·
                refine ⟨13521595160958847178806925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014396773972564785871283 13521595160958847178806925)
                ·
                  refine ⟨5070598185359567692052597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13521595160958847178806925 5070598185359567692052597)
                  ·
                    refine ⟨475368579877459471129931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5070598185359567692052597 475368579877459471129931)
                    ·
                      rfl

theorem cell23_2777331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 1, 3, 5].length) (baseStart_2777331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777331 prefixEnd_2777331 := by exact prefixLift 2777331
  have htrace : WordTrace (prefixWord ++ tailWord_2777331) baseStart_2777331 baseEnd_2777331 := by
    simpa [prefixWord, tailWord_2777331, baseEnd_2777331] using wordTrace_append hprefix tailTrace_2777331
  have hstable : (prefixWord ++ tailWord_2777331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777331).length < 2 ^ (prefixWord ++ tailWord_2777331).sum := by decide
  have hdescent : baseEnd_2777331 < baseStart_2777331 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777371 : List Nat := [1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5]
def baseStart_2777371 : Nat := 118140960795 + 2777371 * 2 ^ 59
def prefixEnd_2777371 : Nat := 4983230072969 + 3 ^ 40 * 2777371 * 2
def baseEnd_2777371 : Nat := 1426126278858558256889609

theorem tailTrace_2777371 : CollatzResearch.WordTrace tailWord_2777371 prefixEnd_2777371 1426126278858558256889609 := by
  unfold tailWord_2777371
  simp only [CollatzResearch.WordTrace]
  refine ⟨101299042421066679047995967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67532694947377786031997311 101299042421066679047995967)
  ·
    refine ⟨151948563631600018571993951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101299042421066679047995967 151948563631600018571993951)
    ·
      refine ⟨227922845447400027857990927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151948563631600018571993951 227922845447400027857990927)
      ·
        refine ⟨341884268171100041786986391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227922845447400027857990927 341884268171100041786986391)
        ·
          refine ⟨512826402256650062680479587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 341884268171100041786986391 512826402256650062680479587)
          ·
            refine ⟨769239603384975094020719381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 512826402256650062680479587 769239603384975094020719381)
            ·
              refine ⟨36058106408670707532221221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 769239603384975094020719381 36058106408670707532221221)
              ·
                refine ⟨6760894951625757662291479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36058106408670707532221221 6760894951625757662291479)
                ·
                  refine ⟨10141342427438636493437219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760894951625757662291479 10141342427438636493437219)
                  ·
                    refine ⟨15212013641157954740155829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10141342427438636493437219 15212013641157954740155829)
                    ·
                      refine ⟨1426126278858558256889609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15212013641157954740155829 1426126278858558256889609)
                      ·
                        rfl

theorem cell23_2777371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 4, 1, 1, 5].length) (baseStart_2777371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777371 prefixEnd_2777371 := by exact prefixLift 2777371
  have htrace : WordTrace (prefixWord ++ tailWord_2777371) baseStart_2777371 baseEnd_2777371 := by
    simpa [prefixWord, tailWord_2777371, baseEnd_2777371] using wordTrace_append hprefix tailTrace_2777371
  have hstable : (prefixWord ++ tailWord_2777371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777371).length < 2 ^ (prefixWord ++ tailWord_2777371).sum := by decide
  have hdescent : baseEnd_2777371 < baseStart_2777371 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777378 : List Nat := [3, 3, 1, 1, 3, 1, 1, 3, 1, 6]
def baseStart_2777378 : Nat := 118140960795 + 2777378 * 2 ^ 59
def prefixEnd_2777378 : Nat := 4983230072969 + 3 ^ 40 * 2777378 * 2
def baseEnd_2777378 : Nat := 475376624407713243167359

theorem tailTrace_2777378 : CollatzResearch.WordTrace tailWord_2777378 prefixEnd_2777378 475376624407713243167359 := by
  unfold tailWord_2777378
  simp only [CollatzResearch.WordTrace]
  refine ⟨25324824433010329810875197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67532865154694212829000525 25324824433010329810875197)
  ·
    refine ⟨9496809162378873679078199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25324824433010329810875197 9496809162378873679078199)
    ·
      refine ⟨14245213743568310518617299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9496809162378873679078199 14245213743568310518617299)
      ·
        refine ⟨21367820615352465777925949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14245213743568310518617299 21367820615352465777925949)
        ·
          refine ⟨8012932730757174666722231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21367820615352465777925949 8012932730757174666722231)
          ·
            refine ⟨12019399096135762000083347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8012932730757174666722231 12019399096135762000083347)
            ·
              refine ⟨18029098644203643000125021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12019399096135762000083347 18029098644203643000125021)
              ·
                refine ⟨6760911991576366125046883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18029098644203643000125021 6760911991576366125046883)
                ·
                  refine ⟨10141367987364549187570325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6760911991576366125046883 10141367987364549187570325)
                  ·
                    refine ⟨475376624407713243167359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10141367987364549187570325 475376624407713243167359)
                    ·
                      rfl

theorem cell23_2777378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 3, 1, 6].length) (baseStart_2777378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777378 prefixEnd_2777378 := by exact prefixLift 2777378
  have htrace : WordTrace (prefixWord ++ tailWord_2777378) baseStart_2777378 baseEnd_2777378 := by
    simpa [prefixWord, tailWord_2777378, baseEnd_2777378] using wordTrace_append hprefix tailTrace_2777378
  have hstable : (prefixWord ++ tailWord_2777378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777378).length < 2 ^ (prefixWord ++ tailWord_2777378).sum := by decide
  have hdescent : baseEnd_2777378 < baseStart_2777378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777388 : List Nat := [2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 3]
def baseStart_2777388 : Nat := 118140960795 + 2777388 * 2 ^ 59
def prefixEnd_2777388 : Nat := 4983230072969 + 3 ^ 40 * 2777388 * 2
def baseEnd_2777388 : Nat := 1426135008029684690377031

theorem tailTrace_2777388 : CollatzResearch.WordTrace tailWord_2777388 prefixEnd_2777388 1426135008029684690377031 := by
  unfold tailWord_2777388
  simp only [CollatzResearch.WordTrace]
  refine ⟨50649831231002545475682409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67533108308003393967576545 50649831231002545475682409)
  ·
    refine ⟨37987373423251909106761807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50649831231002545475682409 37987373423251909106761807)
    ·
      refine ⟨56981060134877863660142711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37987373423251909106761807 56981060134877863660142711)
      ·
        refine ⟨85471590202316795490214067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56981060134877863660142711 85471590202316795490214067)
        ·
          refine ⟨128207385303475193235321101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85471590202316795490214067 128207385303475193235321101)
          ·
            refine ⟨48077769488803197463245413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128207385303475193235321101 48077769488803197463245413)
            ·
              refine ⟨9014581779150599524358515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48077769488803197463245413 9014581779150599524358515)
              ·
                refine ⟨13521872668725899286537773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014581779150599524358515 13521872668725899286537773)
                ·
                  refine ⟨5070702250772212232451665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13521872668725899286537773 5070702250772212232451665)
                  ·
                    refine ⟨3803026688079159174338749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5070702250772212232451665 3803026688079159174338749)
                    ·
                      refine ⟨1426135008029684690377031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803026688079159174338749 1426135008029684690377031)
                      ·
                        rfl

theorem cell23_2777388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 3].length) (baseStart_2777388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777388 prefixEnd_2777388 := by exact prefixLift 2777388
  have htrace : WordTrace (prefixWord ++ tailWord_2777388) baseStart_2777388 baseEnd_2777388 := by
    simpa [prefixWord, tailWord_2777388, baseEnd_2777388] using wordTrace_append hprefix tailTrace_2777388
  have hstable : (prefixWord ++ tailWord_2777388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777388).length < 2 ^ (prefixWord ++ tailWord_2777388).sum := by decide
  have hdescent : baseEnd_2777388 < baseStart_2777388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777402 : List Nat := [3, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4]
def baseStart_2777402 : Nat := 118140960795 + 2777402 * 2 ^ 59
def prefixEnd_2777402 : Nat := 4983230072969 + 3 ^ 40 * 2777402 * 2
def baseEnd_2777402 : Nat := 1426142196758847635601967

theorem tailTrace_2777402 : CollatzResearch.WordTrace tailWord_2777402 prefixEnd_2777402 1426142196758847635601967 := by
  unfold tailWord_2777402
  simp only [CollatzResearch.WordTrace]
  refine ⟨25325043270988592835593615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67533448722636247561582973 25325043270988592835593615)
  ·
    refine ⟨37987564906482889253390423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25325043270988592835593615 37987564906482889253390423)
    ·
      refine ⟨56981347359724333880085635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37987564906482889253390423 56981347359724333880085635)
      ·
        refine ⟨85472021039586500820128453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56981347359724333880085635 85472021039586500820128453)
        ·
          refine ⟨16026003944922468903774085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85472021039586500820128453 16026003944922468903774085)
          ·
            refine ⟨3004875739672962919457641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16026003944922468903774085 3004875739672962919457641)
            ·
              refine ⟨2253656804754722189593231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3004875739672962919457641 2253656804754722189593231)
              ·
                refine ⟨3380485207132083284389847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253656804754722189593231 3380485207132083284389847)
                ·
                  refine ⟨5070727810698124926584771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3380485207132083284389847 5070727810698124926584771)
                  ·
                    refine ⟨7606091716047187389877157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5070727810698124926584771 7606091716047187389877157)
                    ·
                      refine ⟨1426142196758847635601967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7606091716047187389877157 1426142196758847635601967)
                      ·
                        rfl

theorem cell23_2777402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4].length) (baseStart_2777402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777402 prefixEnd_2777402 := by exact prefixLift 2777402
  have htrace : WordTrace (prefixWord ++ tailWord_2777402) baseStart_2777402 baseEnd_2777402 := by
    simpa [prefixWord, tailWord_2777402, baseEnd_2777402] using wordTrace_append hprefix tailTrace_2777402
  have hstable : (prefixWord ++ tailWord_2777402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777402).length < 2 ^ (prefixWord ++ tailWord_2777402).sum := by decide
  have hdescent : baseEnd_2777402 < baseStart_2777402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777412 : List Nat := [2, 3, 4, 1, 2, 1, 1, 1, 4, 4]
def baseStart_2777412 : Nat := 118140960795 + 2777412 * 2 ^ 59
def prefixEnd_2777412 : Nat := 4983230072969 + 3 ^ 40 * 2777412 * 2
def baseEnd_2777412 : Nat := 475382443855130865492307

theorem tailTrace_2777412 : CollatzResearch.WordTrace tailWord_2777412 prefixEnd_2777412 475382443855130865492307 := by
  unfold tailWord_2777412
  simp only [CollatzResearch.WordTrace]
  refine ⟨50650268906959071525119245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67533691875945428700158993 50650268906959071525119245)
  ·
    refine ⟨18993850840109651821919717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50650268906959071525119245 18993850840109651821919717)
    ·
      refine ⟨3561347032520559716609947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18993850840109651821919717 3561347032520559716609947)
      ·
        refine ⟨5342020548780839574914921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3561347032520559716609947 5342020548780839574914921)
        ·
          refine ⟨4006515411585629681186191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5342020548780839574914921 4006515411585629681186191)
          ·
            refine ⟨6009773117378444521779287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4006515411585629681186191 6009773117378444521779287)
            ·
              refine ⟨9014659676067666782668931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6009773117378444521779287 9014659676067666782668931)
              ·
                refine ⟨13521989514101500174003397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9014659676067666782668931 13521989514101500174003397)
                ·
                  refine ⟨2535373033894031282625637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13521989514101500174003397 2535373033894031282625637)
                  ·
                    refine ⟨475382443855130865492307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2535373033894031282625637 475382443855130865492307)
                    ·
                      rfl

theorem cell23_2777412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_2777412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777412 prefixEnd_2777412 := by exact prefixLift 2777412
  have htrace : WordTrace (prefixWord ++ tailWord_2777412) baseStart_2777412 baseEnd_2777412 := by
    simpa [prefixWord, tailWord_2777412, baseEnd_2777412] using wordTrace_append hprefix tailTrace_2777412
  have hstable : (prefixWord ++ tailWord_2777412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777412).length < 2 ^ (prefixWord ++ tailWord_2777412).sum := by decide
  have hdescent : baseEnd_2777412 < baseStart_2777412 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777448 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 2, 2, 5]
def baseStart_2777448 : Nat := 118140960795 + 2777448 * 2 ^ 59
def prefixEnd_2777448 : Nat := 4983230072969 + 3 ^ 40 * 2777448 * 2
def baseEnd_2777448 : Nat := 1426165816868954455626755

theorem tailTrace_2777448 : CollatzResearch.WordTrace tailWord_2777448 prefixEnd_2777448 1426165816868954455626755 := by
  unfold tailWord_2777448
  simp only [CollatzResearch.WordTrace]
  refine ⟨50650925420893860599274499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67534567227858480799032665 50650925420893860599274499)
  ·
    refine ⟨75976388131340790898911749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50650925420893860599274499 75976388131340790898911749)
    ·
      refine ⟨14245572774626398293545953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 75976388131340790898911749 14245572774626398293545953)
      ·
        refine ⟨10684179580969798720159465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14245572774626398293545953 10684179580969798720159465)
        ·
          refine ⟨8013134685727349040119599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10684179580969798720159465 8013134685727349040119599)
          ·
            refine ⟨12019702028591023560179399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8013134685727349040119599 12019702028591023560179399)
            ·
              refine ⟨18029553042886535340269099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12019702028591023560179399 18029553042886535340269099)
              ·
                refine ⟨27044329564329803010403649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18029553042886535340269099 27044329564329803010403649)
                ·
                  refine ⟨20283247173247352257802737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27044329564329803010403649 20283247173247352257802737)
                  ·
                    refine ⟨15212435379935514193352053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20283247173247352257802737 15212435379935514193352053)
                    ·
                      refine ⟨1426165816868954455626755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15212435379935514193352053 1426165816868954455626755)
                      ·
                        rfl

theorem cell23_2777448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_2777448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777448 prefixEnd_2777448 := by exact prefixLift 2777448
  have htrace : WordTrace (prefixWord ++ tailWord_2777448) baseStart_2777448 baseEnd_2777448 := by
    simpa [prefixWord, tailWord_2777448, baseEnd_2777448] using wordTrace_append hprefix tailTrace_2777448
  have hstable : (prefixWord ++ tailWord_2777448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777448).length < 2 ^ (prefixWord ++ tailWord_2777448).sum := by decide
  have hdescent : baseEnd_2777448 < baseStart_2777448 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777486 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3]
def baseStart_2777486 : Nat := 118140960795 + 2777486 * 2 ^ 59
def prefixEnd_2777486 : Nat := 4983230072969 + 3 ^ 40 * 2777486 * 2
def baseEnd_2777486 : Nat := 1426185329133825306951581

theorem tailTrace_2777486 : CollatzResearch.WordTrace tailWord_2777486 prefixEnd_2777486 1426185329133825306951581 := by
  unfold tailWord_2777486
  simp only [CollatzResearch.WordTrace]
  refine ⟨12662904601956256711054039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67535491210433369125621541 12662904601956256711054039)
  ·
    refine ⟨18994356902934385066581059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12662904601956256711054039 18994356902934385066581059)
    ·
      refine ⟨28491535354401577599871589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18994356902934385066581059 28491535354401577599871589)
      ·
        refine ⟨5342162878950295799975923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28491535354401577599871589 5342162878950295799975923)
        ·
          refine ⟨8013244318425443699963885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5342162878950295799975923 8013244318425443699963885)
          ·
            refine ⟨3004966619409541387486457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8013244318425443699963885 3004966619409541387486457)
            ·
              refine ⟨2253724964557156040614843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3004966619409541387486457 2253724964557156040614843)
              ·
                refine ⟨3380587446835734060922265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253724964557156040614843 3380587446835734060922265)
                ·
                  refine ⟨2535440585126800545691699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380587446835734060922265 2535440585126800545691699)
                  ·
                    refine ⟨3803160877690200818537549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535440585126800545691699 3803160877690200818537549)
                    ·
                      refine ⟨1426185329133825306951581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803160877690200818537549 1426185329133825306951581)
                      ·
                        rfl

theorem cell23_2777486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_2777486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777486 prefixEnd_2777486 := by exact prefixLift 2777486
  have htrace : WordTrace (prefixWord ++ tailWord_2777486) baseStart_2777486 baseEnd_2777486 := by
    simpa [prefixWord, tailWord_2777486, baseEnd_2777486] using wordTrace_append hprefix tailTrace_2777486
  have hstable : (prefixWord ++ tailWord_2777486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777486).length < 2 ^ (prefixWord ++ tailWord_2777486).sum := by decide
  have hdescent : baseEnd_2777486 < baseStart_2777486 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777532 : List Nat := [2, 2, 2, 4, 1, 2, 1, 4, 5]
def baseStart_2777532 : Nat := 118140960795 + 2777532 * 2 ^ 59
def prefixEnd_2777532 : Nat := 4983230072969 + 3 ^ 40 * 2777532 * 2
def baseEnd_2777532 : Nat := 158467661027103569664041

theorem tailTrace_2777532 : CollatzResearch.WordTrace tailWord_2777532 prefixEnd_2777532 158467661027103569664041 := by
  unfold tailWord_2777532
  simp only [CollatzResearch.WordTrace]
  refine ⟨50652457286741701772303425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67536609715655602363071233 50652457286741701772303425)
  ·
    refine ⟨37989342965056276329227569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50652457286741701772303425 37989342965056276329227569)
    ·
      refine ⟨28492007223792207246920677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37989342965056276329227569 28492007223792207246920677)
      ·
        refine ⟨5342251354461038858797627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28492007223792207246920677 5342251354461038858797627)
        ·
          refine ⟨8013377031691558288196441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5342251354461038858797627 8013377031691558288196441)
          ·
            refine ⟨6010032773768668716147331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8013377031691558288196441 6010032773768668716147331)
            ·
              refine ⟨9015049160653003074220997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6010032773768668716147331 9015049160653003074220997)
              ·
                refine ⟨1690321717622438076416437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9015049160653003074220997 1690321717622438076416437)
                ·
                  refine ⟨158467661027103569664041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1690321717622438076416437 158467661027103569664041)
                  ·
                    rfl

theorem cell23_2777532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 4, 5].length) (baseStart_2777532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777532 prefixEnd_2777532 := by exact prefixLift 2777532
  have htrace : WordTrace (prefixWord ++ tailWord_2777532) baseStart_2777532 baseEnd_2777532 := by
    simpa [prefixWord, tailWord_2777532, baseEnd_2777532] using wordTrace_append hprefix tailTrace_2777532
  have hstable : (prefixWord ++ tailWord_2777532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777532).length < 2 ^ (prefixWord ++ tailWord_2777532).sum := by decide
  have hdescent : baseEnd_2777532 < baseStart_2777532 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777565 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 4]
def baseStart_2777565 : Nat := 118140960795 + 2777565 * 2 ^ 59
def prefixEnd_2777565 : Nat := 4983230072969 + 3 ^ 40 * 2777565 * 2
def baseEnd_2777565 : Nat := 1426225894105530497863717

theorem tailTrace_2777565 : CollatzResearch.WordTrace tailWord_2777565 prefixEnd_2777565 1426225894105530497863717 := by
  unfold tailWord_2777565
  simp only [CollatzResearch.WordTrace]
  refine ⟨101306118182363850180558149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67537412121575900120372099 101306118182363850180558149)
  ·
    refine ⟨18994897159193221908854653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101306118182363850180558149 18994897159193221908854653)
    ·
      refine ⟨7123086434697458215820495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18994897159193221908854653 7123086434697458215820495)
      ·
        refine ⟨10684629652046187323730743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123086434697458215820495 10684629652046187323730743)
        ·
          refine ⟨16026944478069280985596115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10684629652046187323730743 16026944478069280985596115)
          ·
            refine ⟨24040416717103921478394173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16026944478069280985596115 24040416717103921478394173)
            ·
              refine ⟨9015156268913970554397815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24040416717103921478394173 9015156268913970554397815)
              ·
                refine ⟨13522734403370955831596723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9015156268913970554397815 13522734403370955831596723)
                ·
                  refine ⟨20284101605056433747395085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13522734403370955831596723 20284101605056433747395085)
                  ·
                    refine ⟨7606538101896162655273157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20284101605056433747395085 7606538101896162655273157)
                    ·
                      refine ⟨1426225894105530497863717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7606538101896162655273157 1426225894105530497863717)
                      ·
                        rfl

theorem cell23_2777565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 1, 3, 4].length) (baseStart_2777565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777565 prefixEnd_2777565 := by exact prefixLift 2777565
  have htrace : WordTrace (prefixWord ++ tailWord_2777565) baseStart_2777565 baseEnd_2777565 := by
    simpa [prefixWord, tailWord_2777565, baseEnd_2777565] using wordTrace_append hprefix tailTrace_2777565
  have hstable : (prefixWord ++ tailWord_2777565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777565).length < 2 ^ (prefixWord ++ tailWord_2777565).sum := by decide
  have hdescent : baseEnd_2777565 < baseStart_2777565 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777575 : List Nat := [1, 1, 5, 2, 1, 1, 1, 2, 5, 4]
def baseStart_2777575 : Nat := 118140960795 + 2777575 * 2 ^ 59
def prefixEnd_2777575 : Nat := 4983230072969 + 3 ^ 40 * 2777575 * 2
def baseEnd_2777575 : Nat := 475410342970691819579557

theorem tailTrace_2777575 : CollatzResearch.WordTrace tailWord_2777575 prefixEnd_2777575 475410342970691819579557 := by
  unfold tailWord_2777575
  simp only [CollatzResearch.WordTrace]
  refine ⟨101306482912327621888422179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67537655274885081258948119 101306482912327621888422179)
  ·
    refine ⟨151959724368491432832633269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101306482912327621888422179 151959724368491432832633269)
    ·
      refine ⟨14246224159546071828059369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151959724368491432832633269 14246224159546071828059369)
      ·
        refine ⟨10684668119659553871044527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14246224159546071828059369 10684668119659553871044527)
        ·
          refine ⟨16027002179489330806566791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10684668119659553871044527 16027002179489330806566791)
          ·
            refine ⟨24040503269233996209850187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16027002179489330806566791 24040503269233996209850187)
            ·
              refine ⟨36060754903850994314775281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24040503269233996209850187 36060754903850994314775281)
              ·
                refine ⟨27045566177888245736081461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36060754903850994314775281 27045566177888245736081461)
                ·
                  refine ⟨2535521829177023037757637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 27045566177888245736081461 2535521829177023037757637)
                  ·
                    refine ⟨475410342970691819579557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2535521829177023037757637 475410342970691819579557)
                    ·
                      rfl

theorem cell23_2777575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 5, 4].length) (baseStart_2777575 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777575 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777575 prefixEnd_2777575 := by exact prefixLift 2777575
  have htrace : WordTrace (prefixWord ++ tailWord_2777575) baseStart_2777575 baseEnd_2777575 := by
    simpa [prefixWord, tailWord_2777575, baseEnd_2777575] using wordTrace_append hprefix tailTrace_2777575
  have hstable : (prefixWord ++ tailWord_2777575).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777575).length < 2 ^ (prefixWord ++ tailWord_2777575).sum := by decide
  have hdescent : baseEnd_2777575 < baseStart_2777575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777582 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2]
def baseStart_2777582 : Nat := 118140960795 + 2777582 * 2 ^ 59
def prefixEnd_2777582 : Nat := 4983230072969 + 3 ^ 40 * 2777582 * 2
def baseEnd_2777582 : Nat := 1426234623276656931351139

theorem tailTrace_2777582 : CollatzResearch.WordTrace tailWord_2777582 prefixEnd_2777582 1426234623276656931351139 := by
  unfold tailWord_2777582
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663342277912782760490875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67537825482201508055951333 12663342277912782760490875)
  ·
    refine ⟨18995013416869174140736313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12663342277912782760490875 18995013416869174140736313)
    ·
      refine ⟨14246260062651880605552235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18995013416869174140736313 14246260062651880605552235)
      ·
        refine ⟨21369390093977820908328353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14246260062651880605552235 21369390093977820908328353)
        ·
          refine ⟨16027042570483365681246265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21369390093977820908328353 16027042570483365681246265)
          ·
            refine ⟨12020281927862524260934699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16027042570483365681246265 12020281927862524260934699)
            ·
              refine ⟨18030422891793786391402049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12020281927862524260934699 18030422891793786391402049)
              ·
                refine ⟨13522817168845339793551537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18030422891793786391402049 13522817168845339793551537)
                ·
                  refine ⟨10142112876634004845163653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13522817168845339793551537 10142112876634004845163653)
                  ·
                    refine ⟨1901646164368875908468185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10142112876634004845163653 1901646164368875908468185)
                    ·
                      refine ⟨1426234623276656931351139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901646164368875908468185 1426234623276656931351139)
                      ·
                        rfl

theorem cell23_2777582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 2, 4, 2].length) (baseStart_2777582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777582 prefixEnd_2777582 := by exact prefixLift 2777582
  have htrace : WordTrace (prefixWord ++ tailWord_2777582) baseStart_2777582 baseEnd_2777582 := by
    simpa [prefixWord, tailWord_2777582, baseEnd_2777582] using wordTrace_append hprefix tailTrace_2777582
  have hstable : (prefixWord ++ tailWord_2777582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777582).length < 2 ^ (prefixWord ++ tailWord_2777582).sum := by decide
  have hdescent : baseEnd_2777582 < baseStart_2777582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777585 : List Nat := [1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 3]
def baseStart_2777585 : Nat := 118140960795 + 2777585 * 2 ^ 59
def prefixEnd_2777585 : Nat := 4983230072969 + 3 ^ 40 * 2777585 * 2
def baseEnd_2777585 : Nat := 1426236163718620419613625

theorem tailTrace_2777585 : CollatzResearch.WordTrace tailWord_2777585 prefixEnd_2777585 1426236163718620419613625 := by
  unfold tailWord_2777585
  simp only [CollatzResearch.WordTrace]
  refine ⟨101306847642291393596286209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67537898428194262397524139 101306847642291393596286209)
  ·
    refine ⟨75980135731718545197214657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101306847642291393596286209 75980135731718545197214657)
    ·
      refine ⟨56985101798788908897910993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75980135731718545197214657 56985101798788908897910993)
      ·
        refine ⟨42738826349091681673433245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56985101798788908897910993 42738826349091681673433245)
        ·
          refine ⟨16027059880909380627537467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42738826349091681673433245 16027059880909380627537467)
          ·
            refine ⟨24040589821364070941306201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16027059880909380627537467 24040589821364070941306201)
            ·
              refine ⟨18030442366023053205979651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24040589821364070941306201 18030442366023053205979651)
              ·
                refine ⟨27045663549034579808969477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18030442366023053205979651 27045663549034579808969477)
                ·
                  refine ⟨5071061915443983714181777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27045663549034579808969477 5071061915443983714181777)
                  ·
                    refine ⟨3803296436582987785636333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5071061915443983714181777 3803296436582987785636333)
                    ·
                      refine ⟨1426236163718620419613625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803296436582987785636333 1426236163718620419613625)
                      ·
                        rfl

theorem cell23_2777585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_2777585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777585 prefixEnd_2777585 := by exact prefixLift 2777585
  have htrace : WordTrace (prefixWord ++ tailWord_2777585) baseStart_2777585 baseEnd_2777585 := by
    simpa [prefixWord, tailWord_2777585, baseEnd_2777585] using wordTrace_append hprefix tailTrace_2777585
  have hstable : (prefixWord ++ tailWord_2777585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777585).length < 2 ^ (prefixWord ++ tailWord_2777585).sum := by decide
  have hdescent : baseEnd_2777585 < baseStart_2777585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777592 : List Nat := [2, 1, 2, 1, 1, 4, 1, 6, 1, 4]
def baseStart_2777592 : Nat := 118140960795 + 2777592 * 2 ^ 59
def prefixEnd_2777592 : Nat := 4983230072969 + 3 ^ 40 * 2777592 * 2
def baseEnd_2777592 : Nat := 475413252694400630742031

theorem tailTrace_2777592 : CollatzResearch.WordTrace tailWord_2777592 prefixEnd_2777592 475413252694400630742031 := by
  unfold tailWord_2777592
  simp only [CollatzResearch.WordTrace]
  refine ⟨50653551476633016895895515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67538068635510689194527353 50653551476633016895895515)
  ·
    refine ⟨75980327214949525343843273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50653551476633016895895515 75980327214949525343843273)
    ·
      refine ⟨56985245411212144007882455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75980327214949525343843273 56985245411212144007882455)
      ·
        refine ⟨85477868116818216011823683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56985245411212144007882455 85477868116818216011823683)
        ·
          refine ⟨128216802175227324017735525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85477868116818216011823683 128216802175227324017735525)
          ·
            refine ⟨24040650407855123253325411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 128216802175227324017735525 24040650407855123253325411)
            ·
              refine ⟨36060975611782684879988117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24040650407855123253325411 36060975611782684879988117)
              ·
                refine ⟨1690358231802313353749443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36060975611782684879988117 1690358231802313353749443)
                ·
                  refine ⟨2535537347703470030624165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690358231802313353749443 2535537347703470030624165)
                  ·
                    refine ⟨475413252694400630742031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2535537347703470030624165 475413252694400630742031)
                    ·
                      rfl

theorem cell23_2777592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 1, 4].length) (baseStart_2777592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777592 prefixEnd_2777592 := by exact prefixLift 2777592
  have htrace : WordTrace (prefixWord ++ tailWord_2777592) baseStart_2777592 baseEnd_2777592 := by
    simpa [prefixWord, tailWord_2777592, baseEnd_2777592] using wordTrace_append hprefix tailTrace_2777592
  have hstable : (prefixWord ++ tailWord_2777592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777592).length < 2 ^ (prefixWord ++ tailWord_2777592).sum := by decide
  have hdescent : baseEnd_2777592 < baseStart_2777592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777608 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 3, 2, 6]
def baseStart_2777608 : Nat := 118140960795 + 2777608 * 2 ^ 59
def prefixEnd_2777608 : Nat := 4983230072969 + 3 ^ 40 * 2777608 * 2
def baseEnd_2777608 : Nat := 1426247973773673829626019

theorem tailTrace_2777608 : CollatzResearch.WordTrace tailWord_2777608 prefixEnd_2777608 1426247973773673829626019 := by
  unfold tailWord_2777608
  simp only [CollatzResearch.WordTrace]
  refine ⟨50653843260604034262186739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67538457680805379016248985 50653843260604034262186739)
  ·
    refine ⟨75980764890906051393280109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50653843260604034262186739 75980764890906051393280109)
    ·
      refine ⟨28492786834089769272480041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75980764890906051393280109 28492786834089769272480041)
      ·
        refine ⟨21369590125567326954360031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28492786834089769272480041 21369590125567326954360031)
        ·
          refine ⟨32054385188350990431540047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21369590125567326954360031 32054385188350990431540047)
          ·
            refine ⟨48081577782526485647310071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32054385188350990431540047 48081577782526485647310071)
            ·
              refine ⟨72122366673789728470965107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48081577782526485647310071 72122366673789728470965107)
              ·
                refine ⟨108183550010684592706447661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72122366673789728470965107 108183550010684592706447661)
                ·
                  refine ⟨40568831254006722264917873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 108183550010684592706447661 40568831254006722264917873)
                  ·
                    refine ⟨30426623440505041698688405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 40568831254006722264917873 30426623440505041698688405)
                    ·
                      refine ⟨1426247973773673829626019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30426623440505041698688405 1426247973773673829626019)
                      ·
                        rfl

theorem cell23_2777608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_2777608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777608 prefixEnd_2777608 := by exact prefixLift 2777608
  have htrace : WordTrace (prefixWord ++ tailWord_2777608) baseStart_2777608 baseEnd_2777608 := by
    simpa [prefixWord, tailWord_2777608, baseEnd_2777608] using wordTrace_append hprefix tailTrace_2777608
  have hstable : (prefixWord ++ tailWord_2777608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777608).length < 2 ^ (prefixWord ++ tailWord_2777608).sum := by decide
  have hdescent : baseEnd_2777608 < baseStart_2777608 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777649 : List Nat := [1, 2, 2, 3, 1, 1, 2, 6, 1, 1, 3]
def baseStart_2777649 : Nat := 118140960795 + 2777649 * 2 ^ 59
def prefixEnd_2777649 : Nat := 4983230072969 + 3 ^ 40 * 2777649 * 2
def baseEnd_2777649 : Nat := 1426269026480508169213331

theorem tailTrace_2777649 : CollatzResearch.WordTrace tailWord_2777649 prefixEnd_2777649 1426269026480508169213331 := by
  unfold tailWord_2777649
  simp only [CollatzResearch.WordTrace]
  refine ⟨101309181914059532526616001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67539454609373021684410667 101309181914059532526616001)
  ·
    refine ⟨75981886435544649394962001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101309181914059532526616001 75981886435544649394962001)
    ·
      refine ⟨56986414826658487046221501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75981886435544649394962001 56986414826658487046221501)
      ·
        refine ⟨21369905559996932642333063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 56986414826658487046221501 21369905559996932642333063)
        ·
          refine ⟨32054858339995398963499595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21369905559996932642333063 32054858339995398963499595)
          ·
            refine ⟨48082287509993098445249393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32054858339995398963499595 48082287509993098445249393)
            ·
              refine ⟨36061715632494823833937045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48082287509993098445249393 36061715632494823833937045)
              ·
                refine ⟨1690392920273194867215799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 36061715632494823833937045 1690392920273194867215799)
                ·
                  refine ⟨2535589380409792300823699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690392920273194867215799 2535589380409792300823699)
                  ·
                    refine ⟨3803384070614688451235549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535589380409792300823699 3803384070614688451235549)
                    ·
                      refine ⟨1426269026480508169213331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803384070614688451235549 1426269026480508169213331)
                      ·
                        rfl

theorem cell23_2777649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_2777649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777649 prefixEnd_2777649 := by exact prefixLift 2777649
  have htrace : WordTrace (prefixWord ++ tailWord_2777649) baseStart_2777649 baseEnd_2777649 := by
    simpa [prefixWord, tailWord_2777649, baseEnd_2777649] using wordTrace_append hprefix tailTrace_2777649
  have hstable : (prefixWord ++ tailWord_2777649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777649).length < 2 ^ (prefixWord ++ tailWord_2777649).sum := by decide
  have hdescent : baseEnd_2777649 < baseStart_2777649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777655 : List Nat := [1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 4]
def baseStart_2777655 : Nat := 118140960795 + 2777655 * 2 ^ 59
def prefixEnd_2777655 : Nat := 4983230072969 + 3 ^ 40 * 2777655 * 2
def baseEnd_2777655 : Nat := 1426272107364435145738303

theorem tailTrace_2777655 : CollatzResearch.WordTrace tailWord_2777655 prefixEnd_2777655 1426272107364435145738303 := by
  unfold tailWord_2777655
  simp only [CollatzResearch.WordTrace]
  refine ⟨101309400752037795551334419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67539600501358530367556279 101309400752037795551334419)
  ·
    refine ⟨151964101128056693327001629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101309400752037795551334419 151964101128056693327001629)
    ·
      refine ⟨56986537923021259997625611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151964101128056693327001629 56986537923021259997625611)
      ·
        refine ⟨85479806884531889996438417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56986537923021259997625611 85479806884531889996438417)
        ·
          refine ⟨64109855163398917497328813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85479806884531889996438417 64109855163398917497328813)
          ·
            refine ⟨24041195686274594061498305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64109855163398917497328813 24041195686274594061498305)
            ·
              refine ⟨18030896764705945546123729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24041195686274594061498305 18030896764705945546123729)
              ·
                refine ⟨13523172573529459159592797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18030896764705945546123729 13523172573529459159592797)
                ·
                  refine ⟨5071189715073547184847299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13523172573529459159592797 5071189715073547184847299)
                  ·
                    refine ⟨7606784572610320777270949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5071189715073547184847299 7606784572610320777270949)
                    ·
                      refine ⟨1426272107364435145738303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7606784572610320777270949 1426272107364435145738303)
                      ·
                        rfl

theorem cell23_2777655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 2, 2, 3, 1, 4].length) (baseStart_2777655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777655 prefixEnd_2777655 := by exact prefixLift 2777655
  have htrace : WordTrace (prefixWord ++ tailWord_2777655) baseStart_2777655 baseEnd_2777655 := by
    simpa [prefixWord, tailWord_2777655, baseEnd_2777655] using wordTrace_append hprefix tailTrace_2777655
  have hstable : (prefixWord ++ tailWord_2777655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777655).length < 2 ^ (prefixWord ++ tailWord_2777655).sum := by decide
  have hdescent : baseEnd_2777655 < baseStart_2777655 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777685 : List Nat := [1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 4]
def baseStart_2777685 : Nat := 118140960795 + 2777685 * 2 ^ 59
def prefixEnd_2777685 : Nat := 4983230072969 + 3 ^ 40 * 2777685 * 2
def baseEnd_2777685 : Nat := 1426287511784070028363165

theorem tailTrace_2777685 : CollatzResearch.WordTrace tailWord_2777685 prefixEnd_2777685 1426287511784070028363165 := by
  unfold tailWord_2777685
  simp only [CollatzResearch.WordTrace]
  refine ⟨101310494941929110674926509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67540329961286073783284339 101310494941929110674926509)
  ·
    refine ⟨37991435603223416503097441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101310494941929110674926509 37991435603223416503097441)
    ·
      refine ⟨28493576702417562377323081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37991435603223416503097441 28493576702417562377323081)
      ·
        refine ⟨21370182526813171782992311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28493576702417562377323081 21370182526813171782992311)
        ·
          refine ⟨32055273790219757674488467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21370182526813171782992311 32055273790219757674488467)
          ·
            refine ⟨48082910685329636511732701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32055273790219757674488467 48082910685329636511732701)
            ·
              refine ⟨18031091506998613691899763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48082910685329636511732701 18031091506998613691899763)
              ·
                refine ⟨27046637260497920537849645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18031091506998613691899763 27046637260497920537849645)
                ·
                  refine ⟨10142488972686720201693617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27046637260497920537849645 10142488972686720201693617)
                  ·
                    refine ⟨7606866729515040151270213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10142488972686720201693617 7606866729515040151270213)
                    ·
                      refine ⟨1426287511784070028363165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7606866729515040151270213 1426287511784070028363165)
                      ·
                        rfl

theorem cell23_2777685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 1, 3, 2, 4].length) (baseStart_2777685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777685 prefixEnd_2777685 := by exact prefixLift 2777685
  have htrace : WordTrace (prefixWord ++ tailWord_2777685) baseStart_2777685 baseEnd_2777685 := by
    simpa [prefixWord, tailWord_2777685, baseEnd_2777685] using wordTrace_append hprefix tailTrace_2777685
  have hstable : (prefixWord ++ tailWord_2777685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777685).length < 2 ^ (prefixWord ++ tailWord_2777685).sum := by decide
  have hdescent : baseEnd_2777685 < baseStart_2777685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777694 : List Nat := [4, 4, 1, 2, 2, 1, 2, 2, 1, 4]
def baseStart_2777694 : Nat := 118140960795 + 2777694 * 2 ^ 59
def prefixEnd_2777694 : Nat := 4983230072969 + 3 ^ 40 * 2777694 * 2
def baseEnd_2777694 : Nat := 475430711036653497716875

theorem tailTrace_2777694 : CollatzResearch.WordTrace tailWord_2777694 prefixEnd_2777694 475430711036653497716875 := by
  unfold tailWord_2777694
  simp only [CollatzResearch.WordTrace]
  refine ⟨12663852899862063151500517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 67540548799264336808002757 12663852899862063151500517)
  ·
    refine ⟨2374472418724136840906347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12663852899862063151500517 2374472418724136840906347)
    ·
      refine ⟨3561708628086205261359521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2374472418724136840906347 3561708628086205261359521)
      ·
        refine ⟨2671281471064653946019641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3561708628086205261359521 2671281471064653946019641)
        ·
          refine ⟨2003461103298490459514731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2671281471064653946019641 2003461103298490459514731)
          ·
            refine ⟨3005191654947735689272097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003461103298490459514731 3005191654947735689272097)
            ·
              refine ⟨2253893741210801766954073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005191654947735689272097 2253893741210801766954073)
              ·
                refine ⟨1690420305908101325215555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2253893741210801766954073 1690420305908101325215555)
                ·
                  refine ⟨2535630458862151987823333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690420305908101325215555 2535630458862151987823333)
                  ·
                    refine ⟨475430711036653497716875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2535630458862151987823333 475430711036653497716875)
                    ·
                      rfl

theorem cell23_2777694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_2777694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777694 prefixEnd_2777694 := by exact prefixLift 2777694
  have htrace : WordTrace (prefixWord ++ tailWord_2777694) baseStart_2777694 baseEnd_2777694 := by
    simpa [prefixWord, tailWord_2777694, baseEnd_2777694] using wordTrace_append hprefix tailTrace_2777694
  have hstable : (prefixWord ++ tailWord_2777694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777694).length < 2 ^ (prefixWord ++ tailWord_2777694).sum := by decide
  have hdescent : baseEnd_2777694 < baseStart_2777694 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777705 : List Nat := [1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 3]
def baseStart_2777705 : Nat := 118140960795 + 2777705 * 2 ^ 59
def prefixEnd_2777705 : Nat := 4983230072969 + 3 ^ 40 * 2777705 * 2
def baseEnd_2777705 : Nat := 1426297781397159950113073

theorem tailTrace_2777705 : CollatzResearch.WordTrace tailWord_2777705 prefixEnd_2777705 1426297781397159950113073 := by
  unfold tailWord_2777705
  simp only [CollatzResearch.WordTrace]
  refine ⟨101311224401856654090654569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67540816267904436060436379 101311224401856654090654569)
  ·
    refine ⟨75983418301392490567990927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101311224401856654090654569 75983418301392490567990927)
    ·
      refine ⟨113975127452088735851986391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75983418301392490567990927 113975127452088735851986391)
      ·
        refine ⟨170962691178133103777979587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113975127452088735851986391 170962691178133103777979587)
        ·
          refine ⟨256444036767199655666969381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170962691178133103777979587 256444036767199655666969381)
          ·
            refine ⟨48083256893849935437556759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 256444036767199655666969381 48083256893849935437556759)
            ·
              refine ⟨72124885340774903156335139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48083256893849935437556759 72124885340774903156335139)
              ·
                refine ⟨108187328011162354734502709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72124885340774903156335139 108187328011162354734502709)
                ·
                  refine ⟨10142562001046470756359629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 108187328011162354734502709 10142562001046470756359629)
                  ·
                    refine ⟨3803460750392426533634861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10142562001046470756359629 3803460750392426533634861)
                    ·
                      refine ⟨1426297781397159950113073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803460750392426533634861 1426297781397159950113073)
                      ·
                        rfl

theorem cell23_2777705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 5, 3, 3].length) (baseStart_2777705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777705 prefixEnd_2777705 := by exact prefixLift 2777705
  have htrace : WordTrace (prefixWord ++ tailWord_2777705) baseStart_2777705 baseEnd_2777705 := by
    simpa [prefixWord, tailWord_2777705, baseEnd_2777705] using wordTrace_append hprefix tailTrace_2777705
  have hstable : (prefixWord ++ tailWord_2777705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777705).length < 2 ^ (prefixWord ++ tailWord_2777705).sum := by decide
  have hdescent : baseEnd_2777705 < baseStart_2777705 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777712 : List Nat := [2, 1, 1, 1, 7, 2, 1, 8]
def baseStart_2777712 : Nat := 118140960795 + 2777712 * 2 ^ 59
def prefixEnd_2777712 : Nat := 4983230072969 + 3 ^ 40 * 2777712 * 2
def baseEnd_2777712 : Nat := 52825976880064497137983

theorem tailTrace_2777712 : CollatzResearch.WordTrace tailWord_2777712 prefixEnd_2777712 52825976880064497137983 := by
  unfold tailWord_2777712
  simp only [CollatzResearch.WordTrace]
  refine ⟨50655739856415647143079695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67540986475220862857439593 50655739856415647143079695)
  ·
    refine ⟨75983609784623470714619543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50655739856415647143079695 75983609784623470714619543)
    ·
      refine ⟨113975414676935206071929315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75983609784623470714619543 113975414676935206071929315)
      ·
        refine ⟨170963122015402809107893973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113975414676935206071929315 170963122015402809107893973)
        ·
          refine ⟨4006948172236003338466265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 170963122015402809107893973 4006948172236003338466265)
          ·
            refine ⟨3005211129177002503849699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4006948172236003338466265 3005211129177002503849699)
            ·
              refine ⟨4507816693765503755774549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005211129177002503849699 4507816693765503755774549)
              ·
                refine ⟨52825976880064497137983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4507816693765503755774549 52825976880064497137983)
                ·
                  rfl

theorem cell23_2777712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 8].length) (baseStart_2777712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777712 prefixEnd_2777712 := by exact prefixLift 2777712
  have htrace : WordTrace (prefixWord ++ tailWord_2777712) baseStart_2777712 baseEnd_2777712 := by
    simpa [prefixWord, tailWord_2777712, baseEnd_2777712] using wordTrace_append hprefix tailTrace_2777712
  have hstable : (prefixWord ++ tailWord_2777712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777712).length < 2 ^ (prefixWord ++ tailWord_2777712).sum := by decide
  have hdescent : baseEnd_2777712 < baseStart_2777712 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777735 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 5]
def baseStart_2777735 : Nat := 118140960795 + 2777735 * 2 ^ 59
def prefixEnd_2777735 : Nat := 4983230072969 + 3 ^ 40 * 2777735 * 2
def baseEnd_2777735 : Nat := 1426313185816794832737935

theorem tailTrace_2777735 : CollatzResearch.WordTrace tailWord_2777735 prefixEnd_2777735 1426313185816794832737935 := by
  unfold tailWord_2777735
  simp only [CollatzResearch.WordTrace]
  refine ⟨101312318591747969214246659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67541545727831979476164439 101312318591747969214246659)
  ·
    refine ⟨151968477887621953821369989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101312318591747969214246659 151968477887621953821369989)
    ·
      refine ⟨28494089603929116341506873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151968477887621953821369989 28494089603929116341506873)
      ·
        refine ⟨21370567202946837256130155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28494089603929116341506873 21370567202946837256130155)
        ·
          refine ⟨32055850804420255884195233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21370567202946837256130155 32055850804420255884195233)
          ·
            refine ⟨24041888103315191913146425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32055850804420255884195233 24041888103315191913146425)
            ·
              refine ⟨18031416077486393934859819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24041888103315191913146425 18031416077486393934859819)
              ·
                refine ⟨27047124116229590902289729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18031416077486393934859819 27047124116229590902289729)
                ·
                  refine ⟨20285343087172193176717297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27047124116229590902289729 20285343087172193176717297)
                  ·
                    refine ⟨15214007315379144882537973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 20285343087172193176717297 15214007315379144882537973)
                    ·
                      refine ⟨1426313185816794832737935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15214007315379144882537973 1426313185816794832737935)
                      ·
                        rfl

theorem cell23_2777735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_2777735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777735 prefixEnd_2777735 := by exact prefixLift 2777735
  have htrace : WordTrace (prefixWord ++ tailWord_2777735) baseStart_2777735 baseEnd_2777735 := by
    simpa [prefixWord, tailWord_2777735, baseEnd_2777735] using wordTrace_append hprefix tailTrace_2777735
  have hstable : (prefixWord ++ tailWord_2777735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777735).length < 2 ^ (prefixWord ++ tailWord_2777735).sum := by decide
  have hdescent : baseEnd_2777735 < baseStart_2777735 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777756 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 2, 1, 3]
def baseStart_2777756 : Nat := 118140960795 + 2777756 * 2 ^ 59
def prefixEnd_2777756 : Nat := 4983230072969 + 3 ^ 40 * 2777756 * 2
def baseEnd_2777756 : Nat := 1426323968910539250575339

theorem tailTrace_2777756 : CollatzResearch.WordTrace tailWord_2777756 prefixEnd_2777756 1426323968910539250575339 := by
  unfold tailWord_2777756
  simp only [CollatzResearch.WordTrace]
  refine ⟨50656542262335944900380561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67542056349781259867174081 50656542262335944900380561)
  ·
    refine ⟨37992406696751958675285421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50656542262335944900380561 37992406696751958675285421)
    ·
      refine ⟨14247152511281984503232033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37992406696751958675285421 14247152511281984503232033)
      ·
        refine ⟨10685364383461488377424025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14247152511281984503232033 10685364383461488377424025)
        ·
          refine ⟨8014023287596116283068019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10685364383461488377424025 8014023287596116283068019)
          ·
            refine ⟨12021034931394174424602029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014023287596116283068019 12021034931394174424602029)
            ·
              refine ⟨4507888099272815409225761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12021034931394174424602029 4507888099272815409225761)
              ·
                refine ⟨3380916074454611556919321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4507888099272815409225761 3380916074454611556919321)
                ·
                  refine ⟨2535687055840958667689491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380916074454611556919321 2535687055840958667689491)
                  ·
                    refine ⟨3803530583761438001534237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535687055840958667689491 3803530583761438001534237)
                    ·
                      refine ⟨1426323968910539250575339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803530583761438001534237 1426323968910539250575339)
                      ·
                        rfl

theorem cell23_2777756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_2777756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777756 prefixEnd_2777756 := by exact prefixLift 2777756
  have htrace : WordTrace (prefixWord ++ tailWord_2777756) baseStart_2777756 baseEnd_2777756 := by
    simpa [prefixWord, tailWord_2777756, baseEnd_2777756] using wordTrace_append hprefix tailTrace_2777756
  have hstable : (prefixWord ++ tailWord_2777756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777756).length < 2 ^ (prefixWord ++ tailWord_2777756).sum := by decide
  have hdescent : baseEnd_2777756 < baseStart_2777756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777765 : List Nat := [1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 5]
def baseStart_2777765 : Nat := 118140960795 + 2777765 * 2 ^ 59
def prefixEnd_2777765 : Nat := 4983230072969 + 3 ^ 40 * 2777765 * 2
def baseEnd_2777765 : Nat := 1426328590236429715362797

theorem tailTrace_2777765 : CollatzResearch.WordTrace tailWord_2777765 prefixEnd_2777765 1426328590236429715362797 := by
  unfold tailWord_2777765
  simp only [CollatzResearch.WordTrace]
  refine ⟨101313412781639284337838749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67542275187759522891892499 101313412781639284337838749)
  ·
    refine ⟨37992529793114731626689531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101313412781639284337838749 37992529793114731626689531)
    ·
      refine ⟨56988794689672097440034297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37992529793114731626689531 56988794689672097440034297)
      ·
        refine ⟨42741596017254073080025723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56988794689672097440034297 42741596017254073080025723)
        ·
          refine ⟨64112394025881109620038585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42741596017254073080025723 64112394025881109620038585)
          ·
            refine ⟨48084295519410832215028939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64112394025881109620038585 48084295519410832215028939)
            ·
              refine ⟨72126443279116248322543409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48084295519410832215028939 72126443279116248322543409)
              ·
                refine ⟨54094832459337186241907557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72126443279116248322543409 54094832459337186241907557)
                ·
                  refine ⟨10142781086125722420357667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 54094832459337186241907557 10142781086125722420357667)
                  ·
                    refine ⟨15214171629188583630536501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10142781086125722420357667 15214171629188583630536501)
                    ·
                      refine ⟨1426328590236429715362797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15214171629188583630536501 1426328590236429715362797)
                      ·
                        rfl

theorem cell23_2777765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_2777765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777765 prefixEnd_2777765 := by exact prefixLift 2777765
  have htrace : WordTrace (prefixWord ++ tailWord_2777765) baseStart_2777765 baseEnd_2777765 := by
    simpa [prefixWord, tailWord_2777765, baseEnd_2777765] using wordTrace_append hprefix tailTrace_2777765
  have hstable : (prefixWord ++ tailWord_2777765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777765).length < 2 ^ (prefixWord ++ tailWord_2777765).sum := by decide
  have hdescent : baseEnd_2777765 < baseStart_2777765 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777773 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 2, 1, 3]
def baseStart_2777773 : Nat := 118140960795 + 2777773 * 2 ^ 59
def prefixEnd_2777773 : Nat := 4983230072969 + 3 ^ 40 * 2777773 * 2
def baseEnd_2777773 : Nat := 1426332698081665684062761

theorem tailTrace_2777773 : CollatzResearch.WordTrace tailWord_2777773 prefixEnd_2777773 1426332698081665684062761 := by
  unfold tailWord_2777773
  simp only [CollatzResearch.WordTrace]
  refine ⟨101313704565610301704129973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67542469710406867802753315 101313704565610301704129973)
  ·
    refine ⟨9498159803025965784762185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 101313704565610301704129973 9498159803025965784762185)
    ·
      refine ⟨7123619852269474338571639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9498159803025965784762185 7123619852269474338571639)
      ·
        refine ⟨10685429778404211507857459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123619852269474338571639 10685429778404211507857459)
        ·
          refine ⟨16028144667606317261786189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10685429778404211507857459 16028144667606317261786189)
          ·
            refine ⟨6010554250352368973169821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16028144667606317261786189 6010554250352368973169821)
            ·
              refine ⟨2253957843882138364938683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6010554250352368973169821 2253957843882138364938683)
              ·
                refine ⟨3380936765823207547408025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2253957843882138364938683 3380936765823207547408025)
                ·
                  refine ⟨2535702574367405660556019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3380936765823207547408025 2535702574367405660556019)
                  ·
                    refine ⟨3803553861551108490834029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535702574367405660556019 3803553861551108490834029)
                    ·
                      refine ⟨1426332698081665684062761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803553861551108490834029 1426332698081665684062761)
                      ·
                        rfl

theorem cell23_2777773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 2, 1, 3].length) (baseStart_2777773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777773 prefixEnd_2777773 := by exact prefixLift 2777773
  have htrace : WordTrace (prefixWord ++ tailWord_2777773) baseStart_2777773 baseEnd_2777773 := by
    simpa [prefixWord, tailWord_2777773, baseEnd_2777773] using wordTrace_append hprefix tailTrace_2777773
  have hstable : (prefixWord ++ tailWord_2777773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777773).length < 2 ^ (prefixWord ++ tailWord_2777773).sum := by decide
  have hdescent : baseEnd_2777773 < baseStart_2777773 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777779 : List Nat := [1, 1, 1, 2, 3, 4, 3, 1, 1, 4, 2]
def baseStart_2777779 : Nat := 118140960795 + 2777779 * 2 ^ 59
def prefixEnd_2777779 : Nat := 4983230072969 + 3 ^ 40 * 2777779 * 2
def baseEnd_2777779 : Nat := 1426335778965592660587733

theorem tailTrace_2777779 : CollatzResearch.WordTrace tailWord_2777779 prefixEnd_2777779 1426335778965592660587733 := by
  unfold tailWord_2777779
  simp only [CollatzResearch.WordTrace]
  refine ⟨101313923403588564728848391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67542615602392376485898927 101313923403588564728848391)
  ·
    refine ⟨151970885105382847093272587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101313923403588564728848391 151970885105382847093272587)
    ·
      refine ⟨227956327658074270639908881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151970885105382847093272587 227956327658074270639908881)
      ·
        refine ⟨170967245743555702979931661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 227956327658074270639908881 170967245743555702979931661)
        ·
          refine ⟨64112717153833388617474373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170967245743555702979931661 64112717153833388617474373)
          ·
            refine ⟨12021134466343760365776445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64112717153833388617474373 12021134466343760365776445)
            ·
              refine ⟨4507925424878910137166167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12021134466343760365776445 4507925424878910137166167)
              ·
                refine ⟨6761888137318365205749251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4507925424878910137166167 6761888137318365205749251)
                ·
                  refine ⟨10142832205977547808623877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6761888137318365205749251 10142832205977547808623877)
                  ·
                    refine ⟨1901781038620790214116977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10142832205977547808623877 1901781038620790214116977)
                    ·
                      refine ⟨1426335778965592660587733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901781038620790214116977 1426335778965592660587733)
                      ·
                        rfl

theorem cell23_2777779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 3, 1, 1, 4, 2].length) (baseStart_2777779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777779 prefixEnd_2777779 := by exact prefixLift 2777779
  have htrace : WordTrace (prefixWord ++ tailWord_2777779) baseStart_2777779 baseEnd_2777779 := by
    simpa [prefixWord, tailWord_2777779, baseEnd_2777779] using wordTrace_append hprefix tailTrace_2777779
  have hstable : (prefixWord ++ tailWord_2777779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777779).length < 2 ^ (prefixWord ++ tailWord_2777779).sum := by decide
  have hdescent : baseEnd_2777779 < baseStart_2777779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777796 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 4, 2, 2]
def baseStart_2777796 : Nat := 118140960795 + 2777796 * 2 ^ 59
def prefixEnd_2777796 : Nat := 4983230072969 + 3 ^ 40 * 2777796 * 2
def baseEnd_2777796 : Nat := 1426344508136719094075155

theorem tailTrace_2777796 : CollatzResearch.WordTrace tailWord_2777796 prefixEnd_2777796 1426344508136719094075155 := by
  unfold tailWord_2777796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50657271722263488316108621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67543028963017984421478161 50657271722263488316108621)
  ·
    refine ⟨18996476895848808118540733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50657271722263488316108621 18996476895848808118540733)
    ·
      refine ⟨7123678835943303044452775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18996476895848808118540733 7123678835943303044452775)
      ·
        refine ⟨10685518253914954566679163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123678835943303044452775 10685518253914954566679163)
        ·
          refine ⟨16028277380872431850018745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10685518253914954566679163 16028277380872431850018745)
          ·
            refine ⟨12021208035654323887514059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16028277380872431850018745 12021208035654323887514059)
            ·
              refine ⟨18031812053481485831271089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12021208035654323887514059 18031812053481485831271089)
              ·
                refine ⟨13523859040111114373453317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18031812053481485831271089 13523859040111114373453317)
                ·
                  refine ⟨2535723570020833945022497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13523859040111114373453317 2535723570020833945022497)
                  ·
                    refine ⟨1901792677515625458766873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535723570020833945022497 1901792677515625458766873)
                    ·
                      refine ⟨1426344508136719094075155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901792677515625458766873 1426344508136719094075155)
                      ·
                        rfl

theorem cell23_2777796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 4, 2, 2].length) (baseStart_2777796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777796 prefixEnd_2777796 := by exact prefixLift 2777796
  have htrace : WordTrace (prefixWord ++ tailWord_2777796) baseStart_2777796 baseEnd_2777796 := by
    simpa [prefixWord, tailWord_2777796, baseEnd_2777796] using wordTrace_append hprefix tailTrace_2777796
  have hstable : (prefixWord ++ tailWord_2777796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777796).length < 2 ^ (prefixWord ++ tailWord_2777796).sum := by decide
  have hdescent : baseEnd_2777796 < baseStart_2777796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777956 : List Nat := [2, 3, 1, 1, 4, 2, 2, 2, 1, 5]
def baseStart_2777956 : Nat := 118140960795 + 2777956 * 2 ^ 59
def prefixEnd_2777956 : Nat := 4983230072969 + 3 ^ 40 * 2777956 * 2
def baseEnd_2777956 : Nat := 475475555013812822691473

theorem tailTrace_2777956 : CollatzResearch.WordTrace tailWord_2777956 prefixEnd_2777956 475475555013812822691473 := by
  unfold tailWord_2777956
  simp only [CollatzResearch.WordTrace]
  refine ⟨50660189561973661979020861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67546919415964882638694481 50660189561973661979020861)
  ·
    refine ⟨18997571085740123242132823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50660189561973661979020861 18997571085740123242132823)
    ·
      refine ⟨28496356628610184863199235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18997571085740123242132823 28496356628610184863199235)
      ·
        refine ⟨42744534942915277294798853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28496356628610184863199235 42744534942915277294798853)
        ·
          refine ⟨8014600301796614492774785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42744534942915277294798853 8014600301796614492774785)
          ·
            refine ⟨6010950226347460869581089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8014600301796614492774785 6010950226347460869581089)
            ·
              refine ⟨4508212669760595652185817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6010950226347460869581089 4508212669760595652185817)
              ·
                refine ⟨3381159502320446739139363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4508212669760595652185817 3381159502320446739139363)
                ·
                  refine ⟨5071739253480670108709045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381159502320446739139363 5071739253480670108709045)
                  ·
                    refine ⟨475475555013812822691473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5071739253480670108709045 475475555013812822691473)
                    ·
                      rfl

theorem cell23_2777956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_2777956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777956 prefixEnd_2777956 := by exact prefixLift 2777956
  have htrace : WordTrace (prefixWord ++ tailWord_2777956) baseStart_2777956 baseEnd_2777956 := by
    simpa [prefixWord, tailWord_2777956, baseEnd_2777956] using wordTrace_append hprefix tailTrace_2777956
  have hstable : (prefixWord ++ tailWord_2777956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777956).length < 2 ^ (prefixWord ++ tailWord_2777956).sum := by decide
  have hdescent : baseEnd_2777956 < baseStart_2777956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777969 : List Nat := [1, 2, 2, 2, 1, 4, 1, 2, 4, 4]
def baseStart_2777969 : Nat := 118140960795 + 2777969 * 2 ^ 59
def prefixEnd_2777969 : Nat := 4983230072969 + 3 ^ 40 * 2777969 * 2
def baseEnd_2777969 : Nat := 475477780096648972403953

theorem tailTrace_2777969 : CollatzResearch.WordTrace tailWord_2777969 prefixEnd_2777969 475477780096648972403953 := by
  unfold tailWord_2777969
  simp only [CollatzResearch.WordTrace]
  refine ⟨101320853272900227178264961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67547235515266818118843307 101320853272900227178264961)
  ·
    refine ⟨75990639954675170383698721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101320853272900227178264961 75990639954675170383698721)
    ·
      refine ⟨56992979966006377787774041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 75990639954675170383698721 56992979966006377787774041)
      ·
        refine ⟨42744734974504783340830531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56992979966006377787774041 42744734974504783340830531)
        ·
          refine ⟨64117102461757175011245797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42744734974504783340830531 64117102461757175011245797)
          ·
            refine ⟨12021956711579470314608587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64117102461757175011245797 12021956711579470314608587)
            ·
              refine ⟨18032935067369205471912881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12021956711579470314608587 18032935067369205471912881)
              ·
                refine ⟨13524701300526904103934661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18032935067369205471912881 13524701300526904103934661)
                ·
                  refine ⟨2535881493848794519487749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13524701300526904103934661 2535881493848794519487749)
                  ·
                    refine ⟨475477780096648972403953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2535881493848794519487749 475477780096648972403953)
                    ·
                      rfl

theorem cell23_2777969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_2777969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777969 prefixEnd_2777969 := by exact prefixLift 2777969
  have htrace : WordTrace (prefixWord ++ tailWord_2777969) baseStart_2777969 baseEnd_2777969 := by
    simpa [prefixWord, tailWord_2777969, baseEnd_2777969] using wordTrace_append hprefix tailTrace_2777969
  have hstable : (prefixWord ++ tailWord_2777969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777969).length < 2 ^ (prefixWord ++ tailWord_2777969).sum := by decide
  have hdescent : baseEnd_2777969 < baseStart_2777969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2777993 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 3, 2, 2]
def baseStart_2777993 : Nat := 118140960795 + 2777993 * 2 ^ 59
def prefixEnd_2777993 : Nat := 4983230072969 + 3 ^ 40 * 2777993 * 2
def baseEnd_2777993 : Nat := 1426445663825654823311749

theorem tailTrace_2777993 : CollatzResearch.WordTrace tailWord_2777993 prefixEnd_2777993 1426445663825654823311749 := by
  unfold tailWord_2777993
  simp only [CollatzResearch.WordTrace]
  refine ⟨101321728624813279277138633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67547819083208852851425755 101321728624813279277138633)
  ·
    refine ⟨75991296468609959457853975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101321728624813279277138633 75991296468609959457853975)
    ·
      refine ⟨113986944702914939186780963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75991296468609959457853975 113986944702914939186780963)
      ·
        refine ⟨170980417054372408780171445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113986944702914939186780963 170980417054372408780171445)
        ·
          refine ⟨16029414098847413323141073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 170980417054372408780171445 16029414098847413323141073)
          ·
            refine ⟨12022060574135559992355805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16029414098847413323141073 12022060574135559992355805)
            ·
              refine ⟨4508272715300834997133427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12022060574135559992355805 4508272715300834997133427)
              ·
                refine ⟨6762409072951252495700141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4508272715300834997133427 6762409072951252495700141)
                ·
                  refine ⟨2535903402356719685887553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6762409072951252495700141 2535903402356719685887553)
                  ·
                    refine ⟨1901927551767539764415665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535903402356719685887553 1901927551767539764415665)
                    ·
                      refine ⟨1426445663825654823311749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901927551767539764415665 1426445663825654823311749)
                      ·
                        rfl

theorem cell23_2777993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 3, 2, 2].length) (baseStart_2777993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2777993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2777993 prefixEnd_2777993 := by exact prefixLift 2777993
  have htrace : WordTrace (prefixWord ++ tailWord_2777993) baseStart_2777993 baseEnd_2777993 := by
    simpa [prefixWord, tailWord_2777993, baseEnd_2777993] using wordTrace_append hprefix tailTrace_2777993
  have hstable : (prefixWord ++ tailWord_2777993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2777993).length < 2 ^ (prefixWord ++ tailWord_2777993).sum := by decide
  have hdescent : baseEnd_2777993 < baseStart_2777993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2777993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778009 : List Nat := [1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 3]
def baseStart_2778009 : Nat := 118140960795 + 2778009 * 2 ^ 59
def prefixEnd_2778009 : Nat := 4983230072969 + 3 ^ 40 * 2778009 * 2
def baseEnd_2778009 : Nat := 1426453879516126760711675

theorem tailTrace_2778009 : CollatzResearch.WordTrace tailWord_2778009 prefixEnd_2778009 1426453879516126760711675 := by
  unfold tailWord_2778009
  simp only [CollatzResearch.WordTrace]
  refine ⟨101322312192755314009721081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67548208128503542673147387 101322312192755314009721081)
  ·
    refine ⟨75991734144566485507290811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101322312192755314009721081 75991734144566485507290811)
    ·
      refine ⟨113987601216849728260936217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75991734144566485507290811 113987601216849728260936217)
      ·
        refine ⟨85490700912637296195702163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113987601216849728260936217 85490700912637296195702163)
        ·
          refine ⟨128236051368955944293553245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85490700912637296195702163 128236051368955944293553245)
          ·
            refine ⟨48088519263358479110082467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128236051368955944293553245 48088519263358479110082467)
            ·
              refine ⟨72132778895037718665123701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48088519263358479110082467 72132778895037718665123701)
              ·
                refine ⟨6762448021409786124855347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 72132778895037718665123701 6762448021409786124855347)
                ·
                  refine ⟨10143672032114679187283021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6762448021409786124855347 10143672032114679187283021)
                  ·
                    refine ⟨3803877012043004695231133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10143672032114679187283021 3803877012043004695231133)
                    ·
                      refine ⟨1426453879516126760711675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803877012043004695231133 1426453879516126760711675)
                      ·
                        rfl

theorem cell23_2778009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 1, 5, 1, 3, 3].length) (baseStart_2778009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778009 prefixEnd_2778009 := by exact prefixLift 2778009
  have htrace : WordTrace (prefixWord ++ tailWord_2778009) baseStart_2778009 baseEnd_2778009 := by
    simpa [prefixWord, tailWord_2778009, baseEnd_2778009] using wordTrace_append hprefix tailTrace_2778009
  have hstable : (prefixWord ++ tailWord_2778009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778009).length < 2 ^ (prefixWord ++ tailWord_2778009).sum := by decide
  have hdescent : baseEnd_2778009 < baseStart_2778009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778010 : List Nat := [3, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4]
def baseStart_2778010 : Nat := 118140960795 + 2778010 * 2 ^ 59
def prefixEnd_2778010 : Nat := 4983230072969 + 3 ^ 40 * 2778010 * 2
def baseEnd_2778010 : Nat := 1426454392996781256799171

theorem tailTrace_2778010 : CollatzResearch.WordTrace tailWord_2778010 prefixEnd_2778010 1426454392996781256799171 := by
  unfold tailWord_2778010
  simp only [CollatzResearch.WordTrace]
  refine ⟨25330587166437922795126871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67548232443834460787004989 25330587166437922795126871)
  ·
    refine ⟨37995880749656884192690307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25330587166437922795126871 37995880749656884192690307)
    ·
      refine ⟨56993821124485326289035461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37995880749656884192690307 56993821124485326289035461)
      ·
        refine ⟨10686341460840998679194149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 56993821124485326289035461 10686341460840998679194149)
        ·
          refine ⟨2003689023907687252348903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10686341460840998679194149 2003689023907687252348903)
          ·
            refine ⟨3005533535861530878523355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2003689023907687252348903 3005533535861530878523355)
            ·
              refine ⟨4508300303792296317785033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005533535861530878523355 4508300303792296317785033)
              ·
                refine ⟨3381225227844222238338775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4508300303792296317785033 3381225227844222238338775)
                ·
                  refine ⟨5071837841766333357508163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381225227844222238338775 5071837841766333357508163)
                  ·
                    refine ⟨7607756762649500036262245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5071837841766333357508163 7607756762649500036262245)
                    ·
                      refine ⟨1426454392996781256799171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7607756762649500036262245 1426454392996781256799171)
                      ·
                        rfl

theorem cell23_2778010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_2778010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778010 prefixEnd_2778010 := by exact prefixLift 2778010
  have htrace : WordTrace (prefixWord ++ tailWord_2778010) baseStart_2778010 baseEnd_2778010 := by
    simpa [prefixWord, tailWord_2778010, baseEnd_2778010] using wordTrace_append hprefix tailTrace_2778010
  have hstable : (prefixWord ++ tailWord_2778010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778010).length < 2 ^ (prefixWord ++ tailWord_2778010).sum := by decide
  have hdescent : baseEnd_2778010 < baseStart_2778010 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778038 : List Nat := [5, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3]
def baseStart_2778038 : Nat := 118140960795 + 2778038 * 2 ^ 59
def prefixEnd_2778038 : Nat := 4983230072969 + 3 ^ 40 * 2778038 * 2
def baseEnd_2778038 : Nat := 1426468770455107147249043

theorem tailTrace_2778038 : CollatzResearch.WordTrace tailWord_2778038 prefixEnd_2778038 1426468770455107147249043 := by
  unfold tailWord_2778038
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332710619353140747657923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67548913273100167975017845 6332710619353140747657923)
  ·
    refine ⟨9499065929029711121486885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6332710619353140747657923 9499065929029711121486885)
    ·
      refine ⟨1781074861693070835278791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9499065929029711121486885 1781074861693070835278791)
      ·
        refine ⟨2671612292539606252918187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781074861693070835278791 2671612292539606252918187)
        ·
          refine ⟨4007418438809409379377281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671612292539606252918187 4007418438809409379377281)
          ·
            refine ⟨3005563829107057034532961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007418438809409379377281 3005563829107057034532961)
            ·
              refine ⟨2254172871830292775899721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005563829107057034532961 2254172871830292775899721)
              ·
                refine ⟨1690629653872719581924791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254172871830292775899721 1690629653872719581924791)
                ·
                  refine ⟨2535944480809079372887187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690629653872719581924791 2535944480809079372887187)
                  ·
                    refine ⟨3803916721213619059330781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2535944480809079372887187 3803916721213619059330781)
                    ·
                      refine ⟨1426468770455107147249043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3803916721213619059330781 1426468770455107147249043)
                      ·
                        rfl

theorem cell23_2778038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_2778038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778038 prefixEnd_2778038 := by exact prefixLift 2778038
  have htrace : WordTrace (prefixWord ++ tailWord_2778038) baseStart_2778038 baseEnd_2778038 := by
    simpa [prefixWord, tailWord_2778038, baseEnd_2778038] using wordTrace_append hprefix tailTrace_2778038
  have hstable : (prefixWord ++ tailWord_2778038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778038).length < 2 ^ (prefixWord ++ tailWord_2778038).sum := by decide
  have hdescent : baseEnd_2778038 < baseStart_2778038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778059 : List Nat := [1, 1, 1, 1, 3, 6, 1, 1, 2, 6]
def baseStart_2778059 : Nat := 118140960795 + 2778059 * 2 ^ 59
def prefixEnd_2778059 : Nat := 4983230072969 + 3 ^ 40 * 2778059 * 2
def baseEnd_2778059 : Nat := 475493184516283855028815

theorem tailTrace_2778059 : CollatzResearch.WordTrace tailWord_2778059 prefixEnd_2778059 475493184516283855028815 := by
  unfold tailWord_2778059
  simp only [CollatzResearch.WordTrace]
  refine ⟨101324135842574172549041231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67549423895049448366027487 101324135842574172549041231)
  ·
    refine ⟨151986203763861258823561847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101324135842574172549041231 151986203763861258823561847)
    ·
      refine ⟨227979305645791888235342771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151986203763861258823561847 227979305645791888235342771)
      ·
        refine ⟨341968958468687832353014157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227979305645791888235342771 341968958468687832353014157)
        ·
          refine ⟨128238359425757937132380309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 341968958468687832353014157 128238359425757937132380309)
          ·
            refine ⟨6011173098082403303080327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 128238359425757937132380309 6011173098082403303080327)
            ·
              refine ⟨9016759647123604954620491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011173098082403303080327 9016759647123604954620491)
              ·
                refine ⟨13525139470685407431930737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9016759647123604954620491 13525139470685407431930737)
                ·
                  refine ⟨10143854603014055573948053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13525139470685407431930737 10143854603014055573948053)
                  ·
                    refine ⟨475493184516283855028815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10143854603014055573948053 475493184516283855028815)
                    ·
                      rfl

theorem cell23_2778059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 1, 2, 6].length) (baseStart_2778059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778059 prefixEnd_2778059 := by exact prefixLift 2778059
  have htrace : WordTrace (prefixWord ++ tailWord_2778059) baseStart_2778059 baseEnd_2778059 := by
    simpa [prefixWord, tailWord_2778059, baseEnd_2778059] using wordTrace_append hprefix tailTrace_2778059
  have hstable : (prefixWord ++ tailWord_2778059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778059).length < 2 ^ (prefixWord ++ tailWord_2778059).sum := by decide
  have hdescent : baseEnd_2778059 < baseStart_2778059 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778070 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2]
def baseStart_2778070 : Nat := 118140960795 + 2778070 * 2 ^ 59
def prefixEnd_2778070 : Nat := 4983230072969 + 3 ^ 40 * 2778070 * 2
def baseEnd_2778070 : Nat := 1426485201836051022048895

theorem tailTrace_2778070 : CollatzResearch.WordTrace tailWord_2778070 prefixEnd_2778070 1426485201836051022048895 := by
  unfold tailWord_2778070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6332783565345895089230729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67549691363689547618461109 6332783565345895089230729)
  ·
    refine ⟨4749587674009421316923047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6332783565345895089230729 4749587674009421316923047)
    ·
      refine ⟨7124381511014131975384571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4749587674009421316923047 7124381511014131975384571)
      ·
        refine ⟨10686572266521197963076857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7124381511014131975384571 10686572266521197963076857)
        ·
          refine ⟨8014929199890898472307643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10686572266521197963076857 8014929199890898472307643)
          ·
            refine ⟨12022393799836347708461465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8014929199890898472307643 12022393799836347708461465)
            ·
              refine ⟨9016795349877260781346099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12022393799836347708461465 9016795349877260781346099)
              ·
                refine ⟨13525193024815891172019149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9016795349877260781346099 13525193024815891172019149)
                ·
                  refine ⟨5071947384305959189507181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13525193024815891172019149 5071947384305959189507181)
                  ·
                    refine ⟨1901980269114734696065193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5071947384305959189507181 1901980269114734696065193)
                    ·
                      refine ⟨1426485201836051022048895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901980269114734696065193 1426485201836051022048895)
                      ·
                        rfl

theorem cell23_2778070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_2778070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778070 prefixEnd_2778070 := by exact prefixLift 2778070
  have htrace : WordTrace (prefixWord ++ tailWord_2778070) baseStart_2778070 baseEnd_2778070 := by
    simpa [prefixWord, tailWord_2778070, baseEnd_2778070] using wordTrace_append hprefix tailTrace_2778070
  have hstable : (prefixWord ++ tailWord_2778070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778070).length < 2 ^ (prefixWord ++ tailWord_2778070).sum := by decide
  have hdescent : baseEnd_2778070 < baseStart_2778070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778083 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2778083 : Nat := 118140960795 + 2778083 * 2 ^ 59
def prefixEnd_2778083 : Nat := 4983230072969 + 3 ^ 40 * 2778083 * 2
def baseEnd_2778083 : Nat := 1426491877084559471186335

theorem tailTrace_2778083 : CollatzResearch.WordTrace tailWord_2778083 prefixEnd_2778083 1426491877084559471186335 := by
  unfold tailWord_2778083
  simp only [CollatzResearch.WordTrace]
  refine ⟨101325011194487224647914903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67550007462991483098609935 101325011194487224647914903)
  ·
    refine ⟨151987516791730836971872355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101325011194487224647914903 151987516791730836971872355)
    ·
      refine ⟨227981275187596255457808533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151987516791730836971872355 227981275187596255457808533)
      ·
        refine ⟨10686622274418574474584775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 227981275187596255457808533 10686622274418574474584775)
        ·
          refine ⟨16029933411627861711877163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10686622274418574474584775 16029933411627861711877163)
          ·
            refine ⟨24044900117441792567815745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16029933411627861711877163 24044900117441792567815745)
            ·
              refine ⟨18033675088081344425861809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24044900117441792567815745 18033675088081344425861809)
              ·
                refine ⟨13525256316061008319396357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18033675088081344425861809 13525256316061008319396357)
                ·
                  refine ⟨2535985559261439059886817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13525256316061008319396357 2535985559261439059886817)
                  ·
                    refine ⟨1901989169446079294915113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2535985559261439059886817 1901989169446079294915113)
                    ·
                      refine ⟨1426491877084559471186335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901989169446079294915113 1426491877084559471186335)
                      ·
                        rfl

theorem cell23_2778083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2778083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778083 prefixEnd_2778083 := by exact prefixLift 2778083
  have htrace : WordTrace (prefixWord ++ tailWord_2778083) baseStart_2778083 baseEnd_2778083 := by
    simpa [prefixWord, tailWord_2778083, baseEnd_2778083] using wordTrace_append hprefix tailTrace_2778083
  have hstable : (prefixWord ++ tailWord_2778083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778083).length < 2 ^ (prefixWord ++ tailWord_2778083).sum := by decide
  have hdescent : baseEnd_2778083 < baseStart_2778083 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778087 : List Nat := [1, 1, 5, 2, 2, 3, 2, 1, 1, 3, 2]
def baseStart_2778087 : Nat := 118140960795 + 2778087 * 2 ^ 59
def prefixEnd_2778087 : Nat := 4983230072969 + 3 ^ 40 * 2778087 * 2
def baseEnd_2778087 : Nat := 1426493931007177455536317

theorem tailTrace_2778087 : CollatzResearch.WordTrace tailWord_2778087 prefixEnd_2778087 1426493931007177455536317 := by
  unfold tailWord_2778087
  simp only [CollatzResearch.WordTrace]
  refine ⟨101325157086472733331060515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67550104724315155554040343 101325157086472733331060515)
  ·
    refine ⟨151987735629709099996590773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101325157086472733331060515 151987735629709099996590773)
    ·
      refine ⟨14248850215285228124680385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 151987735629709099996590773 14248850215285228124680385)
      ·
        refine ⟨10686637661463921093510289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14248850215285228124680385 10686637661463921093510289)
        ·
          refine ⟨8014978246097940820132717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10686637661463921093510289 8014978246097940820132717)
          ·
            refine ⟨3005616842286727807549769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8014978246097940820132717 3005616842286727807549769)
            ·
              refine ⟨2254212631715045855662327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005616842286727807549769 2254212631715045855662327)
              ·
                refine ⟨3381318947572568783493491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254212631715045855662327 3381318947572568783493491)
                ·
                  refine ⟨5071978421358853175240237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381318947572568783493491 5071978421358853175240237)
                  ·
                    refine ⟨1901991908009569940715089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5071978421358853175240237 1901991908009569940715089)
                    ·
                      refine ⟨1426493931007177455536317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1901991908009569940715089 1426493931007177455536317)
                      ·
                        rfl

theorem cell23_2778087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_2778087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778087 prefixEnd_2778087 := by exact prefixLift 2778087
  have htrace : WordTrace (prefixWord ++ tailWord_2778087) baseStart_2778087 baseEnd_2778087 := by
    simpa [prefixWord, tailWord_2778087, baseEnd_2778087] using wordTrace_append hprefix tailTrace_2778087
  have hstable : (prefixWord ++ tailWord_2778087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778087).length < 2 ^ (prefixWord ++ tailWord_2778087).sum := by decide
  have hdescent : baseEnd_2778087 < baseStart_2778087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778119 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 3, 7]
def baseStart_2778119 : Nat := 118140960795 + 2778119 * 2 ^ 59
def prefixEnd_2778119 : Nat := 4983230072969 + 3 ^ 40 * 2778119 * 2
def baseEnd_2778119 : Nat := 475503454129373776778723

theorem tailTrace_2778119 : CollatzResearch.WordTrace tailWord_2778119 prefixEnd_2778119 475503454129373776778723 := by
  unfold tailWord_2778119
  simp only [CollatzResearch.WordTrace]
  refine ⟨101326324222356802796225411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67550882814904535197483607 101326324222356802796225411)
  ·
    refine ⟨151989486333535204194338117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101326324222356802796225411 151989486333535204194338117)
    ·
      refine ⟨28498028687537850786438397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 151989486333535204194338117 28498028687537850786438397)
      ·
        refine ⟨10686760757826694044914399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28498028687537850786438397 10686760757826694044914399)
        ·
          refine ⟨16030141136740041067371599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10686760757826694044914399 16030141136740041067371599)
          ·
            refine ⟨24045211705110061601057399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16030141136740041067371599 24045211705110061601057399)
            ·
              refine ⟨36067817557665092401586099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24045211705110061601057399 36067817557665092401586099)
              ·
                refine ⟨54101726336497638602379149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36067817557665092401586099 54101726336497638602379149)
                ·
                  refine ⟨20288147376186614475892181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54101726336497638602379149 20288147376186614475892181)
                  ·
                    refine ⟨475503454129373776778723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 20288147376186614475892181 475503454129373776778723)
                    ·
                      rfl

theorem cell23_2778119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 3, 7].length) (baseStart_2778119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778119 prefixEnd_2778119 := by exact prefixLift 2778119
  have htrace : WordTrace (prefixWord ++ tailWord_2778119) baseStart_2778119 baseEnd_2778119 := by
    simpa [prefixWord, tailWord_2778119, baseEnd_2778119] using wordTrace_append hprefix tailTrace_2778119
  have hstable : (prefixWord ++ tailWord_2778119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778119).length < 2 ^ (prefixWord ++ tailWord_2778119).sum := by decide
  have hdescent : baseEnd_2778119 < baseStart_2778119 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778140 : List Nat := [2, 2, 3, 1, 4, 2, 1, 3, 5]
def baseStart_2778140 : Nat := 118140960795 + 2778140 * 2 ^ 59
def prefixEnd_2778140 : Nat := 4983230072969 + 3 ^ 40 * 2778140 * 2
def baseEnd_2778140 : Nat := 158502349497985083130397

theorem tailTrace_2778140 : CollatzResearch.WordTrace tailWord_2778140 prefixEnd_2778140 158502349497985083130397 := by
  unfold tailWord_2778140
  simp only [CollatzResearch.WordTrace]
  refine ⟨50663545077640361691369937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67551393436853815588493249 50663545077640361691369937)
  ·
    refine ⟨37997658808230271268527453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50663545077640361691369937 37997658808230271268527453)
    ·
      refine ⟨14249122053086351725697795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 37997658808230271268527453 14249122053086351725697795)
      ·
        refine ⟨21373683079629527588546693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14249122053086351725697795 21373683079629527588546693)
        ·
          refine ⟨4007565577430536422852505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21373683079629527588546693 4007565577430536422852505)
          ·
            refine ⟨3005674183072902317139379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4007565577430536422852505 3005674183072902317139379)
            ·
              refine ⟨4508511274609353475709069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3005674183072902317139379 4508511274609353475709069)
              ·
                refine ⟨1690691727978507553390901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4508511274609353475709069 1690691727978507553390901)
                ·
                  refine ⟨158502349497985083130397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1690691727978507553390901 158502349497985083130397)
                  ·
                    rfl

theorem cell23_2778140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 3, 5].length) (baseStart_2778140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778140 prefixEnd_2778140 := by exact prefixLift 2778140
  have htrace : WordTrace (prefixWord ++ tailWord_2778140) baseStart_2778140 baseEnd_2778140 := by
    simpa [prefixWord, tailWord_2778140, baseEnd_2778140] using wordTrace_append hprefix tailTrace_2778140
  have hstable : (prefixWord ++ tailWord_2778140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778140).length < 2 ^ (prefixWord ++ tailWord_2778140).sum := by decide
  have hdescent : baseEnd_2778140 < baseStart_2778140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778156 : List Nat := [2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 4]
def baseStart_2778156 : Nat := 118140960795 + 2778156 * 2 ^ 59
def prefixEnd_2778156 : Nat := 4983230072969 + 3 ^ 40 * 2778156 * 2
def baseEnd_2778156 : Nat := 1426529361172337685573499

theorem tailTrace_2778156 : CollatzResearch.WordTrace tailWord_2778156 prefixEnd_2778156 1426529361172337685573499 := by
  unfold tailWord_2778156
  simp only [CollatzResearch.WordTrace]
  refine ⟨50663836861611379057661161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67551782482148505410214881 50663836861611379057661161)
  ·
    refine ⟨37997877646208534293245871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50663836861611379057661161 37997877646208534293245871)
    ·
      refine ⟨56996816469312801439868807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 37997877646208534293245871 56996816469312801439868807)
      ·
        refine ⟨85495224703969202159803211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 56996816469312801439868807 85495224703969202159803211)
        ·
          refine ⟨128242837055953803239704817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85495224703969202159803211 128242837055953803239704817)
          ·
            refine ⟨96182127791965352429778613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 128242837055953803239704817 96182127791965352429778613)
            ·
              refine ⟨9017074480496751790291745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 96182127791965352429778613 9017074480496751790291745)
              ·
                refine ⟨6762805860372563842718809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9017074480496751790291745 6762805860372563842718809)
                ·
                  refine ⟨5072104395279422882039107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6762805860372563842718809 5072104395279422882039107)
                  ·
                    refine ⟨7608156592919134323058661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5072104395279422882039107 7608156592919134323058661)
                    ·
                      refine ⟨1426529361172337685573499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7608156592919134323058661 1426529361172337685573499)
                      ·
                        rfl

theorem cell23_2778156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 4].length) (baseStart_2778156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778156 prefixEnd_2778156 := by exact prefixLift 2778156
  have htrace : WordTrace (prefixWord ++ tailWord_2778156) baseStart_2778156 baseEnd_2778156 := by
    simpa [prefixWord, tailWord_2778156, baseEnd_2778156] using wordTrace_append hprefix tailTrace_2778156
  have hstable : (prefixWord ++ tailWord_2778156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778156).length < 2 ^ (prefixWord ++ tailWord_2778156).sum := by decide
  have hdescent : baseEnd_2778156 < baseStart_2778156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778176 : List Nat := [2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3]
def baseStart_2778176 : Nat := 118140960795 + 2778176 * 2 ^ 59
def prefixEnd_2778176 : Nat := 4983230072969 + 3 ^ 40 * 2778176 * 2
def baseEnd_2778176 : Nat := 1426539630785427607323407

theorem tailTrace_2778176 : CollatzResearch.WordTrace tailWord_2778176 prefixEnd_2778176 1426539630785427607323407 := by
  unfold tailWord_2778176
  simp only [CollatzResearch.WordTrace]
  refine ⟨50664201591575150765525191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67552268788766867687366921 50664201591575150765525191)
  ·
    refine ⟨75996302387362726148287787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50664201591575150765525191 75996302387362726148287787)
    ·
      refine ⟨113994453581044089222431681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75996302387362726148287787 113994453581044089222431681)
      ·
        refine ⟨85495840185783066916823761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 113994453581044089222431681 85495840185783066916823761)
        ·
          refine ⟨64121880139337300187617821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85495840185783066916823761 64121880139337300187617821)
          ·
            refine ⟨24045705052251487570356683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64121880139337300187617821 24045705052251487570356683)
            ·
              refine ⟨36068557578377231355535025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24045705052251487570356683 36068557578377231355535025)
              ·
                refine ⟨27051418183782923516651269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36068557578377231355535025 27051418183782923516651269)
                ·
                  refine ⟨5072140909459298159372113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27051418183782923516651269 5072140909459298159372113)
                  ·
                    refine ⟨3804105682094473619529085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5072140909459298159372113 3804105682094473619529085)
                    ·
                      refine ⟨1426539630785427607323407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804105682094473619529085 1426539630785427607323407)
                      ·
                        rfl

theorem cell23_2778176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 3].length) (baseStart_2778176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778176 prefixEnd_2778176 := by exact prefixLift 2778176
  have htrace : WordTrace (prefixWord ++ tailWord_2778176) baseStart_2778176 baseEnd_2778176 := by
    simpa [prefixWord, tailWord_2778176, baseEnd_2778176] using wordTrace_append hprefix tailTrace_2778176
  have hstable : (prefixWord ++ tailWord_2778176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778176).length < 2 ^ (prefixWord ++ tailWord_2778176).sum := by decide
  have hdescent : baseEnd_2778176 < baseStart_2778176 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778199 : List Nat := [1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 8]
def baseStart_2778199 : Nat := 118140960795 + 2778199 * 2 ^ 59
def prefixEnd_2778199 : Nat := 4983230072969 + 3 ^ 40 * 2778199 * 2
def baseEnd_2778199 : Nat := 1426551440840481017335801

theorem tailTrace_2778199 : CollatzResearch.WordTrace tailWord_2778199 prefixEnd_2778199 1426551440840481017335801 := by
  unfold tailWord_2778199
  simp only [CollatzResearch.WordTrace]
  refine ⟨101329242062066976459137651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67552828041377984306091767 101329242062066976459137651)
  ·
    refine ⟨151993863093100464688706477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101329242062066976459137651 151993863093100464688706477)
    ·
      refine ⟨56997698659912674258264929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 151993863093100464688706477 56997698659912674258264929)
      ·
        refine ⟨42748273994934505693698697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 56997698659912674258264929 42748273994934505693698697)
        ·
          refine ⟨32061205496200879270274023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42748273994934505693698697 32061205496200879270274023)
          ·
            refine ⟨48091808244301318905411035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32061205496200879270274023 48091808244301318905411035)
            ·
              refine ⟨72137712366451978358116553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48091808244301318905411035 72137712366451978358116553)
              ·
                refine ⟨54103284274838983768587415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72137712366451978358116553 54103284274838983768587415)
                ·
                  refine ⟨81154926412258475652881123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54103284274838983768587415 81154926412258475652881123)
                  ·
                    refine ⟨121732389618387713479321685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81154926412258475652881123 121732389618387713479321685)
                    ·
                      refine ⟨1426551440840481017335801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 121732389618387713479321685 1426551440840481017335801)
                      ·
                        rfl

theorem cell23_2778199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_2778199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778199 prefixEnd_2778199 := by exact prefixLift 2778199
  have htrace : WordTrace (prefixWord ++ tailWord_2778199) baseStart_2778199 baseEnd_2778199 := by
    simpa [prefixWord, tailWord_2778199, baseEnd_2778199] using wordTrace_append hprefix tailTrace_2778199
  have hstable : (prefixWord ++ tailWord_2778199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778199).length < 2 ^ (prefixWord ++ tailWord_2778199).sum := by decide
  have hdescent : baseEnd_2778199 < baseStart_2778199 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778210 : List Nat := [3, 3, 2, 2, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2778210 : Nat := 118140960795 + 2778210 * 2 ^ 59
def prefixEnd_2778210 : Nat := 4983230072969 + 3 ^ 40 * 2778210 * 2
def baseEnd_2778210 : Nat := 1426557089127680474298251

theorem tailTrace_2778210 : CollatzResearch.WordTrace tailWord_2778210 prefixEnd_2778210 1426557089127680474298251 := by
  unfold tailWord_2778210
  simp only [CollatzResearch.WordTrace]
  refine ⟨25332410816256781334447021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67553095510018083558525389 25332410816256781334447021)
  ·
    refine ⟨9499654056096293000417633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 25332410816256781334447021 9499654056096293000417633)
    ·
      refine ⟨7124740542072219750313225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9499654056096293000417633 7124740542072219750313225)
      ·
        refine ⟨5343555406554164812734919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7124740542072219750313225 5343555406554164812734919)
        ·
          refine ⟨8015333109831247219102379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343555406554164812734919 8015333109831247219102379)
          ·
            refine ⟨12022999664746870828653569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8015333109831247219102379 12022999664746870828653569)
            ·
              refine ⟨9017249748560153121490177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12022999664746870828653569 9017249748560153121490177)
              ·
                refine ⟨6762937311420114841117633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9017249748560153121490177 6762937311420114841117633)
                ·
                  refine ⟨5072202983565086130838225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6762937311420114841117633 5072202983565086130838225)
                  ·
                    refine ⟨3804152237673814598128669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5072202983565086130838225 3804152237673814598128669)
                    ·
                      refine ⟨1426557089127680474298251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804152237673814598128669 1426557089127680474298251)
                      ·
                        rfl

theorem cell23_2778210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2778210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778210 prefixEnd_2778210 := by exact prefixLift 2778210
  have htrace : WordTrace (prefixWord ++ tailWord_2778210) baseStart_2778210 baseEnd_2778210 := by
    simpa [prefixWord, tailWord_2778210, baseEnd_2778210] using wordTrace_append hprefix tailTrace_2778210
  have hstable : (prefixWord ++ tailWord_2778210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778210).length < 2 ^ (prefixWord ++ tailWord_2778210).sum := by decide
  have hdescent : baseEnd_2778210 < baseStart_2778210 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778217 : List Nat := [1, 2, 1, 1, 1, 8, 2, 2, 1, 4]
def baseStart_2778217 : Nat := 118140960795 + 2778217 * 2 ^ 59
def prefixEnd_2778217 : Nat := 4983230072969 + 3 ^ 40 * 2778217 * 2
def baseEnd_2778217 : Nat := 475520227830753982303573

theorem tailTrace_2778217 : CollatzResearch.WordTrace tailWord_2778217 prefixEnd_2778217 475520227830753982303573 := by
  unfold tailWord_2778217
  simp only [CollatzResearch.WordTrace]
  refine ⟨101329898576001765533292905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67553265717334510355528603 101329898576001765533292905)
  ·
    refine ⟨75997423932001324149969679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101329898576001765533292905 75997423932001324149969679)
    ·
      refine ⟨113996135898001986224954519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 75997423932001324149969679 113996135898001986224954519)
      ·
        refine ⟨170994203847002979337431779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113996135898001986224954519 170994203847002979337431779)
        ·
          refine ⟨256491305770504469006147669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 170994203847002979337431779 256491305770504469006147669)
          ·
            refine ⟨3005757489498099246165793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 256491305770504469006147669 3005757489498099246165793)
            ·
              refine ⟨2254318117123574434624345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3005757489498099246165793 2254318117123574434624345)
              ·
                refine ⟨1690738587842680825968259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254318117123574434624345 1690738587842680825968259)
                ·
                  refine ⟨2536107881764021238952389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690738587842680825968259 2536107881764021238952389)
                  ·
                    refine ⟨475520227830753982303573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2536107881764021238952389 475520227830753982303573)
                    ·
                      rfl

theorem cell23_2778217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 2, 2, 1, 4].length) (baseStart_2778217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778217 prefixEnd_2778217 := by exact prefixLift 2778217
  have htrace : WordTrace (prefixWord ++ tailWord_2778217) baseStart_2778217 baseEnd_2778217 := by
    simpa [prefixWord, tailWord_2778217, baseEnd_2778217] using wordTrace_append hprefix tailTrace_2778217
  have hstable : (prefixWord ++ tailWord_2778217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778217).length < 2 ^ (prefixWord ++ tailWord_2778217).sum := by decide
  have hdescent : baseEnd_2778217 < baseStart_2778217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778219 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5]
def baseStart_2778219 : Nat := 118140960795 + 2778219 * 2 ^ 59
def prefixEnd_2778219 : Nat := 4983230072969 + 3 ^ 40 * 2778219 * 2
def baseEnd_2778219 : Nat := 1426561710453570939085709

theorem tailTrace_2778219 : CollatzResearch.WordTrace tailWord_2778219 prefixEnd_2778219 1426561710453570939085709 := by
  unfold tailWord_2778219
  simp only [CollatzResearch.WordTrace]
  refine ⟨101329971521994519874865711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67553314347996346583243807 101329971521994519874865711)
  ·
    refine ⟨151994957282991779812298567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101329971521994519874865711 151994957282991779812298567)
    ·
      refine ⟨227992435924487669718447851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 151994957282991779812298567 227992435924487669718447851)
      ·
        refine ⟨341988653886731504577671777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 227992435924487669718447851 341988653886731504577671777)
        ·
          refine ⟨256491490415048628433253833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 341988653886731504577671777 256491490415048628433253833)
          ·
            refine ⟨192368617811286471324940375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256491490415048628433253833 192368617811286471324940375)
            ·
              refine ⟨288552926716929706987410563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192368617811286471324940375 288552926716929706987410563)
              ·
                refine ⟨432829390075394560481115845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288552926716929706987410563 432829390075394560481115845)
                ·
                  refine ⟨81155510639136480090209221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 432829390075394560481115845 81155510639136480090209221)
                  ·
                    refine ⟨15216658244838090016914229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 81155510639136480090209221 15216658244838090016914229)
                    ·
                      refine ⟨1426561710453570939085709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15216658244838090016914229 1426561710453570939085709)
                      ·
                        rfl

theorem cell23_2778219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_2778219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778219 prefixEnd_2778219 := by exact prefixLift 2778219
  have htrace : WordTrace (prefixWord ++ tailWord_2778219) baseStart_2778219 baseEnd_2778219 := by
    simpa [prefixWord, tailWord_2778219, baseEnd_2778219] using wordTrace_append hprefix tailTrace_2778219
  have hstable : (prefixWord ++ tailWord_2778219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778219).length < 2 ^ (prefixWord ++ tailWord_2778219).sum := by decide
  have hdescent : baseEnd_2778219 < baseStart_2778219 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778223 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 3]
def baseStart_2778223 : Nat := 118140960795 + 2778223 * 2 ^ 59
def prefixEnd_2778223 : Nat := 4983230072969 + 3 ^ 40 * 2778223 * 2
def baseEnd_2778223 : Nat := 1426563764376188923435691

theorem tailTrace_2778223 : CollatzResearch.WordTrace tailWord_2778223 prefixEnd_2778223 1426563764376188923435691 := by
  unfold tailWord_2778223
  simp only [CollatzResearch.WordTrace]
  refine ⟨101330117413980028558011323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67553411609320019038674215 101330117413980028558011323)
  ·
    refine ⟨151995176120970042837016985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101330117413980028558011323 151995176120970042837016985)
    ·
      refine ⟨113996382090727532127762739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 151995176120970042837016985 113996382090727532127762739)
      ·
        refine ⟨170994573136091298191644109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 113996382090727532127762739 170994573136091298191644109)
        ·
          refine ⟨64122964926034236821866541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 170994573136091298191644109 64122964926034236821866541)
          ·
            refine ⟨24046111847262838808199953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64122964926034236821866541 24046111847262838808199953)
            ·
              refine ⟨18034583885447129106149965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24046111847262838808199953 18034583885447129106149965)
              ·
                refine ⟨6762968957042673414806237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18034583885447129106149965 6762968957042673414806237)
                ·
                  refine ⟨2536113358891002530552339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6762968957042673414806237 2536113358891002530552339)
                  ·
                    refine ⟨3804170038336503795828509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536113358891002530552339 3804170038336503795828509)
                    ·
                      refine ⟨1426563764376188923435691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804170038336503795828509 1426563764376188923435691)
                      ·
                        rfl

theorem cell23_2778223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 3, 1, 3].length) (baseStart_2778223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778223 prefixEnd_2778223 := by exact prefixLift 2778223
  have htrace : WordTrace (prefixWord ++ tailWord_2778223) baseStart_2778223 baseEnd_2778223 := by
    simpa [prefixWord, tailWord_2778223, baseEnd_2778223] using wordTrace_append hprefix tailTrace_2778223
  have hstable : (prefixWord ++ tailWord_2778223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778223).length < 2 ^ (prefixWord ++ tailWord_2778223).sum := by decide
  have hdescent : baseEnd_2778223 < baseStart_2778223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778226 : List Nat := [3, 2, 1, 2, 2, 1, 1, 1, 5, 5]
def baseStart_2778226 : Nat := 118140960795 + 2778226 * 2 ^ 59
def prefixEnd_2778226 : Nat := 4983230072969 + 3 ^ 40 * 2778226 * 2
def baseEnd_2778226 : Nat := 475521768272717470566059

theorem tailTrace_2778226 : CollatzResearch.WordTrace tailWord_2778226 prefixEnd_2778226 475521768272717470566059 := by
  unfold tailWord_2778226
  simp only [CollatzResearch.WordTrace]
  refine ⟨25332556708242290017592633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67553484555312773380247021 25332556708242290017592633)
  ·
    refine ⟨18999417531181717513194475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25332556708242290017592633 18999417531181717513194475)
    ·
      refine ⟨28499126296772576269791713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18999417531181717513194475 28499126296772576269791713)
      ·
        refine ⟨21374344722579432202343785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28499126296772576269791713 21374344722579432202343785)
        ·
          refine ⟨16030758541934574151757839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21374344722579432202343785 16030758541934574151757839)
          ·
            refine ⟨24046137812901861227636759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16030758541934574151757839 24046137812901861227636759)
            ·
              refine ⟨36069206719352791841455139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24046137812901861227636759 36069206719352791841455139)
              ·
                refine ⟨54103810079029187762182709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36069206719352791841455139 54103810079029187762182709)
                ·
                  refine ⟨5072232194908986352704629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54103810079029187762182709 5072232194908986352704629)
                  ·
                    refine ⟨475521768272717470566059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5072232194908986352704629 475521768272717470566059)
                    ·
                      rfl

theorem cell23_2778226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 5, 5].length) (baseStart_2778226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778226 prefixEnd_2778226 := by exact prefixLift 2778226
  have htrace : WordTrace (prefixWord ++ tailWord_2778226) baseStart_2778226 baseEnd_2778226 := by
    simpa [prefixWord, tailWord_2778226, baseEnd_2778226] using wordTrace_append hprefix tailTrace_2778226
  have hstable : (prefixWord ++ tailWord_2778226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778226).length < 2 ^ (prefixWord ++ tailWord_2778226).sum := by decide
  have hdescent : baseEnd_2778226 < baseStart_2778226 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778273 : List Nat := [1, 2, 3, 3, 1, 1, 3, 1, 4, 4]
def baseStart_2778273 : Nat := 118140960795 + 2778273 * 2 ^ 59
def prefixEnd_2778273 : Nat := 4983230072969 + 3 ^ 40 * 2778273 * 2
def baseEnd_2778273 : Nat := 475529812802971242603487

theorem tailTrace_2778273 : CollatzResearch.WordTrace tailWord_2778273 prefixEnd_2778273 475529812802971242603487 := by
  unfold tailWord_2778273
  simp only [CollatzResearch.WordTrace]
  refine ⟨101331941063798887097331473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67554627375865924731554315 101331941063798887097331473)
  ·
    refine ⟨75998955797849165322998605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101331941063798887097331473 75998955797849165322998605)
    ·
      refine ⟨28499608424193436996124477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 75998955797849165322998605 28499608424193436996124477)
      ·
        refine ⟨10687353159072538873546679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28499608424193436996124477 10687353159072538873546679)
        ·
          refine ⟨16031029738608808310320019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10687353159072538873546679 16031029738608808310320019)
          ·
            refine ⟨24046544607913212465480029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16031029738608808310320019 24046544607913212465480029)
            ·
              refine ⟨9017454227967454674555011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24046544607913212465480029 9017454227967454674555011)
              ·
                refine ⟨13526181341951182011832517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9017454227967454674555011 13526181341951182011832517)
                ·
                  refine ⟨2536159001615846627218597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13526181341951182011832517 2536159001615846627218597)
                  ·
                    refine ⟨475529812802971242603487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2536159001615846627218597 475529812802971242603487)
                    ·
                      rfl

theorem cell23_2778273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 4, 4].length) (baseStart_2778273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778273 prefixEnd_2778273 := by exact prefixLift 2778273
  have htrace : WordTrace (prefixWord ++ tailWord_2778273) baseStart_2778273 baseEnd_2778273 := by
    simpa [prefixWord, tailWord_2778273, baseEnd_2778273] using wordTrace_append hprefix tailTrace_2778273
  have hstable : (prefixWord ++ tailWord_2778273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778273).length < 2 ^ (prefixWord ++ tailWord_2778273).sum := by decide
  have hdescent : baseEnd_2778273 < baseStart_2778273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778294 : List Nat := [5, 1, 3, 2, 1, 1, 2, 2, 1, 5]
def baseStart_2778294 : Nat := 118140960795 + 2778294 * 2 ^ 59
def prefixEnd_2778294 : Nat := 4983230072969 + 3 ^ 40 * 2778294 * 2
def baseEnd_2778294 : Nat := 475533407167552715215955

theorem tailTrace_2778294 : CollatzResearch.WordTrace tailWord_2778294 prefixEnd_2778294 475533407167552715215955 := by
  unfold tailWord_2778294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6333294187295175480240371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67555137997815205122563957 6333294187295175480240371)
  ·
    refine ⟨9499941280942763220360557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6333294187295175480240371 9499941280942763220360557)
    ·
      refine ⟨3562477980353536207635209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9499941280942763220360557 3562477980353536207635209)
      ·
        refine ⟨2671858485265152155726407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3562477980353536207635209 2671858485265152155726407)
        ·
          refine ⟨4007787727897728233589611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671858485265152155726407 4007787727897728233589611)
          ·
            refine ⟨6011681591846592350384417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007787727897728233589611 6011681591846592350384417)
            ·
              refine ⟨4508761193884944262788313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6011681591846592350384417 4508761193884944262788313)
              ·
                refine ⟨3381570895413708197091235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4508761193884944262788313 3381570895413708197091235)
                ·
                  refine ⟨5072356343120562295636853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381570895413708197091235 5072356343120562295636853)
                  ·
                    refine ⟨475533407167552715215955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5072356343120562295636853 475533407167552715215955)
                    ·
                      rfl

theorem cell23_2778294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 1, 2, 2, 1, 5].length) (baseStart_2778294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778294 prefixEnd_2778294 := by exact prefixLift 2778294
  have htrace : WordTrace (prefixWord ++ tailWord_2778294) baseStart_2778294 baseEnd_2778294 := by
    simpa [prefixWord, tailWord_2778294, baseEnd_2778294] using wordTrace_append hprefix tailTrace_2778294
  have hstable : (prefixWord ++ tailWord_2778294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778294).length < 2 ^ (prefixWord ++ tailWord_2778294).sum := by decide
  have hdescent : baseEnd_2778294 < baseStart_2778294 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778300 : List Nat := [2, 2, 2, 3, 2, 1, 1, 4, 1, 2, 3]
def baseStart_2778300 : Nat := 118140960795 + 2778300 * 2 ^ 59
def prefixEnd_2778300 : Nat := 4983230072969 + 3 ^ 40 * 2778300 * 2
def baseEnd_2778300 : Nat := 1426603302386585122172837

theorem tailTrace_2778300 : CollatzResearch.WordTrace tailWord_2778300 prefixEnd_2778300 1426603302386585122172837 := by
  unfold tailWord_2778300
  simp only [CollatzResearch.WordTrace]
  refine ⟨50666462917350535354282177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67555283889800713805709569 50666462917350535354282177)
  ·
    refine ⟨37999847188012901515711633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50666462917350535354282177 37999847188012901515711633)
    ·
      refine ⟨28499885391009676136783725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 37999847188012901515711633 28499885391009676136783725)
      ·
        refine ⟨10687457021628628551293897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28499885391009676136783725 10687457021628628551293897)
        ·
          refine ⟨8015592766221471413470423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10687457021628628551293897 8015592766221471413470423)
          ·
            refine ⟨12023389149332207120205635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8015592766221471413470423 12023389149332207120205635)
            ·
              refine ⟨18035083723998310680308453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12023389149332207120205635 18035083723998310680308453)
              ·
                refine ⟨3381578198249683252557835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18035083723998310680308453 3381578198249683252557835)
                ·
                  refine ⟨5072367297374524878836753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3381578198249683252557835 5072367297374524878836753)
                  ·
                    refine ⟨3804275473030893659127565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5072367297374524878836753 3804275473030893659127565)
                    ·
                      refine ⟨1426603302386585122172837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804275473030893659127565 1426603302386585122172837)
                      ·
                        rfl

theorem cell23_2778300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_2778300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778300 prefixEnd_2778300 := by exact prefixLift 2778300
  have htrace : WordTrace (prefixWord ++ tailWord_2778300) baseStart_2778300 baseEnd_2778300 := by
    simpa [prefixWord, tailWord_2778300, baseEnd_2778300] using wordTrace_append hprefix tailTrace_2778300
  have hstable : (prefixWord ++ tailWord_2778300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778300).length < 2 ^ (prefixWord ++ tailWord_2778300).sum := by decide
  have hdescent : baseEnd_2778300 < baseStart_2778300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778314 : List Nat := [3, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2]
def baseStart_2778314 : Nat := 118140960795 + 2778314 * 2 ^ 59
def prefixEnd_2778314 : Nat := 4983230072969 + 3 ^ 40 * 2778314 * 2
def baseEnd_2778314 : Nat := 1426610491115748067397773

theorem tailTrace_2778314 : CollatzResearch.WordTrace tailWord_2778314 prefixEnd_2778314 1426610491115748067397773 := by
  unfold tailWord_2778314
  simp only [CollatzResearch.WordTrace]
  refine ⟨25333359114162587774893499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67555624304433567399715997 25333359114162587774893499)
  ·
    refine ⟨38000038671243881662340249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25333359114162587774893499 38000038671243881662340249)
    ·
      refine ⟨28500029003432911246755187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38000038671243881662340249 28500029003432911246755187)
      ·
        refine ⟨42750043505149366870132781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28500029003432911246755187 42750043505149366870132781)
        ·
          refine ⟨16031266314431012576299793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42750043505149366870132781 16031266314431012576299793)
          ·
            refine ⟨12023449735823259432224845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16031266314431012576299793 12023449735823259432224845)
            ·
              refine ⟨4508793650933722287084317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12023449735823259432224845 4508793650933722287084317)
              ·
                refine ⟨1690797619100145857656619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4508793650933722287084317 1690797619100145857656619)
                ·
                  refine ⟨2536196428650218786484929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1690797619100145857656619 2536196428650218786484929)
                  ·
                    refine ⟨1902147321487664089863697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2536196428650218786484929 1902147321487664089863697)
                    ·
                      refine ⟨1426610491115748067397773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902147321487664089863697 1426610491115748067397773)
                      ·
                        rfl

theorem cell23_2778314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 3, 1, 2, 2].length) (baseStart_2778314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778314 prefixEnd_2778314 := by exact prefixLift 2778314
  have htrace : WordTrace (prefixWord ++ tailWord_2778314) baseStart_2778314 baseEnd_2778314 := by
    simpa [prefixWord, tailWord_2778314, baseEnd_2778314] using wordTrace_append hprefix tailTrace_2778314
  have hstable : (prefixWord ++ tailWord_2778314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778314).length < 2 ^ (prefixWord ++ tailWord_2778314).sum := by decide
  have hdescent : baseEnd_2778314 < baseStart_2778314 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778330 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_2778330 : Nat := 118140960795 + 2778330 * 2 ^ 59
def prefixEnd_2778330 : Nat := 4983230072969 + 3 ^ 40 * 2778330 * 2
def baseEnd_2778330 : Nat := 1426618706806220004797699

theorem tailTrace_2778330 : CollatzResearch.WordTrace tailWord_2778330 prefixEnd_2778330 1426618706806220004797699 := by
  unfold tailWord_2778330
  simp only [CollatzResearch.WordTrace]
  refine ⟨25333505006148096458039111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67556013349728257221437629 25333505006148096458039111)
  ·
    refine ⟨38000257509222144687058667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25333505006148096458039111 38000257509222144687058667)
    ·
      refine ⟨57000386263833217030588001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38000257509222144687058667 57000386263833217030588001)
      ·
        refine ⟨42750289697874912772941001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57000386263833217030588001 42750289697874912772941001)
        ·
          refine ⟨32062717273406184579705751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42750289697874912772941001 32062717273406184579705751)
          ·
            refine ⟨48094075910109276869558627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32062717273406184579705751 48094075910109276869558627)
            ·
              refine ⟨72141113865163915304337941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48094075910109276869558627 72141113865163915304337941)
              ·
                refine ⟨3381614712429558529890841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 72141113865163915304337941 3381614712429558529890841)
                ·
                  refine ⟨2536211034322168897418131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3381614712429558529890841 2536211034322168897418131)
                  ·
                    refine ⟨3804316551483253346127197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536211034322168897418131 3804316551483253346127197)
                    ·
                      refine ⟨1426618706806220004797699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804316551483253346127197 1426618706806220004797699)
                      ·
                        rfl

theorem cell23_2778330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_2778330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778330 prefixEnd_2778330 := by exact prefixLift 2778330
  have htrace : WordTrace (prefixWord ++ tailWord_2778330) baseStart_2778330 baseEnd_2778330 := by
    simpa [prefixWord, tailWord_2778330, baseEnd_2778330] using wordTrace_append hprefix tailTrace_2778330
  have hstable : (prefixWord ++ tailWord_2778330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778330).length < 2 ^ (prefixWord ++ tailWord_2778330).sum := by decide
  have hdescent : baseEnd_2778330 < baseStart_2778330 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778347 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 2, 1, 3]
def baseStart_2778347 : Nat := 118140960795 + 2778347 * 2 ^ 59
def prefixEnd_2778347 : Nat := 4983230072969 + 3 ^ 40 * 2778347 * 2
def baseEnd_2778347 : Nat := 1426627435977346438285121

theorem tailTrace_2778347 : CollatzResearch.WordTrace tailWord_2778347 prefixEnd_2778347 1426627435977346438285121 := by
  unfold tailWord_2778347
  simp only [CollatzResearch.WordTrace]
  refine ⟨101334640065530797735525295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67556426710353865157016863 101334640065530797735525295)
  ·
    refine ⟨152001960098296196603287943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101334640065530797735525295 152001960098296196603287943)
    ·
      refine ⟨228002940147444294904931915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152001960098296196603287943 228002940147444294904931915)
      ·
        refine ⟨342004410221166442357397873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228002940147444294904931915 342004410221166442357397873)
        ·
          refine ⟨256503307665874831768048405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342004410221166442357397873 256503307665874831768048405)
          ·
            refine ⟨12023592546837882739127269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 256503307665874831768048405 12023592546837882739127269)
            ·
              refine ⟨2254423602532103013586363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12023592546837882739127269 2254423602532103013586363)
              ·
                refine ⟨3381635403798154520379545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254423602532103013586363 3381635403798154520379545)
                ·
                  refine ⟨2536226552848615890284659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3381635403798154520379545 2536226552848615890284659)
                  ·
                    refine ⟨3804339829272923835426989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536226552848615890284659 3804339829272923835426989)
                    ·
                      refine ⟨1426627435977346438285121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804339829272923835426989 1426627435977346438285121)
                      ·
                        rfl

theorem cell23_2778347_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 2, 1, 3].length) (baseStart_2778347 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778347 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778347 prefixEnd_2778347 := by exact prefixLift 2778347
  have htrace : WordTrace (prefixWord ++ tailWord_2778347) baseStart_2778347 baseEnd_2778347 := by
    simpa [prefixWord, tailWord_2778347, baseEnd_2778347] using wordTrace_append hprefix tailTrace_2778347
  have hstable : (prefixWord ++ tailWord_2778347).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778347).length < 2 ^ (prefixWord ++ tailWord_2778347).sum := by decide
  have hdescent : baseEnd_2778347 < baseStart_2778347 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778347) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778400 : List Nat := [2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4]
def baseStart_2778400 : Nat := 118140960795 + 2778400 * 2 ^ 59
def prefixEnd_2778400 : Nat := 4983230072969 + 3 ^ 40 * 2778400 * 2
def baseEnd_2778400 : Nat := 1426654650452034730922377

theorem tailTrace_2778400 : CollatzResearch.WordTrace tailWord_2778400 prefixEnd_2778400 1426654650452034730922377 := by
  unfold tailWord_2778400
  simp only [CollatzResearch.WordTrace]
  refine ⟨50668286567169393893602327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67557715422892525191469769 50668286567169393893602327)
  ·
    refine ⟨76002429850754090840403491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50668286567169393893602327 76002429850754090840403491)
    ·
      refine ⟨114003644776131136260605237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76002429850754090840403491 114003644776131136260605237)
      ·
        refine ⟨10687841697762294024431741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 114003644776131136260605237 10687841697762294024431741)
        ·
          refine ⟨4007940636660860259161903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10687841697762294024431741 4007940636660860259161903)
          ·
            refine ⟨6011910954991290388742855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007940636660860259161903 6011910954991290388742855)
            ·
              refine ⟨9017866432486935583114283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011910954991290388742855 9017866432486935583114283)
              ·
                refine ⟨13526799648730403374671425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9017866432486935583114283 13526799648730403374671425)
                ·
                  refine ⟨10145099736547802531003569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13526799648730403374671425 10145099736547802531003569)
                  ·
                    refine ⟨7608824802410851898252677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10145099736547802531003569 7608824802410851898252677)
                    ·
                      refine ⟨1426654650452034730922377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7608824802410851898252677 1426654650452034730922377)
                      ·
                        rfl

theorem cell23_2778400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_2778400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778400 prefixEnd_2778400 := by exact prefixLift 2778400
  have htrace : WordTrace (prefixWord ++ tailWord_2778400) baseStart_2778400 baseEnd_2778400 := by
    simpa [prefixWord, tailWord_2778400, baseEnd_2778400] using wordTrace_append hprefix tailTrace_2778400
  have hstable : (prefixWord ++ tailWord_2778400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778400).length < 2 ^ (prefixWord ++ tailWord_2778400).sum := by decide
  have hdescent : baseEnd_2778400 < baseStart_2778400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778403 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 3]
def baseStart_2778403 : Nat := 118140960795 + 2778403 * 2 ^ 59
def prefixEnd_2778403 : Nat := 4983230072969 + 3 ^ 40 * 2778403 * 2
def baseEnd_2778403 : Nat := 1426656190893998219184863

theorem tailTrace_2778403 : CollatzResearch.WordTrace tailWord_2778403 prefixEnd_2778403 1426656190893998219184863 := by
  unfold tailWord_2778403
  simp only [CollatzResearch.WordTrace]
  refine ⟨101336682553327919299563863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67557788368885279533042575 101336682553327919299563863)
  ·
    refine ⟨152005023829991878949345795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101336682553327919299563863 152005023829991878949345795)
    ·
      refine ⟨228007535744987818424018693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152005023829991878949345795 228007535744987818424018693)
      ·
        refine ⟨42751412952185215954503505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228007535744987818424018693 42751412952185215954503505)
        ·
          refine ⟨32063559714138911965877629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42751412952185215954503505 32063559714138911965877629)
          ·
            refine ⟨12023834892802091987204111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32063559714138911965877629 12023834892802091987204111)
            ·
              refine ⟨18035752339203137980806167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12023834892802091987204111 18035752339203137980806167)
              ·
                refine ⟨27053628508804706971209251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18035752339203137980806167 27053628508804706971209251)
                ·
                  refine ⟨40580442763207060456813877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27053628508804706971209251 40580442763207060456813877)
                  ·
                    refine ⟨3804416509050661917826301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40580442763207060456813877 3804416509050661917826301)
                    ·
                      refine ⟨1426656190893998219184863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804416509050661917826301 1426656190893998219184863)
                      ·
                        rfl

theorem cell23_2778403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_2778403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778403 prefixEnd_2778403 := by exact prefixLift 2778403
  have htrace : WordTrace (prefixWord ++ tailWord_2778403) baseStart_2778403 baseEnd_2778403 := by
    simpa [prefixWord, tailWord_2778403, baseEnd_2778403] using wordTrace_append hprefix tailTrace_2778403
  have hstable : (prefixWord ++ tailWord_2778403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778403).length < 2 ^ (prefixWord ++ tailWord_2778403).sum := by decide
  have hdescent : baseEnd_2778403 < baseStart_2778403 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778410 : List Nat := [3, 1, 4, 2, 1, 2, 1, 2, 7]
def baseStart_2778410 : Nat := 118140960795 + 2778410 * 2 ^ 59
def prefixEnd_2778410 : Nat := 4983230072969 + 3 ^ 40 * 2778410 * 2
def baseEnd_2778410 : Nat := 158517753917619965755259

theorem tailTrace_2778410 : CollatzResearch.WordTrace tailWord_2778410 prefixEnd_2778410 158517753917619965755259 := by
  unfold tailWord_2778410
  simp only [CollatzResearch.WordTrace]
  refine ⟨25334234466075639873767171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67557958576201706330045789 25334234466075639873767171)
  ·
    refine ⟨38001351699113459810650757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25334234466075639873767171 38001351699113459810650757)
    ·
      refine ⟨7125253443583773714497017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38001351699113459810650757 7125253443583773714497017)
      ·
        refine ⟨5343940082687830285872763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7125253443583773714497017 5343940082687830285872763)
        ·
          refine ⟨8015910124031745428809145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5343940082687830285872763 8015910124031745428809145)
          ·
            refine ⟨6011932593023809071606859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8015910124031745428809145 6011932593023809071606859)
            ·
              refine ⟨9017898889535713607410289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011932593023809071606859 9017898889535713607410289)
              ·
                refine ⟨6763424167151785205557717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9017898889535713607410289 6763424167151785205557717)
                ·
                  refine ⟨158517753917619965755259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6763424167151785205557717 158517753917619965755259)
                  ·
                    rfl

theorem cell23_2778410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 2, 7].length) (baseStart_2778410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778410 prefixEnd_2778410 := by exact prefixLift 2778410
  have htrace : WordTrace (prefixWord ++ tailWord_2778410) baseStart_2778410 baseEnd_2778410 := by
    simpa [prefixWord, tailWord_2778410, baseEnd_2778410] using wordTrace_append hprefix tailTrace_2778410
  have hstable : (prefixWord ++ tailWord_2778410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778410).length < 2 ^ (prefixWord ++ tailWord_2778410).sum := by decide
  have hdescent : baseEnd_2778410 < baseStart_2778410 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778420 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_2778420 : Nat := 118140960795 + 2778420 * 2 ^ 59
def prefixEnd_2778420 : Nat := 4983230072969 + 3 ^ 40 * 2778420 * 2
def baseEnd_2778420 : Nat := 1426664920065124652672285

theorem tailTrace_2778420 : CollatzResearch.WordTrace tailWord_2778420 prefixEnd_2778420 1426664920065124652672285 := by
  unfold tailWord_2778420
  simp only [CollatzResearch.WordTrace]
  refine ⟨50668651297133165601466357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67558201729510887468621809 50668651297133165601466357)
  ·
    refine ⟨4750186059106234275137471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 50668651297133165601466357 4750186059106234275137471)
    ·
      refine ⟨7125279088659351412706207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750186059106234275137471 7125279088659351412706207)
      ·
        refine ⟨10687918632989027119059311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7125279088659351412706207 10687918632989027119059311)
        ·
          refine ⟨16031877949483540678588967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10687918632989027119059311 16031877949483540678588967)
          ·
            refine ⟨24047816924225311017883451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16031877949483540678588967 24047816924225311017883451)
            ·
              refine ⟨36071725386337966526825177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24047816924225311017883451 36071725386337966526825177)
              ·
                refine ⟨27053794039753474895118883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36071725386337966526825177 27053794039753474895118883)
                ·
                  refine ⟨40580691059630212342678325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27053794039753474895118883 40580691059630212342678325)
                  ·
                    refine ⟨3804439786840332407126093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40580691059630212342678325 3804439786840332407126093)
                    ·
                      refine ⟨1426664920065124652672285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804439786840332407126093 1426664920065124652672285)
                      ·
                        rfl

theorem cell23_2778420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_2778420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778420 prefixEnd_2778420 := by exact prefixLift 2778420
  have htrace : WordTrace (prefixWord ++ tailWord_2778420) baseStart_2778420 baseEnd_2778420 := by
    simpa [prefixWord, tailWord_2778420, baseEnd_2778420] using wordTrace_append hprefix tailTrace_2778420
  have hstable : (prefixWord ++ tailWord_2778420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778420).length < 2 ^ (prefixWord ++ tailWord_2778420).sum := by decide
  have hdescent : baseEnd_2778420 < baseStart_2778420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778438 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2]
def baseStart_2778438 : Nat := 118140960795 + 2778438 * 2 ^ 59
def prefixEnd_2778438 : Nat := 4983230072969 + 3 ^ 40 * 2778438 * 2
def baseEnd_2778438 : Nat := 1426674162716905582247203

theorem tailTrace_2778438 : CollatzResearch.WordTrace tailWord_2778438 prefixEnd_2778438 1426674162716905582247203 := by
  unfold tailWord_2778438
  simp only [CollatzResearch.WordTrace]
  refine ⟨3166811222131285008658999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67558639405467413518058645 3166811222131285008658999)
  ·
    refine ⟨4750216833196927512988499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3166811222131285008658999 4750216833196927512988499)
    ·
      refine ⟨7125325249795391269482749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4750216833196927512988499 7125325249795391269482749)
      ·
        refine ⟨2671996968673271726056031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7125325249795391269482749 2671996968673271726056031)
        ·
          refine ⟨4007995453009907589084047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2671996968673271726056031 4007995453009907589084047)
          ·
            refine ⟨6011993179514861383626071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4007995453009907589084047 6011993179514861383626071)
            ·
              refine ⟨9017989769272292075439107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6011993179514861383626071 9017989769272292075439107)
              ·
                refine ⟨13526984653908438113158661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9017989769272292075439107 13526984653908438113158661)
                ·
                  refine ⟨2536309622607832146217249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13526984653908438113158661 2536309622607832146217249)
                  ·
                    refine ⟨1902232216955874109662937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2536309622607832146217249 1902232216955874109662937)
                    ·
                      refine ⟨1426674162716905582247203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902232216955874109662937 1426674162716905582247203)
                      ·
                        rfl

theorem cell23_2778438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2].length) (baseStart_2778438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778438 prefixEnd_2778438 := by exact prefixLift 2778438
  have htrace : WordTrace (prefixWord ++ tailWord_2778438) baseStart_2778438 baseEnd_2778438 := by
    simpa [prefixWord, tailWord_2778438, baseEnd_2778438] using wordTrace_append hprefix tailTrace_2778438
  have hstable : (prefixWord ++ tailWord_2778438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778438).length < 2 ^ (prefixWord ++ tailWord_2778438).sum := by decide
  have hdescent : baseEnd_2778438 < baseStart_2778438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778480 : List Nat := [2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3]
def baseStart_2778480 : Nat := 118140960795 + 2778480 * 2 ^ 59
def prefixEnd_2778480 : Nat := 4983230072969 + 3 ^ 40 * 2778480 * 2
def baseEnd_2778480 : Nat := 1426695728904394417922009

theorem tailTrace_2778480 : CollatzResearch.WordTrace tailWord_2778480 prefixEnd_2778480 1426695728904394417922009 := by
  unfold tailWord_2778480
  simp only [CollatzResearch.WordTrace]
  refine ⟨50669745487024480725058447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67559660649365974300077929 50669745487024480725058447)
  ·
    refine ⟨76004618230536721087587671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50669745487024480725058447 76004618230536721087587671)
    ·
      refine ⟨114006927345805081631381507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76004618230536721087587671 114006927345805081631381507)
      ·
        refine ⟨171010391018707622447072261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114006927345805081631381507 171010391018707622447072261)
        ·
          refine ⟨32064448316007679208826049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171010391018707622447072261 32064448316007679208826049)
          ·
            refine ⟨24048336237005759406619537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32064448316007679208826049 24048336237005759406619537)
            ·
              refine ⟨18036252177754319554964653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24048336237005759406619537 18036252177754319554964653)
              ·
                refine ⟨6763594566657869833111745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18036252177754319554964653 6763594566657869833111745)
                ·
                  refine ⟨5072695924993402374833809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6763594566657869833111745 5072695924993402374833809)
                  ·
                    refine ⟨3804521943745051781125357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5072695924993402374833809 3804521943745051781125357)
                    ·
                      refine ⟨1426695728904394417922009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804521943745051781125357 1426695728904394417922009)
                      ·
                        rfl

theorem cell23_2778480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 3].length) (baseStart_2778480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778480 prefixEnd_2778480 := by exact prefixLift 2778480
  have htrace : WordTrace (prefixWord ++ tailWord_2778480) baseStart_2778480 baseEnd_2778480 := by
    simpa [prefixWord, tailWord_2778480, baseEnd_2778480] using wordTrace_append hprefix tailTrace_2778480
  have hstable : (prefixWord ++ tailWord_2778480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778480).length < 2 ^ (prefixWord ++ tailWord_2778480).sum := by decide
  have hdescent : baseEnd_2778480 < baseStart_2778480 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778513 : List Nat := [1, 2, 2, 1, 1, 1, 2, 3, 5, 5]
def baseStart_2778513 : Nat := 118140960795 + 2778513 * 2 ^ 59
def prefixEnd_2778513 : Nat := 4983230072969 + 3 ^ 40 * 2778513 * 2
def baseEnd_2778513 : Nat := 475570891255330929603119

theorem tailTrace_2778513 : CollatzResearch.WordTrace tailWord_2778513 prefixEnd_2778513 475570891255330929603119 := by
  unfold tailWord_2778513
  simp only [CollatzResearch.WordTrace]
  refine ⟨101340694582929408086068193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67560463055286272057378795 101340694582929408086068193)
  ·
    refine ⟨76005520937197056064551145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101340694582929408086068193 76005520937197056064551145)
    ·
      refine ⟨57004140702897792048413359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76005520937197056064551145 57004140702897792048413359)
      ·
        refine ⟨85506211054346688072620039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57004140702897792048413359 85506211054346688072620039)
        ·
          refine ⟨128259316581520032108930059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85506211054346688072620039 128259316581520032108930059)
          ·
            refine ⟨192388974872280048163395089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128259316581520032108930059 192388974872280048163395089)
            ·
              refine ⟨144291731154210036122546317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 192388974872280048163395089 144291731154210036122546317)
              ·
                refine ⟨54109399182828763545954869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 144291731154210036122546317 54109399182828763545954869)
                ·
                  refine ⟨5072756173390196582433269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54109399182828763545954869 5072756173390196582433269)
                  ·
                    refine ⟨475570891255330929603119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5072756173390196582433269 475570891255330929603119)
                    ·
                      rfl

theorem cell23_2778513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 5].length) (baseStart_2778513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778513 prefixEnd_2778513 := by exact prefixLift 2778513
  have htrace : WordTrace (prefixWord ++ tailWord_2778513) baseStart_2778513 baseEnd_2778513 := by
    simpa [prefixWord, tailWord_2778513, baseEnd_2778513] using wordTrace_append hprefix tailTrace_2778513
  have hstable : (prefixWord ++ tailWord_2778513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778513).length < 2 ^ (prefixWord ++ tailWord_2778513).sum := by decide
  have hdescent : baseEnd_2778513 < baseStart_2778513 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778560 : List Nat := [2, 1, 1, 2, 3, 1, 2, 3, 4, 4]
def baseStart_2778560 : Nat := 118140960795 + 2778560 * 2 ^ 59
def prefixEnd_2778560 : Nat := 4983230072969 + 3 ^ 40 * 2778560 * 2
def baseEnd_2778560 : Nat := 475578935785584701640547

theorem tailTrace_2778560 : CollatzResearch.WordTrace tailWord_2778560 prefixEnd_2778560 475578935785584701640547 := by
  unfold tailWord_2778560
  simp only [CollatzResearch.WordTrace]
  refine ⟨50671204406879567556514567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67561605875839423408686089 50671204406879567556514567)
  ·
    refine ⟨76006806610319351334771851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50671204406879567556514567 76006806610319351334771851)
    ·
      refine ⟨114010209915479027002157777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76006806610319351334771851 114010209915479027002157777)
      ·
        refine ⟨85507657436609270251618333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114010209915479027002157777 85507657436609270251618333)
        ·
          refine ⟨32065371538728476344356875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85507657436609270251618333 32065371538728476344356875)
          ·
            refine ⟨48098057308092714516535313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32065371538728476344356875 48098057308092714516535313)
            ·
              refine ⟨36073542981069535887401485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48098057308092714516535313 36073542981069535887401485)
              ·
                refine ⟨13527578617901075957775557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36073542981069535887401485 13527578617901075957775557)
                ·
                  refine ⟨2536420990856451742082917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13527578617901075957775557 2536420990856451742082917)
                  ·
                    refine ⟨475578935785584701640547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2536420990856451742082917 475578935785584701640547)
                    ·
                      rfl

theorem cell23_2778560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 2, 3, 4, 4].length) (baseStart_2778560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778560 prefixEnd_2778560 := by exact prefixLift 2778560
  have htrace : WordTrace (prefixWord ++ tailWord_2778560) baseStart_2778560 baseEnd_2778560 := by
    simpa [prefixWord, tailWord_2778560, baseEnd_2778560] using wordTrace_append hprefix tailTrace_2778560
  have hstable : (prefixWord ++ tailWord_2778560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778560).length < 2 ^ (prefixWord ++ tailWord_2778560).sum := by decide
  have hdescent : baseEnd_2778560 < baseStart_2778560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778563 : List Nat := [1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6]
def baseStart_2778563 : Nat := 118140960795 + 2778563 * 2 ^ 59
def prefixEnd_2778563 : Nat := 4983230072969 + 3 ^ 40 * 2778563 * 2
def baseEnd_2778563 : Nat := 1426738347798717593184127

theorem tailTrace_2778563 : CollatzResearch.WordTrace tailWord_2778563 prefixEnd_2778563 1426738347798717593184127 := by
  unfold tailWord_2778563
  simp only [CollatzResearch.WordTrace]
  refine ⟨101342518232748266625388343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67561678821832177750258895 101342518232748266625388343)
  ·
    refine ⟨152013777349122399938082515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101342518232748266625388343 152013777349122399938082515)
    ·
      refine ⟨228020666023683599907123773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152013777349122399938082515 228020666023683599907123773)
      ·
        refine ⟨85507749758881349965171415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228020666023683599907123773 85507749758881349965171415)
        ·
          refine ⟨128261624638322024947757123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85507749758881349965171415 128261624638322024947757123)
          ·
            refine ⟨192392436957483037421635685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128261624638322024947757123 192392436957483037421635685)
            ·
              refine ⟨36073581929528069516556691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192392436957483037421635685 36073581929528069516556691)
              ·
                refine ⟨54110372894292104274835037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36073581929528069516556691 54110372894292104274835037)
                ·
                  refine ⟨20291389835359539103063139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 54110372894292104274835037 20291389835359539103063139)
                  ·
                    refine ⟨30437084753039308654594709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20291389835359539103063139 30437084753039308654594709)
                    ·
                      refine ⟨1426738347798717593184127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30437084753039308654594709 1426738347798717593184127)
                      ·
                        rfl

theorem cell23_2778563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_2778563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778563 prefixEnd_2778563 := by exact prefixLift 2778563
  have htrace : WordTrace (prefixWord ++ tailWord_2778563) baseStart_2778563 baseEnd_2778563 := by
    simpa [prefixWord, tailWord_2778563, baseEnd_2778563] using wordTrace_append hprefix tailTrace_2778563
  have hstable : (prefixWord ++ tailWord_2778563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778563).length < 2 ^ (prefixWord ++ tailWord_2778563).sum := by decide
  have hdescent : baseEnd_2778563 < baseStart_2778563 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778583 : List Nat := [1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 7]
def baseStart_2778583 : Nat := 118140960795 + 2778583 * 2 ^ 59
def prefixEnd_2778583 : Nat := 4983230072969 + 3 ^ 40 * 2778583 * 2
def baseEnd_2778583 : Nat := 1426748617411807514934035

theorem tailTrace_2778583 : CollatzResearch.WordTrace tailWord_2778583 prefixEnd_2778583 1426748617411807514934035 := by
  unfold tailWord_2778583
  simp only [CollatzResearch.WordTrace]
  refine ⟨101343247692675810041116403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67562165128450540027410935 101343247692675810041116403)
  ·
    refine ⟨152014871539013715061674605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101343247692675810041116403 152014871539013715061674605)
    ·
      refine ⟨57005576827130143148127977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152014871539013715061674605 57005576827130143148127977)
      ·
        refine ⟨42754182620347607361095983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57005576827130143148127977 42754182620347607361095983)
        ·
          refine ⟨64131273930521411041643975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42754182620347607361095983 64131273930521411041643975)
          ·
            refine ⟨96196910895782116562465963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64131273930521411041643975 96196910895782116562465963)
            ·
              refine ⟨144295366343673174843698945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 96196910895782116562465963 144295366343673174843698945)
              ·
                refine ⟨108221524757754881132774209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 144295366343673174843698945 108221524757754881132774209)
                ·
                  refine ⟨81166143568316160849580657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108221524757754881132774209 81166143568316160849580657)
                  ·
                    refine ⟨60874607676237120637185493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 81166143568316160849580657 60874607676237120637185493)
                    ·
                      refine ⟨1426748617411807514934035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60874607676237120637185493 1426748617411807514934035)
                      ·
                        rfl

theorem cell23_2778583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_2778583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778583 prefixEnd_2778583 := by exact prefixLift 2778583
  have htrace : WordTrace (prefixWord ++ tailWord_2778583) baseStart_2778583 baseEnd_2778583 := by
    simpa [prefixWord, tailWord_2778583, baseEnd_2778583] using wordTrace_append hprefix tailTrace_2778583
  have hstable : (prefixWord ++ tailWord_2778583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778583).length < 2 ^ (prefixWord ++ tailWord_2778583).sum := by decide
  have hdescent : baseEnd_2778583 < baseStart_2778583 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778597 : List Nat := [1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2778597 : Nat := 118140960795 + 2778597 * 2 ^ 59
def prefixEnd_2778597 : Nat := 4983230072969 + 3 ^ 40 * 2778597 * 2
def baseEnd_2778597 : Nat := 1426755806140970460158971

theorem tailTrace_2778597 : CollatzResearch.WordTrace tailWord_2778597 prefixEnd_2778597 1426755806140970460158971 := by
  unfold tailWord_2778597
  simp only [CollatzResearch.WordTrace]
  refine ⟨101343758314625090432126045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67562505543083393621417363 101343758314625090432126045)
  ·
    refine ⟨38003909367984408912047267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101343758314625090432126045 38003909367984408912047267)
    ·
      refine ⟨57005864051976613368070901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38003909367984408912047267 57005864051976613368070901)
      ·
        refine ⟨5344299754872807503256647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 57005864051976613368070901 5344299754872807503256647)
        ·
          refine ⟨8016449632309211254884971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344299754872807503256647 8016449632309211254884971)
          ·
            refine ⟨12024674448463816882327457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8016449632309211254884971 12024674448463816882327457)
            ·
              refine ⟨9018505836347862661745593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12024674448463816882327457 9018505836347862661745593)
              ·
                refine ⟨6763879377260896996309195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9018505836347862661745593 6763879377260896996309195)
                ·
                  refine ⟨10145819065891345494463793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763879377260896996309195 10145819065891345494463793)
                  ·
                    refine ⟨7609364299418509120847845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10145819065891345494463793 7609364299418509120847845)
                    ·
                      refine ⟨1426755806140970460158971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7609364299418509120847845 1426755806140970460158971)
                      ·
                        rfl

theorem cell23_2778597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2778597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778597 prefixEnd_2778597 := by exact prefixLift 2778597
  have htrace : WordTrace (prefixWord ++ tailWord_2778597) baseStart_2778597 baseEnd_2778597 := by
    simpa [prefixWord, tailWord_2778597, baseEnd_2778597] using wordTrace_append hprefix tailTrace_2778597
  have hstable : (prefixWord ++ tailWord_2778597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778597).length < 2 ^ (prefixWord ++ tailWord_2778597).sum := by decide
  have hdescent : baseEnd_2778597 < baseStart_2778597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778603 : List Nat := [1, 1, 1, 1, 2, 3, 2, 2, 1, 9]
def baseStart_2778603 : Nat := 118140960795 + 2778603 * 2 ^ 59
def prefixEnd_2778603 : Nat := 4983230072969 + 3 ^ 40 * 2778603 * 2
def baseEnd_2778603 : Nat := 475586295674965812227981

theorem tailTrace_2778603 : CollatzResearch.WordTrace tailWord_2778603 prefixEnd_2778603 475586295674965812227981 := by
  unfold tailWord_2778603
  simp only [CollatzResearch.WordTrace]
  refine ⟨101343977152603353456844463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67562651435068902304562975 101343977152603353456844463)
  ·
    refine ⟨152015965728905030185266695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101343977152603353456844463 152015965728905030185266695)
    ·
      refine ⟨228023948593357545277900043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152015965728905030185266695 228023948593357545277900043)
      ·
        refine ⟨342035922890036317916850065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228023948593357545277900043 342035922890036317916850065)
        ·
          refine ⟨256526942167527238437637549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 342035922890036317916850065 256526942167527238437637549)
          ·
            refine ⟨96197603312822714414114081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 256526942167527238437637549 96197603312822714414114081)
            ·
              refine ⟨72148202484617035810585561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96197603312822714414114081 72148202484617035810585561)
              ·
                refine ⟨54111151863462776857939171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72148202484617035810585561 54111151863462776857939171)
                ·
                  refine ⟨81166727795194165286908757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54111151863462776857939171 81166727795194165286908757)
                  ·
                    refine ⟨475586295674965812227981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 81166727795194165286908757 475586295674965812227981)
                    ·
                      rfl

theorem cell23_2778603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 9].length) (baseStart_2778603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778603 prefixEnd_2778603 := by exact prefixLift 2778603
  have htrace : WordTrace (prefixWord ++ tailWord_2778603) baseStart_2778603 baseEnd_2778603 := by
    simpa [prefixWord, tailWord_2778603, baseEnd_2778603] using wordTrace_append hprefix tailTrace_2778603
  have hstable : (prefixWord ++ tailWord_2778603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778603).length < 2 ^ (prefixWord ++ tailWord_2778603).sum := by decide
  have hdescent : baseEnd_2778603 < baseStart_2778603 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778627 : List Nat := [1, 1, 1, 3, 2, 1, 2, 4, 3, 3, 2]
def baseStart_2778627 : Nat := 118140960795 + 2778627 * 2 ^ 59
def prefixEnd_2778627 : Nat := 4983230072969 + 3 ^ 40 * 2778627 * 2
def baseEnd_2778627 : Nat := 1426771210560605342783833

theorem tailTrace_2778627 : CollatzResearch.WordTrace tailWord_2778627 prefixEnd_2778627 1426771210560605342783833 := by
  unfold tailWord_2778627
  simp only [CollatzResearch.WordTrace]
  refine ⟨101344852504516405555718135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67563235003010937037145423 101344852504516405555718135)
  ·
    refine ⟨152017278756774608333577203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101344852504516405555718135 152017278756774608333577203)
    ·
      refine ⟨228025918135161912500365805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152017278756774608333577203 228025918135161912500365805)
      ·
        refine ⟨85509719300685717187637177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 228025918135161912500365805 85509719300685717187637177)
        ·
          refine ⟨64132289475514287890727883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85509719300685717187637177 64132289475514287890727883)
          ·
            refine ⟨96198434213271431836091825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64132289475514287890727883 96198434213271431836091825)
            ·
              refine ⟨72148825659953573877068869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96198434213271431836091825 72148825659953573877068869)
              ·
                refine ⟨13527904811241295101950413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 72148825659953573877068869 13527904811241295101950413)
                ·
                  refine ⟨5072964304215485663231405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13527904811241295101950413 5072964304215485663231405)
                  ·
                    refine ⟨1902361614080807123711777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5072964304215485663231405 1902361614080807123711777)
                    ·
                      refine ⟨1426771210560605342783833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902361614080807123711777 1426771210560605342783833)
                      ·
                        rfl

theorem cell23_2778627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 2, 4, 3, 3, 2].length) (baseStart_2778627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778627 prefixEnd_2778627 := by exact prefixLift 2778627
  have htrace : WordTrace (prefixWord ++ tailWord_2778627) baseStart_2778627 baseEnd_2778627 := by
    simpa [prefixWord, tailWord_2778627, baseEnd_2778627] using wordTrace_append hprefix tailTrace_2778627
  have hstable : (prefixWord ++ tailWord_2778627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778627).length < 2 ^ (prefixWord ++ tailWord_2778627).sum := by decide
  have hdescent : baseEnd_2778627 < baseStart_2778627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778634 : List Nat := [3, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_2778634 : Nat := 118140960795 + 2778634 * 2 ^ 59
def prefixEnd_2778634 : Nat := 4983230072969 + 3 ^ 40 * 2778634 * 2
def baseEnd_2778634 : Nat := 1426774804925186815396301

theorem tailTrace_2778634 : CollatzResearch.WordTrace tailWord_2778634 prefixEnd_2778634 1426774804925186815396301 := by
  unfold tailWord_2778634
  simp only [CollatzResearch.WordTrace]
  refine ⟨25336276953872761437805739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67563405210327363834148637 25336276953872761437805739)
  ·
    refine ⟨38004415430809142156708609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25336276953872761437805739 38004415430809142156708609)
    ·
      refine ⟨28503311573106856617531457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38004415430809142156708609 28503311573106856617531457)
      ·
        refine ⟨21377483679830142463148593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28503311573106856617531457 21377483679830142463148593)
        ·
          refine ⟨16033112759872606847361445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21377483679830142463148593 16033112759872606847361445)
          ·
            refine ⟨3006208642476113783880271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16033112759872606847361445 3006208642476113783880271)
            ·
              refine ⟨4509312963714170675820407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006208642476113783880271 4509312963714170675820407)
              ·
                refine ⟨6763969445571256013730611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509312963714170675820407 6763969445571256013730611)
                ·
                  refine ⟨10145954168356884020595917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6763969445571256013730611 10145954168356884020595917)
                  ·
                    refine ⟨3804732813133831507723469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10145954168356884020595917 3804732813133831507723469)
                    ·
                      refine ⟨1426774804925186815396301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804732813133831507723469 1426774804925186815396301)
                      ·
                        rfl

theorem cell23_2778634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_2778634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778634 prefixEnd_2778634 := by exact prefixLift 2778634
  have htrace : WordTrace (prefixWord ++ tailWord_2778634) baseStart_2778634 baseEnd_2778634 := by
    simpa [prefixWord, tailWord_2778634, baseEnd_2778634] using wordTrace_append hprefix tailTrace_2778634
  have hstable : (prefixWord ++ tailWord_2778634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778634).length < 2 ^ (prefixWord ++ tailWord_2778634).sum := by decide
  have hdescent : baseEnd_2778634 < baseStart_2778634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778685 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 2, 1, 3]
def baseStart_2778685 : Nat := 118140960795 + 2778685 * 2 ^ 59
def prefixEnd_2778685 : Nat := 4983230072969 + 3 ^ 40 * 2778685 * 2
def baseEnd_2778685 : Nat := 1426800992438566115858567

theorem tailTrace_2778685 : CollatzResearch.WordTrace tailWord_2778685 prefixEnd_2778685 1426800992438566115858567 := by
  unfold tailWord_2778685
  simp only [CollatzResearch.WordTrace]
  refine ⟨101346967938306281461329509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67564645292204187640886339 101346967938306281461329509)
  ·
    refine ⟨19002556488432427773999283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101346967938306281461329509 19002556488432427773999283)
    ·
      refine ⟨28503834732648641660998925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19002556488432427773999283 28503834732648641660998925)
      ·
        refine ⟨10688938024743240622874597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28503834732648641660998925 10688938024743240622874597)
        ·
          refine ⟨2004175879639357616788987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10688938024743240622874597 2004175879639357616788987)
          ·
            refine ⟨3006263819459036425183481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004175879639357616788987 3006263819459036425183481)
            ·
              refine ⟨2254697864594277318887611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3006263819459036425183481 2254697864594277318887611)
              ·
                refine ⟨3382046796891415978331417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254697864594277318887611 3382046796891415978331417)
                ·
                  refine ⟨2536535097668561983748563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382046796891415978331417 2536535097668561983748563)
                  ·
                    refine ⟨3804802646502842975622845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536535097668561983748563 3804802646502842975622845)
                    ·
                      refine ⟨1426800992438566115858567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3804802646502842975622845 1426800992438566115858567)
                      ·
                        rfl

theorem cell23_2778685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 2, 1, 3].length) (baseStart_2778685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778685 prefixEnd_2778685 := by exact prefixLift 2778685
  have htrace : WordTrace (prefixWord ++ tailWord_2778685) baseStart_2778685 baseEnd_2778685 := by
    simpa [prefixWord, tailWord_2778685, baseEnd_2778685] using wordTrace_append hprefix tailTrace_2778685
  have hstable : (prefixWord ++ tailWord_2778685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778685).length < 2 ^ (prefixWord ++ tailWord_2778685).sum := by decide
  have hdescent : baseEnd_2778685 < baseStart_2778685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778727 : List Nat := [1, 1, 5, 1, 1, 1, 4, 2, 2, 5]
def baseStart_2778727 : Nat := 118140960795 + 2778727 * 2 ^ 59
def prefixEnd_2778727 : Nat := 4983230072969 + 3 ^ 40 * 2778727 * 2
def baseEnd_2778727 : Nat := 475607519542018317177791

theorem tailTrace_2778727 : CollatzResearch.WordTrace tailWord_2778727 prefixEnd_2778727 475607519542018317177791 := by
  unfold tailWord_2778727
  simp only [CollatzResearch.WordTrace]
  refine ⟨101348499804154122634358435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67565666536102748422905623 101348499804154122634358435)
  ·
    refine ⟨152022749706231183951537653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101348499804154122634358435 152022749706231183951537653)
    ·
      refine ⟨14252132784959173495456655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152022749706231183951537653 14252132784959173495456655)
      ·
        refine ⟨21378199177438760243184983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14252132784959173495456655 21378199177438760243184983)
        ·
          refine ⟨32067298766158140364777475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21378199177438760243184983 32067298766158140364777475)
          ·
            refine ⟨48100948149237210547166213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32067298766158140364777475 48100948149237210547166213)
            ·
              refine ⟨9018927777981976977593665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48100948149237210547166213 9018927777981976977593665)
              ·
                refine ⟨6764195833486482733195249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9018927777981976977593665 6764195833486482733195249)
                ·
                  refine ⟨5073146875114862049896437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6764195833486482733195249 5073146875114862049896437)
                  ·
                    refine ⟨475607519542018317177791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5073146875114862049896437 475607519542018317177791)
                    ·
                      rfl

theorem cell23_2778727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_2778727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778727 prefixEnd_2778727 := by exact prefixLift 2778727
  have htrace : WordTrace (prefixWord ++ tailWord_2778727) baseStart_2778727 baseEnd_2778727 := by
    simpa [prefixWord, tailWord_2778727, baseEnd_2778727] using wordTrace_append hprefix tailTrace_2778727
  have hstable : (prefixWord ++ tailWord_2778727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778727).length < 2 ^ (prefixWord ++ tailWord_2778727).sum := by decide
  have hdescent : baseEnd_2778727 < baseStart_2778727 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778824 : List Nat := [2, 1, 3, 1, 2, 2, 1, 3, 1, 5, 2]
def baseStart_2778824 : Nat := 118140960795 + 2778824 * 2 ^ 59
def prefixEnd_2778824 : Nat := 4983230072969 + 3 ^ 40 * 2778824 * 2
def baseEnd_2778824 : Nat := 1426872366249541072020427

theorem tailTrace_2778824 : CollatzResearch.WordTrace tailWord_2778824 prefixEnd_2778824 1426872366249541072020427 := by
  unfold tailWord_2778824
  simp only [CollatzResearch.WordTrace]
  refine ⟨50676018842401354100319763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67568025123201805467093017 50676018842401354100319763)
  ·
    refine ⟨76014028263602031150479645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50676018842401354100319763 76014028263602031150479645)
    ·
      refine ⟨28505260598850761681429867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76014028263602031150479645 28505260598850761681429867)
      ·
        refine ⟨42757890898276142522144801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28505260598850761681429867 42757890898276142522144801)
        ·
          refine ⟨32068418173707106891608601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42757890898276142522144801 32068418173707106891608601)
          ·
            refine ⟨24051313630280330168706451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32068418173707106891608601 24051313630280330168706451)
            ·
              refine ⟨36076970445420495253059677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24051313630280330168706451 36076970445420495253059677)
              ·
                refine ⟨13528863917032685719897379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36076970445420495253059677 13528863917032685719897379)
                ·
                  refine ⟨20293295875549028579846069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13528863917032685719897379 20293295875549028579846069)
                  ·
                    refine ⟨1902496488332721429360569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 20293295875549028579846069 1902496488332721429360569)
                    ·
                      refine ⟨1426872366249541072020427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902496488332721429360569 1426872366249541072020427)
                      ·
                        rfl

theorem cell23_2778824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 3, 1, 5, 2].length) (baseStart_2778824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778824 prefixEnd_2778824 := by exact prefixLift 2778824
  have htrace : WordTrace (prefixWord ++ tailWord_2778824) baseStart_2778824 baseEnd_2778824 := by
    simpa [prefixWord, tailWord_2778824, baseEnd_2778824] using wordTrace_append hprefix tailTrace_2778824
  have hstable : (prefixWord ++ tailWord_2778824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778824).length < 2 ^ (prefixWord ++ tailWord_2778824).sum := by decide
  have hdescent : baseEnd_2778824 < baseStart_2778824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778841 : List Nat := [1, 2, 1, 2, 3, 4, 1, 2, 2, 3, 2]
def baseStart_2778841 : Nat := 118140960795 + 2778841 * 2 ^ 59
def prefixEnd_2778841 : Nat := 4983230072969 + 3 ^ 40 * 2778841 * 2
def baseEnd_2778841 : Nat := 1426881095420667505507849

theorem tailTrace_2778841 : CollatzResearch.WordTrace tailWord_2778841 prefixEnd_2778841 1426881095420667505507849 := by
  unfold tailWord_2778841
  simp only [CollatzResearch.WordTrace]
  refine ⟨101352657725741120104008377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67568438483827413402672251 101352657725741120104008377)
  ·
    refine ⟨76014493294305840078006283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101352657725741120104008377 76014493294305840078006283)
    ·
      refine ⟨114021739941458760117009425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76014493294305840078006283 114021739941458760117009425)
      ·
        refine ⟨85516304956094070087757069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114021739941458760117009425 85516304956094070087757069)
        ·
          refine ⟨32068614358535276282908901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85516304956094070087757069 32068614358535276282908901)
          ·
            refine ⟨6012865192225364303045419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32068614358535276282908901 6012865192225364303045419)
            ·
              refine ⟨9019297788338046454568129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012865192225364303045419 9019297788338046454568129)
              ·
                refine ⟨6764473341253534840926097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9019297788338046454568129 6764473341253534840926097)
                ·
                  refine ⟨5073355005940151130694573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6764473341253534840926097 5073355005940151130694573)
                  ·
                    refine ⟨1902508127227556674010465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5073355005940151130694573 1902508127227556674010465)
                    ·
                      refine ⟨1426881095420667505507849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902508127227556674010465 1426881095420667505507849)
                      ·
                        rfl

theorem cell23_2778841_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 2, 3, 2].length) (baseStart_2778841 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778841 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778841 prefixEnd_2778841 := by exact prefixLift 2778841
  have htrace : WordTrace (prefixWord ++ tailWord_2778841) baseStart_2778841 baseEnd_2778841 := by
    simpa [prefixWord, tailWord_2778841, baseEnd_2778841] using wordTrace_append hprefix tailTrace_2778841
  have hstable : (prefixWord ++ tailWord_2778841).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778841).length < 2 ^ (prefixWord ++ tailWord_2778841).sum := by decide
  have hdescent : baseEnd_2778841 < baseStart_2778841 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778841) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778855 : List Nat := [1, 1, 5, 4, 2, 1, 2, 1, 6]
def baseStart_2778855 : Nat := 118140960795 + 2778855 * 2 ^ 59
def prefixEnd_2778855 : Nat := 4983230072969 + 3 ^ 40 * 2778855 * 2
def baseEnd_2778855 : Nat := 158543142683314494525865

theorem tailTrace_2778855 : CollatzResearch.WordTrace tailWord_2778855 prefixEnd_2778855 158543142683314494525865 := by
  unfold tailWord_2778855
  simp only [CollatzResearch.WordTrace]
  refine ⟨101353168347690400495018019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67568778898460266996678679 101353168347690400495018019)
  ·
    refine ⟨152029752521535600742527029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101353168347690400495018019 152029752521535600742527029)
    ·
      refine ⟨14252789298893962569611909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 152029752521535600742527029 14252789298893962569611909)
      ·
        refine ⟨2672397993542617981802233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14252789298893962569611909 2672397993542617981802233)
        ·
          refine ⟨2004298495156963486351675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2672397993542617981802233 2004298495156963486351675)
          ·
            refine ⟨3006447742735445229527513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004298495156963486351675 3006447742735445229527513)
            ·
              refine ⟨2254835807051583922145635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3006447742735445229527513 2254835807051583922145635)
              ·
                refine ⟨3382253710577375883218453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254835807051583922145635 3382253710577375883218453)
                ·
                  refine ⟨158543142683314494525865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3382253710577375883218453 158543142683314494525865)
                  ·
                    rfl

theorem cell23_2778855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 1, 6].length) (baseStart_2778855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778855 prefixEnd_2778855 := by exact prefixLift 2778855
  have htrace : WordTrace (prefixWord ++ tailWord_2778855) baseStart_2778855 baseEnd_2778855 := by
    simpa [prefixWord, tailWord_2778855, baseEnd_2778855] using wordTrace_append hprefix tailTrace_2778855
  have hstable : (prefixWord ++ tailWord_2778855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778855).length < 2 ^ (prefixWord ++ tailWord_2778855).sum := by decide
  have hdescent : baseEnd_2778855 < baseStart_2778855 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778857 : List Nat := [1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 3]
def baseStart_2778857 : Nat := 118140960795 + 2778857 * 2 ^ 59
def prefixEnd_2778857 : Nat := 4983230072969 + 3 ^ 40 * 2778857 * 2
def baseEnd_2778857 : Nat := 1426889311111139442907775

theorem tailTrace_2778857 : CollatzResearch.WordTrace tailWord_2778857 prefixEnd_2778857 1426889311111139442907775 := by
  unfold tailWord_2778857
  simp only [CollatzResearch.WordTrace]
  refine ⟨101353241293683154836590825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67568827529122103224393883 101353241293683154836590825)
  ·
    refine ⟨76014930970262366127443119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101353241293683154836590825 76014930970262366127443119)
    ·
      refine ⟨114022396455393549191164679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76014930970262366127443119 114022396455393549191164679)
      ·
        refine ⟨171033594683090323786747019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114022396455393549191164679 171033594683090323786747019)
        ·
          refine ⟨256550392024635485680120529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171033594683090323786747019 256550392024635485680120529)
          ·
            refine ⟨192412794018476614260090397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 256550392024635485680120529 192412794018476614260090397)
            ·
              refine ⟨72154797756928730347533899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 192412794018476614260090397 72154797756928730347533899)
              ·
                refine ⟨108232196635393095521300849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72154797756928730347533899 108232196635393095521300849)
                ·
                  refine ⟨81174147476544821640975637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 108232196635393095521300849 81174147476544821640975637)
                  ·
                    refine ⟨3805038162963038514420733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 81174147476544821640975637 3805038162963038514420733)
                    ·
                      refine ⟨1426889311111139442907775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3805038162963038514420733 1426889311111139442907775)
                      ·
                        rfl

theorem cell23_2778857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 1, 2, 6, 3].length) (baseStart_2778857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778857 prefixEnd_2778857 := by exact prefixLift 2778857
  have htrace : WordTrace (prefixWord ++ tailWord_2778857) baseStart_2778857 baseEnd_2778857 := by
    simpa [prefixWord, tailWord_2778857, baseEnd_2778857] using wordTrace_append hprefix tailTrace_2778857
  have hstable : (prefixWord ++ tailWord_2778857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778857).length < 2 ^ (prefixWord ++ tailWord_2778857).sum := by decide
  have hdescent : baseEnd_2778857 < baseStart_2778857 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778867 : List Nat := [1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6]
def baseStart_2778867 : Nat := 118140960795 + 2778867 * 2 ^ 59
def prefixEnd_2778867 : Nat := 4983230072969 + 3 ^ 40 * 2778867 * 2
def baseEnd_2778867 : Nat := 1426894445917684403782729

theorem tailTrace_2778867 : CollatzResearch.WordTrace tailWord_2778867 prefixEnd_2778867 1426894445917684403782729 := by
  unfold tailWord_2778867
  simp only [CollatzResearch.WordTrace]
  refine ⟨101353606023646926544454855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67569070682431284362969903 101353606023646926544454855)
  ·
    refine ⟨152030409035470389816682283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101353606023646926544454855 152030409035470389816682283)
    ·
      refine ⟨228045613553205584725023425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152030409035470389816682283 228045613553205584725023425)
      ·
        refine ⟨171034210164904188543767569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 228045613553205584725023425 171034210164904188543767569)
        ·
          refine ⟨128275657623678141407825677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171034210164904188543767569 128275657623678141407825677)
          ·
            refine ⟨48103371608879303027934629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128275657623678141407825677 48103371608879303027934629)
            ·
              refine ⟨9019382176664869317737743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 48103371608879303027934629 9019382176664869317737743)
              ·
                refine ⟨13529073264997303976606615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9019382176664869317737743 13529073264997303976606615)
                ·
                  refine ⟨20293609897495955964909923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13529073264997303976606615 20293609897495955964909923)
                  ·
                    refine ⟨30440414846243933947364885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20293609897495955964909923 30440414846243933947364885)
                    ·
                      refine ⟨1426894445917684403782729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30440414846243933947364885 1426894445917684403782729)
                      ·
                        rfl

theorem cell23_2778867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_2778867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778867 prefixEnd_2778867 := by exact prefixLift 2778867
  have htrace : WordTrace (prefixWord ++ tailWord_2778867) baseStart_2778867 baseEnd_2778867 := by
    simpa [prefixWord, tailWord_2778867, baseEnd_2778867] using wordTrace_append hprefix tailTrace_2778867
  have hstable : (prefixWord ++ tailWord_2778867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778867).length < 2 ^ (prefixWord ++ tailWord_2778867).sum := by decide
  have hdescent : baseEnd_2778867 < baseStart_2778867 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778868 : List Nat := [2, 6, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2778868 : Nat := 118140960795 + 2778868 * 2 ^ 59
def prefixEnd_2778868 : Nat := 4983230072969 + 3 ^ 40 * 2778868 * 2
def baseEnd_2778868 : Nat := 475631653132779633290075

theorem tailTrace_2778868 : CollatzResearch.WordTrace tailWord_2778868 prefixEnd_2778868 475631653132779633290075 := by
  unfold tailWord_2778868
  simp only [CollatzResearch.WordTrace]
  refine ⟨50676821248321651857620629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67569094997762202476827505 50676821248321651857620629)
  ·
    refine ⟨2375475996015077430825967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 50676821248321651857620629 2375475996015077430825967)
    ·
      refine ⟨3563213994022616146238951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2375475996015077430825967 3563213994022616146238951)
      ·
        refine ⟨5344820991033924219358427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563213994022616146238951 5344820991033924219358427)
        ·
          refine ⟨8017231486550886329037641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344820991033924219358427 8017231486550886329037641)
          ·
            refine ⟨6012923614913164746778231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8017231486550886329037641 6012923614913164746778231)
            ·
              refine ⟨9019385422369747120167347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6012923614913164746778231 9019385422369747120167347)
              ·
                refine ⟨13529078133554620680251021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9019385422369747120167347 13529078133554620680251021)
                ·
                  refine ⟨5073404300082982755094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13529078133554620680251021 5073404300082982755094133)
                  ·
                    refine ⟨475631653132779633290075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5073404300082982755094133 475631653132779633290075)
                    ·
                      rfl

theorem cell23_2778868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2778868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778868 prefixEnd_2778868 := by exact prefixLift 2778868
  have htrace : WordTrace (prefixWord ++ tailWord_2778868) baseStart_2778868 baseEnd_2778868 := by
    simpa [prefixWord, tailWord_2778868, baseEnd_2778868] using wordTrace_append hprefix tailTrace_2778868
  have hstable : (prefixWord ++ tailWord_2778868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778868).length < 2 ^ (prefixWord ++ tailWord_2778868).sum := by decide
  have hdescent : baseEnd_2778868 < baseStart_2778868 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778871 : List Nat := [1, 1, 3, 1, 1, 1, 4, 4, 3, 2, 2]
def baseStart_2778871 : Nat := 118140960795 + 2778871 * 2 ^ 59
def prefixEnd_2778871 : Nat := 4983230072969 + 3 ^ 40 * 2778871 * 2
def baseEnd_2778871 : Nat := 1426896499840302388132711

theorem tailTrace_2778871 : CollatzResearch.WordTrace tailWord_2778871 prefixEnd_2778871 1426896499840302388132711 := by
  unfold tailWord_2778871
  simp only [CollatzResearch.WordTrace]
  refine ⟨101353751915632435227600467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67569167943754956818400311 101353751915632435227600467)
  ·
    refine ⟨152030627873448652841400701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101353751915632435227600467 152030627873448652841400701)
    ·
      refine ⟨57011485452543244815525263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152030627873448652841400701 57011485452543244815525263)
      ·
        refine ⟨85517228178814867223287895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57011485452543244815525263 85517228178814867223287895)
        ·
          refine ⟨128275842268222300834931843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85517228178814867223287895 128275842268222300834931843)
          ·
            refine ⟨192413763402333451252397765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128275842268222300834931843 192413763402333451252397765)
            ·
              refine ⟨36077580637937522109824581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 192413763402333451252397765 36077580637937522109824581)
              ·
                refine ⟨6764546369613285395592109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36077580637937522109824581 6764546369613285395592109)
                ·
                  refine ⟨2536704888604982023347041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6764546369613285395592109 2536704888604982023347041)
                  ·
                    refine ⟨1902528666453736517510281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2536704888604982023347041 1902528666453736517510281)
                    ·
                      refine ⟨1426896499840302388132711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902528666453736517510281 1426896499840302388132711)
                      ·
                        rfl

theorem cell23_2778871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 4, 3, 2, 2].length) (baseStart_2778871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778871 prefixEnd_2778871 := by exact prefixLift 2778871
  have htrace : WordTrace (prefixWord ++ tailWord_2778871) baseStart_2778871 baseEnd_2778871 := by
    simpa [prefixWord, tailWord_2778871, baseEnd_2778871] using wordTrace_append hprefix tailTrace_2778871
  have hstable : (prefixWord ++ tailWord_2778871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778871).length < 2 ^ (prefixWord ++ tailWord_2778871).sum := by decide
  have hdescent : baseEnd_2778871 < baseStart_2778871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778884 : List Nat := [2, 3, 2, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_2778884 : Nat := 118140960795 + 2778884 * 2 ^ 59
def prefixEnd_2778884 : Nat := 4983230072969 + 3 ^ 40 * 2778884 * 2
def baseEnd_2778884 : Nat := 1426903175088810837270151

theorem tailTrace_2778884 : CollatzResearch.WordTrace tailWord_2778884 prefixEnd_2778884 1426903175088810837270151 := by
  unfold tailWord_2778884
  simp only [CollatzResearch.WordTrace]
  refine ⟨50677113032292669223911853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67569484043056892298549137 50677113032292669223911853)
  ·
    refine ⟨19003917387109750958966945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50677113032292669223911853 19003917387109750958966945)
    ·
      refine ⟨14252938040332313219225209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19003917387109750958966945 14252938040332313219225209)
      ·
        refine ⟨10689703530249234914418907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14252938040332313219225209 10689703530249234914418907)
        ·
          refine ⟨16034555295373852371628361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10689703530249234914418907 16034555295373852371628361)
          ·
            refine ⟨12025916471530389278721271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16034555295373852371628361 12025916471530389278721271)
            ·
              refine ⟨18038874707295583918081907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12025916471530389278721271 18038874707295583918081907)
              ·
                refine ⟨27058312060943375877122861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18038874707295583918081907 27058312060943375877122861)
                ·
                  refine ⟨10146867022853765953921073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27058312060943375877122861 10146867022853765953921073)
                  ·
                    refine ⟨7610150267140324465440805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10146867022853765953921073 7610150267140324465440805)
                    ·
                      refine ⟨1426903175088810837270151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7610150267140324465440805 1426903175088810837270151)
                      ·
                        rfl

theorem cell23_2778884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_2778884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778884 prefixEnd_2778884 := by exact prefixLift 2778884
  have htrace : WordTrace (prefixWord ++ tailWord_2778884) baseStart_2778884 baseEnd_2778884 := by
    simpa [prefixWord, tailWord_2778884, baseEnd_2778884] using wordTrace_append hprefix tailTrace_2778884
  have hstable : (prefixWord ++ tailWord_2778884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778884).length < 2 ^ (prefixWord ++ tailWord_2778884).sum := by decide
  have hdescent : baseEnd_2778884 < baseStart_2778884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778893 : List Nat := [1, 7, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_2778893 : Nat := 118140960795 + 2778893 * 2 ^ 59
def prefixEnd_2778893 : Nat := 4983230072969 + 3 ^ 40 * 2778893 * 2
def baseEnd_2778893 : Nat := 475635932138233767352537

theorem tailTrace_2778893 : CollatzResearch.WordTrace tailWord_2778893 prefixEnd_2778893 475635932138233767352537 := by
  unfold tailWord_2778893
  simp only [CollatzResearch.WordTrace]
  refine ⟨101354554321552732984901333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67569702881035155323267555 101354554321552732984901333)
  ·
    refine ⟨2375497366911392179333625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 101354554321552732984901333 2375497366911392179333625)
    ·
      refine ⟨1781623025183544134500219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2375497366911392179333625 1781623025183544134500219)
      ·
        refine ⟨2672434537775316201750329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1781623025183544134500219 2672434537775316201750329)
        ·
          refine ⟨2004325903331487151312747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2672434537775316201750329 2004325903331487151312747)
          ·
            refine ⟨3006488854997230726969121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004325903331487151312747 3006488854997230726969121)
            ·
              refine ⟨2254866641247923045226841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3006488854997230726969121 2254866641247923045226841)
              ·
                refine ⟨1691149980935942283920131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2254866641247923045226841 1691149980935942283920131)
                ·
                  refine ⟨2536724971403913425880197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691149980935942283920131 2536724971403913425880197)
                  ·
                    refine ⟨475635932138233767352537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2536724971403913425880197 475635932138233767352537)
                    ·
                      rfl

theorem cell23_2778893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_2778893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778893 prefixEnd_2778893 := by exact prefixLift 2778893
  have htrace : WordTrace (prefixWord ++ tailWord_2778893) baseStart_2778893 baseEnd_2778893 := by
    simpa [prefixWord, tailWord_2778893, baseEnd_2778893] using wordTrace_append hprefix tailTrace_2778893
  have hstable : (prefixWord ++ tailWord_2778893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778893).length < 2 ^ (prefixWord ++ tailWord_2778893).sum := by decide
  have hdescent : baseEnd_2778893 < baseStart_2778893 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778898 : List Nat := [3, 2, 4, 1, 1, 1, 1, 4, 2, 4]
def baseStart_2778898 : Nat := 118140960795 + 2778898 * 2 ^ 59
def prefixEnd_2778898 : Nat := 4983230072969 + 3 ^ 40 * 2778898 * 2
def baseEnd_2778898 : Nat := 475636787939324594165029

theorem tailTrace_2778898 : CollatzResearch.WordTrace tailWord_2778898 prefixEnd_2778898 475636787939324594165029 := by
  unfold tailWord_2778898
  simp only [CollatzResearch.WordTrace]
  refine ⟨25338684171633654709708337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67569824457689745892555565 25338684171633654709708337)
  ·
    refine ⟨19004013128725241032281253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25338684171633654709708337 19004013128725241032281253)
    ·
      refine ⟨3563252461635982693552735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19004013128725241032281253 3563252461635982693552735)
      ·
        refine ⟨5344878692453974040329103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563252461635982693552735 5344878692453974040329103)
        ·
          refine ⟨8017318038680961060493655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5344878692453974040329103 8017318038680961060493655)
          ·
            refine ⟨12025977058021441590740483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8017318038680961060493655 12025977058021441590740483)
            ·
              refine ⟨18038965587032162386110725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12025977058021441590740483 18038965587032162386110725)
              ·
                refine ⟨3382306047568530447395761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18038965587032162386110725 3382306047568530447395761)
                ·
                  refine ⟨2536729535676397835546821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382306047568530447395761 2536729535676397835546821)
                  ·
                    refine ⟨475636787939324594165029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2536729535676397835546821 475636787939324594165029)
                    ·
                      rfl

theorem cell23_2778898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_2778898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778898 prefixEnd_2778898 := by exact prefixLift 2778898
  have htrace : WordTrace (prefixWord ++ tailWord_2778898) baseStart_2778898 baseEnd_2778898 := by
    simpa [prefixWord, tailWord_2778898, baseEnd_2778898] using wordTrace_append hprefix tailTrace_2778898
  have hstable : (prefixWord ++ tailWord_2778898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778898).length < 2 ^ (prefixWord ++ tailWord_2778898).sum := by decide
  have hdescent : baseEnd_2778898 < baseStart_2778898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778972 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 2, 1, 3]
def baseStart_2778972 : Nat := 118140960795 + 2778972 * 2 ^ 59
def prefixEnd_2778972 : Nat := 4983230072969 + 3 ^ 40 * 2778972 * 2
def baseEnd_2778972 : Nat := 1426948361386406492969747

theorem tailTrace_2778972 : CollatzResearch.WordTrace tailWord_2778972 prefixEnd_2778972 1426948361386406492969747 := by
  unfold tailWord_2778972
  simp only [CollatzResearch.WordTrace]
  refine ⟨50678717844133264738513585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67571623792177686318018113 50678717844133264738513585)
  ·
    refine ⟨38009038383099948553885189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50678717844133264738513585 38009038383099948553885189)
    ·
      refine ⟨7126694696831240353853473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38009038383099948553885189 7126694696831240353853473)
      ·
        refine ⟨5345021022623430265390105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7126694696831240353853473 5345021022623430265390105)
        ·
          refine ⟨4008765766967572699042579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5345021022623430265390105 4008765766967572699042579)
          ·
            refine ⟨6013148650451359048563869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008765766967572699042579 6013148650451359048563869)
            ·
              refine ⟨2254930743919259643211451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6013148650451359048563869 2254930743919259643211451)
              ·
                refine ⟨3382396115878889464817177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2254930743919259643211451 3382396115878889464817177)
                ·
                  refine ⟨2536797086909167098612883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3382396115878889464817177 2536797086909167098612883)
                  ·
                    refine ⟨3805195630363750647919325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536797086909167098612883 3805195630363750647919325)
                    ·
                      refine ⟨1426948361386406492969747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3805195630363750647919325 1426948361386406492969747)
                      ·
                        rfl

theorem cell23_2778972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_2778972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778972 prefixEnd_2778972 := by exact prefixLift 2778972
  have htrace : WordTrace (prefixWord ++ tailWord_2778972) baseStart_2778972 baseEnd_2778972 := by
    simpa [prefixWord, tailWord_2778972, baseEnd_2778972] using wordTrace_append hprefix tailTrace_2778972
  have hstable : (prefixWord ++ tailWord_2778972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778972).length < 2 ^ (prefixWord ++ tailWord_2778972).sum := by decide
  have hdescent : baseEnd_2778972 < baseStart_2778972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778984 : List Nat := [2, 1, 4, 2, 1, 1, 1, 4, 7]
def baseStart_2778984 : Nat := 118140960795 + 2778984 * 2 ^ 59
def prefixEnd_2778984 : Nat := 4983230072969 + 3 ^ 40 * 2778984 * 2
def baseEnd_2778984 : Nat := 158550502572695605113299

theorem tailTrace_2778984 : CollatzResearch.WordTrace tailWord_2778984 prefixEnd_2778984 158550502572695605113299 := by
  unfold tailWord_2778984
  simp only [CollatzResearch.WordTrace]
  refine ⟨50678936682111527763232003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67571915576148703684309337 50678936682111527763232003)
  ·
    refine ⟨76018405023167291644848005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50678936682111527763232003 76018405023167291644848005)
    ·
      refine ⟨14253450941843867183409001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 76018405023167291644848005 14253450941843867183409001)
      ·
        refine ⟨10690088206382900387556751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14253450941843867183409001 10690088206382900387556751)
        ·
          refine ⟨16035132309574350581335127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10690088206382900387556751 16035132309574350581335127)
          ·
            refine ⟨24052698464361525872002691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16035132309574350581335127 24052698464361525872002691)
            ·
              refine ⟨36079047696542288808004037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24052698464361525872002691 36079047696542288808004037)
              ·
                refine ⟨6764821443101679151500757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36079047696542288808004037 6764821443101679151500757)
                ·
                  refine ⟨158550502572695605113299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6764821443101679151500757 158550502572695605113299)
                  ·
                    rfl

theorem cell23_2778984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 4, 7].length) (baseStart_2778984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778984 prefixEnd_2778984 := by exact prefixLift 2778984
  have htrace : WordTrace (prefixWord ++ tailWord_2778984) baseStart_2778984 baseEnd_2778984 := by
    simpa [prefixWord, tailWord_2778984, baseEnd_2778984] using wordTrace_append hprefix tailTrace_2778984
  have hstable : (prefixWord ++ tailWord_2778984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778984).length < 2 ^ (prefixWord ++ tailWord_2778984).sum := by decide
  have hdescent : baseEnd_2778984 < baseStart_2778984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2778998 : List Nat := [5, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5]
def baseStart_2778998 : Nat := 118140960795 + 2778998 * 2 ^ 59
def prefixEnd_2778998 : Nat := 4983230072969 + 3 ^ 40 * 2778998 * 2
def baseEnd_2778998 : Nat := 1426961711883423391244627

theorem tailTrace_2778998 : CollatzResearch.WordTrace tailWord_2778998 prefixEnd_2778998 1426961711883423391244627 := by
  unfold tailWord_2778998
  simp only [CollatzResearch.WordTrace]
  refine ⟨6334898999135770994842103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67572255990781557278315765 6334898999135770994842103)
  ·
    refine ⟨9502348498703656492263155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6334898999135770994842103 9502348498703656492263155)
    ·
      refine ⟨14253522748055484738394733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9502348498703656492263155 14253522748055484738394733)
      ·
        refine ⟨5345071030520806776898025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14253522748055484738394733 5345071030520806776898025)
        ·
          refine ⟨4008803272890605082673519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5345071030520806776898025 4008803272890605082673519)
          ·
            refine ⟨6013204909335907624010279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4008803272890605082673519 6013204909335907624010279)
            ·
              refine ⟨9019807364003861436015419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013204909335907624010279 9019807364003861436015419)
              ·
                refine ⟨13529711046005792154023129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9019807364003861436015419 13529711046005792154023129)
                ·
                  refine ⟨10147283284504344115517347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13529711046005792154023129 10147283284504344115517347)
                  ·
                    refine ⟨15220924926756516173276021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10147283284504344115517347 15220924926756516173276021)
                    ·
                      refine ⟨1426961711883423391244627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15220924926756516173276021 1426961711883423391244627)
                      ·
                        rfl

theorem cell23_2778998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 2, 1, 5].length) (baseStart_2778998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2778998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2778998 prefixEnd_2778998 := by exact prefixLift 2778998
  have htrace : WordTrace (prefixWord ++ tailWord_2778998) baseStart_2778998 baseEnd_2778998 := by
    simpa [prefixWord, tailWord_2778998, baseEnd_2778998] using wordTrace_append hprefix tailTrace_2778998
  have hstable : (prefixWord ++ tailWord_2778998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2778998).length < 2 ^ (prefixWord ++ tailWord_2778998).sum := by decide
  have hdescent : baseEnd_2778998 < baseStart_2778998 := by decide
  rcases family_descends (prefixWord ++ tailWord_2778998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779018 : List Nat := [3, 1, 2, 4, 2, 2, 1, 1, 7]
def baseStart_2779018 : Nat := 118140960795 + 2779018 * 2 ^ 59
def prefixEnd_2779018 : Nat := 4983230072969 + 3 ^ 40 * 2779018 * 2
def baseEnd_2779018 : Nat := 158552442388501479221615

theorem tailTrace_2779018 : CollatzResearch.WordTrace tailWord_2779018 prefixEnd_2779018 158552442388501479221615 := by
  unfold tailWord_2779018
  simp only [CollatzResearch.WordTrace]
  refine ⟨25339778361524969833300427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67572742297399919555467805 25339778361524969833300427)
  ·
    refine ⟨38009667542287454749950641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25339778361524969833300427 38009667542287454749950641)
    ·
      refine ⟨28507250656715591062462981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38009667542287454749950641 28507250656715591062462981)
      ·
        refine ⟨5345109498134173324211809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28507250656715591062462981 5345109498134173324211809)
        ·
          refine ⟨4008832123600629993158857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5345109498134173324211809 4008832123600629993158857)
          ·
            refine ⟨3006624092700472494869143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4008832123600629993158857 3006624092700472494869143)
            ·
              refine ⟨4509936139050708742303715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006624092700472494869143 4509936139050708742303715)
              ·
                refine ⟨6764904208576063113455573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4509936139050708742303715 6764904208576063113455573)
                ·
                  refine ⟨158552442388501479221615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 6764904208576063113455573 158552442388501479221615)
                  ·
                    rfl

theorem cell23_2779018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_2779018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779018 prefixEnd_2779018 := by exact prefixLift 2779018
  have htrace : WordTrace (prefixWord ++ tailWord_2779018) baseStart_2779018 baseEnd_2779018 := by
    simpa [prefixWord, tailWord_2779018, baseEnd_2779018] using wordTrace_append hprefix tailTrace_2779018
  have hstable : (prefixWord ++ tailWord_2779018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779018).length < 2 ^ (prefixWord ++ tailWord_2779018).sum := by decide
  have hdescent : baseEnd_2779018 < baseStart_2779018 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779064 : List Nat := [2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 6]
def baseStart_2779064 : Nat := 118140960795 + 2779064 * 2 ^ 59
def prefixEnd_2779064 : Nat := 4983230072969 + 3 ^ 40 * 2779064 * 2
def baseEnd_2779064 : Nat := 1426995601606620133019323

theorem tailTrace_2779064 : CollatzResearch.WordTrace tailWord_2779064 prefixEnd_2779064 1426995601606620133019323 := by
  unfold tailWord_2779064
  simp only [CollatzResearch.WordTrace]
  refine ⟨50680395601966614594688123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67573860802622152792917497 50680395601966614594688123)
  ·
    refine ⟨76020593402949921892032185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50680395601966614594688123 76020593402949921892032185)
    ·
      refine ⟨57015445052212441419024139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76020593402949921892032185 57015445052212441419024139)
      ·
        refine ⟨85523167578318662128536209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57015445052212441419024139 85523167578318662128536209)
        ·
          refine ⟨64142375683738996596402157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85523167578318662128536209 64142375683738996596402157)
          ·
            refine ⟨24053390881402123723650809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 64142375683738996596402157 24053390881402123723650809)
            ·
              refine ⟨18040043161051592792738107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24053390881402123723650809 18040043161051592792738107)
              ·
                refine ⟨27060064741577389189107161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18040043161051592792738107 27060064741577389189107161)
                ·
                  refine ⟨20295048556183041891830371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27060064741577389189107161 20295048556183041891830371)
                  ·
                    refine ⟨30442572834274562837745557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 20295048556183041891830371 30442572834274562837745557)
                    ·
                      refine ⟨1426995601606620133019323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 30442572834274562837745557 1426995601606620133019323)
                      ·
                        rfl

theorem cell23_2779064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 2, 1, 2, 1, 6].length) (baseStart_2779064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779064 prefixEnd_2779064 := by exact prefixLift 2779064
  have htrace : WordTrace (prefixWord ++ tailWord_2779064) baseStart_2779064 baseEnd_2779064 := by
    simpa [prefixWord, tailWord_2779064, baseEnd_2779064] using wordTrace_append hprefix tailTrace_2779064
  have hstable : (prefixWord ++ tailWord_2779064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779064).length < 2 ^ (prefixWord ++ tailWord_2779064).sum := by decide
  have hdescent : baseEnd_2779064 < baseStart_2779064 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779071 : List Nat := [1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 3]
def baseStart_2779071 : Nat := 118140960795 + 2779071 * 2 ^ 59
def prefixEnd_2779071 : Nat := 4983230072969 + 3 ^ 40 * 2779071 * 2
def baseEnd_2779071 : Nat := 1426999195971201605631791

theorem tailTrace_2779071 : CollatzResearch.WordTrace tailWord_2779071 prefixEnd_2779071 1426999195971201605631791 := by
  unfold tailWord_2779071
  simp only [CollatzResearch.WordTrace]
  refine ⟨101361046514907869384881067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67574031009938579589920711 101361046514907869384881067)
  ·
    refine ⟨152041569772361804077321601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101361046514907869384881067 152041569772361804077321601)
    ·
      refine ⟨114031177329271353057991201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152041569772361804077321601 114031177329271353057991201)
      ·
        refine ⟨85523382996953514793493401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114031177329271353057991201 85523382996953514793493401)
        ·
          refine ⟨64142537247715136095120051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85523382996953514793493401 64142537247715136095120051)
          ·
            refine ⟨96213805871572704142680077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64142537247715136095120051 96213805871572704142680077)
            ·
              refine ⟨36080177201839764053505029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 96213805871572704142680077 36080177201839764053505029)
              ·
                refine ⟨6765033225344955760032193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36080177201839764053505029 6765033225344955760032193)
                ·
                  refine ⟨5073774919008716820024145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6765033225344955760032193 5073774919008716820024145)
                  ·
                    refine ⟨3805331189256537615018109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5073774919008716820024145 3805331189256537615018109)
                    ·
                      refine ⟨1426999195971201605631791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3805331189256537615018109 1426999195971201605631791)
                      ·
                        rfl

theorem cell23_2779071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 4, 2, 2, 3].length) (baseStart_2779071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779071 prefixEnd_2779071 := by exact prefixLift 2779071
  have htrace : WordTrace (prefixWord ++ tailWord_2779071) baseStart_2779071 baseEnd_2779071 := by
    simpa [prefixWord, tailWord_2779071, baseEnd_2779071] using wordTrace_append hprefix tailTrace_2779071
  have hstable : (prefixWord ++ tailWord_2779071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779071).length < 2 ^ (prefixWord ++ tailWord_2779071).sum := by decide
  have hdescent : baseEnd_2779071 < baseStart_2779071 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779128 : List Nat := [2, 1, 2, 1, 1, 3, 2, 4, 2, 3, 2]
def baseStart_2779128 : Nat := 118140960795 + 2779128 * 2 ^ 59
def prefixEnd_2779128 : Nat := 4983230072969 + 3 ^ 40 * 2779128 * 2
def baseEnd_2779128 : Nat := 1427028464368507882619029

theorem tailTrace_2779128 : CollatzResearch.WordTrace tailWord_2779128 prefixEnd_2779128 1427028464368507882619029 := by
  unfold tailWord_2779128
  simp only [CollatzResearch.WordTrace]
  refine ⟨50681562737850684059853019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67575416983800912079804025 50681562737850684059853019)
  ·
    refine ⟨76022344106776026089779529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50681562737850684059853019 76022344106776026089779529)
    ·
      refine ⟨57016758080082019567334647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76022344106776026089779529 57016758080082019567334647)
      ·
        refine ⟨85525137120123029351001971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57016758080082019567334647 85525137120123029351001971)
        ·
          refine ⟨128287705680184544026502957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85525137120123029351001971 128287705680184544026502957)
          ·
            refine ⟨48107889630069204009938609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128287705680184544026502957 48107889630069204009938609)
            ·
              refine ⟨36080917222551903007453957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48107889630069204009938609 36080917222551903007453957)
              ·
                refine ⟨6765171979228481813897617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36080917222551903007453957 6765171979228481813897617)
                ·
                  refine ⟨5073878984421361360423213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6765171979228481813897617 5073878984421361360423213)
                  ·
                    refine ⟨1902704619158010510158705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5073878984421361360423213 1902704619158010510158705)
                    ·
                      refine ⟨1427028464368507882619029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902704619158010510158705 1427028464368507882619029)
                      ·
                        rfl

theorem cell23_2779128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 4, 2, 3, 2].length) (baseStart_2779128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779128 prefixEnd_2779128 := by exact prefixLift 2779128
  have htrace : WordTrace (prefixWord ++ tailWord_2779128) baseStart_2779128 baseEnd_2779128 := by
    simpa [prefixWord, tailWord_2779128, baseEnd_2779128] using wordTrace_append hprefix tailTrace_2779128
  have hstable : (prefixWord ++ tailWord_2779128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779128).length < 2 ^ (prefixWord ++ tailWord_2779128).sum := by decide
  have hdescent : baseEnd_2779128 < baseStart_2779128 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779169 : List Nat := [1, 2, 3, 2, 4, 2, 1, 3, 1, 1, 3]
def baseStart_2779169 : Nat := 118140960795 + 2779169 * 2 ^ 59
def prefixEnd_2779169 : Nat := 4983230072969 + 3 ^ 40 * 2779169 * 2
def baseEnd_2779169 : Nat := 1427049517075342222206341

theorem tailTrace_2779169 : CollatzResearch.WordTrace tailWord_2779169 prefixEnd_2779169 1427049517075342222206341 := by
  unfold tailWord_2779169
  simp only [CollatzResearch.WordTrace]
  refine ⟨101364620868552832121948561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67576413912368554747965707 101364620868552832121948561)
  ·
    refine ⟨76023465651414624091461421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101364620868552832121948561 76023465651414624091461421)
    ·
      refine ⟨28508799619280484034298033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76023465651414624091461421 28508799619280484034298033)
      ·
        refine ⟨21381599714460363025723525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28508799619280484034298033 21381599714460363025723525)
        ·
          refine ⟨4009049946461318067323161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21381599714460363025723525 4009049946461318067323161)
          ·
            refine ⟨3006787459845988550492371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4009049946461318067323161 3006787459845988550492371)
            ·
              refine ⟨4510181189768982825738557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3006787459845988550492371 4510181189768982825738557)
              ·
                refine ⟨1691317946163368559651959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4510181189768982825738557 1691317946163368559651959)
                ·
                  refine ⟨2536976919245052839477939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691317946163368559651959 2536976919245052839477939)
                  ·
                    refine ⟨3805465378867579259216909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2536976919245052839477939 3805465378867579259216909)
                    ·
                      refine ⟨1427049517075342222206341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3805465378867579259216909 1427049517075342222206341)
                      ·
                        rfl

theorem cell23_2779169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 1, 1, 3].length) (baseStart_2779169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779169 prefixEnd_2779169 := by exact prefixLift 2779169
  have htrace : WordTrace (prefixWord ++ tailWord_2779169) baseStart_2779169 baseEnd_2779169 := by
    simpa [prefixWord, tailWord_2779169, baseEnd_2779169] using wordTrace_append hprefix tailTrace_2779169
  have hstable : (prefixWord ++ tailWord_2779169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779169).length < 2 ^ (prefixWord ++ tailWord_2779169).sum := by decide
  have hdescent : baseEnd_2779169 < baseStart_2779169 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779171 : List Nat := [1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4]
def baseStart_2779171 : Nat := 118140960795 + 2779171 * 2 ^ 59
def prefixEnd_2779171 : Nat := 4983230072969 + 3 ^ 40 * 2779171 * 2
def baseEnd_2779171 : Nat := 1427050544036651214381331

theorem tailTrace_2779171 : CollatzResearch.WordTrace tailWord_2779171 prefixEnd_2779171 1427050544036651214381331 := by
  unfold tailWord_2779171
  simp only [CollatzResearch.WordTrace]
  refine ⟨101364693814545586463521367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67576462543030390975680911 101364693814545586463521367)
  ·
    refine ⟨152047040721818379695282051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101364693814545586463521367 152047040721818379695282051)
    ·
      refine ⟨228070561082727569542923077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152047040721818379695282051 228070561082727569542923077)
      ·
        refine ⟨42763230203011419289298077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228070561082727569542923077 42763230203011419289298077)
        ·
          refine ⟨16036211326129282233486779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42763230203011419289298077 16036211326129282233486779)
          ·
            refine ⟨24054316989193923350230169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036211326129282233486779 24054316989193923350230169)
            ·
              refine ⟨18040737741895442512672627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24054316989193923350230169 18040737741895442512672627)
              ·
                refine ⟨27061106612843163769008941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18040737741895442512672627 27061106612843163769008941)
                ·
                  refine ⟨10147914979816186413378353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 27061106612843163769008941 10147914979816186413378353)
                  ·
                    refine ⟨7610936234862139810033765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10147914979816186413378353 7610936234862139810033765)
                    ·
                      refine ⟨1427050544036651214381331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7610936234862139810033765 1427050544036651214381331)
                      ·
                        rfl

theorem cell23_2779171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_2779171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779171 prefixEnd_2779171 := by exact prefixLift 2779171
  have htrace : WordTrace (prefixWord ++ tailWord_2779171) baseStart_2779171 baseEnd_2779171 := by
    simpa [prefixWord, tailWord_2779171, baseEnd_2779171] using wordTrace_append hprefix tailTrace_2779171
  have hstable : (prefixWord ++ tailWord_2779171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779171).length < 2 ^ (prefixWord ++ tailWord_2779171).sum := by decide
  have hdescent : baseEnd_2779171 < baseStart_2779171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779178 : List Nat := [3, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_2779178 : Nat := 118140960795 + 2779178 * 2 ^ 59
def prefixEnd_2779178 : Nat := 4983230072969 + 3 ^ 40 * 2779178 * 2
def baseEnd_2779178 : Nat := 1427054138401232686993799

theorem tailTrace_2779178 : CollatzResearch.WordTrace tailWord_2779178 prefixEnd_2779178 1427054138401232686993799 := by
  unfold tailWord_2779178
  simp only [CollatzResearch.WordTrace]
  refine ⟨25341237281380056664756547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67576632750346817772684125 25341237281380056664756547)
  ·
    refine ⟨38011855922070084997134821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25341237281380056664756547 38011855922070084997134821)
    ·
      refine ⟨7127222985388140936962779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 38011855922070084997134821 7127222985388140936962779)
      ·
        refine ⟨10690834478082211405444169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127222985388140936962779 10690834478082211405444169)
        ·
          refine ⟨8018125858561658554083127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10690834478082211405444169 8018125858561658554083127)
          ·
            refine ⟨12027188787842487831124691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8018125858561658554083127 12027188787842487831124691)
            ·
              refine ⟨18040783181763731746687037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12027188787842487831124691 18040783181763731746687037)
              ·
                refine ⟨6765293693161399405007639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18040783181763731746687037 6765293693161399405007639)
                ·
                  refine ⟨10147940539742099107511459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765293693161399405007639 10147940539742099107511459)
                  ·
                    refine ⟨15221910809613148661267189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10147940539742099107511459 15221910809613148661267189)
                    ·
                      refine ⟨1427054138401232686993799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15221910809613148661267189 1427054138401232686993799)
                      ·
                        rfl

theorem cell23_2779178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_2779178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779178 prefixEnd_2779178 := by exact prefixLift 2779178
  have htrace : WordTrace (prefixWord ++ tailWord_2779178) baseStart_2779178 baseEnd_2779178 := by
    simpa [prefixWord, tailWord_2779178, baseEnd_2779178] using wordTrace_append hprefix tailTrace_2779178
  have hstable : (prefixWord ++ tailWord_2779178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779178).length < 2 ^ (prefixWord ++ tailWord_2779178).sum := by decide
  have hdescent : baseEnd_2779178 < baseStart_2779178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779208 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 6, 1, 3]
def baseStart_2779208 : Nat := 118140960795 + 2779208 * 2 ^ 59
def prefixEnd_2779208 : Nat := 4983230072969 + 3 ^ 40 * 2779208 * 2
def baseEnd_2779208 : Nat := 1427069542820867569618661

theorem tailTrace_2779208 : CollatzResearch.WordTrace tailWord_2779208 prefixEnd_2779208 1427069542820867569618661 := by
  unfold tailWord_2779208
  simp only [CollatzResearch.WordTrace]
  refine ⟨50683021657705770891309139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67577362210274361188412185 50683021657705770891309139)
  ·
    refine ⟨76024532486558656336963709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50683021657705770891309139 76024532486558656336963709)
    ·
      refine ⟨28509199682459496126361391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76024532486558656336963709 28509199682459496126361391)
      ·
        refine ⟨42763799523689244189542087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28509199682459496126361391 42763799523689244189542087)
        ·
          refine ⟨64145699285533866284313131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42763799523689244189542087 64145699285533866284313131)
          ·
            refine ⟨96218548928300799426469697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64145699285533866284313131 96218548928300799426469697)
            ·
              refine ⟨72163911696225599569852273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 96218548928300799426469697 72163911696225599569852273)
              ·
                refine ⟨54122933772169199677389205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72163911696225599569852273 54122933772169199677389205)
                ·
                  refine ⟨2537012520570431234877619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 54122933772169199677389205 2537012520570431234877619)
                  ·
                    refine ⟨3805518780855646852316429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2537012520570431234877619 3805518780855646852316429)
                    ·
                      refine ⟨1427069542820867569618661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3805518780855646852316429 1427069542820867569618661)
                      ·
                        rfl

theorem cell23_2779208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 6, 1, 3].length) (baseStart_2779208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779208 prefixEnd_2779208 := by exact prefixLift 2779208
  have htrace : WordTrace (prefixWord ++ tailWord_2779208) baseStart_2779208 baseEnd_2779208 := by
    simpa [prefixWord, tailWord_2779208, baseEnd_2779208] using wordTrace_append hprefix tailTrace_2779208
  have hstable : (prefixWord ++ tailWord_2779208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779208).length < 2 ^ (prefixWord ++ tailWord_2779208).sum := by decide
  have hdescent : baseEnd_2779208 < baseStart_2779208 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779222 : List Nat := [5, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4]
def baseStart_2779222 : Nat := 118140960795 + 2779222 * 2 ^ 59
def prefixEnd_2779222 : Nat := 4983230072969 + 3 ^ 40 * 2779222 * 2
def baseEnd_2779222 : Nat := 1427076731550030514843597

theorem tailTrace_2779222 : CollatzResearch.WordTrace tailWord_2779222 prefixEnd_2779222 1427076731550030514843597 := by
  unfold tailWord_2779222
  simp only [CollatzResearch.WordTrace]
  refine ⟨6335409621085051385851745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67577702624907214782418613 6335409621085051385851745)
  ·
    refine ⟨4751557215813788539388809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6335409621085051385851745 4751557215813788539388809)
    ·
      refine ⟨3563667911860341404541607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4751557215813788539388809 3563667911860341404541607)
      ·
        refine ⟨5345501867790512106812411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563667911860341404541607 5345501867790512106812411)
        ·
          refine ⟨8018252801685768160218617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5345501867790512106812411 8018252801685768160218617)
          ·
            refine ⟨6013689601264326120163963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8018252801685768160218617 6013689601264326120163963)
            ·
              refine ⟨9020534401896489180245945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6013689601264326120163963 9020534401896489180245945)
              ·
                refine ⟨6765400801422366885184459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9020534401896489180245945 6765400801422366885184459)
                ·
                  refine ⟨10148101202133550327776689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6765400801422366885184459 10148101202133550327776689)
                  ·
                    refine ⟨7611075901600162745832517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10148101202133550327776689 7611075901600162745832517)
                    ·
                      refine ⟨1427076731550030514843597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7611075901600162745832517 1427076731550030514843597)
                      ·
                        rfl

theorem cell23_2779222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_2779222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779222 prefixEnd_2779222 := by exact prefixLift 2779222
  have htrace : WordTrace (prefixWord ++ tailWord_2779222) baseStart_2779222 baseEnd_2779222 := by
    simpa [prefixWord, tailWord_2779222, baseEnd_2779222] using wordTrace_append hprefix tailTrace_2779222
  have hstable : (prefixWord ++ tailWord_2779222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779222).length < 2 ^ (prefixWord ++ tailWord_2779222).sum := by decide
  have hdescent : baseEnd_2779222 < baseStart_2779222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779229 : List Nat := [1, 4, 4, 1, 1, 2, 3, 1, 1, 2, 3]
def baseStart_2779229 : Nat := 118140960795 + 2779229 * 2 ^ 59
def prefixEnd_2779229 : Nat := 4983230072969 + 3 ^ 40 * 2779229 * 2
def baseEnd_2779229 : Nat := 1427080325914611987456065

theorem tailTrace_2779229 : CollatzResearch.WordTrace tailWord_2779229 prefixEnd_2779229 1427080325914611987456065 := by
  unfold tailWord_2779229
  simp only [CollatzResearch.WordTrace]
  refine ⟨101366809248335462369132741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67577872832223641579421827 101366809248335462369132741)
  ·
    refine ⟨19006276734062899194212389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 101366809248335462369132741 19006276734062899194212389)
    ·
      refine ⟨3563676887636793598914823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19006276734062899194212389 3563676887636793598914823)
      ·
        refine ⟨5345515331455190398372235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3563676887636793598914823 5345515331455190398372235)
        ·
          refine ⟨8018272997182785597558353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5345515331455190398372235 8018272997182785597558353)
          ·
            refine ⟨6013704747887089198168765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8018272997182785597558353 6013704747887089198168765)
            ·
              refine ⟨2255139280457658449313287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6013704747887089198168765 2255139280457658449313287)
              ·
                refine ⟨3382708920686487673969931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255139280457658449313287 3382708920686487673969931)
                ·
                  refine ⟨5074063381029731510954897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382708920686487673969931 5074063381029731510954897)
                  ·
                    refine ⟨3805547535772298633216173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5074063381029731510954897 3805547535772298633216173)
                    ·
                      refine ⟨1427080325914611987456065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3805547535772298633216173 1427080325914611987456065)
                      ·
                        rfl

theorem cell23_2779229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_2779229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779229 prefixEnd_2779229 := by exact prefixLift 2779229
  have htrace : WordTrace (prefixWord ++ tailWord_2779229) baseStart_2779229 baseEnd_2779229 := by
    simpa [prefixWord, tailWord_2779229, baseEnd_2779229] using wordTrace_append hprefix tailTrace_2779229
  have hstable : (prefixWord ++ tailWord_2779229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779229).length < 2 ^ (prefixWord ++ tailWord_2779229).sum := by decide
  have hdescent : baseEnd_2779229 < baseStart_2779229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779235 : List Nat := [1, 1, 1, 5, 1, 1, 2, 5, 1, 3, 2]
def baseStart_2779235 : Nat := 118140960795 + 2779235 * 2 ^ 59
def prefixEnd_2779235 : Nat := 4983230072969 + 3 ^ 40 * 2779235 * 2
def baseEnd_2779235 : Nat := 1427083406798538963981037

theorem tailTrace_2779235 : CollatzResearch.WordTrace tailWord_2779235 prefixEnd_2779235 1427083406798538963981037 := by
  unfold tailWord_2779235
  simp only [CollatzResearch.WordTrace]
  refine ⟨101367028086313725393851159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67578018724209150262567439 101367028086313725393851159)
  ·
    refine ⟨152050542129470588090776739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101367028086313725393851159 152050542129470588090776739)
    ·
      refine ⟨228075813194205882136165109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152050542129470588090776739 228075813194205882136165109)
      ·
        refine ⟨21382107486956801450265479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228075813194205882136165109 21382107486956801450265479)
        ·
          refine ⟨32073161230435202175398219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21382107486956801450265479 32073161230435202175398219)
          ·
            refine ⟨48109741845652803263097329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32073161230435202175398219 48109741845652803263097329)
            ·
              refine ⟨36082306384239602447322997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48109741845652803263097329 36082306384239602447322997)
              ·
                refine ⟨3382716223522462729436531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 36082306384239602447322997 3382716223522462729436531)
                ·
                  refine ⟨5074074335283694094154797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3382716223522462729436531 5074074335283694094154797)
                  ·
                    refine ⟨1902777875731385285308049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5074074335283694094154797 1902777875731385285308049)
                    ·
                      refine ⟨1427083406798538963981037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902777875731385285308049 1427083406798538963981037)
                      ·
                        rfl

theorem cell23_2779235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_2779235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779235 prefixEnd_2779235 := by exact prefixLift 2779235
  have htrace : WordTrace (prefixWord ++ tailWord_2779235) baseStart_2779235 baseEnd_2779235 := by
    simpa [prefixWord, tailWord_2779235, baseEnd_2779235] using wordTrace_append hprefix tailTrace_2779235
  have hstable : (prefixWord ++ tailWord_2779235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779235).length < 2 ^ (prefixWord ++ tailWord_2779235).sum := by decide
  have hdescent : baseEnd_2779235 < baseStart_2779235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779241 : List Nat := [1, 2, 1, 1, 1, 5, 2, 2, 2, 6]
def baseStart_2779241 : Nat := 118140960795 + 2779241 * 2 ^ 59
def prefixEnd_2779241 : Nat := 4983230072969 + 3 ^ 40 * 2779241 * 2
def baseEnd_2779241 : Nat := 475695495894155313502003

theorem tailTrace_2779241 : CollatzResearch.WordTrace tailWord_2779241 prefixEnd_2779241 475695495894155313502003 := by
  unfold tailWord_2779241
  simp only [CollatzResearch.WordTrace]
  refine ⟨101367246924291988418569577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67578164616194658945713051 101367246924291988418569577)
  ·
    refine ⟨76025435193218991313927183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101367246924291988418569577 76025435193218991313927183)
    ·
      refine ⟨114038152789828486970890775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76025435193218991313927183 114038152789828486970890775)
      ·
        refine ⟨171057229184742730456336163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114038152789828486970890775 171057229184742730456336163)
        ·
          refine ⟨256585843777114095684504245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171057229184742730456336163 256585843777114095684504245)
          ·
            refine ⟨24054922854104446470422273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 256585843777114095684504245 24054922854104446470422273)
            ·
              refine ⟨18041192140578334852816705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24054922854104446470422273 18041192140578334852816705)
              ·
                refine ⟨13530894105433751139612529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18041192140578334852816705 13530894105433751139612529)
                ·
                  refine ⟨10148170579075313354709397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13530894105433751139612529 10148170579075313354709397)
                  ·
                    refine ⟨475695495894155313502003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10148170579075313354709397 475695495894155313502003)
                    ·
                      rfl

theorem cell23_2779241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_2779241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779241 prefixEnd_2779241 := by exact prefixLift 2779241
  have htrace : WordTrace (prefixWord ++ tailWord_2779241) baseStart_2779241 baseEnd_2779241 := by
    simpa [prefixWord, tailWord_2779241, baseEnd_2779241] using wordTrace_append hprefix tailTrace_2779241
  have hstable : (prefixWord ++ tailWord_2779241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779241).length < 2 ^ (prefixWord ++ tailWord_2779241).sum := by decide
  have hdescent : baseEnd_2779241 < baseStart_2779241 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779268 : List Nat := [2, 3, 2, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_2779268 : Nat := 118140960795 + 2779268 * 2 ^ 59
def prefixEnd_2779268 : Nat := 4983230072969 + 3 ^ 40 * 2779268 * 2
def baseEnd_2779268 : Nat := 1427100351660137334868385

theorem tailTrace_2779268 : CollatzResearch.WordTrace tailWord_2779268 prefixEnd_2779268 1427100351660137334868385 := by
  unfold tailWord_2779268
  simp only [CollatzResearch.WordTrace]
  refine ⟨50684115847597086014901229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67578821130129448019868305 50684115847597086014901229)
  ·
    refine ⟨19006543442848907255587961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50684115847597086014901229 19006543442848907255587961)
    ·
      refine ⟨14254907582136680441690971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19006543442848907255587961 14254907582136680441690971)
      ·
        refine ⟨21382361373205020662536457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14254907582136680441690971 21382361373205020662536457)
        ·
          refine ⟨16036771029903765496902343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21382361373205020662536457 16036771029903765496902343)
          ·
            refine ⟨24055156544855648245353515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036771029903765496902343 24055156544855648245353515)
            ·
              refine ⟨36082734817283472368030273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24055156544855648245353515 36082734817283472368030273)
              ·
                refine ⟨27062051112962604276022705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 36082734817283472368030273 27062051112962604276022705)
                ·
                  refine ⟨20296538334721953207017029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 27062051112962604276022705 20296538334721953207017029)
                  ·
                    refine ⟨3805600937760366226315693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 20296538334721953207017029 3805600937760366226315693)
                    ·
                      refine ⟨1427100351660137334868385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3805600937760366226315693 1427100351660137334868385)
                      ·
                        rfl

theorem cell23_2779268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_2779268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779268 prefixEnd_2779268 := by exact prefixLift 2779268
  have htrace : WordTrace (prefixWord ++ tailWord_2779268) baseStart_2779268 baseEnd_2779268 := by
    simpa [prefixWord, tailWord_2779268, baseEnd_2779268] using wordTrace_append hprefix tailTrace_2779268
  have hstable : (prefixWord ++ tailWord_2779268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779268).length < 2 ^ (prefixWord ++ tailWord_2779268).sum := by decide
  have hdescent : baseEnd_2779268 < baseStart_2779268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779271 : List Nat := [1, 1, 4, 2, 1, 1, 3, 1, 9]
def baseStart_2779271 : Nat := 118140960795 + 2779271 * 2 ^ 59
def prefixEnd_2779271 : Nat := 4983230072969 + 3 ^ 40 * 2779271 * 2
def baseEnd_2779271 : Nat := 158566876900233424792319

theorem tailTrace_2779271 : CollatzResearch.WordTrace tailWord_2779271 prefixEnd_2779271 158566876900233424792319 := by
  unfold tailWord_2779271
  simp only [CollatzResearch.WordTrace]
  refine ⟨101368341114183303542161667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67578894076122202361441111 101368341114183303542161667)
  ·
    refine ⟨152052511671274955313242501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101368341114183303542161667 152052511671274955313242501)
    ·
      refine ⟨28509845938364054121232969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152052511671274955313242501 28509845938364054121232969)
      ·
        refine ⟨21382384453773040590924727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28509845938364054121232969 21382384453773040590924727)
        ·
          refine ⟨32073576680659560886387091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21382384453773040590924727 32073576680659560886387091)
          ·
            refine ⟨48110365020989341329580637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32073576680659560886387091 48110365020989341329580637)
            ·
              refine ⟨18041386882871002998592739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48110365020989341329580637 18041386882871002998592739)
              ·
                refine ⟨27062080324306504497889109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18041386882871002998592739 27062080324306504497889109)
                ·
                  refine ⟨158566876900233424792319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 27062080324306504497889109 158566876900233424792319)
                  ·
                    rfl

theorem cell23_2779271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 3, 1, 9].length) (baseStart_2779271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779271 prefixEnd_2779271 := by exact prefixLift 2779271
  have htrace : WordTrace (prefixWord ++ tailWord_2779271) baseStart_2779271 baseEnd_2779271 := by
    simpa [prefixWord, tailWord_2779271, baseEnd_2779271] using wordTrace_append hprefix tailTrace_2779271
  have hstable : (prefixWord ++ tailWord_2779271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779271).length < 2 ^ (prefixWord ++ tailWord_2779271).sum := by decide
  have hdescent : baseEnd_2779271 < baseStart_2779271 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779282 : List Nat := [3, 2, 3, 1, 1, 1, 2, 2, 4, 2, 2]
def baseStart_2779282 : Nat := 118140960795 + 2779282 * 2 ^ 59
def prefixEnd_2779282 : Nat := 4983230072969 + 3 ^ 40 * 2779282 * 2
def baseEnd_2779282 : Nat := 1427107540389300280093321

theorem tailTrace_2779282 : CollatzResearch.WordTrace tailWord_2779282 prefixEnd_2779282 1427107540389300280093321 := by
  unfold tailWord_2779282
  simp only [CollatzResearch.WordTrace]
  refine ⟨25342185579285863105203025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67579161544762301613874733 25342185579285863105203025)
  ·
    refine ⟨19006639184464397328902269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25342185579285863105203025 19006639184464397328902269)
    ·
      refine ⟨7127489694174148998338351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19006639184464397328902269 7127489694174148998338351)
      ·
        refine ⟨10691234541261223497507527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7127489694174148998338351 10691234541261223497507527)
        ·
          refine ⟨16036851811891835246261291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10691234541261223497507527 16036851811891835246261291)
          ·
            refine ⟨24055277717837752869391937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16036851811891835246261291 24055277717837752869391937)
            ·
              refine ⟨18041458288378314652043953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24055277717837752869391937 18041458288378314652043953)
              ·
                refine ⟨13531093716283735989032965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18041458288378314652043953 13531093716283735989032965)
                ·
                  refine ⟨2537080071803200497943681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13531093716283735989032965 2537080071803200497943681)
                  ·
                    refine ⟨1902810053852400373457761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537080071803200497943681 1902810053852400373457761)
                    ·
                      refine ⟨1427107540389300280093321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902810053852400373457761 1427107540389300280093321)
                      ·
                        rfl

theorem cell23_2779282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_2779282 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779282 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779282 prefixEnd_2779282 := by exact prefixLift 2779282
  have htrace : WordTrace (prefixWord ++ tailWord_2779282) baseStart_2779282 baseEnd_2779282 := by
    simpa [prefixWord, tailWord_2779282, baseEnd_2779282] using wordTrace_append hprefix tailTrace_2779282
  have hstable : (prefixWord ++ tailWord_2779282).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779282).length < 2 ^ (prefixWord ++ tailWord_2779282).sum := by decide
  have hdescent : baseEnd_2779282 < baseStart_2779282 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779311 : List Nat := [1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 7]
def baseStart_2779311 : Nat := 118140960795 + 2779311 * 2 ^ 59
def prefixEnd_2779311 : Nat := 4983230072969 + 3 ^ 40 * 2779311 * 2
def baseEnd_2779311 : Nat := 1427122431328280666630687

theorem tailTrace_2779311 : CollatzResearch.WordTrace tailWord_2779311 prefixEnd_2779311 1427122431328280666630687 := by
  unfold tailWord_2779311
  simp only [CollatzResearch.WordTrace]
  refine ⟨101369800034038390373617787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67579866689358926915745191 101369800034038390373617787)
  ·
    refine ⟨152054700051057585560426681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101369800034038390373617787 152054700051057585560426681)
    ·
      refine ⟨114041025038293189170320011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152054700051057585560426681 114041025038293189170320011)
      ·
        refine ⟨171061537557439783755480017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114041025038293189170320011 171061537557439783755480017)
        ·
          refine ⟨128296153168079837816610013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 171061537557439783755480017 128296153168079837816610013)
          ·
            refine ⟨48111057438029939181228755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 128296153168079837816610013 48111057438029939181228755)
            ·
              refine ⟨72166586157044908771843133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48111057438029939181228755 72166586157044908771843133)
              ·
                refine ⟨27062469808891840789441175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 72166586157044908771843133 27062469808891840789441175)
                ·
                  refine ⟨40593704713337761184161763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27062469808891840789441175 40593704713337761184161763)
                  ·
                    refine ⟨60890557070006641776242645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 40593704713337761184161763 60890557070006641776242645)
                    ·
                      refine ⟨1427122431328280666630687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 60890557070006641776242645 1427122431328280666630687)
                      ·
                        rfl

theorem cell23_2779311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 1, 7].length) (baseStart_2779311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779311 prefixEnd_2779311 := by exact prefixLift 2779311
  have htrace : WordTrace (prefixWord ++ tailWord_2779311) baseStart_2779311 baseEnd_2779311 := by
    simpa [prefixWord, tailWord_2779311, baseEnd_2779311] using wordTrace_append hprefix tailTrace_2779311
  have hstable : (prefixWord ++ tailWord_2779311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779311).length < 2 ^ (prefixWord ++ tailWord_2779311).sum := by decide
  have hdescent : baseEnd_2779311 < baseStart_2779311 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779338 : List Nat := [3, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_2779338 : Nat := 118140960795 + 2779338 * 2 ^ 59
def prefixEnd_2779338 : Nat := 4983230072969 + 3 ^ 40 * 2779338 * 2
def baseEnd_2779338 : Nat := 1427136295305952060993063

theorem tailTrace_2779338 : CollatzResearch.WordTrace tailWord_2779338 prefixEnd_2779338 1427136295305952060993063 := by
  unfold tailWord_2779338
  simp only [CollatzResearch.WordTrace]
  refine ⟨25342696201235143496212667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67580523203293715989900445 25342696201235143496212667)
  ·
    refine ⟨38014044301852715244319001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25342696201235143496212667 38014044301852715244319001)
    ·
      refine ⟨28510533226389536433239251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38014044301852715244319001 28510533226389536433239251)
      ·
        refine ⟨42765799839584304649858877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28510533226389536433239251 42765799839584304649858877)
        ·
          refine ⟨16037174939844114243697079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42765799839584304649858877 16037174939844114243697079)
          ·
            refine ⟨24055762409766171365545619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16037174939844114243697079 24055762409766171365545619)
            ·
              refine ⟨36083643614649257048318429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24055762409766171365545619 36083643614649257048318429)
              ·
                refine ⟨13531366355493471393119411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36083643614649257048318429 13531366355493471393119411)
                ·
                  refine ⟨20297049533240207089679117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 13531366355493471393119411 20297049533240207089679117)
                  ·
                    refine ⟨7611393574965077658629669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 20297049533240207089679117 7611393574965077658629669)
                    ·
                      refine ⟨1427136295305952060993063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7611393574965077658629669 1427136295305952060993063)
                      ·
                        rfl

theorem cell23_2779338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_2779338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779338 prefixEnd_2779338 := by exact prefixLift 2779338
  have htrace : WordTrace (prefixWord ++ tailWord_2779338) baseStart_2779338 baseEnd_2779338 := by
    simpa [prefixWord, tailWord_2779338, baseEnd_2779338] using wordTrace_append hprefix tailTrace_2779338
  have hstable : (prefixWord ++ tailWord_2779338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779338).length < 2 ^ (prefixWord ++ tailWord_2779338).sum := by decide
  have hdescent : baseEnd_2779338 < baseStart_2779338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779356 : List Nat := [2, 2, 5, 2, 1, 1, 3, 2, 5]
def baseStart_2779356 : Nat := 118140960795 + 2779356 * 2 ^ 59
def prefixEnd_2779356 : Nat := 4983230072969 + 3 ^ 40 * 2779356 * 2
def baseEnd_2779356 : Nat := 158571726439748110063109

theorem tailTrace_2779356 : CollatzResearch.WordTrace tailWord_2779356 prefixEnd_2779356 158571726439748110063109 := by
  unfold tailWord_2779356
  simp only [CollatzResearch.WordTrace]
  refine ⟨50685720659437681529502961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67580960879250242039337281 50685720659437681529502961)
  ·
    refine ⟨38014290494578261147127221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50685720659437681529502961 38014290494578261147127221)
    ·
      refine ⟨3563839733866711982543177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38014290494578261147127221 3563839733866711982543177)
      ·
        refine ⟨2672879800400033986907383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3563839733866711982543177 2672879800400033986907383)
        ·
          refine ⟨4009319700600050980361075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2672879800400033986907383 4009319700600050980361075)
          ·
            refine ⟨6013979550900076470541613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009319700600050980361075 6013979550900076470541613)
            ·
              refine ⟨2255242331587528676453105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6013979550900076470541613 2255242331587528676453105)
              ·
                refine ⟨1691431748690646507339829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2255242331587528676453105 1691431748690646507339829)
                ·
                  refine ⟨158571726439748110063109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1691431748690646507339829 158571726439748110063109)
                  ·
                    rfl

theorem cell23_2779356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 3, 2, 5].length) (baseStart_2779356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779356 prefixEnd_2779356 := by exact prefixLift 2779356
  have htrace : WordTrace (prefixWord ++ tailWord_2779356) baseStart_2779356 baseEnd_2779356 := by
    simpa [prefixWord, tailWord_2779356, baseEnd_2779356] using wordTrace_append hprefix tailTrace_2779356
  have hstable : (prefixWord ++ tailWord_2779356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779356).length < 2 ^ (prefixWord ++ tailWord_2779356).sum := by decide
  have hdescent : baseEnd_2779356 < baseStart_2779356 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779445 : List Nat := [1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 4]
def baseStart_2779445 : Nat := 118140960795 + 2779445 * 2 ^ 59
def prefixEnd_2779445 : Nat := 4983230072969 + 3 ^ 40 * 2779445 * 2
def baseEnd_2779445 : Nat := 1427191237735983142355071

theorem tailTrace_2779445 : CollatzResearch.WordTrace tailWord_2779445 prefixEnd_2779445 1427191237735983142355071 := by
  unfold tailWord_2779445
  simp only [CollatzResearch.WordTrace]
  refine ⟨101374687415552931258995789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67583124943701954172663859 101374687415552931258995789)
  ·
    refine ⟨38015507780832349222123421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101374687415552931258995789 38015507780832349222123421)
    ·
      refine ⟨14255815417812130958296283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38015507780832349222123421 14255815417812130958296283)
      ·
        refine ⟨21383723126718196437444425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14255815417812130958296283 21383723126718196437444425)
        ·
          refine ⟨16037792345038647328083319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21383723126718196437444425 16037792345038647328083319)
          ·
            refine ⟨24056688517557970992124979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16037792345038647328083319 24056688517557970992124979)
            ·
              refine ⟨36085032776336956488187469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24056688517557970992124979 36085032776336956488187469)
              ·
                refine ⟨13531887291126358683070301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36085032776336956488187469 13531887291126358683070301)
                ·
                  refine ⟨5074457734172384506151363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13531887291126358683070301 5074457734172384506151363)
                  ·
                    refine ⟨7611686601258576759227045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5074457734172384506151363 7611686601258576759227045)
                    ·
                      refine ⟨1427191237735983142355071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7611686601258576759227045 1427191237735983142355071)
                      ·
                        rfl

theorem cell23_2779445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 1, 3, 3, 1, 4].length) (baseStart_2779445 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779445 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779445 prefixEnd_2779445 := by exact prefixLift 2779445
  have htrace : WordTrace (prefixWord ++ tailWord_2779445) baseStart_2779445 baseEnd_2779445 := by
    simpa [prefixWord, tailWord_2779445, baseEnd_2779445] using wordTrace_append hprefix tailTrace_2779445
  have hstable : (prefixWord ++ tailWord_2779445).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779445).length < 2 ^ (prefixWord ++ tailWord_2779445).sum := by decide
  have hdescent : baseEnd_2779445 < baseStart_2779445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779449 : List Nat := [1, 2, 1, 6, 1, 1, 3, 1, 2, 3, 2]
def baseStart_2779449 : Nat := 118140960795 + 2779449 * 2 ^ 59
def prefixEnd_2779449 : Nat := 4983230072969 + 3 ^ 40 * 2779449 * 2
def baseEnd_2779449 : Nat := 1427193291658601126705053

theorem tailTrace_2779449 : CollatzResearch.WordTrace tailWord_2779449 prefixEnd_2779449 1427193291658601126705053 := by
  unfold tailWord_2779449
  simp only [CollatzResearch.WordTrace]
  refine ⟨101374833307538439942141401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67583222205025626628094267 101374833307538439942141401)
  ·
    refine ⟨76031124980653829956606051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101374833307538439942141401 76031124980653829956606051)
    ·
      refine ⟨114046687470980744934909077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76031124980653829956606051 114046687470980744934909077)
      ·
        refine ⟨5345938475202222418823863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 114046687470980744934909077 5345938475202222418823863)
        ·
          refine ⟨8018907712803333628235795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5345938475202222418823863 8018907712803333628235795)
          ·
            refine ⟨12028361569205000442353693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8018907712803333628235795 12028361569205000442353693)
            ·
              refine ⟨4510635588451875165882635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12028361569205000442353693 4510635588451875165882635)
              ·
                refine ⟨6765953382677812748823953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510635588451875165882635 6765953382677812748823953)
                ·
                  refine ⟨5074465037008359561617965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6765953382677812748823953 5074465037008359561617965)
                  ·
                    refine ⟨1902924388878134835606737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5074465037008359561617965 1902924388878134835606737)
                    ·
                      refine ⟨1427193291658601126705053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902924388878134835606737 1427193291658601126705053)
                      ·
                        rfl

theorem cell23_2779449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 1, 3, 1, 2, 3, 2].length) (baseStart_2779449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779449 prefixEnd_2779449 := by exact prefixLift 2779449
  have htrace : WordTrace (prefixWord ++ tailWord_2779449) baseStart_2779449 baseEnd_2779449 := by
    simpa [prefixWord, tailWord_2779449, baseEnd_2779449] using wordTrace_append hprefix tailTrace_2779449
  have hstable : (prefixWord ++ tailWord_2779449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779449).length < 2 ^ (prefixWord ++ tailWord_2779449).sum := by decide
  have hdescent : baseEnd_2779449 < baseStart_2779449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779455 : List Nat := [1, 1, 2, 2, 4, 1, 2, 2, 4, 4]
def baseStart_2779455 : Nat := 118140960795 + 2779455 * 2 ^ 59
def prefixEnd_2779455 : Nat := 4983230072969 + 3 ^ 40 * 2779455 * 2
def baseEnd_2779455 : Nat := 475732124180842701076675

theorem tailTrace_2779455 : CollatzResearch.WordTrace tailWord_2779455 prefixEnd_2779455 475732124180842701076675 := by
  unfold tailWord_2779455
  simp only [CollatzResearch.WordTrace]
  refine ⟨101375052145516702966859819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67583368097011135311239879 101375052145516702966859819)
  ·
    refine ⟨152062578218275054450289729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101375052145516702966859819 152062578218275054450289729)
    ·
      refine ⟨114046933663706290837717297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152062578218275054450289729 114046933663706290837717297)
      ·
        refine ⟨85535200247779718128287973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114046933663706290837717297 85535200247779718128287973)
        ·
          refine ⟨16037850046458697149053995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 85535200247779718128287973 16037850046458697149053995)
          ·
            refine ⟨24056775069688045723580993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16037850046458697149053995 24056775069688045723580993)
            ·
              refine ⟨18042581302266034292685745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24056775069688045723580993 18042581302266034292685745)
              ·
                refine ⟨13531935976699525719514309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18042581302266034292685745 13531935976699525719514309)
                ·
                  refine ⟨2537237995631161072408933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13531935976699525719514309 2537237995631161072408933)
                  ·
                    refine ⟨475732124180842701076675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537237995631161072408933 475732124180842701076675)
                    ·
                      rfl

theorem cell23_2779455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 4, 4].length) (baseStart_2779455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779455 prefixEnd_2779455 := by exact prefixLift 2779455
  have htrace : WordTrace (prefixWord ++ tailWord_2779455) baseStart_2779455 baseEnd_2779455 := by
    simpa [prefixWord, tailWord_2779455, baseEnd_2779455] using wordTrace_append hprefix tailTrace_2779455
  have hstable : (prefixWord ++ tailWord_2779455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779455).length < 2 ^ (prefixWord ++ tailWord_2779455).sum := by decide
  have hdescent : baseEnd_2779455 < baseStart_2779455 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779468 : List Nat := [2, 2, 1, 3, 2, 1, 12]
def baseStart_2779468 : Nat := 118140960795 + 2779468 * 2 ^ 59
def prefixEnd_2779468 : Nat := 4983230072969 + 3 ^ 40 * 2779468 * 2
def baseEnd_2779468 : Nat := 17619790713469587066265

theorem tailTrace_2779468 : CollatzResearch.WordTrace tailWord_2779468 prefixEnd_2779468 17619790713469587066265 := by
  unfold tailWord_2779468
  simp only [CollatzResearch.WordTrace]
  refine ⟨50687763147234803093541529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67583684196313070791388705 50687763147234803093541529)
  ·
    refine ⟨38015822360426102320156147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50687763147234803093541529 38015822360426102320156147)
    ·
      refine ⟨57023733540639153480234221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38015822360426102320156147 57023733540639153480234221)
      ·
        refine ⟨21383900077739682555087833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57023733540639153480234221 21383900077739682555087833)
        ·
          refine ⟨16037925058304761916315875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21383900077739682555087833 16037925058304761916315875)
          ·
            refine ⟨24056887587457142874473813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16037925058304761916315875 24056887587457142874473813)
            ·
              refine ⟨17619790713469587066265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 24056887587457142874473813 17619790713469587066265)
              ·
                rfl

theorem cell23_2779468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 12].length) (baseStart_2779468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779468 prefixEnd_2779468 := by exact prefixLift 2779468
  have htrace : WordTrace (prefixWord ++ tailWord_2779468) baseStart_2779468 baseEnd_2779468 := by
    simpa [prefixWord, tailWord_2779468, baseEnd_2779468] using wordTrace_append hprefix tailTrace_2779468
  have hstable : (prefixWord ++ tailWord_2779468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779468).length < 2 ^ (prefixWord ++ tailWord_2779468).sum := by decide
  have hdescent : baseEnd_2779468 < baseStart_2779468 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779472 : List Nat := [2, 1, 1, 1, 1, 6, 3, 2, 2, 4]
def baseStart_2779472 : Nat := 118140960795 + 2779472 * 2 ^ 59
def prefixEnd_2779472 : Nat := 4983230072969 + 3 ^ 40 * 2779472 * 2
def baseEnd_2779472 : Nat := 475735033904551512239149

theorem tailTrace_2779472 : CollatzResearch.WordTrace tailWord_2779472 prefixEnd_2779472 475735033904551512239149 := by
  unfold tailWord_2779472
  simp only [CollatzResearch.WordTrace]
  refine ⟨50687836093227557435114335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67583781457636743246819113 50687836093227557435114335)
  ·
    refine ⟨76031754139841336152671503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50687836093227557435114335 76031754139841336152671503)
    ·
      refine ⟨114047631209762004229007255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76031754139841336152671503 114047631209762004229007255)
      ·
        refine ⟨171071446814643006343510883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114047631209762004229007255 171071446814643006343510883)
        ·
          refine ⟨256607170221964509515266325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 171071446814643006343510883 256607170221964509515266325)
          ·
            refine ⟨12028461104154586383528109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 256607170221964509515266325 12028461104154586383528109)
            ·
              refine ⟨4510672914057969893823041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12028461104154586383528109 4510672914057969893823041)
              ·
                refine ⟨3383004685543477420367281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510672914057969893823041 3383004685543477420367281)
                ·
                  refine ⟨2537253514157608065275461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383004685543477420367281 2537253514157608065275461)
                  ·
                    refine ⟨475735033904551512239149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537253514157608065275461 475735033904551512239149)
                    ·
                      rfl

theorem cell23_2779472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 2, 2, 4].length) (baseStart_2779472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779472 prefixEnd_2779472 := by exact prefixLift 2779472
  have htrace : WordTrace (prefixWord ++ tailWord_2779472) baseStart_2779472 baseEnd_2779472 := by
    simpa [prefixWord, tailWord_2779472, baseEnd_2779472] using wordTrace_append hprefix tailTrace_2779472
  have hstable : (prefixWord ++ tailWord_2779472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779472).length < 2 ^ (prefixWord ++ tailWord_2779472).sum := by decide
  have hdescent : baseEnd_2779472 < baseStart_2779472 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779479 : List Nat := [1, 1, 3, 2, 3, 1, 4, 1, 3, 2, 2]
def baseStart_2779479 : Nat := 118140960795 + 2779479 * 2 ^ 59
def prefixEnd_2779479 : Nat := 4983230072969 + 3 ^ 40 * 2779479 * 2
def baseEnd_2779479 : Nat := 1427208696078236009329915

theorem tailTrace_2779479 : CollatzResearch.WordTrace tailWord_2779479 prefixEnd_2779479 1427208696078236009329915 := by
  unfold tailWord_2779479
  simp only [CollatzResearch.WordTrace]
  refine ⟨101375927497429755065733491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67583951664953170043822327 101375927497429755065733491)
  ·
    refine ⟨152063891246144632598600237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101375927497429755065733491 152063891246144632598600237)
    ·
      refine ⟨57023959217304237224475089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152063891246144632598600237 57023959217304237224475089)
      ·
        refine ⟨42767969412978177918356317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57023959217304237224475089 42767969412978177918356317)
        ·
          refine ⟨16037988529866816719383619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42767969412978177918356317 16037988529866816719383619)
          ·
            refine ⟨24056982794800225079075429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16037988529866816719383619 24056982794800225079075429)
            ·
              refine ⟨4510684274025042202326643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24056982794800225079075429 4510684274025042202326643)
              ·
                refine ⟨6766026411037563303489965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510684274025042202326643 6766026411037563303489965)
                ·
                  refine ⟨2537259904139086238808737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6766026411037563303489965 2537259904139086238808737)
                  ·
                    refine ⟨1902944928104314679106553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537259904139086238808737 1902944928104314679106553)
                    ·
                      refine ⟨1427208696078236009329915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902944928104314679106553 1427208696078236009329915)
                      ·
                        rfl

theorem cell23_2779479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_2779479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779479 prefixEnd_2779479 := by exact prefixLift 2779479
  have htrace : WordTrace (prefixWord ++ tailWord_2779479) baseStart_2779479 baseEnd_2779479 := by
    simpa [prefixWord, tailWord_2779479, baseEnd_2779479] using wordTrace_append hprefix tailTrace_2779479
  have hstable : (prefixWord ++ tailWord_2779479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779479).length < 2 ^ (prefixWord ++ tailWord_2779479).sum := by decide
  have hdescent : baseEnd_2779479 < baseStart_2779479 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779530 : List Nat := [3, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2]
def baseStart_2779530 : Nat := 118140960795 + 2779530 * 2 ^ 59
def prefixEnd_2779530 : Nat := 4983230072969 + 3 ^ 40 * 2779530 * 2
def baseEnd_2779530 : Nat := 1427234883591615309792181

theorem tailTrace_2779530 : CollatzResearch.WordTrace tailWord_2779530 prefixEnd_2779530 1427234883591615309792181 := by
  unfold tailWord_2779530
  simp only [CollatzResearch.WordTrace]
  refine ⟨25344446905061247693960011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67585191746829993850560029 25344446905061247693960011)
  ·
    refine ⟨38016670357591871540940017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25344446905061247693960011 38016670357591871540940017)
    ·
      refine ⟨28512502768193903655705013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38016670357591871540940017 28512502768193903655705013)
      ·
        refine ⟨2673047134518178467722345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 28512502768193903655705013 2673047134518178467722345)
        ·
          refine ⟨2004785350888633850791759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673047134518178467722345 2004785350888633850791759)
          ·
            refine ⟨3007178026332950776187639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004785350888633850791759 3007178026332950776187639)
            ·
              refine ⟨4510767039499426164281459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007178026332950776187639 4510767039499426164281459)
              ·
                refine ⟨6766150559249139246422189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4510767039499426164281459 6766150559249139246422189)
                ·
                  refine ⟨2537306459718427217408321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6766150559249139246422189 2537306459718427217408321)
                  ·
                    refine ⟨1902979844788820413056241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537306459718427217408321 1902979844788820413056241)
                    ·
                      refine ⟨1427234883591615309792181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1902979844788820413056241 1427234883591615309792181)
                      ·
                        rfl

theorem cell23_2779530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 1, 3, 2, 2].length) (baseStart_2779530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779530 prefixEnd_2779530 := by exact prefixLift 2779530
  have htrace : WordTrace (prefixWord ++ tailWord_2779530) baseStart_2779530 baseEnd_2779530 := by
    simpa [prefixWord, tailWord_2779530, baseEnd_2779530] using wordTrace_append hprefix tailTrace_2779530
  have hstable : (prefixWord ++ tailWord_2779530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779530).length < 2 ^ (prefixWord ++ tailWord_2779530).sum := by decide
  have hdescent : baseEnd_2779530 < baseStart_2779530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779546 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3]
def baseStart_2779546 : Nat := 118140960795 + 2779546 * 2 ^ 59
def prefixEnd_2779546 : Nat := 4983230072969 + 3 ^ 40 * 2779546 * 2
def baseEnd_2779546 : Nat := 1427243099282087247192107

theorem tailTrace_2779546 : CollatzResearch.WordTrace tailWord_2779546 prefixEnd_2779546 1427243099282087247192107 := by
  unfold tailWord_2779546
  simp only [CollatzResearch.WordTrace]
  refine ⟨25344592797046756377105623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67585580792124683672281661 25344592797046756377105623)
  ·
    refine ⟨38016889195570134565658435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25344592797046756377105623 38016889195570134565658435)
    ·
      refine ⟨57025333793355201848487653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38016889195570134565658435 57025333793355201848487653)
      ·
        refine ⟨10692250086254100346591435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57025333793355201848487653 10692250086254100346591435)
        ·
          refine ⟨16038375129381150519887153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10692250086254100346591435 16038375129381150519887153)
          ·
            refine ⟨12028781347035862889915365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16038375129381150519887153 12028781347035862889915365)
            ·
              refine ⟨2255396502569224291859131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12028781347035862889915365 2255396502569224291859131)
              ·
                refine ⟨3383094753853836437788697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255396502569224291859131 3383094753853836437788697)
                ·
                  refine ⟨2537321065390377328341523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383094753853836437788697 2537321065390377328341523)
                  ·
                    refine ⟨3805981598085565992512285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2537321065390377328341523 3805981598085565992512285)
                    ·
                      refine ⟨1427243099282087247192107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3805981598085565992512285 1427243099282087247192107)
                      ·
                        rfl

theorem cell23_2779546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_2779546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779546 prefixEnd_2779546 := by exact prefixLift 2779546
  have htrace : WordTrace (prefixWord ++ tailWord_2779546) baseStart_2779546 baseEnd_2779546 := by
    simpa [prefixWord, tailWord_2779546, baseEnd_2779546] using wordTrace_append hprefix tailTrace_2779546
  have hstable : (prefixWord ++ tailWord_2779546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779546).length < 2 ^ (prefixWord ++ tailWord_2779546).sum := by decide
  have hdescent : baseEnd_2779546 < baseStart_2779546 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779555 : List Nat := [1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5]
def baseStart_2779555 : Nat := 118140960795 + 2779555 * 2 ^ 59
def prefixEnd_2779555 : Nat := 4983230072969 + 3 ^ 40 * 2779555 * 2
def baseEnd_2779555 : Nat := 1427247720607977711979565

theorem tailTrace_2779555 : CollatzResearch.WordTrace tailWord_2779555 prefixEnd_2779555 1427247720607977711979565 := by
  unfold tailWord_2779555
  simp only [CollatzResearch.WordTrace]
  refine ⟨101378699445154420045500119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67585799630102946697000079 101378699445154420045500119)
  ·
    refine ⟨152068049167731630068250179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101378699445154420045500119 152068049167731630068250179)
    ·
      refine ⟨228102073751597445102375269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152068049167731630068250179 228102073751597445102375269)
      ·
        refine ⟨42769138828424520956695363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 228102073751597445102375269 42769138828424520956695363)
        ·
          refine ⟨64153708242636781435043045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42769138828424520956695363 64153708242636781435043045)
          ·
            refine ⟨12028820295494396519070571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 64153708242636781435043045 12028820295494396519070571)
            ·
              refine ⟨18043230443241594778605857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12028820295494396519070571 18043230443241594778605857)
              ·
                refine ⟨13532422832431196083954393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18043230443241594778605857 13532422832431196083954393)
                ·
                  refine ⟨10149317124323397062965795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13532422832431196083954393 10149317124323397062965795)
                  ·
                    refine ⟨15223975686485095594448693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10149317124323397062965795 15223975686485095594448693)
                    ·
                      refine ⟨1427247720607977711979565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 15223975686485095594448693 1427247720607977711979565)
                      ·
                        rfl

theorem cell23_2779555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_2779555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779555 prefixEnd_2779555 := by exact prefixLift 2779555
  have htrace : WordTrace (prefixWord ++ tailWord_2779555) baseStart_2779555 baseEnd_2779555 := by
    simpa [prefixWord, tailWord_2779555, baseEnd_2779555] using wordTrace_append hprefix tailTrace_2779555
  have hstable : (prefixWord ++ tailWord_2779555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779555).length < 2 ^ (prefixWord ++ tailWord_2779555).sum := by decide
  have hdescent : baseEnd_2779555 < baseStart_2779555 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779569 : List Nat := [1, 2, 2, 4, 1, 3, 1, 2, 1, 4, 2]
def baseStart_2779569 : Nat := 118140960795 + 2779569 * 2 ^ 59
def prefixEnd_2779569 : Nat := 4983230072969 + 3 ^ 40 * 2779569 * 2
def baseEnd_2779569 : Nat := 1427254909337140657204501

theorem tailTrace_2779569 : CollatzResearch.WordTrace tailWord_2779569 prefixEnd_2779569 1427254909337140657204501 := by
  unfold tailWord_2779569
  simp only [CollatzResearch.WordTrace]
  refine ⟨101379210067103700436509761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67586140044735800291006507 101379210067103700436509761)
  ·
    refine ⟨76034407550327775327382321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101379210067103700436509761 76034407550327775327382321)
    ·
      refine ⟨57025805662745831495536741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76034407550327775327382321 57025805662745831495536741)
      ·
        refine ⟨10692338561764843405413139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57025805662745831495536741 10692338561764843405413139)
        ·
          refine ⟨16038507842647265108119709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10692338561764843405413139 16038507842647265108119709)
          ·
            refine ⟨6014440440992724415544891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16038507842647265108119709 6014440440992724415544891)
            ·
              refine ⟨9021660661489086623317337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6014440440992724415544891 9021660661489086623317337)
              ·
                refine ⟨6766245496116814967488003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9021660661489086623317337 6766245496116814967488003)
                ·
                  refine ⟨10149368244175222451232005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766245496116814967488003 10149368244175222451232005)
                  ·
                    refine ⟨1903006545782854209606001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10149368244175222451232005 1903006545782854209606001)
                    ·
                      refine ⟨1427254909337140657204501, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903006545782854209606001 1427254909337140657204501)
                      ·
                        rfl

theorem cell23_2779569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_2779569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779569 prefixEnd_2779569 := by exact prefixLift 2779569
  have htrace : WordTrace (prefixWord ++ tailWord_2779569) baseStart_2779569 baseEnd_2779569 := by
    simpa [prefixWord, tailWord_2779569, baseEnd_2779569] using wordTrace_append hprefix tailTrace_2779569
  have hstable : (prefixWord ++ tailWord_2779569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779569).length < 2 ^ (prefixWord ++ tailWord_2779569).sum := by decide
  have hdescent : baseEnd_2779569 < baseStart_2779569 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779573 : List Nat := [1, 3, 3, 2, 3, 1, 3, 1, 1, 3, 2]
def baseStart_2779573 : Nat := 118140960795 + 2779573 * 2 ^ 59
def prefixEnd_2779573 : Nat := 4983230072969 + 3 ^ 40 * 2779573 * 2
def baseEnd_2779573 : Nat := 1427256963259758641554483

theorem tailTrace_2779573 : CollatzResearch.WordTrace tailWord_2779573 prefixEnd_2779573 1427256963259758641554483 := by
  unfold tailWord_2779573
  simp only [CollatzResearch.WordTrace]
  refine ⟨101379355959089209119655373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67586237306059472746436915 101379355959089209119655373)
  ·
    refine ⟨38017258484658453419870765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101379355959089209119655373 38017258484658453419870765)
    ·
      refine ⟨14256471931746920032451537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 38017258484658453419870765 14256471931746920032451537)
      ·
        refine ⟨10692353948810190024338653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14256471931746920032451537 10692353948810190024338653)
        ·
          refine ⟨4009632730803821259126995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10692353948810190024338653 4009632730803821259126995)
          ·
            refine ⟨6014449096205731888690493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4009632730803821259126995 6014449096205731888690493)
            ·
              refine ⟨2255418411077149458258935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6014449096205731888690493 2255418411077149458258935)
              ·
                refine ⟨3383127616615724187388403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255418411077149458258935 3383127616615724187388403)
                ·
                  refine ⟨5074691424923586281082605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383127616615724187388403 5074691424923586281082605)
                  ·
                    refine ⟨1903009284346344855405977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5074691424923586281082605 1903009284346344855405977)
                    ·
                      refine ⟨1427256963259758641554483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903009284346344855405977 1427256963259758641554483)
                      ·
                        rfl

theorem cell23_2779573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 1, 3, 2].length) (baseStart_2779573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779573 prefixEnd_2779573 := by exact prefixLift 2779573
  have htrace : WordTrace (prefixWord ++ tailWord_2779573) baseStart_2779573 baseEnd_2779573 := by
    simpa [prefixWord, tailWord_2779573, baseEnd_2779573] using wordTrace_append hprefix tailTrace_2779573
  have hstable : (prefixWord ++ tailWord_2779573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779573).length < 2 ^ (prefixWord ++ tailWord_2779573).sum := by decide
  have hdescent : baseEnd_2779573 < baseStart_2779573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779637 : List Nat := [1, 3, 5, 1, 3, 1, 1, 2, 2, 2, 2]
def baseStart_2779637 : Nat := 118140960795 + 2779637 * 2 ^ 59
def prefixEnd_2779637 : Nat := 4983230072969 + 3 ^ 40 * 2779637 * 2
def baseEnd_2779637 : Nat := 1427289826021646391154189

theorem tailTrace_2779637 : CollatzResearch.WordTrace tailWord_2779637 prefixEnd_2779637 1427289826021646391154189 := by
  unfold tailWord_2779637
  simp only [CollatzResearch.WordTrace]
  refine ⟨101381690230857348049985165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67587793487238232033323443 101381690230857348049985165)
  ·
    refine ⟨38018133836571505518744437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101381690230857348049985165 38018133836571505518744437)
    ·
      refine ⟨3564200047178578642382291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 38018133836571505518744437 3564200047178578642382291)
      ·
        refine ⟨5346300070767867963573437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564200047178578642382291 5346300070767867963573437)
        ·
          refine ⟨2004862526537950486340039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5346300070767867963573437 2004862526537950486340039)
          ·
            refine ⟨3007293789806925729510059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2004862526537950486340039 3007293789806925729510059)
            ·
              refine ⟨4510940684710388594265089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007293789806925729510059 4510940684710388594265089)
              ·
                refine ⟨3383205513532791445698817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4510940684710388594265089 3383205513532791445698817)
                ·
                  refine ⟨2537404135149593584274113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383205513532791445698817 2537404135149593584274113)
                  ·
                    refine ⟨1903053101362195188205585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537404135149593584274113 1903053101362195188205585)
                    ·
                      refine ⟨1427289826021646391154189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903053101362195188205585 1427289826021646391154189)
                      ·
                        rfl

theorem cell23_2779637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_2779637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779637 prefixEnd_2779637 := by exact prefixLift 2779637
  have htrace : WordTrace (prefixWord ++ tailWord_2779637) baseStart_2779637 baseEnd_2779637 := by
    simpa [prefixWord, tailWord_2779637, baseEnd_2779637] using wordTrace_append hprefix tailTrace_2779637
  have hstable : (prefixWord ++ tailWord_2779637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779637).length < 2 ^ (prefixWord ++ tailWord_2779637).sum := by decide
  have hdescent : baseEnd_2779637 < baseStart_2779637 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779654 : List Nat := [6, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2]
def baseStart_2779654 : Nat := 118140960795 + 2779654 * 2 ^ 59
def prefixEnd_2779654 : Nat := 4983230072969 + 3 ^ 40 * 2779654 * 2
def baseEnd_2779654 : Nat := 1427298555192772824641611

theorem tailTrace_2779654 : CollatzResearch.WordTrace tailWord_2779654 prefixEnd_2779654 1427298555192772824641611 := by
  unfold tailWord_2779654
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168197195993617498542313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 67588206847863839968902677 3168197195993617498542313)
  ·
    refine ⟨2376147896995213123906735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3168197195993617498542313 2376147896995213123906735)
    ·
      refine ⟨3564221845492819685860103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376147896995213123906735 3564221845492819685860103)
      ·
        refine ⟨5346332768239229528790155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564221845492819685860103 5346332768239229528790155)
        ·
          refine ⟨8019499152358844293185233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5346332768239229528790155 8019499152358844293185233)
          ·
            refine ⟨6014624364269133219888925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8019499152358844293185233 6014624364269133219888925)
            ·
              refine ⟨2255484136600924957458347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6014624364269133219888925 2255484136600924957458347)
              ·
                refine ⟨3383226204901387436187521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255484136600924957458347 3383226204901387436187521)
                ·
                  refine ⟨2537419653676040577140641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383226204901387436187521 2537419653676040577140641)
                  ·
                    refine ⟨1903064740257030432855481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537419653676040577140641 1903064740257030432855481)
                    ·
                      refine ⟨1427298555192772824641611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903064740257030432855481 1427298555192772824641611)
                      ·
                        rfl

theorem cell23_2779654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2].length) (baseStart_2779654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779654 prefixEnd_2779654 := by exact prefixLift 2779654
  have htrace : WordTrace (prefixWord ++ tailWord_2779654) baseStart_2779654 baseEnd_2779654 := by
    simpa [prefixWord, tailWord_2779654, baseEnd_2779654] using wordTrace_append hprefix tailTrace_2779654
  have hstable : (prefixWord ++ tailWord_2779654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779654).length < 2 ^ (prefixWord ++ tailWord_2779654).sum := by decide
  have hdescent : baseEnd_2779654 < baseStart_2779654 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779659 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 2, 4, 2]
def baseStart_2779659 : Nat := 118140960795 + 2779659 * 2 ^ 59
def prefixEnd_2779659 : Nat := 4983230072969 + 3 ^ 40 * 2779659 * 2
def baseEnd_2779659 : Nat := 1427301122596045305079087

theorem tailTrace_2779659 : CollatzResearch.WordTrace tailWord_2779659 prefixEnd_2779659 1427301122596045305079087 := by
  unfold tailWord_2779659
  simp only [CollatzResearch.WordTrace]
  refine ⟨101382492636777645807286031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67588328424518430538190687 101382492636777645807286031)
  ·
    refine ⟨152073738955166468710929047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101382492636777645807286031 152073738955166468710929047)
    ·
      refine ⟨228110608432749703066393571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152073738955166468710929047 228110608432749703066393571)
      ·
        refine ⟨342165912649124554599590357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228110608432749703066393571 342165912649124554599590357)
        ·
          refine ⟨8019513577713856748427899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 342165912649124554599590357 8019513577713856748427899)
          ·
            refine ⟨12029270366570785122641849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8019513577713856748427899 12029270366570785122641849)
            ·
              refine ⟨9021952774928088841981387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12029270366570785122641849 9021952774928088841981387)
              ·
                refine ⟨13532929162392133262972081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9021952774928088841981387 13532929162392133262972081)
                ·
                  refine ⟨10149696871794099947229061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 13532929162392133262972081 10149696871794099947229061)
                  ·
                    refine ⟨1903068163461393740105449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10149696871794099947229061 1903068163461393740105449)
                    ·
                      refine ⟨1427301122596045305079087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903068163461393740105449 1427301122596045305079087)
                      ·
                        rfl

theorem cell23_2779659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 2, 4, 2].length) (baseStart_2779659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779659 prefixEnd_2779659 := by exact prefixLift 2779659
  have htrace : WordTrace (prefixWord ++ tailWord_2779659) baseStart_2779659 baseEnd_2779659 := by
    simpa [prefixWord, tailWord_2779659, baseEnd_2779659] using wordTrace_append hprefix tailTrace_2779659
  have hstable : (prefixWord ++ tailWord_2779659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779659).length < 2 ^ (prefixWord ++ tailWord_2779659).sum := by decide
  have hdescent : baseEnd_2779659 < baseStart_2779659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779729 : List Nat := [1, 2, 2, 1, 3, 3, 3, 2, 1, 5]
def baseStart_2779729 : Nat := 118140960795 + 2779729 * 2 ^ 59
def prefixEnd_2779729 : Nat := 4983230072969 + 3 ^ 40 * 2779729 * 2
def baseEnd_2779729 : Nat := 475779022080620010401255

theorem tailTrace_2779729 : CollatzResearch.WordTrace tailWord_2779729 prefixEnd_2779729 475779022080620010401255 := by
  unfold tailWord_2779729
  simp only [CollatzResearch.WordTrace]
  refine ⟨101385045746524047762334241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67590030497682698508222827 101385045746524047762334241)
  ·
    refine ⟨76038784309893035821750681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101385045746524047762334241 76038784309893035821750681)
    ·
      refine ⟨57029088232419776866313011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76038784309893035821750681 57029088232419776866313011)
      ·
        refine ⟨85543632348629665299469517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57029088232419776866313011 85543632348629665299469517)
        ·
          refine ⟨32078862130736124487301069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 85543632348629665299469517 32078862130736124487301069)
          ·
            refine ⟨12029573299026046682737901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 32078862130736124487301069 12029573299026046682737901)
            ·
              refine ⟨4511089987134767506026713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12029573299026046682737901 4511089987134767506026713)
              ·
                refine ⟨3383317490351075629520035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4511089987134767506026713 3383317490351075629520035)
                ·
                  refine ⟨5074976235526613444280053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383317490351075629520035 5074976235526613444280053)
                  ·
                    refine ⟨475779022080620010401255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5074976235526613444280053 475779022080620010401255)
                    ·
                      rfl

theorem cell23_2779729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 3, 3, 2, 1, 5].length) (baseStart_2779729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779729 prefixEnd_2779729 := by exact prefixLift 2779729
  have htrace : WordTrace (prefixWord ++ tailWord_2779729) baseStart_2779729 baseEnd_2779729 := by
    simpa [prefixWord, tailWord_2779729, baseEnd_2779729] using wordTrace_append hprefix tailTrace_2779729
  have hstable : (prefixWord ++ tailWord_2779729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779729).length < 2 ^ (prefixWord ++ tailWord_2779729).sum := by decide
  have hdescent : baseEnd_2779729 < baseStart_2779729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779759 : List Nat := [1, 1, 2, 1, 3, 2, 3, 4, 2, 4]
def baseStart_2779759 : Nat := 118140960795 + 2779759 * 2 ^ 59
def prefixEnd_2779759 : Nat := 4983230072969 + 3 ^ 40 * 2779759 * 2
def baseEnd_2779759 : Nat := 475784156887164971276209

theorem tailTrace_2779759 : CollatzResearch.WordTrace tailWord_2779759 prefixEnd_2779759 475784156887164971276209 := by
  unfold tailWord_2779759
  simp only [CollatzResearch.WordTrace]
  refine ⟨101386139936415362885926331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67590759957610241923950887 101386139936415362885926331)
  ·
    refine ⟨152079209904623044328889497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101386139936415362885926331 152079209904623044328889497)
    ·
      refine ⟨114059407428467283246667123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 152079209904623044328889497 114059407428467283246667123)
      ·
        refine ⟨171089111142700924870000685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114059407428467283246667123 171089111142700924870000685)
        ·
          refine ⟨64158416678512846826250257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 171089111142700924870000685 64158416678512846826250257)
          ·
            refine ⟨48118812508884635119687693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64158416678512846826250257 48118812508884635119687693)
            ·
              refine ⟨18044554690831738169882885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48118812508884635119687693 18044554690831738169882885)
              ·
                refine ⟨3383354004530950906853041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18044554690831738169882885 3383354004530950906853041)
                ·
                  refine ⟨2537515503398213180139781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383354004530950906853041 2537515503398213180139781)
                  ·
                    refine ⟨475784156887164971276209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2537515503398213180139781 475784156887164971276209)
                    ·
                      rfl

theorem cell23_2779759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 4, 2, 4].length) (baseStart_2779759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779759 prefixEnd_2779759 := by exact prefixLift 2779759
  have htrace : WordTrace (prefixWord ++ tailWord_2779759) baseStart_2779759 baseEnd_2779759 := by
    simpa [prefixWord, tailWord_2779759, baseEnd_2779759] using wordTrace_append hprefix tailTrace_2779759
  have hstable : (prefixWord ++ tailWord_2779759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779759).length < 2 ^ (prefixWord ++ tailWord_2779759).sum := by decide
  have hdescent : baseEnd_2779759 < baseStart_2779759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779769 : List Nat := [1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 3]
def baseStart_2779769 : Nat := 118140960795 + 2779769 * 2 ^ 59
def prefixEnd_2779769 : Nat := 4983230072969 + 3 ^ 40 * 2779769 * 2
def baseEnd_2779769 : Nat := 1427357605468039874703581

theorem tailTrace_2779769 : CollatzResearch.WordTrace tailWord_2779769 prefixEnd_2779769 1427357605468039874703581 := by
  unfold tailWord_2779769
  simp only [CollatzResearch.WordTrace]
  refine ⟨101386504666379134593790361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67591003110919423062526907 101386504666379134593790361)
  ·
    refine ⟨76039878499784350945342771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101386504666379134593790361 76039878499784350945342771)
    ·
      refine ⟨114059817749676526418014157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76039878499784350945342771 114059817749676526418014157)
      ·
        refine ⟨42772431656128697406755309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114059817749676526418014157 42772431656128697406755309)
        ·
          refine ⟨16039661871048261527533241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42772431656128697406755309 16039661871048261527533241)
          ·
            refine ⟨12029746403286196145649931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16039661871048261527533241 12029746403286196145649931)
            ·
              refine ⟨18044619604929294218474897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12029746403286196145649931 18044619604929294218474897)
              ·
                refine ⟨13533464703696970663856173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18044619604929294218474897 13533464703696970663856173)
                ·
                  refine ⟨5075049263886363998946065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 13533464703696970663856173 5075049263886363998946065)
                  ·
                    refine ⟨3806286947914772999209549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5075049263886363998946065 3806286947914772999209549)
                    ·
                      refine ⟨1427357605468039874703581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3806286947914772999209549 1427357605468039874703581)
                      ·
                        rfl

theorem cell23_2779769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 1, 2, 3, 2, 3].length) (baseStart_2779769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779769 prefixEnd_2779769 := by exact prefixLift 2779769
  have htrace : WordTrace (prefixWord ++ tailWord_2779769) baseStart_2779769 baseEnd_2779769 := by
    simpa [prefixWord, tailWord_2779769, baseEnd_2779769] using wordTrace_append hprefix tailTrace_2779769
  have hstable : (prefixWord ++ tailWord_2779769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779769).length < 2 ^ (prefixWord ++ tailWord_2779769).sum := by decide
  have hdescent : baseEnd_2779769 < baseStart_2779769 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779772 : List Nat := [2, 2, 2, 1, 1, 2, 5, 8]
def baseStart_2779772 : Nat := 118140960795 + 2779772 * 2 ^ 59
def prefixEnd_2779772 : Nat := 4983230072969 + 3 ^ 40 * 2779772 * 2
def baseEnd_2779772 : Nat := 52865153552222346776521

theorem tailTrace_2779772 : CollatzResearch.WordTrace tailWord_2779772 prefixEnd_2779772 52865153552222346776521 := by
  unfold tailWord_2779772
  simp only [CollatzResearch.WordTrace]
  refine ⟨50693307042684133053074785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67591076056912177404099713 50693307042684133053074785)
  ·
    refine ⟨38019980282013099789806089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 50693307042684133053074785 38019980282013099789806089)
    ·
      refine ⟨28514985211509824842354567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38019980282013099789806089 28514985211509824842354567)
      ·
        refine ⟨42772477817264737263531851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28514985211509824842354567 42772477817264737263531851)
        ·
          refine ⟨64158716725897105895297777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42772477817264737263531851 64158716725897105895297777)
          ·
            refine ⟨48119037544422829421473333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64158716725897105895297777 48119037544422829421473333)
            ·
              refine ⟨4511159769789640258263125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 48119037544422829421473333 4511159769789640258263125)
              ·
                refine ⟨52865153552222346776521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4511159769789640258263125 52865153552222346776521)
                ·
                  rfl

theorem cell23_2779772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 8].length) (baseStart_2779772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779772 prefixEnd_2779772 := by exact prefixLift 2779772
  have htrace : WordTrace (prefixWord ++ tailWord_2779772) baseStart_2779772 baseEnd_2779772 := by
    simpa [prefixWord, tailWord_2779772, baseEnd_2779772] using wordTrace_append hprefix tailTrace_2779772
  have hstable : (prefixWord ++ tailWord_2779772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779772).length < 2 ^ (prefixWord ++ tailWord_2779772).sum := by decide
  have hdescent : baseEnd_2779772 < baseStart_2779772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779796 : List Nat := [2, 4, 2, 2, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2779796 : Nat := 118140960795 + 2779796 * 2 ^ 59
def prefixEnd_2779796 : Nat := 4983230072969 + 3 ^ 40 * 2779796 * 2
def baseEnd_2779796 : Nat := 1427371469445711269065957

theorem tailTrace_2779796 : CollatzResearch.WordTrace tailWord_2779796 prefixEnd_2779796 1427371469445711269065957 := by
  unfold tailWord_2779796
  simp only [CollatzResearch.WordTrace]
  refine ⟨50693744718640659102511621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67591659624854212136682161 50693744718640659102511621)
  ·
    refine ⟨9505077134745123581720929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 50693744718640659102511621 9505077134745123581720929)
    ·
      refine ⟨7128807851058842686290697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9505077134745123581720929 7128807851058842686290697)
      ·
        refine ⟨5346605888294132014718023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7128807851058842686290697 5346605888294132014718023)
        ·
          refine ⟨8019908832441198022077035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5346605888294132014718023 8019908832441198022077035)
          ·
            refine ⟨12029863248661797033115553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8019908832441198022077035 12029863248661797033115553)
            ·
              refine ⟨9022397436496347774836665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12029863248661797033115553 9022397436496347774836665)
              ·
                refine ⟨6766798077372260831127499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9022397436496347774836665 6766798077372260831127499)
                ·
                  refine ⟨10150197116058391246691249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766798077372260831127499 10150197116058391246691249)
                  ·
                    refine ⟨7612647837043793435018437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10150197116058391246691249 7612647837043793435018437)
                    ·
                      refine ⟨1427371469445711269065957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7612647837043793435018437 1427371469445711269065957)
                      ·
                        rfl

theorem cell23_2779796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2779796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779796 prefixEnd_2779796 := by exact prefixLift 2779796
  have htrace : WordTrace (prefixWord ++ tailWord_2779796) baseStart_2779796 baseEnd_2779796 := by
    simpa [prefixWord, tailWord_2779796, baseEnd_2779796] using wordTrace_append hprefix tailTrace_2779796
  have hstable : (prefixWord ++ tailWord_2779796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779796).length < 2 ^ (prefixWord ++ tailWord_2779796).sum := by decide
  have hdescent : baseEnd_2779796 < baseStart_2779796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779799 : List Nat := [1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 3]
def baseStart_2779799 : Nat := 118140960795 + 2779799 * 2 ^ 59
def prefixEnd_2779799 : Nat := 4983230072969 + 3 ^ 40 * 2779799 * 2
def baseEnd_2779799 : Nat := 1427373009887674757328443

theorem tailTrace_2779799 : CollatzResearch.WordTrace tailWord_2779799 prefixEnd_2779799 1427373009887674757328443 := by
  unfold tailWord_2779799
  simp only [CollatzResearch.WordTrace]
  refine ⟨101387598856270449717382451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67591732570846966478254967 101387598856270449717382451)
  ·
    refine ⟨152081398284405674576073677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101387598856270449717382451 152081398284405674576073677)
    ·
      refine ⟨57030524356652127966027629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 152081398284405674576073677 57030524356652127966027629)
      ·
        refine ⟨21386446633744547987260361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 57030524356652127966027629 21386446633744547987260361)
        ·
          refine ⟨16039834975308410990445271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21386446633744547987260361 16039834975308410990445271)
          ·
            refine ⟨24059752462962616485667907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16039834975308410990445271 24059752462962616485667907)
            ·
              refine ⟨36089628694443924728501861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24059752462962616485667907 36089628694443924728501861)
              ·
                refine ⟨6766805380208235886594099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 36089628694443924728501861 6766805380208235886594099)
                ·
                  refine ⟨10150208070312353829891149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766805380208235886594099 10150208070312353829891149)
                  ·
                    refine ⟨3806328026367132686209181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10150208070312353829891149 3806328026367132686209181)
                    ·
                      refine ⟨1427373009887674757328443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3806328026367132686209181 1427373009887674757328443)
                      ·
                        rfl

theorem cell23_2779799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_2779799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779799 prefixEnd_2779799 := by exact prefixLift 2779799
  have htrace : WordTrace (prefixWord ++ tailWord_2779799) baseStart_2779799 baseEnd_2779799 := by
    simpa [prefixWord, tailWord_2779799, baseEnd_2779799] using wordTrace_append hprefix tailTrace_2779799
  have hstable : (prefixWord ++ tailWord_2779799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779799).length < 2 ^ (prefixWord ++ tailWord_2779799).sum := by decide
  have hdescent : baseEnd_2779799 < baseStart_2779799 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779800 : List Nat := [2, 1, 2, 4, 1, 1, 4, 3, 1, 2, 2]
def baseStart_2779800 : Nat := 118140960795 + 2779800 * 2 ^ 59
def prefixEnd_2779800 : Nat := 4983230072969 + 3 ^ 40 * 2779800 * 2
def baseEnd_2779800 : Nat := 1427373523368329253415939

theorem tailTrace_2779800 : CollatzResearch.WordTrace tailWord_2779800 prefixEnd_2779800 1427373523368329253415939 := by
  unfold tailWord_2779800
  simp only [CollatzResearch.WordTrace]
  refine ⟨50693817664633413444084427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67591756886177884592112569 50693817664633413444084427)
  ·
    refine ⟨76040726496950120166126641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50693817664633413444084427 76040726496950120166126641)
    ·
      refine ⟨57030544872712590124594981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76040726496950120166126641 57030544872712590124594981)
      ·
        refine ⟨10693227163633610648361559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 57030544872712590124594981 10693227163633610648361559)
        ·
          refine ⟨16039840745450415972542339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10693227163633610648361559 16039840745450415972542339)
          ·
            refine ⟨24059761118175623958813509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16039840745450415972542339 24059761118175623958813509)
            ·
              refine ⟨4511205209657929492277533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24059761118175623958813509 4511205209657929492277533)
              ·
                refine ⟨1691701953621723559604075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4511205209657929492277533 1691701953621723559604075)
                ·
                  refine ⟨2537552930432585339406113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1691701953621723559604075 2537552930432585339406113)
                  ·
                    refine ⟨1903164697824439004554585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537552930432585339406113 1903164697824439004554585)
                    ·
                      refine ⟨1427373523368329253415939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903164697824439004554585 1427373523368329253415939)
                      ·
                        rfl

theorem cell23_2779800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_2779800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779800 prefixEnd_2779800 := by exact prefixLift 2779800
  have htrace : WordTrace (prefixWord ++ tailWord_2779800) baseStart_2779800 baseEnd_2779800 := by
    simpa [prefixWord, tailWord_2779800, baseEnd_2779800] using wordTrace_append hprefix tailTrace_2779800
  have hstable : (prefixWord ++ tailWord_2779800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779800).length < 2 ^ (prefixWord ++ tailWord_2779800).sum := by decide
  have hdescent : baseEnd_2779800 < baseStart_2779800 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779830 : List Nat := [5, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4]
def baseStart_2779830 : Nat := 118140960795 + 2779830 * 2 ^ 59
def prefixEnd_2779830 : Nat := 4983230072969 + 3 ^ 40 * 2779830 * 2
def baseEnd_2779830 : Nat := 1427388927787964136040801

theorem tailTrace_2779830 : CollatzResearch.WordTrace tailWord_2779830 prefixEnd_2779830 1427388927787964136040801 := by
  unfold tailWord_2779830
  simp only [CollatzResearch.WordTrace]
  refine ⟨6336795594947383875735059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67592486346105428007840629 6336795594947383875735059)
  ·
    refine ⟨9505193392421075813602589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6336795594947383875735059 9505193392421075813602589)
    ·
      refine ⟨3564447522157903430100971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9505193392421075813602589 3564447522157903430100971)
      ·
        refine ⟨5346671283236855145151457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564447522157903430100971 5346671283236855145151457)
        ·
          refine ⟨4010003462427641358863593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5346671283236855145151457 4010003462427641358863593)
          ·
            refine ⟨3007502596820731019147695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4010003462427641358863593 3007502596820731019147695)
            ·
              refine ⟨4511253895231096528721543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3007502596820731019147695 4511253895231096528721543)
              ·
                refine ⟨6766880842846644793082315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4511253895231096528721543 6766880842846644793082315)
                ·
                  refine ⟨10150321264269967189623473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6766880842846644793082315 10150321264269967189623473)
                  ·
                    refine ⟨7612740948202475392217605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10150321264269967189623473 7612740948202475392217605)
                    ·
                      refine ⟨1427388927787964136040801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7612740948202475392217605 1427388927787964136040801)
                      ·
                        rfl

theorem cell23_2779830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_2779830 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779830 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779830 prefixEnd_2779830 := by exact prefixLift 2779830
  have htrace : WordTrace (prefixWord ++ tailWord_2779830) baseStart_2779830 baseEnd_2779830 := by
    simpa [prefixWord, tailWord_2779830, baseEnd_2779830] using wordTrace_append hprefix tailTrace_2779830
  have hstable : (prefixWord ++ tailWord_2779830).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779830).length < 2 ^ (prefixWord ++ tailWord_2779830).sum := by decide
  have hdescent : baseEnd_2779830 < baseStart_2779830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779872 : List Nat := [2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9]
def baseStart_2779872 : Nat := 118140960795 + 2779872 * 2 ^ 59
def prefixEnd_2779872 : Nat := 4983230072969 + 3 ^ 40 * 2779872 * 2
def baseEnd_2779872 : Nat := 1427410493975452971715607

theorem tailTrace_2779872 : CollatzResearch.WordTrace tailWord_2779872 prefixEnd_2779872 1427410493975452971715607 := by
  unfold tailWord_2779872
  simp only [CollatzResearch.WordTrace]
  refine ⟨50695130692502991592394935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67593507590003988789859913 50695130692502991592394935)
  ·
    refine ⟨76042696038754487388592403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50695130692502991592394935 76042696038754487388592403)
    ·
      refine ⟨114064044058131731082888605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76042696038754487388592403 114064044058131731082888605)
      ·
        refine ⟨42774016521799399156083227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 114064044058131731082888605 42774016521799399156083227)
        ·
          refine ⟨64161024782699098734124841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42774016521799399156083227 64161024782699098734124841)
          ·
            refine ⟨48120768587024324050593631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64161024782699098734124841 48120768587024324050593631)
            ·
              refine ⟨72181152880536486075890447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48120768587024324050593631 72181152880536486075890447)
              ·
                refine ⟨108271729320804729113835671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 72181152880536486075890447 108271729320804729113835671)
                ·
                  refine ⟨162407593981207093670753507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 108271729320804729113835671 162407593981207093670753507)
                  ·
                    refine ⟨243611390971810640506130261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 162407593981207093670753507 243611390971810640506130261)
                    ·
                      refine ⟨1427410493975452971715607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 243611390971810640506130261 1427410493975452971715607)
                      ·
                        rfl

theorem cell23_2779872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_2779872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779872 prefixEnd_2779872 := by exact prefixLift 2779872
  have htrace : WordTrace (prefixWord ++ tailWord_2779872) baseStart_2779872 baseEnd_2779872 := by
    simpa [prefixWord, tailWord_2779872, baseEnd_2779872] using wordTrace_append hprefix tailTrace_2779872
  have hstable : (prefixWord ++ tailWord_2779872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779872).length < 2 ^ (prefixWord ++ tailWord_2779872).sum := by decide
  have hdescent : baseEnd_2779872 < baseStart_2779872 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779873 : List Nat := [1, 2, 3, 1, 4, 1, 2, 1, 4, 2, 2]
def baseStart_2779873 : Nat := 118140960795 + 2779873 * 2 ^ 59
def prefixEnd_2779873 : Nat := 4983230072969 + 3 ^ 40 * 2779873 * 2
def baseEnd_2779873 : Nat := 1427411007456107467803103

theorem tailTrace_2779873 : CollatzResearch.WordTrace tailWord_2779873 prefixEnd_2779873 1427411007456107467803103 := by
  unfold tailWord_2779873
  simp only [CollatzResearch.WordTrace]
  refine ⟨101390297858002360355576273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67593531905334906903717515 101390297858002360355576273)
  ·
    refine ⟨76042723393501770266682205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101390297858002360355576273 76042723393501770266682205)
    ·
      refine ⟨28516021272563163850005827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76042723393501770266682205 28516021272563163850005827)
      ·
        refine ⟨42774031908844745775008741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28516021272563163850005827 42774031908844745775008741)
        ·
          refine ⟨8020130982908389832814139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 42774031908844745775008741 8020130982908389832814139)
          ·
            refine ⟨12030196474362584749221209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8020130982908389832814139 12030196474362584749221209)
            ·
              refine ⟨9022647355771938561915907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12030196474362584749221209 9022647355771938561915907)
              ·
                refine ⟨13533971033657907842873861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9022647355771938561915907 13533971033657907842873861)
                ·
                  refine ⟨2537619568810857720538849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13533971033657907842873861 2537619568810857720538849)
                  ·
                    refine ⟨1903214676608143290404137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537619568810857720538849 1903214676608143290404137)
                    ·
                      refine ⟨1427411007456107467803103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903214676608143290404137 1427411007456107467803103)
                      ·
                        rfl

theorem cell23_2779873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 1, 2, 1, 4, 2, 2].length) (baseStart_2779873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779873 prefixEnd_2779873 := by exact prefixLift 2779873
  have htrace : WordTrace (prefixWord ++ tailWord_2779873) baseStart_2779873 baseEnd_2779873 := by
    simpa [prefixWord, tailWord_2779873, baseEnd_2779873] using wordTrace_append hprefix tailTrace_2779873
  have hstable : (prefixWord ++ tailWord_2779873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779873).length < 2 ^ (prefixWord ++ tailWord_2779873).sum := by decide
  have hdescent : baseEnd_2779873 < baseStart_2779873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779889 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 3]
def baseStart_2779889 : Nat := 118140960795 + 2779889 * 2 ^ 59
def prefixEnd_2779889 : Nat := 4983230072969 + 3 ^ 40 * 2779889 * 2
def baseEnd_2779889 : Nat := 1427419223146579405203029

theorem tailTrace_2779889 : CollatzResearch.WordTrace tailWord_2779889 prefixEnd_2779889 1427419223146579405203029 := by
  unfold tailWord_2779889
  simp only [CollatzResearch.WordTrace]
  refine ⟨101390881425944395088158721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67593920950629596725439147 101390881425944395088158721)
  ·
    refine ⟨76043161069458296316119041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101390881425944395088158721 76043161069458296316119041)
    ·
      refine ⟨57032370802093722237089281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 76043161069458296316119041 57032370802093722237089281)
      ·
        refine ⟨42774278101570291677816961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 57032370802093722237089281 42774278101570291677816961)
        ·
          refine ⟨32080708576177718758362721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42774278101570291677816961 32080708576177718758362721)
          ·
            refine ⟨24060531432133289068772041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32080708576177718758362721 24060531432133289068772041)
            ·
              refine ⟨18045398574099966801579031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24060531432133289068772041 18045398574099966801579031)
              ·
                refine ⟨27068097861149950202368547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18045398574099966801579031 27068097861149950202368547)
                ·
                  refine ⟨40602146791724925303552821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 27068097861149950202368547 40602146791724925303552821)
                  ·
                    refine ⟨3806451261724211747208077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 40602146791724925303552821 3806451261724211747208077)
                    ·
                      refine ⟨1427419223146579405203029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3806451261724211747208077 1427419223146579405203029)
                      ·
                        rfl

theorem cell23_2779889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_2779889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779889 prefixEnd_2779889 := by exact prefixLift 2779889
  have htrace : WordTrace (prefixWord ++ tailWord_2779889) baseStart_2779889 baseEnd_2779889 := by
    simpa [prefixWord, tailWord_2779889, baseEnd_2779889] using wordTrace_append hprefix tailTrace_2779889
  have hstable : (prefixWord ++ tailWord_2779889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779889).length < 2 ^ (prefixWord ++ tailWord_2779889).sum := by decide
  have hdescent : baseEnd_2779889 < baseStart_2779889 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779890 : List Nat := [3, 2, 1, 3, 1, 3, 1, 3, 2, 2, 2]
def baseStart_2779890 : Nat := 118140960795 + 2779890 * 2 ^ 59
def prefixEnd_2779890 : Nat := 4983230072969 + 3 ^ 40 * 2779890 * 2
def baseEnd_2779890 : Nat := 1427419736627233901290525

theorem tailTrace_2779890 : CollatzResearch.WordTrace tailWord_2779890 prefixEnd_2779890 1427419736627233901290525 := by
  unfold tailWord_2779890
  simp only [CollatzResearch.WordTrace]
  refine ⟨25347729474735193064736281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67593945265960514839296749 25347729474735193064736281)
  ·
    refine ⟨19010797106051394798552211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 25347729474735193064736281 19010797106051394798552211)
    ·
      refine ⟨28516195659077092197828317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19010797106051394798552211 28516195659077092197828317)
      ·
        refine ⟨10693573372153909574185619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28516195659077092197828317 10693573372153909574185619)
        ·
          refine ⟨16040360058230864361278429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10693573372153909574185619 16040360058230864361278429)
          ·
            refine ⟨6015135021836574135479411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16040360058230864361278429 6015135021836574135479411)
            ·
              refine ⟨9022702532754861203219117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015135021836574135479411 9022702532754861203219117)
              ·
                refine ⟨3383513449783072951207169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9022702532754861203219117 3383513449783072951207169)
                ·
                  refine ⟨2537635087337304713405377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3383513449783072951207169 2537635087337304713405377)
                  ·
                    refine ⟨1903226315502978535054033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2537635087337304713405377 1903226315502978535054033)
                    ·
                      refine ⟨1427419736627233901290525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903226315502978535054033 1427419736627233901290525)
                      ·
                        rfl

theorem cell23_2779890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 3, 2, 2, 2].length) (baseStart_2779890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779890 prefixEnd_2779890 := by exact prefixLift 2779890
  have htrace : WordTrace (prefixWord ++ tailWord_2779890) baseStart_2779890 baseEnd_2779890 := by
    simpa [prefixWord, tailWord_2779890, baseEnd_2779890] using wordTrace_append hprefix tailTrace_2779890
  have hstable : (prefixWord ++ tailWord_2779890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779890).length < 2 ^ (prefixWord ++ tailWord_2779890).sum := by decide
  have hdescent : baseEnd_2779890 < baseStart_2779890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779929 : List Nat := [1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 4]
def baseStart_2779929 : Nat := 118140960795 + 2779929 * 2 ^ 59
def prefixEnd_2779929 : Nat := 4983230072969 + 3 ^ 40 * 2779929 * 2
def baseEnd_2779929 : Nat := 1427439762372759248702845

theorem tailTrace_2779929 : CollatzResearch.WordTrace tailWord_2779929 prefixEnd_2779929 1427439762372759248702845 := by
  unfold tailWord_2779929
  simp only [CollatzResearch.WordTrace]
  refine ⟨101392340345799481919614841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67594893563866321279743227 101392340345799481919614841)
  ·
    refine ⟨76044255259349611439711131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 101392340345799481919614841 76044255259349611439711131)
    ·
      refine ⟨114066382889024417159566697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76044255259349611439711131 114066382889024417159566697)
      ·
        refine ⟨85549787166768312869675023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 114066382889024417159566697 85549787166768312869675023)
        ·
          refine ⟨128324680750152469304512535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 85549787166768312869675023 128324680750152469304512535)
          ·
            refine ⟨192487021125228703956768803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128324680750152469304512535 192487021125228703956768803)
            ·
              refine ⟨288730531687843055935153205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192487021125228703956768803 288730531687843055935153205)
              ·
                refine ⟨27068487345735286493920613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 288730531687843055935153205 27068487345735286493920613)
                ·
                  refine ⟨5075341377325366217610115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 27068487345735286493920613 5075341377325366217610115)
                  ·
                    refine ⟨7613012065988049326415173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5075341377325366217610115 7613012065988049326415173)
                    ·
                      refine ⟨1427439762372759248702845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7613012065988049326415173 1427439762372759248702845)
                      ·
                        rfl

theorem cell23_2779929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 5, 4, 1, 4].length) (baseStart_2779929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779929 prefixEnd_2779929 := by exact prefixLift 2779929
  have htrace : WordTrace (prefixWord ++ tailWord_2779929) baseStart_2779929 baseEnd_2779929 := by
    simpa [prefixWord, tailWord_2779929, baseEnd_2779929] using wordTrace_append hprefix tailTrace_2779929
  have hstable : (prefixWord ++ tailWord_2779929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779929).length < 2 ^ (prefixWord ++ tailWord_2779929).sum := by decide
  have hdescent : baseEnd_2779929 < baseStart_2779929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779979 : List Nat := [1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 3]
def baseStart_2779979 : Nat := 118140960795 + 2779979 * 2 ^ 59
def prefixEnd_2779979 : Nat := 4983230072969 + 3 ^ 40 * 2779979 * 2
def baseEnd_2779979 : Nat := 1427465436405484053077615

theorem tailTrace_2779979 : CollatzResearch.WordTrace tailWord_2779979 prefixEnd_2779979 1427465436405484053077615 := by
  unfold tailWord_2779979
  simp only [CollatzResearch.WordTrace]
  refine ⟨101394163995618340458934991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67596109330412226972623327 101394163995618340458934991)
  ·
    refine ⟨152091245993427510688402487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101394163995618340458934991 152091245993427510688402487)
    ·
      refine ⟨228136868990141266032603731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152091245993427510688402487 228136868990141266032603731)
      ·
        refine ⟨342205303485211899048905597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 228136868990141266032603731 342205303485211899048905597)
        ·
          refine ⟨128326988806954462143339599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 342205303485211899048905597 128326988806954462143339599)
          ·
            refine ⟨192490483210431693215009399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 128326988806954462143339599 192490483210431693215009399)
            ·
              refine ⟨288735724815647539822514099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 192490483210431693215009399 288735724815647539822514099)
              ·
                refine ⟨433103587223471309733771149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 288735724815647539822514099 433103587223471309733771149)
                ·
                  refine ⟨162413845208801741150164181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 433103587223471309733771149 162413845208801741150164181)
                  ·
                    refine ⟨3806574497081290808206973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 162413845208801741150164181 3806574497081290808206973)
                    ·
                      refine ⟨1427465436405484053077615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3806574497081290808206973 1427465436405484053077615)
                      ·
                        rfl

theorem cell23_2779979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 3, 7, 3].length) (baseStart_2779979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779979 prefixEnd_2779979 := by exact prefixLift 2779979
  have htrace : WordTrace (prefixWord ++ tailWord_2779979) baseStart_2779979 baseEnd_2779979 := by
    simpa [prefixWord, tailWord_2779979, baseEnd_2779979] using wordTrace_append hprefix tailTrace_2779979
  have hstable : (prefixWord ++ tailWord_2779979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779979).length < 2 ^ (prefixWord ++ tailWord_2779979).sum := by decide
  have hdescent : baseEnd_2779979 < baseStart_2779979 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2779989 : List Nat := [1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 8]
def baseStart_2779989 : Nat := 118140960795 + 2779989 * 2 ^ 59
def prefixEnd_2779989 : Nat := 4983230072969 + 3 ^ 40 * 2779989 * 2
def baseEnd_2779989 : Nat := 1427470571212029013952569

theorem tailTrace_2779989 : CollatzResearch.WordTrace tailWord_2779989 prefixEnd_2779989 1427470571212029013952569 := by
  unfold tailWord_2779989
  simp only [CollatzResearch.WordTrace]
  refine ⟨101394528725582112166799021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67596352483721408111199347 101394528725582112166799021)
  ·
    refine ⟨38022948272093292062549633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 101394528725582112166799021 38022948272093292062549633)
    ·
      refine ⟨28517211204069969046912225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 38022948272093292062549633 28517211204069969046912225)
      ·
        refine ⟨21387908403052476785184169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28517211204069969046912225 21387908403052476785184169)
        ·
          refine ⟨16040931302289357588888127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21387908403052476785184169 16040931302289357588888127)
          ·
            refine ⟨24061396953434036383332191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16040931302289357588888127 24061396953434036383332191)
            ·
              refine ⟨36092095430151054574998287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24061396953434036383332191 36092095430151054574998287)
              ·
                refine ⟨54138143145226581862497431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 36092095430151054574998287 54138143145226581862497431)
                ·
                  refine ⟨81207214717839872793746147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 54138143145226581862497431 81207214717839872793746147)
                  ·
                    refine ⟨121810822076759809190619221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 81207214717839872793746147 121810822076759809190619221)
                    ·
                      refine ⟨1427470571212029013952569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 121810822076759809190619221 1427470571212029013952569)
                      ·
                        rfl

theorem cell23_2779989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 1, 8].length) (baseStart_2779989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2779989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2779989 prefixEnd_2779989 := by exact prefixLift 2779989
  have htrace : WordTrace (prefixWord ++ tailWord_2779989) baseStart_2779989 baseEnd_2779989 := by
    simpa [prefixWord, tailWord_2779989, baseEnd_2779989] using wordTrace_append hprefix tailTrace_2779989
  have hstable : (prefixWord ++ tailWord_2779989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2779989).length < 2 ^ (prefixWord ++ tailWord_2779989).sum := by decide
  have hdescent : baseEnd_2779989 < baseStart_2779989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2779989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780003 : List Nat := [1, 1, 1, 5, 3, 2, 3, 1, 6]
def baseStart_2780003 : Nat := 118140960795 + 2780003 * 2 ^ 59
def prefixEnd_2780003 : Nat := 4983230072969 + 3 ^ 40 * 2780003 * 2
def baseEnd_2780003 : Nat := 158608639993465773241945

theorem tailTrace_2780003 : CollatzResearch.WordTrace tailWord_2780003 prefixEnd_2780003 158608639993465773241945 := by
  unfold tailWord_2780003
  simp only [CollatzResearch.WordTrace]
  refine ⟨101395039347531392557808663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67596692898354261705205775 101395039347531392557808663)
  ·
    refine ⟨152092559021297088836712995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101395039347531392557808663 152092559021297088836712995)
    ·
      refine ⟨228138838531945633255069493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 152092559021297088836712995 228138838531945633255069493)
      ·
        refine ⟨21388016112369903117662765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 228138838531945633255069493 21388016112369903117662765)
        ·
          refine ⟨8020506042138713669123537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21388016112369903117662765 8020506042138713669123537)
          ·
            refine ⟨6015379531604035251842653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8020506042138713669123537 6015379531604035251842653)
            ·
              refine ⟨2255767324351513219440995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6015379531604035251842653 2255767324351513219440995)
              ·
                refine ⟨3383650986527269829161493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255767324351513219440995 3383650986527269829161493)
                ·
                  refine ⟨158608639993465773241945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3383650986527269829161493 158608639993465773241945)
                  ·
                    rfl

theorem cell23_2780003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 3, 1, 6].length) (baseStart_2780003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780003 prefixEnd_2780003 := by exact prefixLift 2780003
  have htrace : WordTrace (prefixWord ++ tailWord_2780003) baseStart_2780003 baseEnd_2780003 := by
    simpa [prefixWord, tailWord_2780003, baseEnd_2780003] using wordTrace_append hprefix tailTrace_2780003
  have hstable : (prefixWord ++ tailWord_2780003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780003).length < 2 ^ (prefixWord ++ tailWord_2780003).sum := by decide
  have hdescent : baseEnd_2780003 < baseStart_2780003 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780016 : List Nat := [2, 1, 1, 1, 4, 1, 3, 4, 1, 5]
def baseStart_2780016 : Nat := 118140960795 + 2780016 * 2 ^ 59
def prefixEnd_2780016 : Nat := 4983230072969 + 3 ^ 40 * 2780016 * 2
def baseEnd_2780016 : Nat := 475828145063233469438315

theorem tailTrace_2780016 : CollatzResearch.WordTrace tailWord_2780016 prefixEnd_2780016 475828145063233469438315 := by
  unfold tailWord_2780016
  simp only [CollatzResearch.WordTrace]
  refine ⟨50697756748242147889015951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67597008997656197185354601 50697756748242147889015951)
  ·
    refine ⟨76046635122363221833523927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50697756748242147889015951 76046635122363221833523927)
    ·
      refine ⟨114069952683544832750285891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 76046635122363221833523927 114069952683544832750285891)
      ·
        refine ⟨171104929025317249125428837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 114069952683544832750285891 171104929025317249125428837)
        ·
          refine ⟨32082174192246984211017907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 171104929025317249125428837 32082174192246984211017907)
          ·
            refine ⟨48123261288370476316526861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32082174192246984211017907 48123261288370476316526861)
            ·
              refine ⟨18046222983138928618697573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 48123261288370476316526861 18046222983138928618697573)
              ·
                refine ⟨3383666809338549116005795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18046222983138928618697573 3383666809338549116005795)
                ·
                  refine ⟨5075500214007823674008693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383666809338549116005795 5075500214007823674008693)
                  ·
                    refine ⟨475828145063233469438315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5075500214007823674008693 475828145063233469438315)
                    ·
                      rfl

theorem cell23_2780016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 4, 1, 5].length) (baseStart_2780016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780016 prefixEnd_2780016 := by exact prefixLift 2780016
  have htrace : WordTrace (prefixWord ++ tailWord_2780016) baseStart_2780016 baseEnd_2780016 := by
    simpa [prefixWord, tailWord_2780016, baseEnd_2780016] using wordTrace_append hprefix tailTrace_2780016
  have hstable : (prefixWord ++ tailWord_2780016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780016).length < 2 ^ (prefixWord ++ tailWord_2780016).sum := by decide
  have hdescent : baseEnd_2780016 < baseStart_2780016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780036 : List Nat := [2, 3, 2, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_2780036 : Nat := 118140960795 + 2780036 * 2 ^ 59
def prefixEnd_2780036 : Nat := 4983230072969 + 3 ^ 40 * 2780036 * 2
def baseEnd_2780036 : Nat := 1427494704802790330064853

theorem tailTrace_2780036 : CollatzResearch.WordTrace tailWord_2780036 prefixEnd_2780036 1427494704802790330064853 := by
  unfold tailWord_2780036
  simp only [CollatzResearch.WordTrace]
  refine ⟨50698121478205919596879981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67597495304274559462506641 50698121478205919596879981)
  ·
    refine ⟨19011795554327219848829993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 50698121478205919596879981 19011795554327219848829993)
    ·
      refine ⟨14258846665745414886622495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19011795554327219848829993 14258846665745414886622495)
      ·
        refine ⟨21388269998618122329933743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14258846665745414886622495 21388269998618122329933743)
        ·
          refine ⟨32082404997927183494900615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21388269998618122329933743 32082404997927183494900615)
          ·
            refine ⟨48123607496890775242350923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32082404997927183494900615 48123607496890775242350923)
            ·
              refine ⟨72185411245336162863526385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48123607496890775242350923 72185411245336162863526385)
              ·
                refine ⟨54139058434002122147644789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 72185411245336162863526385 54139058434002122147644789)
                ·
                  refine ⟨5075536728187698951341699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 54139058434002122147644789 5075536728187698951341699)
                  ·
                    refine ⟨7613305092281548427012549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5075536728187698951341699 7613305092281548427012549)
                    ·
                      refine ⟨1427494704802790330064853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 7613305092281548427012549 1427494704802790330064853)
                      ·
                        rfl

theorem cell23_2780036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_2780036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780036 prefixEnd_2780036 := by exact prefixLift 2780036
  have htrace : WordTrace (prefixWord ++ tailWord_2780036) baseStart_2780036 baseEnd_2780036 := by
    simpa [prefixWord, tailWord_2780036, baseEnd_2780036] using wordTrace_append hprefix tailTrace_2780036
  have hstable : (prefixWord ++ tailWord_2780036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780036).length < 2 ^ (prefixWord ++ tailWord_2780036).sum := by decide
  have hdescent : baseEnd_2780036 < baseStart_2780036 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780040 : List Nat := [2, 1, 3, 3, 2, 2, 1, 2, 2, 3, 2]
def baseStart_2780040 : Nat := 118140960795 + 2780040 * 2 ^ 59
def prefixEnd_2780040 : Nat := 4983230072969 + 3 ^ 40 * 2780040 * 2
def baseEnd_2780040 : Nat := 1427496758725408314414835

theorem tailTrace_2780040 : CollatzResearch.WordTrace tailWord_2780040 prefixEnd_2780040 1427496758725408314414835 := by
  unfold tailWord_2780040
  simp only [CollatzResearch.WordTrace]
  refine ⟨50698194424198673938452787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 67597592565598231917937049 50698194424198673938452787)
  ·
    refine ⟨76047291636298010907679181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 50698194424198673938452787 76047291636298010907679181)
    ·
      refine ⟨28517734363611754090379693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 76047291636298010907679181 28517734363611754090379693)
      ·
        refine ⟨10694150386354407783892385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 28517734363611754090379693 10694150386354407783892385)
        ·
          refine ⟨8020612789765805837919289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10694150386354407783892385 8020612789765805837919289)
          ·
            refine ⟨6015459592324354378439467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8020612789765805837919289 6015459592324354378439467)
            ·
              refine ⟨9023189388486531567659201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6015459592324354378439467 9023189388486531567659201)
              ·
                refine ⟨6767392041364898675744401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9023189388486531567659201 6767392041364898675744401)
                ·
                  refine ⟨5075544031023674006808301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6767392041364898675744401 5075544031023674006808301)
                  ·
                    refine ⟨1903329011633877752553113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5075544031023674006808301 1903329011633877752553113)
                    ·
                      refine ⟨1427496758725408314414835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1903329011633877752553113 1427496758725408314414835)
                      ·
                        rfl

theorem cell23_2780040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 2, 1, 2, 2, 3, 2].length) (baseStart_2780040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780040 prefixEnd_2780040 := by exact prefixLift 2780040
  have htrace : WordTrace (prefixWord ++ tailWord_2780040) baseStart_2780040 baseEnd_2780040 := by
    simpa [prefixWord, tailWord_2780040, baseEnd_2780040] using wordTrace_append hprefix tailTrace_2780040
  have hstable : (prefixWord ++ tailWord_2780040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780040).length < 2 ^ (prefixWord ++ tailWord_2780040).sum := by decide
  have hdescent : baseEnd_2780040 < baseStart_2780040 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780054 : List Nat := [5, 3, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2780054 : Nat := 118140960795 + 2780054 * 2 ^ 59
def prefixEnd_2780054 : Nat := 4983230072969 + 3 ^ 40 * 2780054 * 2
def baseEnd_2780054 : Nat := 158611549717174584404419

theorem tailTrace_2780054 : CollatzResearch.WordTrace tailWord_2780054 prefixEnd_2780054 158611549717174584404419 := by
  unfold tailWord_2780054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6337306216896664266744701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 67597932980231085511943477 6337306216896664266744701)
  ·
    refine ⟨2376489831336249100029263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6337306216896664266744701 2376489831336249100029263)
    ·
      refine ⟨3564734747004373650043895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2376489831336249100029263 3564734747004373650043895)
      ·
        refine ⟨5347102120506560475065843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3564734747004373650043895 5347102120506560475065843)
        ·
          refine ⟨8020653180759840712598765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347102120506560475065843 8020653180759840712598765)
          ·
            refine ⟨3007744942784940267224537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8020653180759840712598765 3007744942784940267224537)
            ·
              refine ⟨2255808707088705200418403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3007744942784940267224537 2255808707088705200418403)
              ·
                refine ⟨3383713060633057800627605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255808707088705200418403 3383713060633057800627605)
                ·
                  refine ⟨158611549717174584404419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3383713060633057800627605 158611549717174584404419)
                  ·
                    rfl

theorem cell23_2780054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2780054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780054 prefixEnd_2780054 := by exact prefixLift 2780054
  have htrace : WordTrace (prefixWord ++ tailWord_2780054) baseStart_2780054 baseEnd_2780054 := by
    simpa [prefixWord, tailWord_2780054, baseEnd_2780054] using wordTrace_append hprefix tailTrace_2780054
  have hstable : (prefixWord ++ tailWord_2780054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780054).length < 2 ^ (prefixWord ++ tailWord_2780054).sum := by decide
  have hdescent : baseEnd_2780054 < baseStart_2780054 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780090 : List Nat := [3, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3]
def baseStart_2780090 : Nat := 118140960795 + 2780090 * 2 ^ 59
def prefixEnd_2780090 : Nat := 4983230072969 + 3 ^ 40 * 2780090 * 2
def baseEnd_2780090 : Nat := 1427522432758133118789605

theorem tailTrace_2780090 : CollatzResearch.WordTrace tailWord_2780090 prefixEnd_2780090 1427522432758133118789605 := by
  unfold tailWord_2780090
  simp only [CollatzResearch.WordTrace]
  refine ⟨25349553124554051604056431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 67598808332144137610817149 25349553124554051604056431)
  ·
    refine ⟨38024329686831077406084647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 25349553124554051604056431 38024329686831077406084647)
    ·
      refine ⟨57036494530246616109126971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 38024329686831077406084647 57036494530246616109126971)
      ·
        refine ⟨85554741795369924163690457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 57036494530246616109126971 85554741795369924163690457)
        ·
          refine ⟨64166056346527443122767843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 85554741795369924163690457 64166056346527443122767843)
          ·
            refine ⟨96249084519791164684151765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 64166056346527443122767843 96249084519791164684151765)
            ·
              refine ⟨2255837918432605422284807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 96249084519791164684151765 2255837918432605422284807)
              ·
                refine ⟨3383756877648908133427211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2255837918432605422284807 3383756877648908133427211)
                ·
                  refine ⟨5075635316473362200140817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3383756877648908133427211 5075635316473362200140817)
                  ·
                    refine ⟨3806726487355021650105613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5075635316473362200140817 3806726487355021650105613)
                    ·
                      refine ⟨1427522432758133118789605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3806726487355021650105613 1427522432758133118789605)
                      ·
                        rfl

theorem cell23_2780090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 7, 1, 1, 2, 3].length) (baseStart_2780090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780090 prefixEnd_2780090 := by exact prefixLift 2780090
  have htrace : WordTrace (prefixWord ++ tailWord_2780090) baseStart_2780090 baseEnd_2780090 := by
    simpa [prefixWord, tailWord_2780090, baseEnd_2780090] using wordTrace_append hprefix tailTrace_2780090
  have hstable : (prefixWord ++ tailWord_2780090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780090).length < 2 ^ (prefixWord ++ tailWord_2780090).sum := by decide
  have hdescent : baseEnd_2780090 < baseStart_2780090 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2780103 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 3]
def baseStart_2780103 : Nat := 118140960795 + 2780103 * 2 ^ 59
def prefixEnd_2780103 : Nat := 4983230072969 + 3 ^ 40 * 2780103 * 2
def baseEnd_2780103 : Nat := 1427529108006641567927045

theorem tailTrace_2780103 : CollatzResearch.WordTrace tailWord_2780103 prefixEnd_2780103 1427529108006641567927045 := by
  unfold tailWord_2780103
  simp only [CollatzResearch.WordTrace]
  refine ⟨101398686647169109636448963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 67599124431446073090965975 101398686647169109636448963)
  ·
    refine ⟨152098029970753664454673445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 101398686647169109636448963 152098029970753664454673445)
    ·
      refine ⟨28518380619516312085251271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 152098029970753664454673445 28518380619516312085251271)
      ·
        refine ⟨42777570929274468127876907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28518380619516312085251271 42777570929274468127876907)
        ·
          refine ⟨64166356393911702191815361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 42777570929274468127876907 64166356393911702191815361)
          ·
            refine ⟨48124767295433776643861521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 64166356393911702191815361 48124767295433776643861521)
            ·
              refine ⟨36093575471575332482896141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 48124767295433776643861521 36093575471575332482896141)
              ·
                refine ⟨13535090801840749681086053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36093575471575332482896141 13535090801840749681086053)
                ·
                  refine ⟨2537829525345140565203635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 13535090801840749681086053 2537829525345140565203635)
                  ·
                    refine ⟨3806744288017710847805453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2537829525345140565203635 3806744288017710847805453)
                    ·
                      refine ⟨1427529108006641567927045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3806744288017710847805453 1427529108006641567927045)
                      ·
                        rfl

theorem cell23_2780103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 4, 1, 3].length) (baseStart_2780103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2780103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2780103 prefixEnd_2780103 := by exact prefixLift 2780103
  have htrace : WordTrace (prefixWord ++ tailWord_2780103) baseStart_2780103 baseEnd_2780103 := by
    simpa [prefixWord, tailWord_2780103, baseEnd_2780103] using wordTrace_append hprefix tailTrace_2780103
  have hstable : (prefixWord ++ tailWord_2780103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2780103).length < 2 ^ (prefixWord ++ tailWord_2780103).sum := by decide
  have hdescent : baseEnd_2780103 < baseStart_2780103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2780103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
