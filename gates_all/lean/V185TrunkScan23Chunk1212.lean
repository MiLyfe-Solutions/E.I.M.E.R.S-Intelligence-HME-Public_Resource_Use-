import V185TrunkScan23Chunk1211

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_7180978 : List Nat := [3, 2, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_7180978 : Nat := 118140960795 + 7180978 * 2 ^ 59
def prefixEnd_7180978 : Nat := 4983230072969 + 3 ^ 40 * 7180978 * 2
def baseEnd_7180978 : Nat := 1229097761120703541416763

theorem tailTrace_7180978 : CollatzResearch.WordTrace tailWord_7180978 prefixEnd_7180978 1229097761120703541416763 := by
  unfold tailWord_7180978
  simp only [CollatzResearch.WordTrace]
  refine ⟨65477946144637648561937897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174607856385700396165167725 65477946144637648561937897)
  ·
    refine ⟨49108459608478236421453423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65477946144637648561937897 49108459608478236421453423)
    ·
      refine ⟨73662689412717354632180135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49108459608478236421453423 73662689412717354632180135)
      ·
        refine ⟨110494034119076031948270203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73662689412717354632180135 110494034119076031948270203)
        ·
          refine ⟨165741051178614047922405305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110494034119076031948270203 165741051178614047922405305)
          ·
            refine ⟨124305788383960535941803979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165741051178614047922405305 124305788383960535941803979)
            ·
              refine ⟨186458682575940803912705969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124305788383960535941803979 186458682575940803912705969)
              ·
                refine ⟨139844011931955602934529477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186458682575940803912705969 139844011931955602934529477)
                ·
                  refine ⟨26220752237241675550224277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139844011931955602934529477 26220752237241675550224277)
                  ·
                    refine ⟨1229097761120703541416763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26220752237241675550224277 1229097761120703541416763)
                    ·
                      rfl

theorem cell23_7180978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_7180978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7180978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7180978 prefixEnd_7180978 := by exact prefixLift 7180978
  have htrace : WordTrace (prefixWord ++ tailWord_7180978) baseStart_7180978 baseEnd_7180978 := by
    simpa [prefixWord, tailWord_7180978, baseEnd_7180978] using wordTrace_append hprefix tailTrace_7180978
  have hstable : (prefixWord ++ tailWord_7180978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7180978).length < 2 ^ (prefixWord ++ tailWord_7180978).sum := by decide
  have hdescent : baseEnd_7180978 < baseStart_7180978 := by decide
  rcases family_descends (prefixWord ++ tailWord_7180978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181012 : List Nat := [2, 4, 1, 3, 2, 1, 1, 1, 2, 6]
def baseStart_7181012 : Nat := 118140960795 + 7181012 * 2 ^ 59
def prefixEnd_7181012 : Nat := 4983230072969 + 3 ^ 40 * 7181012 * 2
def baseEnd_7181012 : Nat := 1229103580568121163741711

theorem tailTrace_7181012 : CollatzResearch.WordTrace tailWord_7181012 prefixEnd_7181012 1229103580568121163741711 := by
  unfold tailWord_7181012
  simp only [CollatzResearch.WordTrace]
  refine ⟨130956512330213709027244645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174608683106951612036326193 130956512330213709027244645)
  ·
    refine ⟨24554346061915070442608371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130956512330213709027244645 24554346061915070442608371)
    ·
      refine ⟨36831519092872605663912557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24554346061915070442608371 36831519092872605663912557)
      ·
        refine ⟨13811819659827227123967209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36831519092872605663912557 13811819659827227123967209)
        ·
          refine ⟨10358864744870420342975407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13811819659827227123967209 10358864744870420342975407)
          ·
            refine ⟨15538297117305630514463111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10358864744870420342975407 15538297117305630514463111)
            ·
              refine ⟨23307445675958445771694667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15538297117305630514463111 23307445675958445771694667)
              ·
                refine ⟨34961168513937668657542001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23307445675958445771694667 34961168513937668657542001)
                ·
                  refine ⟨26220876385453251493156501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34961168513937668657542001 26220876385453251493156501)
                  ·
                    refine ⟨1229103580568121163741711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26220876385453251493156501 1229103580568121163741711)
                    ·
                      rfl

theorem cell23_7181012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 1, 1, 2, 6].length) (baseStart_7181012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181012 prefixEnd_7181012 := by exact prefixLift 7181012
  have htrace : WordTrace (prefixWord ++ tailWord_7181012) baseStart_7181012 baseEnd_7181012 := by
    simpa [prefixWord, tailWord_7181012, baseEnd_7181012] using wordTrace_append hprefix tailTrace_7181012
  have hstable : (prefixWord ++ tailWord_7181012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181012).length < 2 ^ (prefixWord ++ tailWord_7181012).sum := by decide
  have hdescent : baseEnd_7181012 < baseStart_7181012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181015 : List Nat := [1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 4]
def baseStart_7181015 : Nat := 118140960795 + 7181015 * 2 ^ 59
def prefixEnd_7181015 : Nat := 4983230072969 + 3 ^ 40 * 7181015 * 2
def baseEnd_7181015 : Nat := 3687312282146326979487619

theorem tailTrace_7181015 : CollatzResearch.WordTrace tailWord_7181015 prefixEnd_7181015 3687312282146326979487619 := by
  unfold tailWord_7181015
  simp only [CollatzResearch.WordTrace]
  refine ⟨261913134079416549566848499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174608756052944366377898999 261913134079416549566848499)
  ·
    refine ⟨392869701119124824350272749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261913134079416549566848499 392869701119124824350272749)
    ·
      refine ⟨147326137919671809131352281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392869701119124824350272749 147326137919671809131352281)
      ·
        refine ⟨110494603439753856848514211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147326137919671809131352281 110494603439753856848514211)
        ·
          refine ⟨165741905159630785272771317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110494603439753856848514211 165741905159630785272771317)
          ·
            refine ⟨15538303608715386119322311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165741905159630785272771317 15538303608715386119322311)
            ·
              refine ⟨23307455413073079178983467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15538303608715386119322311 23307455413073079178983467)
              ·
                refine ⟨34961183119609618768475201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23307455413073079178983467 34961183119609618768475201)
                ·
                  refine ⟨26220887339707214076356401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34961183119609618768475201 26220887339707214076356401)
                  ·
                    refine ⟨19665665504780410557267301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26220887339707214076356401 19665665504780410557267301)
                    ·
                      refine ⟨3687312282146326979487619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19665665504780410557267301 3687312282146326979487619)
                      ·
                        rfl

theorem cell23_7181015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_7181015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181015 prefixEnd_7181015 := by exact prefixLift 7181015
  have htrace : WordTrace (prefixWord ++ tailWord_7181015) baseStart_7181015 baseEnd_7181015 := by
    simpa [prefixWord, tailWord_7181015, baseEnd_7181015] using wordTrace_append hprefix tailTrace_7181015
  have hstable : (prefixWord ++ tailWord_7181015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181015).length < 2 ^ (prefixWord ++ tailWord_7181015).sum := by decide
  have hdescent : baseEnd_7181015 < baseStart_7181015 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181025 : List Nat := [1, 2, 3, 1, 4, 2, 1, 2, 7]
def baseStart_7181025 : Nat := 118140960795 + 7181025 * 2 ^ 59
def prefixEnd_7181025 : Nat := 4983230072969 + 3 ^ 40 * 7181025 * 2
def baseEnd_7181025 : Nat := 409701935216985771151397

theorem tailTrace_7181025 : CollatzResearch.WordTrace tailWord_7181025 prefixEnd_7181025 409701935216985771151397 := by
  unfold tailWord_7181025
  simp only [CollatzResearch.WordTrace]
  refine ⟨261913498809380321274712529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174608999206253547516475019 261913498809380321274712529)
  ·
    refine ⟨196435124107035240956034397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261913498809380321274712529 196435124107035240956034397)
    ·
      refine ⟨73663171540138215358512899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196435124107035240956034397 73663171540138215358512899)
      ·
        refine ⟨110494757310207323037769349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73663171540138215358512899 110494757310207323037769349)
        ·
          refine ⟨20717766995663873069581753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110494757310207323037769349 20717766995663873069581753)
          ·
            refine ⟨15538325246747904802186315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20717766995663873069581753 15538325246747904802186315)
            ·
              refine ⟨23307487870121857203279473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15538325246747904802186315 23307487870121857203279473)
              ·
                refine ⟨17480615902591392902459605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23307487870121857203279473 17480615902591392902459605)
                ·
                  refine ⟨409701935216985771151397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17480615902591392902459605 409701935216985771151397)
                  ·
                    rfl

theorem cell23_7181025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 2, 1, 2, 7].length) (baseStart_7181025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181025 prefixEnd_7181025 := by exact prefixLift 7181025
  have htrace : WordTrace (prefixWord ++ tailWord_7181025) baseStart_7181025 baseEnd_7181025 := by
    simpa [prefixWord, tailWord_7181025, baseEnd_7181025] using wordTrace_append hprefix tailTrace_7181025
  have hstable : (prefixWord ++ tailWord_7181025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181025).length < 2 ^ (prefixWord ++ tailWord_7181025).sum := by decide
  have hdescent : baseEnd_7181025 < baseStart_7181025 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181042 : List Nat := [3, 2, 1, 3, 1, 2, 1, 5, 5]
def baseStart_7181042 : Nat := 118140960795 + 7181042 * 2 ^ 59
def prefixEnd_7181042 : Nat := 4983230072969 + 3 ^ 40 * 7181042 * 2
def baseEnd_7181042 : Nat := 409702905124888708205555

theorem tailTrace_7181042 : CollatzResearch.WordTrace tailWord_7181042 prefixEnd_7181042 409702905124888708205555 := by
  unfold tailWord_7181042
  simp only [CollatzResearch.WordTrace]
  refine ⟨65478529712579683294520345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174609412566879155452054253 65478529712579683294520345)
  ·
    refine ⟨49108897284434762470890259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65478529712579683294520345 49108897284434762470890259)
    ·
      refine ⟨73663345926652143706335389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49108897284434762470890259 73663345926652143706335389)
      ·
        refine ⟨27623754722494553889875771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73663345926652143706335389 27623754722494553889875771)
        ·
          refine ⟨41435632083741830834813657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27623754722494553889875771 41435632083741830834813657)
          ·
            refine ⟨31076724062806373126110243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41435632083741830834813657 31076724062806373126110243)
            ·
              refine ⟨46615086094209559689165365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31076724062806373126110243 46615086094209559689165365)
              ·
                refine ⟨4370164321332146220859253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46615086094209559689165365 4370164321332146220859253)
                ·
                  refine ⟨409702905124888708205555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4370164321332146220859253 409702905124888708205555)
                  ·
                    rfl

theorem cell23_7181042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 1, 5, 5].length) (baseStart_7181042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181042 prefixEnd_7181042 := by exact prefixLift 7181042
  have htrace : WordTrace (prefixWord ++ tailWord_7181042) baseStart_7181042 baseEnd_7181042 := by
    simpa [prefixWord, tailWord_7181042, baseEnd_7181042] using wordTrace_append hprefix tailTrace_7181042
  have hstable : (prefixWord ++ tailWord_7181042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181042).length < 2 ^ (prefixWord ++ tailWord_7181042).sum := by decide
  have hdescent : baseEnd_7181042 < baseStart_7181042 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181112 : List Nat := [2, 1, 2, 1, 3, 2, 3, 2, 2, 2, 3]
def baseStart_7181112 : Nat := 118140960795 + 7181112 * 2 ^ 59
def prefixEnd_7181112 : Nat := 4983230072969 + 3 ^ 40 * 7181112 * 2
def baseEnd_7181112 : Nat := 3687362089769813099974673

theorem tailTrace_7181112 : CollatzResearch.WordTrace tailWord_7181112 prefixEnd_7181112 3687362089769813099974673 := by
  unfold tailWord_7181112
  simp only [CollatzResearch.WordTrace]
  refine ⟨130958335980032567566564795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174611114640043423422086393 130958335980032567566564795)
  ·
    refine ⟨196437503970048851349847193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130958335980032567566564795 196437503970048851349847193)
    ·
      refine ⟨147328127977536638512385395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196437503970048851349847193 147328127977536638512385395)
      ·
        refine ⟨220992191966304957768578093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147328127977536638512385395 220992191966304957768578093)
        ·
          refine ⟨82872071987364359163216785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 220992191966304957768578093 82872071987364359163216785)
          ·
            refine ⟨62154053990523269372412589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82872071987364359163216785 62154053990523269372412589)
            ·
              refine ⟨23307770246446226014654721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62154053990523269372412589 23307770246446226014654721)
              ·
                refine ⟨17480827684834669510991041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23307770246446226014654721 17480827684834669510991041)
                ·
                  refine ⟨13110620763626002133243281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17480827684834669510991041 13110620763626002133243281)
                  ·
                    refine ⟨9832965572719501599932461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13110620763626002133243281 9832965572719501599932461)
                    ·
                      refine ⟨3687362089769813099974673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9832965572719501599932461 3687362089769813099974673)
                      ·
                        rfl

theorem cell23_7181112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_7181112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181112 prefixEnd_7181112 := by exact prefixLift 7181112
  have htrace : WordTrace (prefixWord ++ tailWord_7181112) baseStart_7181112 baseEnd_7181112 := by
    simpa [prefixWord, tailWord_7181112, baseEnd_7181112] using wordTrace_append hprefix tailTrace_7181112
  have hstable : (prefixWord ++ tailWord_7181112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181112).length < 2 ^ (prefixWord ++ tailWord_7181112).sum := by decide
  have hdescent : baseEnd_7181112 < baseStart_7181112 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181119 : List Nat := [1, 1, 2, 2, 5, 3, 1, 1, 3, 4]
def baseStart_7181119 : Nat := 118140960795 + 7181119 * 2 ^ 59
def prefixEnd_7181119 : Nat := 4983230072969 + 3 ^ 40 * 7181119 * 2
def baseEnd_7181119 : Nat := 1229121894711464857529047

theorem tailTrace_7181119 : CollatzResearch.WordTrace tailWord_7181119 prefixEnd_7181119 1229121894711464857529047 := by
  unfold tailWord_7181119
  simp only [CollatzResearch.WordTrace]
  refine ⟨261916927271039775328634411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174611284847359850219089607 261916927271039775328634411)
  ·
    refine ⟨392875390906559662992951617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261916927271039775328634411 392875390906559662992951617)
    ·
      refine ⟨294656543179919747244713713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392875390906559662992951617 294656543179919747244713713)
      ·
        refine ⟨220992407384939810433535285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294656543179919747244713713 220992407384939810433535285)
        ·
          refine ⟨20718038192338107228143933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 220992407384939810433535285 20718038192338107228143933)
          ·
            refine ⟨7769264322126790210553975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20718038192338107228143933 7769264322126790210553975)
            ·
              refine ⟨11653896483190185315830963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769264322126790210553975 11653896483190185315830963)
              ·
                refine ⟨17480844724785277973746445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11653896483190185315830963 17480844724785277973746445)
                ·
                  refine ⟨6555316771794479240154917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17480844724785277973746445 6555316771794479240154917)
                  ·
                    refine ⟨1229121894711464857529047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6555316771794479240154917 1229121894711464857529047)
                    ·
                      rfl

theorem cell23_7181119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 3, 1, 1, 3, 4].length) (baseStart_7181119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181119 prefixEnd_7181119 := by exact prefixLift 7181119
  have htrace : WordTrace (prefixWord ++ tailWord_7181119) baseStart_7181119 baseEnd_7181119 := by
    simpa [prefixWord, tailWord_7181119, baseEnd_7181119] using wordTrace_append hprefix tailTrace_7181119
  have hstable : (prefixWord ++ tailWord_7181119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181119).length < 2 ^ (prefixWord ++ tailWord_7181119).sum := by decide
  have hdescent : baseEnd_7181119 < baseStart_7181119 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181125 : List Nat := [1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 3]
def baseStart_7181125 : Nat := 118140960795 + 7181125 * 2 ^ 59
def prefixEnd_7181125 : Nat := 4983230072969 + 3 ^ 40 * 7181125 * 2
def baseEnd_7181125 : Nat := 3687368765018321549112113

theorem tailTrace_7181125 : CollatzResearch.WordTrace tailWord_7181125 prefixEnd_7181125 3687368765018321549112113 := by
  unfold tailWord_7181125
  simp only [CollatzResearch.WordTrace]
  refine ⟨261917146109018038353352829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174611430739345358902235219 261917146109018038353352829)
  ·
    refine ⟨98218929790881764382507311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261917146109018038353352829 98218929790881764382507311)
    ·
      refine ⟨147328394686322646573760967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98218929790881764382507311 147328394686322646573760967)
      ·
        refine ⟨220992592029483969860641451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147328394686322646573760967 220992592029483969860641451)
        ·
          refine ⟨331488888044225954790962177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 220992592029483969860641451 331488888044225954790962177)
          ·
            refine ⟨248616666033169466093221633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331488888044225954790962177 248616666033169466093221633)
            ·
              refine ⟨186462499524877099569916225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248616666033169466093221633 186462499524877099569916225)
              ·
                refine ⟨139846874643657824677437169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186462499524877099569916225 139846874643657824677437169)
                ·
                  refine ⟨104885155982743368508077877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139846874643657824677437169 104885155982743368508077877)
                  ·
                    refine ⟨9832983373382190797632301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104885155982743368508077877 9832983373382190797632301)
                    ·
                      refine ⟨3687368765018321549112113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9832983373382190797632301 3687368765018321549112113)
                      ·
                        rfl

theorem cell23_7181125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 2, 2, 5, 3].length) (baseStart_7181125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181125 prefixEnd_7181125 := by exact prefixLift 7181125
  have htrace : WordTrace (prefixWord ++ tailWord_7181125) baseStart_7181125 baseEnd_7181125 := by
    simpa [prefixWord, tailWord_7181125, baseEnd_7181125] using wordTrace_append hprefix tailTrace_7181125
  have hstable : (prefixWord ++ tailWord_7181125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181125).length < 2 ^ (prefixWord ++ tailWord_7181125).sum := by decide
  have hdescent : baseEnd_7181125 < baseStart_7181125 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181132 : List Nat := [2, 2, 1, 3, 3, 2, 1, 3, 6]
def baseStart_7181132 : Nat := 118140960795 + 7181132 * 2 ^ 59
def prefixEnd_7181132 : Nat := 4983230072969 + 3 ^ 40 * 7181132 * 2
def baseEnd_7181132 : Nat := 409708039931433669080509

theorem tailTrace_7181132 : CollatzResearch.WordTrace tailWord_7181132 prefixEnd_7181132 409708039931433669080509 := by
  unfold tailWord_7181132
  simp only [CollatzResearch.WordTrace]
  refine ⟨130958700709996339274428825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174611600946661785699238433 130958700709996339274428825)
  ·
    refine ⟨98219025532497254455821619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130958700709996339274428825 98219025532497254455821619)
    ·
      refine ⟨147328538298745881683732429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98219025532497254455821619 147328538298745881683732429)
      ·
        refine ⟨55248201862029705631399661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147328538298745881683732429 55248201862029705631399661)
        ·
          refine ⟨20718075698261139611774873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55248201862029705631399661 20718075698261139611774873)
          ·
            refine ⟨15538556773695854708831155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20718075698261139611774873 15538556773695854708831155)
            ·
              refine ⟨23307835160543782063246733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15538556773695854708831155 23307835160543782063246733)
              ·
                refine ⟨8740438185203918273717525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23307835160543782063246733 8740438185203918273717525)
                ·
                  refine ⟨409708039931433669080509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8740438185203918273717525 409708039931433669080509)
                  ·
                    rfl

theorem cell23_7181132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 1, 3, 6].length) (baseStart_7181132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181132 prefixEnd_7181132 := by exact prefixLift 7181132
  have htrace : WordTrace (prefixWord ++ tailWord_7181132) baseStart_7181132 baseEnd_7181132 := by
    simpa [prefixWord, tailWord_7181132, baseEnd_7181132] using wordTrace_append hprefix tailTrace_7181132
  have hstable : (prefixWord ++ tailWord_7181132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181132).length < 2 ^ (prefixWord ++ tailWord_7181132).sum := by decide
  have hdescent : baseEnd_7181132 < baseStart_7181132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181169 : List Nat := [1, 2, 2, 2, 1, 4, 2, 2, 2, 3, 2]
def baseStart_7181169 : Nat := 118140960795 + 7181169 * 2 ^ 59
def prefixEnd_7181169 : Nat := 4983230072969 + 3 ^ 40 * 7181169 * 2
def baseEnd_7181169 : Nat := 3687391358167119376961911

theorem tailTrace_7181169 : CollatzResearch.WordTrace tailWord_7181169 prefixEnd_7181169 3687391358167119376961911 := by
  unfold tailWord_7181169
  simp only [CollatzResearch.WordTrace]
  refine ⟨261918750920858633867954561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174612500613905755911969707 261918750920858633867954561)
  ·
    refine ⟨196439063190643975400965921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261918750920858633867954561 196439063190643975400965921)
    ·
      refine ⟨147329297392982981550724441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196439063190643975400965921 147329297392982981550724441)
      ·
        refine ⟨110496973044737236163043331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147329297392982981550724441 110496973044737236163043331)
        ·
          refine ⟨165745459567105854244564997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110496973044737236163043331 165745459567105854244564997)
          ·
            refine ⟨31077273668832347670855937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165745459567105854244564997 31077273668832347670855937)
            ·
              refine ⟨23307955251624260753141953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31077273668832347670855937 23307955251624260753141953)
              ·
                refine ⟨17480966438718195564856465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23307955251624260753141953 17480966438718195564856465)
                ·
                  refine ⟨13110724829038646673642349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17480966438718195564856465 13110724829038646673642349)
                  ·
                    refine ⟨4916521810889492502615881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13110724829038646673642349 4916521810889492502615881)
                    ·
                      refine ⟨3687391358167119376961911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916521810889492502615881 3687391358167119376961911)
                      ·
                        rfl

theorem cell23_7181169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 2, 2, 2, 3, 2].length) (baseStart_7181169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181169 prefixEnd_7181169 := by exact prefixLift 7181169
  have htrace : WordTrace (prefixWord ++ tailWord_7181169) baseStart_7181169 baseEnd_7181169 := by
    simpa [prefixWord, tailWord_7181169, baseEnd_7181169] using wordTrace_append hprefix tailTrace_7181169
  have hstable : (prefixWord ++ tailWord_7181169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181169).length < 2 ^ (prefixWord ++ tailWord_7181169).sum := by decide
  have hdescent : baseEnd_7181169 < baseStart_7181169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181192 : List Nat := [2, 1, 3, 3, 2, 1, 1, 3, 1, 6]
def baseStart_7181192 : Nat := 118140960795 + 7181192 * 2 ^ 59
def prefixEnd_7181192 : Nat := 4983230072969 + 3 ^ 40 * 7181192 * 2
def baseEnd_7181192 : Nat := 1229134389407390928991435

theorem tailTrace_7181192 : CollatzResearch.WordTrace tailWord_7181192 prefixEnd_7181192 1229134389407390928991435 := by
  unfold tailWord_7181192
  simp only [CollatzResearch.WordTrace]
  refine ⟨130959794899887654398020915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174613059866516872530694553 130959794899887654398020915)
  ·
    refine ⟨196439692349831481597031373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130959794899887654398020915 196439692349831481597031373)
    ·
      refine ⟨73664884631186805598886765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196439692349831481597031373 73664884631186805598886765)
      ·
        refine ⟨27624331736695052099582537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73664884631186805598886765 27624331736695052099582537)
        ·
          refine ⟨20718248802521289074686903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27624331736695052099582537 20718248802521289074686903)
          ·
            refine ⟨31077373203781933612030355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20718248802521289074686903 31077373203781933612030355)
            ·
              refine ⟨46616059805672900418045533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31077373203781933612030355 46616059805672900418045533)
              ·
                refine ⟨17481022427127337656767075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46616059805672900418045533 17481022427127337656767075)
                ·
                  refine ⟨26221533640691006485150613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17481022427127337656767075 26221533640691006485150613)
                  ·
                    refine ⟨1229134389407390928991435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26221533640691006485150613 1229134389407390928991435)
                    ·
                      rfl

theorem cell23_7181192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 3, 1, 6].length) (baseStart_7181192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181192 prefixEnd_7181192 := by exact prefixLift 7181192
  have htrace : WordTrace (prefixWord ++ tailWord_7181192) baseStart_7181192 baseEnd_7181192 := by
    simpa [prefixWord, tailWord_7181192, baseEnd_7181192] using wordTrace_append hprefix tailTrace_7181192
  have hstable : (prefixWord ++ tailWord_7181192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181192).length < 2 ^ (prefixWord ++ tailWord_7181192).sum := by decide
  have hdescent : baseEnd_7181192 < baseStart_7181192 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181195 : List Nat := [1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6]
def baseStart_7181195 : Nat := 118140960795 + 7181195 * 2 ^ 59
def prefixEnd_7181195 : Nat := 4983230072969 + 3 ^ 40 * 7181195 * 2
def baseEnd_7181195 : Nat := 3687404708664136275236791

theorem tailTrace_7181195 : CollatzResearch.WordTrace tailWord_7181195 prefixEnd_7181195 3687404708664136275236791 := by
  unfold tailWord_7181195
  simp only [CollatzResearch.WordTrace]
  refine ⟨261919699218764440308401039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174613132812509626872267359 261919699218764440308401039)
  ·
    refine ⟨392879548828146660462601559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261919699218764440308401039 392879548828146660462601559)
    ·
      refine ⟨589319323242219990693902339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392879548828146660462601559 589319323242219990693902339)
      ·
        refine ⟨883978984863329986040853509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589319323242219990693902339 883978984863329986040853509)
        ·
          refine ⟨165746059661874372382660033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 883978984863329986040853509 165746059661874372382660033)
          ·
            refine ⟨124309544746405779286995025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165746059661874372382660033 124309544746405779286995025)
            ·
              refine ⟨93232158559804334465246269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124309544746405779286995025 93232158559804334465246269)
              ·
                refine ⟨34962059459926625424467351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93232158559804334465246269 34962059459926625424467351)
                ·
                  refine ⟨52443089189889938136701027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34962059459926625424467351 52443089189889938136701027)
                  ·
                    refine ⟨78664633784834907205051541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52443089189889938136701027 78664633784834907205051541)
                    ·
                      refine ⟨3687404708664136275236791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78664633784834907205051541 3687404708664136275236791)
                      ·
                        rfl

theorem cell23_7181195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 6].length) (baseStart_7181195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181195 prefixEnd_7181195 := by exact prefixLift 7181195
  have htrace : WordTrace (prefixWord ++ tailWord_7181195) baseStart_7181195 baseEnd_7181195 := by
    simpa [prefixWord, tailWord_7181195, baseEnd_7181195] using wordTrace_append hprefix tailTrace_7181195
  have hstable : (prefixWord ++ tailWord_7181195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181195).length < 2 ^ (prefixWord ++ tailWord_7181195).sum := by decide
  have hdescent : baseEnd_7181195 < baseStart_7181195 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181233 : List Nat := [1, 2, 2, 4, 3, 1, 2, 1, 3, 2, 2]
def baseStart_7181233 : Nat := 118140960795 + 7181233 * 2 ^ 59
def prefixEnd_7181233 : Nat := 4983230072969 + 3 ^ 40 * 7181233 * 2
def baseEnd_7181233 : Nat := 3687424220929007126561617

theorem tailTrace_7181233 : CollatzResearch.WordTrace tailWord_7181233 prefixEnd_7181233 3687424220929007126561617 := by
  unfold tailWord_7181233
  simp only [CollatzResearch.WordTrace]
  refine ⟨261921085192626772798284353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174614056795084515198856235 261921085192626772798284353)
  ·
    refine ⟨196440813894470079598713265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261921085192626772798284353 196440813894470079598713265)
    ·
      refine ⟨147330610420852559699034949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196440813894470079598713265 147330610420852559699034949)
      ·
        refine ⟨27624489453909854943569053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147330610420852559699034949 27624489453909854943569053)
        ·
          refine ⟨10359183545216195603838395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27624489453909854943569053 10359183545216195603838395)
          ·
            refine ⟨15538775317824293405757593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359183545216195603838395 15538775317824293405757593)
            ·
              refine ⟨11654081488368220054318195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15538775317824293405757593 11654081488368220054318195)
              ·
                refine ⟨17481122232552330081477293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11654081488368220054318195 17481122232552330081477293)
                ·
                  refine ⟨6555420837207123780553985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17481122232552330081477293 6555420837207123780553985)
                  ·
                    refine ⟨4916565627905342835415489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555420837207123780553985 4916565627905342835415489)
                    ·
                      refine ⟨3687424220929007126561617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916565627905342835415489 3687424220929007126561617)
                      ·
                        rfl

theorem cell23_7181233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 1, 2, 1, 3, 2, 2].length) (baseStart_7181233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181233 prefixEnd_7181233 := by exact prefixLift 7181233
  have htrace : WordTrace (prefixWord ++ tailWord_7181233) baseStart_7181233 baseEnd_7181233 := by
    simpa [prefixWord, tailWord_7181233, baseEnd_7181233] using wordTrace_append hprefix tailTrace_7181233
  have hstable : (prefixWord ++ tailWord_7181233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181233).length < 2 ^ (prefixWord ++ tailWord_7181233).sum := by decide
  have hdescent : baseEnd_7181233 < baseStart_7181233 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181235 : List Nat := [1, 1, 1, 2, 3, 1, 2, 3, 2, 7]
def baseStart_7181235 : Nat := 118140960795 + 7181235 * 2 ^ 59
def prefixEnd_7181235 : Nat := 4983230072969 + 3 ^ 40 * 7181235 * 2
def baseEnd_7181235 : Nat := 1229141749296772039578869

theorem tailTrace_7181235 : CollatzResearch.WordTrace tailWord_7181235 prefixEnd_7181235 1229141749296772039578869 := by
  unfold tailWord_7181235
  simp only [CollatzResearch.WordTrace]
  refine ⟨261921158138619527139857159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174614105425746351426571439 261921158138619527139857159)
  ·
    refine ⟨392881737207929290709785739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261921158138619527139857159 392881737207929290709785739)
    ·
      refine ⟨589322605811893936064678609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392881737207929290709785739 589322605811893936064678609)
      ·
        refine ⟨441991954358920452048508957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589322605811893936064678609 441991954358920452048508957)
        ·
          refine ⟨165746982884595169518190859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 441991954358920452048508957 165746982884595169518190859)
          ·
            refine ⟨248620474326892754277286289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165746982884595169518190859 248620474326892754277286289)
            ·
              refine ⟨186465355745169565707964717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248620474326892754277286289 186465355745169565707964717)
              ·
                refine ⟨69924508404438587140486769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186465355745169565707964717 69924508404438587140486769)
                ·
                  refine ⟨52443381303328940355365077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69924508404438587140486769 52443381303328940355365077)
                  ·
                    refine ⟨1229141749296772039578869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52443381303328940355365077 1229141749296772039578869)
                    ·
                      rfl

theorem cell23_7181235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 2, 7].length) (baseStart_7181235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181235 prefixEnd_7181235 := by exact prefixLift 7181235
  have htrace : WordTrace (prefixWord ++ tailWord_7181235) baseStart_7181235 baseEnd_7181235 := by
    simpa [prefixWord, tailWord_7181235, baseEnd_7181235] using wordTrace_append hprefix tailTrace_7181235
  have hstable : (prefixWord ++ tailWord_7181235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181235).length < 2 ^ (prefixWord ++ tailWord_7181235).sum := by decide
  have hdescent : baseEnd_7181235 < baseStart_7181235 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181236 : List Nat := [2, 5, 2, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_7181236 : Nat := 118140960795 + 7181236 * 2 ^ 59
def prefixEnd_7181236 : Nat := 4983230072969 + 3 ^ 40 * 7181236 * 2
def baseEnd_7181236 : Nat := 3687425761370970614824103

theorem tailTrace_7181236 : CollatzResearch.WordTrace tailWord_7181236 prefixEnd_7181236 3687425761370970614824103 := by
  unfold tailWord_7181236
  simp only [CollatzResearch.WordTrace]
  refine ⟨130960597305807952155321781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174614129741077269540429041 130960597305807952155321781)
  ·
    refine ⟨12277555997419495514561417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 130960597305807952155321781 12277555997419495514561417)
    ·
      refine ⟨9208166998064621635921063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12277555997419495514561417 9208166998064621635921063)
      ·
        refine ⟨13812250497096932453881595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9208166998064621635921063 13812250497096932453881595)
        ·
          refine ⟨20718375745645398680822393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13812250497096932453881595 20718375745645398680822393)
          ·
            refine ⟨15538781809234049010616795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20718375745645398680822393 15538781809234049010616795)
            ·
              refine ⟨23308172713851073515925193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15538781809234049010616795 23308172713851073515925193)
              ·
                refine ⟨17481129535388305136943895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23308172713851073515925193 17481129535388305136943895)
                ·
                  refine ⟨26221694303082457705415843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17481129535388305136943895 26221694303082457705415843)
                  ·
                    refine ⟨39332541454623686558123765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26221694303082457705415843 39332541454623686558123765)
                    ·
                      refine ⟨3687425761370970614824103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39332541454623686558123765 3687425761370970614824103)
                      ·
                        rfl

theorem cell23_7181236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_7181236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181236 prefixEnd_7181236 := by exact prefixLift 7181236
  have htrace : WordTrace (prefixWord ++ tailWord_7181236) baseStart_7181236 baseEnd_7181236 := by
    simpa [prefixWord, tailWord_7181236, baseEnd_7181236] using wordTrace_append hprefix tailTrace_7181236
  have hstable : (prefixWord ++ tailWord_7181236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181236).length < 2 ^ (prefixWord ++ tailWord_7181236).sum := by decide
  have hdescent : baseEnd_7181236 < baseStart_7181236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181256 : List Nat := [2, 1, 3, 1, 6, 1, 2, 7]
def baseStart_7181256 : Nat := 118140960795 + 7181256 * 2 ^ 59
def prefixEnd_7181256 : Nat := 4983230072969 + 3 ^ 40 * 7181256 * 2
def baseEnd_7181256 : Nat := 136571704851261501354593

theorem tailTrace_7181256 : CollatzResearch.WordTrace tailWord_7181256 prefixEnd_7181256 136571704851261501354593 := by
  unfold tailWord_7181256
  simp only [CollatzResearch.WordTrace]
  refine ⟨130960962035771723863185811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174614616047695631817581081 130960962035771723863185811)
  ·
    refine ⟨196441443053657585794778717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130960962035771723863185811 196441443053657585794778717)
    ·
      refine ⟨73665541145121594673042019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196441443053657585794778717 73665541145121594673042019)
      ·
        refine ⟨110498311717682392009563029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73665541145121594673042019 110498311717682392009563029)
        ·
          refine ⟨5179608361766362125448267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 110498311717682392009563029 5179608361766362125448267)
          ·
            refine ⟨7769412542649543188172401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179608361766362125448267 7769412542649543188172401)
            ·
              refine ⟨5827059406987157391129301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7769412542649543188172401 5827059406987157391129301)
              ·
                refine ⟨136571704851261501354593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5827059406987157391129301 136571704851261501354593)
                ·
                  rfl

theorem cell23_7181256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 6, 1, 2, 7].length) (baseStart_7181256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181256 prefixEnd_7181256 := by exact prefixLift 7181256
  have htrace : WordTrace (prefixWord ++ tailWord_7181256) baseStart_7181256 baseEnd_7181256 := by
    simpa [prefixWord, tailWord_7181256, baseEnd_7181256] using wordTrace_append hprefix tailTrace_7181256
  have hstable : (prefixWord ++ tailWord_7181256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181256).length < 2 ^ (prefixWord ++ tailWord_7181256).sum := by decide
  have hdescent : baseEnd_7181256 < baseStart_7181256 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181261 : List Nat := [1, 6, 3, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_7181261 : Nat := 118140960795 + 7181261 * 2 ^ 59
def prefixEnd_7181261 : Nat := 4983230072969 + 3 ^ 40 * 7181261 * 2
def baseEnd_7181261 : Nat := 3687438598387333017011489

theorem tailTrace_7181261 : CollatzResearch.WordTrace tailWord_7181261 prefixEnd_7181261 3687438598387333017011489 := by
  unfold tailWord_7181261
  simp only [CollatzResearch.WordTrace]
  refine ⟨261922106436525333580303637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174614737624350222386869091 261922106436525333580303637)
  ·
    refine ⟨12277598739212125011576733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 261922106436525333580303637 12277598739212125011576733)
    ·
      refine ⟨4604099527204546879341275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 12277598739212125011576733 4604099527204546879341275)
      ·
        refine ⟨6906149290806820319011913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604099527204546879341275 6906149290806820319011913)
        ·
          refine ⟨5179611968105115239258935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6906149290806820319011913 5179611968105115239258935)
          ·
            refine ⟨7769417952157672858888403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179611968105115239258935 7769417952157672858888403)
            ·
              refine ⟨11654126928236509288332605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769417952157672858888403 11654126928236509288332605)
              ·
                refine ⟨4370297598088690983124727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11654126928236509288332605 4370297598088690983124727)
                ·
                  refine ⟨6555446397133036474687091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370297598088690983124727 6555446397133036474687091)
                  ·
                    refine ⟨9833169595699554712030637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6555446397133036474687091 9833169595699554712030637)
                    ·
                      refine ⟨3687438598387333017011489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833169595699554712030637 3687438598387333017011489)
                      ·
                        rfl

theorem cell23_7181261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_7181261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181261 prefixEnd_7181261 := by exact prefixLift 7181261
  have htrace : WordTrace (prefixWord ++ tailWord_7181261) baseStart_7181261 baseEnd_7181261 := by
    simpa [prefixWord, tailWord_7181261, baseEnd_7181261] using wordTrace_append hprefix tailTrace_7181261
  have hstable : (prefixWord ++ tailWord_7181261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181261).length < 2 ^ (prefixWord ++ tailWord_7181261).sum := by decide
  have hdescent : baseEnd_7181261 < baseStart_7181261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181262 : List Nat := [4, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_7181262 : Nat := 118140960795 + 7181262 * 2 ^ 59
def prefixEnd_7181262 : Nat := 4983230072969 + 3 ^ 40 * 7181262 * 2
def baseEnd_7181262 : Nat := 3687439111867987513098983

theorem tailTrace_7181262 : CollatzResearch.WordTrace tailWord_7181262 prefixEnd_7181262 3687439111867987513098983 := by
  unfold tailWord_7181262
  simp only [CollatzResearch.WordTrace]
  refine ⟨32740267863690213843886255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174614761939681140500726693 32740267863690213843886255)
  ·
    refine ⟨49110401795535320765829383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32740267863690213843886255 49110401795535320765829383)
    ·
      refine ⟨73665602693302981148744075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49110401795535320765829383 73665602693302981148744075)
      ·
        refine ⟨110498404039954471723116113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73665602693302981148744075 110498404039954471723116113)
        ·
          refine ⟨82873803029965853792337085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110498404039954471723116113 82873803029965853792337085)
          ·
            refine ⟨31077676136237195172126407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82873803029965853792337085 31077676136237195172126407)
            ·
              refine ⟨46616514204355792758189611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31077676136237195172126407 46616514204355792758189611)
              ·
                refine ⟨69924771306533689137284417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46616514204355792758189611 69924771306533689137284417)
                ·
                  refine ⟨52443578479900266852963313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69924771306533689137284417 52443578479900266852963313)
                  ·
                    refine ⟨39332683859925200139722485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52443578479900266852963313 39332683859925200139722485)
                    ·
                      refine ⟨3687439111867987513098983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39332683859925200139722485 3687439111867987513098983)
                      ·
                        rfl

theorem cell23_7181262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_7181262 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181262 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181262 prefixEnd_7181262 := by exact prefixLift 7181262
  have htrace : WordTrace (prefixWord ++ tailWord_7181262) baseStart_7181262 baseEnd_7181262 := by
    simpa [prefixWord, tailWord_7181262, baseEnd_7181262] using wordTrace_append hprefix tailTrace_7181262
  have hstable : (prefixWord ++ tailWord_7181262).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181262).length < 2 ^ (prefixWord ++ tailWord_7181262).sum := by decide
  have hdescent : baseEnd_7181262 < baseStart_7181262 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181266 : List Nat := [3, 2, 2, 3, 1, 1, 1, 2, 4, 1, 3]
def baseStart_7181266 : Nat := 118140960795 + 7181266 * 2 ^ 59
def prefixEnd_7181266 : Nat := 4983230072969 + 3 ^ 40 * 7181266 * 2
def baseEnd_7181266 : Nat := 3687441165790605497448965

theorem tailTrace_7181266 : CollatzResearch.WordTrace tailWord_7181266 prefixEnd_7181266 3687441165790605497448965 := by
  unfold tailWord_7181266
  simp only [CollatzResearch.WordTrace]
  refine ⟨65480572200376804858558913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174614859201004812956157101 65480572200376804858558913)
  ·
    refine ⟨49110429150282603643919185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65480572200376804858558913 49110429150282603643919185)
    ·
      refine ⟨36832821862711952732939389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49110429150282603643919185 36832821862711952732939389)
      ·
        refine ⟨13812308198516982274852271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36832821862711952732939389 13812308198516982274852271)
        ·
          refine ⟨20718462297775473412278407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13812308198516982274852271 20718462297775473412278407)
          ·
            refine ⟨31077693446663210118417611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20718462297775473412278407 31077693446663210118417611)
            ·
              refine ⟨46616540169994815177626417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31077693446663210118417611 46616540169994815177626417)
              ·
                refine ⟨34962405127496111383219813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46616540169994815177626417 34962405127496111383219813)
                ·
                  refine ⟨6555450961405520884353715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34962405127496111383219813 6555450961405520884353715)
                  ·
                    refine ⟨9833176442108281326530573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6555450961405520884353715 9833176442108281326530573)
                    ·
                      refine ⟨3687441165790605497448965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833176442108281326530573 3687441165790605497448965)
                      ·
                        rfl

theorem cell23_7181266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 1, 2, 4, 1, 3].length) (baseStart_7181266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181266 prefixEnd_7181266 := by exact prefixLift 7181266
  have htrace : WordTrace (prefixWord ++ tailWord_7181266) baseStart_7181266 baseEnd_7181266 := by
    simpa [prefixWord, tailWord_7181266, baseEnd_7181266] using wordTrace_append hprefix tailTrace_7181266
  have hstable : (prefixWord ++ tailWord_7181266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181266).length < 2 ^ (prefixWord ++ tailWord_7181266).sum := by decide
  have hdescent : baseEnd_7181266 < baseStart_7181266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181340 : List Nat := [2, 2, 3, 1, 4, 1, 2, 2, 2, 2, 2]
def baseStart_7181340 : Nat := 118140960795 + 7181340 * 2 ^ 59
def prefixEnd_7181340 : Nat := 4983230072969 + 3 ^ 40 * 7181340 * 2
def baseEnd_7181340 : Nat := 3687479163359038207923625

theorem tailTrace_7181340 : CollatzResearch.WordTrace tailWord_7181340 prefixEnd_7181340 3687479163359038207923625 := by
  unfold tailWord_7181340
  simp only [CollatzResearch.WordTrace]
  refine ⟨130962493901619565036214737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174616658535492753381619649 130962493901619565036214737)
  ·
    refine ⟨98221870426214673777161053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130962493901619565036214737 98221870426214673777161053)
    ·
      refine ⟨36833201409830502666435395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98221870426214673777161053 36833201409830502666435395)
      ·
        refine ⟨55249802114745753999653093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36833201409830502666435395 55249802114745753999653093)
        ·
          refine ⟨10359337896514828874934955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55249802114745753999653093 10359337896514828874934955)
          ·
            refine ⟨15539006844772243312402433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359337896514828874934955 15539006844772243312402433)
            ·
              refine ⟨11654255133579182484301825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15539006844772243312402433 11654255133579182484301825)
              ·
                refine ⟨8740691350184386863226369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11654255133579182484301825 8740691350184386863226369)
                ·
                  refine ⟨6555518512638290147419777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8740691350184386863226369 6555518512638290147419777)
                  ·
                    refine ⟨4916638884478717610564833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555518512638290147419777 4916638884478717610564833)
                    ·
                      refine ⟨3687479163359038207923625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916638884478717610564833 3687479163359038207923625)
                      ·
                        rfl

theorem cell23_7181340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 2, 2, 2].length) (baseStart_7181340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181340 prefixEnd_7181340 := by exact prefixLift 7181340
  have htrace : WordTrace (prefixWord ++ tailWord_7181340) baseStart_7181340 baseEnd_7181340 := by
    simpa [prefixWord, tailWord_7181340, baseEnd_7181340] using wordTrace_append hprefix tailTrace_7181340
  have hstable : (prefixWord ++ tailWord_7181340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181340).length < 2 ^ (prefixWord ++ tailWord_7181340).sum := by decide
  have hdescent : baseEnd_7181340 < baseStart_7181340 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181346 : List Nat := [3, 3, 1, 1, 1, 4, 1, 4, 5]
def baseStart_7181346 : Nat := 118140960795 + 7181346 * 2 ^ 59
def prefixEnd_7181346 : Nat := 4983230072969 + 3 ^ 40 * 7181346 * 2
def baseEnd_7181346 : Nat := 409720249360329464938733

theorem tailTrace_7181346 : CollatzResearch.WordTrace tailWord_7181346 prefixEnd_7181346 409720249360329464938733 := by
  unfold tailWord_7181346
  simp only [CollatzResearch.WordTrace]
  refine ⟨65481301660304348274286973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174616804427478262064765261 65481301660304348274286973)
  ·
    refine ⟨24555488122614130602857615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65481301660304348274286973 24555488122614130602857615)
    ·
      refine ⟨36833232183921195904286423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555488122614130602857615 36833232183921195904286423)
      ·
        refine ⟨55249848275881793856429635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36833232183921195904286423 55249848275881793856429635)
        ·
          refine ⟨82874772413822690784644453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55249848275881793856429635 82874772413822690784644453)
          ·
            refine ⟨15539019827591754522120835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82874772413822690784644453 15539019827591754522120835)
            ·
              refine ⟨23308529741387631783181253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15539019827591754522120835 23308529741387631783181253)
              ·
                refine ⟨4370349326510180959346485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23308529741387631783181253 4370349326510180959346485)
                ·
                  refine ⟨409720249360329464938733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4370349326510180959346485 409720249360329464938733)
                  ·
                    rfl

theorem cell23_7181346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_7181346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181346 prefixEnd_7181346 := by exact prefixLift 7181346
  have htrace : WordTrace (prefixWord ++ tailWord_7181346) baseStart_7181346 baseEnd_7181346 := by
    simpa [prefixWord, tailWord_7181346, baseEnd_7181346] using wordTrace_append hprefix tailTrace_7181346
  have hstable : (prefixWord ++ tailWord_7181346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181346).length < 2 ^ (prefixWord ++ tailWord_7181346).sum := by decide
  have hdescent : baseEnd_7181346 < baseStart_7181346 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181349 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 1, 7, 2]
def baseStart_7181349 : Nat := 118140960795 + 7181349 * 2 ^ 59
def prefixEnd_7181349 : Nat := 4983230072969 + 3 ^ 40 * 7181349 * 2
def baseEnd_7181349 : Nat := 3687483784684928672711083

theorem tailTrace_7181349 : CollatzResearch.WordTrace tailWord_7181349 prefixEnd_7181349 3687483784684928672711083 := by
  unfold tailWord_7181349
  simp only [CollatzResearch.WordTrace]
  refine ⟨261925316060206524609507101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174616877373471016406338067 261925316060206524609507101)
  ·
    refine ⟨98221993522577446728565163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261925316060206524609507101 98221993522577446728565163)
    ·
      refine ⟨147332990283866170092847745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98221993522577446728565163 147332990283866170092847745)
      ·
        refine ⟨110499742712899627569635809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147332990283866170092847745 110499742712899627569635809)
        ·
          refine ⟨82874807034674720677226857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110499742712899627569635809 82874807034674720677226857)
          ·
            refine ⟨62156105276006040507920143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82874807034674720677226857 62156105276006040507920143)
            ·
              refine ⟨93234157914009060761880215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62156105276006040507920143 93234157914009060761880215)
              ·
                refine ⟨139851236871013591142820323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93234157914009060761880215 139851236871013591142820323)
                ·
                  refine ⟨209776855306520386714230485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139851236871013591142820323 209776855306520386714230485)
                  ·
                    refine ⟨4916645046246571563614777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 209776855306520386714230485 4916645046246571563614777)
                    ·
                      refine ⟨3687483784684928672711083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916645046246571563614777 3687483784684928672711083)
                      ·
                        rfl

theorem cell23_7181349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_7181349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181349 prefixEnd_7181349 := by exact prefixLift 7181349
  have htrace : WordTrace (prefixWord ++ tailWord_7181349) baseStart_7181349 baseEnd_7181349 := by
    simpa [prefixWord, tailWord_7181349, baseEnd_7181349] using wordTrace_append hprefix tailTrace_7181349
  have hstable : (prefixWord ++ tailWord_7181349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181349).length < 2 ^ (prefixWord ++ tailWord_7181349).sum := by decide
  have hdescent : baseEnd_7181349 < baseStart_7181349 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181379 : List Nat := [1, 1, 1, 3, 1, 2, 3, 2, 1, 6, 2]
def baseStart_7181379 : Nat := 118140960795 + 7181379 * 2 ^ 59
def prefixEnd_7181379 : Nat := 4983230072969 + 3 ^ 40 * 7181379 * 2
def baseEnd_7181379 : Nat := 3687499189104563555335945

theorem tailTrace_7181379 : CollatzResearch.WordTrace tailWord_7181379 prefixEnd_7181379 3687499189104563555335945 := by
  unfold tailWord_7181379
  simp only [CollatzResearch.WordTrace]
  refine ⟨261926410250097839733099191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174617606833398559822066127 261926410250097839733099191)
  ·
    refine ⟨392889615375146759599648787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261926410250097839733099191 392889615375146759599648787)
    ·
      refine ⟨589334423062720139399473181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392889615375146759599648787 589334423062720139399473181)
      ·
        refine ⟨221000408648520052274802443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589334423062720139399473181 221000408648520052274802443)
        ·
          refine ⟨331500612972780078412203665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221000408648520052274802443 331500612972780078412203665)
          ·
            refine ⟨248625459729585058809152749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331500612972780078412203665 248625459729585058809152749)
            ·
              refine ⟨93234547398594397053432281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248625459729585058809152749 93234547398594397053432281)
              ·
                refine ⟨69925910548945797790074211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93234547398594397053432281 69925910548945797790074211)
                ·
                  refine ⟨104888865823418696685111317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69925910548945797790074211 104888865823418696685111317)
                  ·
                    refine ⟨4916665585472751407114593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104888865823418696685111317 4916665585472751407114593)
                    ·
                      refine ⟨3687499189104563555335945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916665585472751407114593 3687499189104563555335945)
                      ·
                        rfl

theorem cell23_7181379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 2, 1, 6, 2].length) (baseStart_7181379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181379 prefixEnd_7181379 := by exact prefixLift 7181379
  have htrace : WordTrace (prefixWord ++ tailWord_7181379) baseStart_7181379 baseEnd_7181379 := by
    simpa [prefixWord, tailWord_7181379, baseEnd_7181379] using wordTrace_append hprefix tailTrace_7181379
  have hstable : (prefixWord ++ tailWord_7181379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181379).length < 2 ^ (prefixWord ++ tailWord_7181379).sum := by decide
  have hdescent : baseEnd_7181379 < baseStart_7181379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181392 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4]
def baseStart_7181392 : Nat := 118140960795 + 7181392 * 2 ^ 59
def prefixEnd_7181392 : Nat := 4983230072969 + 3 ^ 40 * 7181392 * 2
def baseEnd_7181392 : Nat := 3687505864353072004473385

theorem tailTrace_7181392 : CollatzResearch.WordTrace tailWord_7181392 prefixEnd_7181392 3687505864353072004473385 := by
  unfold tailWord_7181392
  simp only [CollatzResearch.WordTrace]
  refine ⟨130963442199525371476661215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174617922932700495302214953 130963442199525371476661215)
  ·
    refine ⟨196445163299288057214991823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130963442199525371476661215 196445163299288057214991823)
    ·
      refine ⟨294667744948932085822487735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196445163299288057214991823 294667744948932085822487735)
      ·
        refine ⟨442001617423398128733731603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294667744948932085822487735 442001617423398128733731603)
        ·
          refine ⟨663002426135097193100597405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442001617423398128733731603 663002426135097193100597405)
          ·
            refine ⟨248625909800661447412724027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663002426135097193100597405 248625909800661447412724027)
            ·
              refine ⟨372938864700992171119086041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248625909800661447412724027 372938864700992171119086041)
              ·
                refine ⟨279704148525744128339314531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372938864700992171119086041 279704148525744128339314531)
                ·
                  refine ⟨419556222788616192508971797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 279704148525744128339314531 419556222788616192508971797)
                  ·
                    refine ⟨19666697943216384023858053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 419556222788616192508971797 19666697943216384023858053)
                    ·
                      refine ⟨3687505864353072004473385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19666697943216384023858053 3687505864353072004473385)
                      ·
                        rfl

theorem cell23_7181392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6, 4].length) (baseStart_7181392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181392 prefixEnd_7181392 := by exact prefixLift 7181392
  have htrace : WordTrace (prefixWord ++ tailWord_7181392) baseStart_7181392 baseEnd_7181392 := by
    simpa [prefixWord, tailWord_7181392, baseEnd_7181392] using wordTrace_append hprefix tailTrace_7181392
  have hstable : (prefixWord ++ tailWord_7181392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181392).length < 2 ^ (prefixWord ++ tailWord_7181392).sum := by decide
  have hdescent : baseEnd_7181392 < baseStart_7181392 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181396 : List Nat := [2, 4, 1, 1, 1, 1, 3, 2, 2, 4, 2]
def baseStart_7181396 : Nat := 118140960795 + 7181396 * 2 ^ 59
def prefixEnd_7181396 : Nat := 4983230072969 + 3 ^ 40 * 7181396 * 2
def baseEnd_7181396 : Nat := 3687507918275689988823367

theorem tailTrace_7181396 : CollatzResearch.WordTrace tailWord_7181396 prefixEnd_7181396 3687507918275689988823367 := by
  unfold tailWord_7181396
  simp only [CollatzResearch.WordTrace]
  refine ⟨130963515145518125818234021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174618020194024167757645361 130963515145518125818234021)
  ·
    refine ⟨24555659089784648590918879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130963515145518125818234021 24555659089784648590918879)
    ·
      refine ⟨36833488634676972886378319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24555659089784648590918879 36833488634676972886378319)
      ·
        refine ⟨55250232952015459329567479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36833488634676972886378319 55250232952015459329567479)
        ·
          refine ⟨82875349428023188994351219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55250232952015459329567479 82875349428023188994351219)
          ·
            refine ⟨124313024142034783491526829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82875349428023188994351219 124313024142034783491526829)
            ·
              refine ⟨46617384053263043809322561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124313024142034783491526829 46617384053263043809322561)
              ·
                refine ⟨34963038039947282856991921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46617384053263043809322561 34963038039947282856991921)
                ·
                  refine ⟨26222278529960462142743941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34963038039947282856991921 26222278529960462142743941)
                  ·
                    refine ⟨4916677224367586651764489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26222278529960462142743941 4916677224367586651764489)
                    ·
                      refine ⟨3687507918275689988823367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916677224367586651764489 3687507918275689988823367)
                      ·
                        rfl

theorem cell23_7181396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 2, 2, 4, 2].length) (baseStart_7181396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181396 prefixEnd_7181396 := by exact prefixLift 7181396
  have htrace : WordTrace (prefixWord ++ tailWord_7181396) baseStart_7181396 baseEnd_7181396 := by
    simpa [prefixWord, tailWord_7181396, baseEnd_7181396] using wordTrace_append hprefix tailTrace_7181396
  have hstable : (prefixWord ++ tailWord_7181396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181396).length < 2 ^ (prefixWord ++ tailWord_7181396).sum := by decide
  have hdescent : baseEnd_7181396 < baseStart_7181396 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181399 : List Nat := [1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 3]
def baseStart_7181399 : Nat := 118140960795 + 7181399 * 2 ^ 59
def prefixEnd_7181399 : Nat := 4983230072969 + 3 ^ 40 * 7181399 * 2
def baseEnd_7181399 : Nat := 3687509458717653477085853

theorem tailTrace_7181399 : CollatzResearch.WordTrace tailWord_7181399 prefixEnd_7181399 3687509458717653477085853 := by
  unfold tailWord_7181399
  simp only [CollatzResearch.WordTrace]
  refine ⟨261927139710025383148827251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174618093140016922099218167 261927139710025383148827251)
  ·
    refine ⟨392890709565038074723240877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261927139710025383148827251 392890709565038074723240877)
    ·
      refine ⟨147334016086889278021215329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392890709565038074723240877 147334016086889278021215329)
      ·
        refine ⟨110500512065166958515911497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147334016086889278021215329 110500512065166958515911497)
        ·
          refine ⟨82875384048875218886933623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110500512065166958515911497 82875384048875218886933623)
          ·
            refine ⟨124313076073312828330400435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82875384048875218886933623 124313076073312828330400435)
            ·
              refine ⟨186469614109969242495600653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124313076073312828330400435 186469614109969242495600653)
              ·
                refine ⟨69926105291238465935850245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186469614109969242495600653 69926105291238465935850245)
                ·
                  refine ⟨13111144742107212362971921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69926105291238465935850245 13111144742107212362971921)
                  ·
                    refine ⟨9833358556580409272228941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13111144742107212362971921 9833358556580409272228941)
                    ·
                      refine ⟨3687509458717653477085853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833358556580409272228941 3687509458717653477085853)
                      ·
                        rfl

theorem cell23_7181399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_7181399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181399 prefixEnd_7181399 := by exact prefixLift 7181399
  have htrace : WordTrace (prefixWord ++ tailWord_7181399) baseStart_7181399 baseEnd_7181399 := by
    simpa [prefixWord, tailWord_7181399, baseEnd_7181399] using wordTrace_append hprefix tailTrace_7181399
  have hstable : (prefixWord ++ tailWord_7181399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181399).length < 2 ^ (prefixWord ++ tailWord_7181399).sum := by decide
  have hdescent : baseEnd_7181399 < baseStart_7181399 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181463 : List Nat := [1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3]
def baseStart_7181463 : Nat := 118140960795 + 7181463 * 2 ^ 59
def prefixEnd_7181463 : Nat := 4983230072969 + 3 ^ 40 * 7181463 * 2
def baseEnd_7181463 : Nat := 3687542321479541226685559

theorem tailTrace_7181463 : CollatzResearch.WordTrace tailWord_7181463 prefixEnd_7181463 3687542321479541226685559 := by
  unfold tailWord_7181463
  simp only [CollatzResearch.WordTrace]
  refine ⟨261929473981793522079157043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174619649321195681386104695 261929473981793522079157043)
  ·
    refine ⟨392894210972690283118735565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261929473981793522079157043 392894210972690283118735565)
    ·
      refine ⟨147335329114758856169525837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392894210972690283118735565 147335329114758856169525837)
      ·
        refine ⟨55250748418034571063572189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147335329114758856169525837 55250748418034571063572189)
        ·
          refine ⟨20719030656762964148839571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55250748418034571063572189 20719030656762964148839571)
          ·
            refine ⟨31078545985144446223259357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20719030656762964148839571 31078545985144446223259357)
            ·
              refine ⟨11654454744429167333722259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31078545985144446223259357 11654454744429167333722259)
              ·
                refine ⟨17481682116643751000583389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11654454744429167333722259 17481682116643751000583389)
                ·
                  refine ⟨6555630793741406625218771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17481682116643751000583389 6555630793741406625218771)
                  ·
                    refine ⟨9833446190612109937828157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6555630793741406625218771 9833446190612109937828157)
                    ·
                      refine ⟨3687542321479541226685559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833446190612109937828157 3687542321479541226685559)
                      ·
                        rfl

theorem cell23_7181463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_7181463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181463 prefixEnd_7181463 := by exact prefixLift 7181463
  have htrace : WordTrace (prefixWord ++ tailWord_7181463) baseStart_7181463 baseEnd_7181463 := by
    simpa [prefixWord, tailWord_7181463, baseEnd_7181463] using wordTrace_append hprefix tailTrace_7181463
  have hstable : (prefixWord ++ tailWord_7181463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181463).length < 2 ^ (prefixWord ++ tailWord_7181463).sum := by decide
  have hdescent : baseEnd_7181463 < baseStart_7181463 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181470 : List Nat := [4, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_7181470 : Nat := 118140960795 + 7181470 * 2 ^ 59
def prefixEnd_7181470 : Nat := 4983230072969 + 3 ^ 40 * 7181470 * 2
def baseEnd_7181470 : Nat := 409727323982680299922003

theorem tailTrace_7181470 : CollatzResearch.WordTrace tailWord_7181470 prefixEnd_7181470 409727323982680299922003 := by
  unfold tailWord_7181470
  simp only [CollatzResearch.WordTrace]
  refine ⟨32741216161596020284332733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174619819528512108183107909 32741216161596020284332733)
  ·
    refine ⟨12277956060598507606624775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32741216161596020284332733 12277956060598507606624775)
    ·
      refine ⟨18416934090897761409937163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12277956060598507606624775 18416934090897761409937163)
      ·
        refine ⟨27625401136346642114905745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18416934090897761409937163 27625401136346642114905745)
        ·
          refine ⟨20719050852259981586179309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27625401136346642114905745 20719050852259981586179309)
          ·
            refine ⟨7769644069597493094817241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20719050852259981586179309 7769644069597493094817241)
            ·
              refine ⟨5827233052198119821112931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7769644069597493094817241 5827233052198119821112931)
              ·
                refine ⟨8740849578297179731669397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827233052198119821112931 8740849578297179731669397)
                ·
                  refine ⟨409727323982680299922003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8740849578297179731669397 409727323982680299922003)
                  ·
                    rfl

theorem cell23_7181470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_7181470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181470 prefixEnd_7181470 := by exact prefixLift 7181470
  have htrace : WordTrace (prefixWord ++ tailWord_7181470) baseStart_7181470 baseEnd_7181470 := by
    simpa [prefixWord, tailWord_7181470, baseEnd_7181470] using wordTrace_append hprefix tailTrace_7181470
  have hstable : (prefixWord ++ tailWord_7181470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181470).length < 2 ^ (prefixWord ++ tailWord_7181470).sum := by decide
  have hdescent : baseEnd_7181470 < baseStart_7181470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181536 : List Nat := [2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3]
def baseStart_7181536 : Nat := 118140960795 + 7181536 * 2 ^ 59
def prefixEnd_7181536 : Nat := 4983230072969 + 3 ^ 40 * 7181536 * 2
def baseEnd_7181536 : Nat := 3687579805567319441072723

theorem tailTrace_7181536 : CollatzResearch.WordTrace tailWord_7181536 prefixEnd_7181536 3687579805567319441072723 := by
  unfold tailWord_7181536
  simp only [CollatzResearch.WordTrace]
  refine ⟨130966068255264527773282231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174621424340352703697709641 130966068255264527773282231)
  ·
    refine ⟨196449102382896791659923347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130966068255264527773282231 196449102382896791659923347)
    ·
      refine ⟨294673653574345187489885021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196449102382896791659923347 294673653574345187489885021)
      ·
        refine ⟨110502620090379445308706883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294673653574345187489885021 110502620090379445308706883)
        ·
          refine ⟨165753930135569167963060325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110502620090379445308706883 165753930135569167963060325)
          ·
            refine ⟨31078861900419218993073811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165753930135569167963060325 31078861900419218993073811)
            ·
              refine ⟨46618292850628828489610717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31078861900419218993073811 46618292850628828489610717)
              ·
                refine ⟨17481859818985810683604019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46618292850628828489610717 17481859818985810683604019)
                ·
                  refine ⟨26222789728478716025406029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17481859818985810683604019 26222789728478716025406029)
                  ·
                    refine ⟨9833546148179518509527261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26222789728478716025406029 9833546148179518509527261)
                    ·
                      refine ⟨3687579805567319441072723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833546148179518509527261 3687579805567319441072723)
                      ·
                        rfl

theorem cell23_7181536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_7181536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181536 prefixEnd_7181536 := by exact prefixLift 7181536
  have htrace : WordTrace (prefixWord ++ tailWord_7181536) baseStart_7181536 baseEnd_7181536 := by
    simpa [prefixWord, tailWord_7181536, baseEnd_7181536] using wordTrace_append hprefix tailTrace_7181536
  have hstable : (prefixWord ++ tailWord_7181536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181536).length < 2 ^ (prefixWord ++ tailWord_7181536).sum := by decide
  have hdescent : baseEnd_7181536 < baseStart_7181536 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181543 : List Nat := [1, 1, 5, 3, 2, 1, 3, 7]
def baseStart_7181543 : Nat := 118140960795 + 7181543 * 2 ^ 59
def prefixEnd_7181543 : Nat := 4983230072969 + 3 ^ 40 * 7181543 * 2
def baseEnd_7181543 : Nat := 136577162960440774580933

theorem tailTrace_7181543 : CollatzResearch.WordTrace tailWord_7181543 prefixEnd_7181543 136577162960440774580933 := by
  unfold tailWord_7181543
  simp only [CollatzResearch.WordTrace]
  refine ⟨261932391821503695742069283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174621594547669130494712855 261932391821503695742069283)
  ·
    refine ⟨392898587732255543613103925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261932391821503695742069283 392898587732255543613103925)
    ·
      refine ⟨36834242599898957213728493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 392898587732255543613103925 36834242599898957213728493)
      ·
        refine ⟨13812840974962108955148185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36834242599898957213728493 13812840974962108955148185)
        ·
          refine ⟨10359630731221581716361139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13812840974962108955148185 10359630731221581716361139)
          ·
            refine ⟨15539446096832372574541709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359630731221581716361139 15539446096832372574541709)
            ·
              refine ⟨5827292286312139715453141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15539446096832372574541709 5827292286312139715453141)
              ·
                refine ⟨136577162960440774580933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5827292286312139715453141 136577162960440774580933)
                ·
                  rfl

theorem cell23_7181543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 1, 3, 7].length) (baseStart_7181543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181543 prefixEnd_7181543 := by exact prefixLift 7181543
  have htrace : WordTrace (prefixWord ++ tailWord_7181543) baseStart_7181543 baseEnd_7181543 := by
    simpa [prefixWord, tailWord_7181543, baseEnd_7181543] using wordTrace_append hprefix tailTrace_7181543
  have hstable : (prefixWord ++ tailWord_7181543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181543).length < 2 ^ (prefixWord ++ tailWord_7181543).sum := by decide
  have hdescent : baseEnd_7181543 < baseStart_7181543 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181554 : List Nat := [3, 2, 1, 3, 3, 1, 2, 3, 1, 2, 2]
def baseStart_7181554 : Nat := 118140960795 + 7181554 * 2 ^ 59
def prefixEnd_7181554 : Nat := 4983230072969 + 3 ^ 40 * 7181554 * 2
def baseEnd_7181554 : Nat := 3687589048219100370647641

theorem tailTrace_7181554 : CollatzResearch.WordTrace tailWord_7181554 prefixEnd_7181554 3687589048219100370647641 := by
  unfold tailWord_7181554
  simp only [CollatzResearch.WordTrace]
  refine ⟨65483198256115961155179929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174621862016309229747146477 65483198256115961155179929)
  ·
    refine ⟨49112398692086970866384947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65483198256115961155179929 49112398692086970866384947)
    ·
      refine ⟨73668598038130456299577421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49112398692086970866384947 73668598038130456299577421)
      ·
        refine ⟨27625724264298921112341533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73668598038130456299577421 27625724264298921112341533)
        ·
          refine ⟨10359646599112095417128075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27625724264298921112341533 10359646599112095417128075)
          ·
            refine ⟨15539469898668143125692113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359646599112095417128075 15539469898668143125692113)
            ·
              refine ⟨11654602424001107344269085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15539469898668143125692113 11654602424001107344269085)
              ·
                refine ⟨4370475909000415254100907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11654602424001107344269085 4370475909000415254100907)
                ·
                  refine ⟨6555713863500622881151361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370475909000415254100907 6555713863500622881151361)
                  ·
                    refine ⟨4916785397625467160863521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555713863500622881151361 4916785397625467160863521)
                    ·
                      refine ⟨3687589048219100370647641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916785397625467160863521 3687589048219100370647641)
                      ·
                        rfl

theorem cell23_7181554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 3, 1, 2, 2].length) (baseStart_7181554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181554 prefixEnd_7181554 := by exact prefixLift 7181554
  have htrace : WordTrace (prefixWord ++ tailWord_7181554) baseStart_7181554 baseEnd_7181554 := by
    simpa [prefixWord, tailWord_7181554, baseEnd_7181554] using wordTrace_append hprefix tailTrace_7181554
  have hstable : (prefixWord ++ tailWord_7181554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181554).length < 2 ^ (prefixWord ++ tailWord_7181554).sum := by decide
  have hdescent : baseEnd_7181554 < baseStart_7181554 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181559 : List Nat := [1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 4]
def baseStart_7181559 : Nat := 118140960795 + 7181559 * 2 ^ 59
def prefixEnd_7181559 : Nat := 4983230072969 + 3 ^ 40 * 7181559 * 2
def baseEnd_7181559 : Nat := 3687591615622372851085117

theorem tailTrace_7181559 : CollatzResearch.WordTrace tailWord_7181559 prefixEnd_7181559 3687591615622372851085117 := by
  unfold tailWord_7181559
  simp only [CollatzResearch.WordTrace]
  refine ⟨261932975389445730474651731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174621983592963820316434487 261932975389445730474651731)
  ·
    refine ⟨392899463084168595711977597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261932975389445730474651731 392899463084168595711977597)
    ·
      refine ⟨147337298656563223391991599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392899463084168595711977597 147337298656563223391991599)
      ·
        refine ⟨221005947984844835087987399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147337298656563223391991599 221005947984844835087987399)
        ·
          refine ⟨331508921977267252631981099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221005947984844835087987399 331508921977267252631981099)
          ·
            refine ⟨497263382965900878947971649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331508921977267252631981099 497263382965900878947971649)
            ·
              refine ⟨372947537224425659210978737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497263382965900878947971649 372947537224425659210978737)
              ·
                refine ⟨279710652918319244408234053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 372947537224425659210978737 279710652918319244408234053)
                ·
                  refine ⟨52445747422184858326543885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279710652918319244408234053 52445747422184858326543885)
                  ·
                    refine ⟨19667155283319321872453957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52445747422184858326543885 19667155283319321872453957)
                    ·
                      refine ⟨3687591615622372851085117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19667155283319321872453957 3687591615622372851085117)
                      ·
                        rfl

theorem cell23_7181559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 4].length) (baseStart_7181559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181559 prefixEnd_7181559 := by exact prefixLift 7181559
  have htrace : WordTrace (prefixWord ++ tailWord_7181559) baseStart_7181559 baseEnd_7181559 := by
    simpa [prefixWord, tailWord_7181559, baseEnd_7181559] using wordTrace_append hprefix tailTrace_7181559
  have hstable : (prefixWord ++ tailWord_7181559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181559).length < 2 ^ (prefixWord ++ tailWord_7181559).sum := by decide
  have hdescent : baseEnd_7181559 < baseStart_7181559 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181596 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_7181596 : Nat := 118140960795 + 7181596 * 2 ^ 59
def prefixEnd_7181596 : Nat := 4983230072969 + 3 ^ 40 * 7181596 * 2
def baseEnd_7181596 : Nat := 3687610614406589206322447

theorem tailTrace_7181596 : CollatzResearch.WordTrace tailWord_7181596 prefixEnd_7181596 3687610614406589206322447 := by
  unfold tailWord_7181596
  simp only [CollatzResearch.WordTrace]
  refine ⟨130967162445155842896874321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174622883260207790529165761 130967162445155842896874321)
  ·
    refine ⟨98225371833866882172655741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130967162445155842896874321 98225371833866882172655741)
    ·
      refine ⟨36834514437700080814745903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98225371833866882172655741 36834514437700080814745903)
      ·
        refine ⟨55251771656550121222118855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36834514437700080814745903 55251771656550121222118855)
        ·
          refine ⟨82877657484825181833178283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55251771656550121222118855 82877657484825181833178283)
          ·
            refine ⟨124316486227237772749767425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82877657484825181833178283 124316486227237772749767425)
            ·
              refine ⟨93237364670428329562325569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124316486227237772749767425 93237364670428329562325569)
              ·
                refine ⟨69928023502821247171744177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93237364670428329562325569 69928023502821247171744177)
                ·
                  refine ⟨52446017627115935378808133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69928023502821247171744177 52446017627115935378808133)
                  ·
                    refine ⟨9833628305084237883526525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52446017627115935378808133 9833628305084237883526525)
                    ·
                      refine ⟨3687610614406589206322447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833628305084237883526525 3687610614406589206322447)
                      ·
                        rfl

theorem cell23_7181596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_7181596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181596 prefixEnd_7181596 := by exact prefixLift 7181596
  have htrace : WordTrace (prefixWord ++ tailWord_7181596) baseStart_7181596 baseEnd_7181596 := by
    simpa [prefixWord, tailWord_7181596, baseEnd_7181596] using wordTrace_append hprefix tailTrace_7181596
  have hstable : (prefixWord ++ tailWord_7181596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181596).length < 2 ^ (prefixWord ++ tailWord_7181596).sum := by decide
  have hdescent : baseEnd_7181596 < baseStart_7181596 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181597 : List Nat := [1, 4, 2, 3, 1, 2, 2, 2, 1, 3, 2]
def baseStart_7181597 : Nat := 118140960795 + 7181597 * 2 ^ 59
def prefixEnd_7181597 : Nat := 4983230072969 + 3 ^ 40 * 7181597 * 2
def baseEnd_7181597 : Nat := 3687611127887243702409943

theorem tailTrace_7181597 : CollatzResearch.WordTrace tailWord_7181597 prefixEnd_7181597 3687611127887243702409943 := by
  unfold tailWord_7181597
  simp only [CollatzResearch.WordTrace]
  refine ⟨261934361363308062964535045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174622907575538708643023363 261934361363308062964535045)
  ·
    refine ⟨49112692755620261805850321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261934361363308062964535045 49112692755620261805850321)
    ·
      refine ⟨36834519566715196354387741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49112692755620261805850321 36834519566715196354387741)
      ·
        refine ⟨13812944837518198632895403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36834519566715196354387741 13812944837518198632895403)
        ·
          refine ⟨20719417256277297949343105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13812944837518198632895403 20719417256277297949343105)
          ·
            refine ⟨15539562942207973462007329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20719417256277297949343105 15539562942207973462007329)
            ·
              refine ⟨11654672206655980096505497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15539562942207973462007329 11654672206655980096505497)
              ·
                refine ⟨8741004154991985072379123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11654672206655980096505497 8741004154991985072379123)
                ·
                  refine ⟨13111506232487977608568685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8741004154991985072379123 13111506232487977608568685)
                  ·
                    refine ⟨4916814837182991603213257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13111506232487977608568685 4916814837182991603213257)
                    ·
                      refine ⟨3687611127887243702409943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916814837182991603213257 3687611127887243702409943)
                      ·
                        rfl

theorem cell23_7181597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 2, 2, 1, 3, 2].length) (baseStart_7181597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181597 prefixEnd_7181597 := by exact prefixLift 7181597
  have htrace : WordTrace (prefixWord ++ tailWord_7181597) baseStart_7181597 baseEnd_7181597 := by
    simpa [prefixWord, tailWord_7181597, baseEnd_7181597] using wordTrace_append hprefix tailTrace_7181597
  have hstable : (prefixWord ++ tailWord_7181597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181597).length < 2 ^ (prefixWord ++ tailWord_7181597).sum := by decide
  have hdescent : baseEnd_7181597 < baseStart_7181597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181613 : List Nat := [1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 5]
def baseStart_7181613 : Nat := 118140960795 + 7181613 * 2 ^ 59
def prefixEnd_7181613 : Nat := 4983230072969 + 3 ^ 40 * 7181613 * 2
def baseEnd_7181613 : Nat := 3687619343577715639809869

theorem tailTrace_7181613 : CollatzResearch.WordTrace tailWord_7181613 prefixEnd_7181613 3687619343577715639809869 := by
  unfold tailWord_7181613
  simp only [CollatzResearch.WordTrace]
  refine ⟨261934944931250097697117493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174623296620833398464744995 261934944931250097697117493)
  ·
    refine ⟨24556401087304696659104765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261934944931250097697117493 24556401087304696659104765)
    ·
      refine ⟨9208650407739261247164287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24556401087304696659104765 9208650407739261247164287)
      ·
        refine ⟨13812975611608891870746431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9208650407739261247164287 13812975611608891870746431)
        ·
          refine ⟨20719463417413337806119647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13812975611608891870746431 20719463417413337806119647)
          ·
            refine ⟨31079195126120006709179471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20719463417413337806119647 31079195126120006709179471)
            ·
              refine ⟨46618792689180010063769207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31079195126120006709179471 46618792689180010063769207)
              ·
                refine ⟨69928189033770015095653811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46618792689180010063769207 69928189033770015095653811)
                ·
                  refine ⟨104892283550655022643480717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69928189033770015095653811 104892283550655022643480717)
                  ·
                    refine ⟨39334606331495633491305269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104892283550655022643480717 39334606331495633491305269)
                    ·
                      refine ⟨3687619343577715639809869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39334606331495633491305269 3687619343577715639809869)
                      ·
                        rfl

theorem cell23_7181613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 1, 3, 5].length) (baseStart_7181613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181613 prefixEnd_7181613 := by exact prefixLift 7181613
  have htrace : WordTrace (prefixWord ++ tailWord_7181613) baseStart_7181613 baseEnd_7181613 := by
    simpa [prefixWord, tailWord_7181613, baseEnd_7181613] using wordTrace_append hprefix tailTrace_7181613
  have hstable : (prefixWord ++ tailWord_7181613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181613).length < 2 ^ (prefixWord ++ tailWord_7181613).sum := by decide
  have hdescent : baseEnd_7181613 < baseStart_7181613 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181633 : List Nat := [1, 2, 5, 2, 1, 1, 3, 1, 7]
def baseStart_7181633 : Nat := 118140960795 + 7181633 * 2 ^ 59
def prefixEnd_7181633 : Nat := 4983230072969 + 3 ^ 40 * 7181633 * 2
def baseEnd_7181633 : Nat := 409736623687867284617753

theorem tailTrace_7181633 : CollatzResearch.WordTrace tailWord_7181633 prefixEnd_7181633 409736623687867284617753 := by
  unfold tailWord_7181633
  simp only [CollatzResearch.WordTrace]
  refine ⟨261935674391177641112845553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174623782927451760741897035 261935674391177641112845553)
  ·
    refine ⟨196451755793383230834634165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261935674391177641112845553 196451755793383230834634165)
    ·
      refine ⟨18417352105629677890746953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196451755793383230834634165 18417352105629677890746953)
      ·
        refine ⟨13813014079222258418060215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18417352105629677890746953 13813014079222258418060215)
        ·
          refine ⟨20719521118833387627090323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13813014079222258418060215 20719521118833387627090323)
          ·
            refine ⟨31079281678250081440635485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20719521118833387627090323 31079281678250081440635485)
            ·
              refine ⟨11654730629343780540238307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31079281678250081440635485 11654730629343780540238307)
              ·
                refine ⟨17482095944015670810357461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11654730629343780540238307 17482095944015670810357461)
                ·
                  refine ⟨409736623687867284617753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17482095944015670810357461 409736623687867284617753)
                  ·
                    rfl

theorem cell23_7181633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 3, 1, 7].length) (baseStart_7181633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181633 prefixEnd_7181633 := by exact prefixLift 7181633
  have htrace : WordTrace (prefixWord ++ tailWord_7181633) baseStart_7181633 baseEnd_7181633 := by
    simpa [prefixWord, tailWord_7181633, baseEnd_7181633] using wordTrace_append hprefix tailTrace_7181633
  have hstable : (prefixWord ++ tailWord_7181633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181633).length < 2 ^ (prefixWord ++ tailWord_7181633).sum := by decide
  have hdescent : baseEnd_7181633 < baseStart_7181633 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181638 : List Nat := [6, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3]
def baseStart_7181638 : Nat := 118140960795 + 7181638 * 2 ^ 59
def prefixEnd_7181638 : Nat := 4983230072969 + 3 ^ 40 * 7181638 * 2
def baseEnd_7181638 : Nat := 3687632180594078041997255

theorem tailTrace_7181638 : CollatzResearch.WordTrace tailWord_7181638 prefixEnd_7181638 3687632180594078041997255 := by
  unfold tailWord_7181638
  simp only [CollatzResearch.WordTrace]
  refine ⟨8185495523629985217711799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174623904504106351311185045 8185495523629985217711799)
  ·
    refine ⟨12278243285444977826567699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8185495523629985217711799 12278243285444977826567699)
    ·
      refine ⟨18417364928167466739851549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12278243285444977826567699 18417364928167466739851549)
      ·
        refine ⟨6906511848062800027444331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18417364928167466739851549 6906511848062800027444331)
        ·
          refine ⟨10359767772094200041166497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906511848062800027444331 10359767772094200041166497)
          ·
            refine ⟨7769825829070650030874873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10359767772094200041166497 7769825829070650030874873)
            ·
              refine ⟨5827369371802987523156155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7769825829070650030874873 5827369371802987523156155)
              ·
                refine ⟨8741054057704481284734233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827369371802987523156155 8741054057704481284734233)
                ·
                  refine ⟨6555790543278360963550675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8741054057704481284734233 6555790543278360963550675)
                  ·
                    refine ⟨9833685814917541445326013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6555790543278360963550675 9833685814917541445326013)
                    ·
                      refine ⟨3687632180594078041997255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833685814917541445326013 3687632180594078041997255)
                      ·
                        rfl

theorem cell23_7181638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3].length) (baseStart_7181638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181638 prefixEnd_7181638 := by exact prefixLift 7181638
  have htrace : WordTrace (prefixWord ++ tailWord_7181638) baseStart_7181638 baseEnd_7181638 := by
    simpa [prefixWord, tailWord_7181638, baseEnd_7181638] using wordTrace_append hprefix tailTrace_7181638
  have hstable : (prefixWord ++ tailWord_7181638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181638).length < 2 ^ (prefixWord ++ tailWord_7181638).sum := by decide
  have hdescent : baseEnd_7181638 < baseStart_7181638 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181644 : List Nat := [2, 2, 1, 3, 2, 4, 2, 1, 2, 2, 2]
def baseStart_7181644 : Nat := 118140960795 + 7181644 * 2 ^ 59
def prefixEnd_7181644 : Nat := 4983230072969 + 3 ^ 40 * 7181644 * 2
def baseEnd_7181644 : Nat := 3687635261478005018522227

theorem tailTrace_7181644 : CollatzResearch.WordTrace tailWord_7181644 prefixEnd_7181644 3687635261478005018522227 := by
  unfold tailWord_7181644
  simp only [CollatzResearch.WordTrace]
  refine ⟨130968037797068894995747993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174624050396091859994330657 130968037797068894995747993)
  ·
    refine ⟨98226028347801671246810995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130968037797068894995747993 98226028347801671246810995)
    ·
      refine ⟨147339042521702506870216493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98226028347801671246810995 147339042521702506870216493)
      ·
        refine ⟨55252140945638440076331185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147339042521702506870216493 55252140945638440076331185)
        ·
          refine ⟨41439105709228830057248389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55252140945638440076331185 41439105709228830057248389)
          ·
            refine ⟨7769832320480405635734073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41439105709228830057248389 7769832320480405635734073)
            ·
              refine ⟨5827374240360304226800555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7769832320480405635734073 5827374240360304226800555)
              ·
                refine ⟨8741061360540456340200833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827374240360304226800555 8741061360540456340200833)
                ·
                  refine ⟨6555796020405342255150625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8741061360540456340200833 6555796020405342255150625)
                  ·
                    refine ⟨4916847015304006691362969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555796020405342255150625 4916847015304006691362969)
                    ·
                      refine ⟨3687635261478005018522227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916847015304006691362969 3687635261478005018522227)
                      ·
                        rfl

theorem cell23_7181644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_7181644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181644 prefixEnd_7181644 := by exact prefixLift 7181644
  have htrace : WordTrace (prefixWord ++ tailWord_7181644) baseStart_7181644 baseEnd_7181644 := by
    simpa [prefixWord, tailWord_7181644, baseEnd_7181644] using wordTrace_append hprefix tailTrace_7181644
  have hstable : (prefixWord ++ tailWord_7181644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181644).length < 2 ^ (prefixWord ++ tailWord_7181644).sum := by decide
  have hdescent : baseEnd_7181644 < baseStart_7181644 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181646 : List Nat := [4, 1, 1, 1, 1, 1, 3, 2, 4, 5]
def baseStart_7181646 : Nat := 118140960795 + 7181646 * 2 ^ 59
def prefixEnd_7181646 : Nat := 4983230072969 + 3 ^ 40 * 7181646 * 2
def baseEnd_7181646 : Nat := 1229212096146438003565739

theorem tailTrace_7181646 : CollatzResearch.WordTrace tailWord_7181646 prefixEnd_7181646 1229212096146438003565739 := by
  unfold tailWord_7181646
  simp only [CollatzResearch.WordTrace]
  refine ⟨32742018567516318041633599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174624099026753696222045861 32742018567516318041633599)
  ·
    refine ⟨49113027851274477062450399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32742018567516318041633599 49113027851274477062450399)
    ·
      refine ⟨73669541776911715593675599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49113027851274477062450399 73669541776911715593675599)
      ·
        refine ⟨110504312665367573390513399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73669541776911715593675599 110504312665367573390513399)
        ·
          refine ⟨165756468998051360085770099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110504312665367573390513399 165756468998051360085770099)
          ·
            refine ⟨248634703497077040128655149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165756468998051360085770099 248634703497077040128655149)
            ·
              refine ⟨93238013811403890048245681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248634703497077040128655149 93238013811403890048245681)
              ·
                refine ⟨69928510358552917536184261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93238013811403890048245681 69928510358552917536184261)
                ·
                  refine ⟨13111595692228672038034549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69928510358552917536184261 13111595692228672038034549)
                  ·
                    refine ⟨1229212096146438003565739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13111595692228672038034549 1229212096146438003565739)
                    ·
                      rfl

theorem cell23_7181646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_7181646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181646 prefixEnd_7181646 := by exact prefixLift 7181646
  have htrace : WordTrace (prefixWord ++ tailWord_7181646) baseStart_7181646 baseEnd_7181646 := by
    simpa [prefixWord, tailWord_7181646, baseEnd_7181646] using wordTrace_append hprefix tailTrace_7181646
  have hstable : (prefixWord ++ tailWord_7181646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181646).length < 2 ^ (prefixWord ++ tailWord_7181646).sum := by decide
  have hdescent : baseEnd_7181646 < baseStart_7181646 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181693 : List Nat := [1, 4, 1, 1, 2, 2, 2, 3, 3, 4]
def baseStart_7181693 : Nat := 118140960795 + 7181693 * 2 ^ 59
def prefixEnd_7181693 : Nat := 4983230072969 + 3 ^ 40 * 7181693 * 2
def baseEnd_7181693 : Nat := 1229220140676691775603167

theorem tailTrace_7181693 : CollatzResearch.WordTrace tailWord_7181693 prefixEnd_7181693 1229220140676691775603167 := by
  unfold tailWord_7181693
  simp only [CollatzResearch.WordTrace]
  refine ⟨261937862770960271360029733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174625241847306847573353155 261937862770960271360029733)
  ·
    refine ⟨49113349269555050880005575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 261937862770960271360029733 49113349269555050880005575)
    ·
      refine ⟨73670023904332576320008363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49113349269555050880005575 73670023904332576320008363)
      ·
        refine ⟨110505035856498864480012545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73670023904332576320008363 110505035856498864480012545)
        ·
          refine ⟨82878776892374148360009409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110505035856498864480012545 82878776892374148360009409)
          ·
            refine ⟨62159082669280611270007057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82878776892374148360009409 62159082669280611270007057)
            ·
              refine ⟨46619312001960458452505293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62159082669280611270007057 46619312001960458452505293)
              ·
                refine ⟨17482242000735171919689485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46619312001960458452505293 17482242000735171919689485)
                ·
                  refine ⟨6555840750275689469883557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17482242000735171919689485 6555840750275689469883557)
                  ·
                    refine ⟨1229220140676691775603167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6555840750275689469883557 1229220140676691775603167)
                    ·
                      rfl

theorem cell23_7181693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 2, 3, 3, 4].length) (baseStart_7181693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181693 prefixEnd_7181693 := by exact prefixLift 7181693
  have htrace : WordTrace (prefixWord ++ tailWord_7181693) baseStart_7181693 baseEnd_7181693 := by
    simpa [prefixWord, tailWord_7181693, baseEnd_7181693] using wordTrace_append hprefix tailTrace_7181693
  have hstable : (prefixWord ++ tailWord_7181693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181693).length < 2 ^ (prefixWord ++ tailWord_7181693).sum := by decide
  have hdescent : baseEnd_7181693 < baseStart_7181693 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181700 : List Nat := [2, 3, 2, 1, 1, 4, 1, 1, 2, 4, 2]
def baseStart_7181700 : Nat := 118140960795 + 7181700 * 2 ^ 59
def prefixEnd_7181700 : Nat := 4983230072969 + 3 ^ 40 * 7181700 * 2
def baseEnd_7181700 : Nat := 3687664016394656799421969

theorem tailTrace_7181700 : CollatzResearch.WordTrace tailWord_7181700 prefixEnd_7181700 3687664016394656799421969 := by
  unfold tailWord_7181700
  simp only [CollatzResearch.WordTrace]
  refine ⟨130969059040967455777767277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174625412054623274370356369 130969059040967455777767277)
  ·
    refine ⟨49113397140362795916662729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130969059040967455777767277 49113397140362795916662729)
    ·
      refine ⟨36835047855272096937497047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49113397140362795916662729 36835047855272096937497047)
      ·
        refine ⟨55252571782908145406245571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36835047855272096937497047 55252571782908145406245571)
        ·
          refine ⟨82878857674362218109368357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55252571782908145406245571 82878857674362218109368357)
          ·
            refine ⟨15539785813942915895506567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82878857674362218109368357 15539785813942915895506567)
            ·
              refine ⟨23309678720914373843259851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15539785813942915895506567 23309678720914373843259851)
              ·
                refine ⟨34964518081371560764889777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23309678720914373843259851 34964518081371560764889777)
                ·
                  refine ⟨26223388561028670573667333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34964518081371560764889777 26223388561028670573667333)
                  ·
                    refine ⟨4916885355192875732562625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26223388561028670573667333 4916885355192875732562625)
                    ·
                      refine ⟨3687664016394656799421969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916885355192875732562625 3687664016394656799421969)
                      ·
                        rfl

theorem cell23_7181700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 1, 2, 4, 2].length) (baseStart_7181700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181700 prefixEnd_7181700 := by exact prefixLift 7181700
  have htrace : WordTrace (prefixWord ++ tailWord_7181700) baseStart_7181700 baseEnd_7181700 := by
    simpa [prefixWord, tailWord_7181700, baseEnd_7181700] using wordTrace_append hprefix tailTrace_7181700
  have hstable : (prefixWord ++ tailWord_7181700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181700).length < 2 ^ (prefixWord ++ tailWord_7181700).sum := by decide
  have hdescent : baseEnd_7181700 < baseStart_7181700 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181714 : List Nat := [3, 2, 3, 3, 2, 1, 1, 1, 2, 5]
def baseStart_7181714 : Nat := 118140960795 + 7181714 * 2 ^ 59
def prefixEnd_7181714 : Nat := 4983230072969 + 3 ^ 40 * 7181714 * 2
def baseEnd_7181714 : Nat := 1229223735041273248215635

theorem tailTrace_7181714 : CollatzResearch.WordTrace tailWord_7181714 prefixEnd_7181714 1229223735041273248215635 := by
  unfold tailWord_7181714
  simp only [CollatzResearch.WordTrace]
  refine ⟨65484657175971047986636049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174625752469256127964362797 65484657175971047986636049)
  ·
    refine ⟨49113492881978285989977037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65484657175971047986636049 49113492881978285989977037)
    ·
      refine ⟨18417559830741857246241389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49113492881978285989977037 18417559830741857246241389)
      ·
        refine ⟨6906584936528196467340521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18417559830741857246241389 6906584936528196467340521)
        ·
          refine ⟨5179938702396147350505391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6906584936528196467340521 5179938702396147350505391)
          ·
            refine ⟨7769908053594221025758087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5179938702396147350505391 7769908053594221025758087)
            ·
              refine ⟨11654862080391331538637131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7769908053594221025758087 11654862080391331538637131)
              ·
                refine ⟨17482293120586997307955697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11654862080391331538637131 17482293120586997307955697)
                ·
                  refine ⟨13111719840440247980966773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17482293120586997307955697 13111719840440247980966773)
                  ·
                    refine ⟨1229223735041273248215635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13111719840440247980966773 1229223735041273248215635)
                    ·
                      rfl

theorem cell23_7181714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 2, 1, 1, 1, 2, 5].length) (baseStart_7181714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181714 prefixEnd_7181714 := by exact prefixLift 7181714
  have htrace : WordTrace (prefixWord ++ tailWord_7181714) baseStart_7181714 baseEnd_7181714 := by
    simpa [prefixWord, tailWord_7181714, baseEnd_7181714] using wordTrace_append hprefix tailTrace_7181714
  have hstable : (prefixWord ++ tailWord_7181714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181714).length < 2 ^ (prefixWord ++ tailWord_7181714).sum := by decide
  have hdescent : baseEnd_7181714 < baseStart_7181714 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181720 : List Nat := [2, 1, 2, 5, 2, 1, 1, 1, 1, 4, 3]
def baseStart_7181720 : Nat := 118140960795 + 7181720 * 2 ^ 59
def prefixEnd_7181720 : Nat := 4983230072969 + 3 ^ 40 * 7181720 * 2
def baseEnd_7181720 : Nat := 3687674286007746721171877

theorem tailTrace_7181720 : CollatzResearch.WordTrace tailWord_7181720 prefixEnd_7181720 3687674286007746721171877 := by
  unfold tailWord_7181720
  simp only [CollatzResearch.WordTrace]
  refine ⟨130969423770931227485631307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174625898361241636647508409 130969423770931227485631307)
  ·
    refine ⟨196454135656396841228446961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130969423770931227485631307 196454135656396841228446961)
    ·
      refine ⟨147340601742297630921335221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196454135656396841228446961 147340601742297630921335221)
      ·
        refine ⟨13813181413340402898875177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147340601742297630921335221 13813181413340402898875177)
        ·
          refine ⟨10359886060005302174156383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13813181413340402898875177 10359886060005302174156383)
          ·
            refine ⟨15539829090007953261234575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10359886060005302174156383 15539829090007953261234575)
            ·
              refine ⟨23309743635011929891851863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15539829090007953261234575 23309743635011929891851863)
              ·
                refine ⟨34964615452517894837777795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23309743635011929891851863 34964615452517894837777795)
                ·
                  refine ⟨52446923178776842256666693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34964615452517894837777795 52446923178776842256666693)
                  ·
                    refine ⟨9833798096020657923125005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52446923178776842256666693 9833798096020657923125005)
                    ·
                      refine ⟨3687674286007746721171877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833798096020657923125005 3687674286007746721171877)
                      ·
                        rfl

theorem cell23_7181720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_7181720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181720 prefixEnd_7181720 := by exact prefixLift 7181720
  have htrace : WordTrace (prefixWord ++ tailWord_7181720) baseStart_7181720 baseEnd_7181720 := by
    simpa [prefixWord, tailWord_7181720, baseEnd_7181720] using wordTrace_append hprefix tailTrace_7181720
  have hstable : (prefixWord ++ tailWord_7181720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181720).length < 2 ^ (prefixWord ++ tailWord_7181720).sum := by decide
  have hdescent : baseEnd_7181720 < baseStart_7181720 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181727 : List Nat := [1, 1, 2, 5, 1, 3, 2, 3, 1, 4]
def baseStart_7181727 : Nat := 118140960795 + 7181727 * 2 ^ 59
def prefixEnd_7181727 : Nat := 4983230072969 + 3 ^ 40 * 7181727 * 2
def baseEnd_7181727 : Nat := 1229225960124109397928115

theorem tailTrace_7181727 : CollatzResearch.WordTrace tailWord_7181727 prefixEnd_7181727 1229225960124109397928115 := by
  unfold tailWord_7181727
  simp only [CollatzResearch.WordTrace]
  refine ⟨261939102852837095166767435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174626068568558063444511623 261939102852837095166767435)
  ·
    refine ⟨392908654279255642750151153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261939102852837095166767435 392908654279255642750151153)
    ·
      refine ⟨294681490709441732062613365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392908654279255642750151153 294681490709441732062613365)
      ·
        refine ⟨27626389754010162380870003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294681490709441732062613365 27626389754010162380870003)
        ·
          refine ⟨41439584631015243571305005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27626389754010162380870003 41439584631015243571305005)
          ·
            refine ⟨15539844236630716339239377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41439584631015243571305005 15539844236630716339239377)
            ·
              refine ⟨11654883177473037254429533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15539844236630716339239377 11654883177473037254429533)
              ·
                refine ⟨4370581191552388970411075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11654883177473037254429533 4370581191552388970411075)
                ·
                  refine ⟨6555871787328583455616613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4370581191552388970411075 6555871787328583455616613)
                  ·
                    refine ⟨1229225960124109397928115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6555871787328583455616613 1229225960124109397928115)
                    ·
                      rfl

theorem cell23_7181727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 2, 3, 1, 4].length) (baseStart_7181727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181727 prefixEnd_7181727 := by exact prefixLift 7181727
  have htrace : WordTrace (prefixWord ++ tailWord_7181727) baseStart_7181727 baseEnd_7181727 := by
    simpa [prefixWord, tailWord_7181727, baseEnd_7181727] using wordTrace_append hprefix tailTrace_7181727
  have hstable : (prefixWord ++ tailWord_7181727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181727).length < 2 ^ (prefixWord ++ tailWord_7181727).sum := by decide
  have hdescent : baseEnd_7181727 < baseStart_7181727 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181746 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7]
def baseStart_7181746 : Nat := 118140960795 + 7181746 * 2 ^ 59
def prefixEnd_7181746 : Nat := 4983230072969 + 3 ^ 40 * 7181746 * 2
def baseEnd_7181746 : Nat := 3687687636504763619446757

theorem tailTrace_7181746 : CollatzResearch.WordTrace tailWord_7181746 prefixEnd_7181746 3687687636504763619446757 := by
  unfold tailWord_7181746
  simp only [CollatzResearch.WordTrace]
  refine ⟨65484948959942065352927273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174626530559845507607806061 65484948959942065352927273)
  ·
    refine ⟨49113711719956549014695455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65484948959942065352927273 49113711719956549014695455)
    ·
      refine ⟨73670567579934823522043183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49113711719956549014695455 73670567579934823522043183)
      ·
        refine ⟨110505851369902235283064775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73670567579934823522043183 110505851369902235283064775)
        ·
          refine ⟨165758777054853352924597163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110505851369902235283064775 165758777054853352924597163)
          ·
            refine ⟨248638165582280029386895745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165758777054853352924597163 248638165582280029386895745)
            ·
              refine ⟨186478624186710022040171809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248638165582280029386895745 186478624186710022040171809)
              ·
                refine ⟨139858968140032516530128857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186478624186710022040171809 139858968140032516530128857)
                ·
                  refine ⟨104894226105024387397596643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139858968140032516530128857 104894226105024387397596643)
                  ·
                    refine ⟨157341339157536581096394965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104894226105024387397596643 157341339157536581096394965)
                    ·
                      refine ⟨3687687636504763619446757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157341339157536581096394965 3687687636504763619446757)
                      ·
                        rfl

theorem cell23_7181746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_7181746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181746 prefixEnd_7181746 := by exact prefixLift 7181746
  have htrace : WordTrace (prefixWord ++ tailWord_7181746) baseStart_7181746 baseEnd_7181746 := by
    simpa [prefixWord, tailWord_7181746, baseEnd_7181746] using wordTrace_append hprefix tailTrace_7181746
  have hstable : (prefixWord ++ tailWord_7181746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181746).length < 2 ^ (prefixWord ++ tailWord_7181746).sum := by decide
  have hdescent : baseEnd_7181746 < baseStart_7181746 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181770 : List Nat := [3, 1, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_7181770 : Nat := 118140960795 + 7181770 * 2 ^ 59
def prefixEnd_7181770 : Nat := 4983230072969 + 3 ^ 40 * 7181770 * 2
def baseEnd_7181770 : Nat := 1229233320013490508515549

theorem tailTrace_7181770 : CollatzResearch.WordTrace tailWord_7181770 prefixEnd_7181770 1229233320013490508515549 := by
  unfold tailWord_7181770
  simp only [CollatzResearch.WordTrace]
  refine ⟨65485167797920328377645691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174627114127787542340388509 65485167797920328377645691)
  ·
    refine ⟨98227751696880492566468537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65485167797920328377645691 98227751696880492566468537)
    ·
      refine ⟨73670813772660369424851403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98227751696880492566468537 73670813772660369424851403)
      ·
        refine ⟨110506220658990554137277105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73670813772660369424851403 110506220658990554137277105)
        ·
          refine ⟨82879665494242915602957829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110506220658990554137277105 82879665494242915602957829)
          ·
            refine ⟨15539937280170546675554593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82879665494242915602957829 15539937280170546675554593)
            ·
              refine ⟨11654952960127910006665945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15539937280170546675554593 11654952960127910006665945)
              ·
                refine ⟨8741214720095932504999459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11654952960127910006665945 8741214720095932504999459)
                ·
                  refine ⟨13111822080143898757499189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8741214720095932504999459 13111822080143898757499189)
                  ·
                    refine ⟨1229233320013490508515549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13111822080143898757499189 1229233320013490508515549)
                    ·
                      rfl

theorem cell23_7181770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_7181770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181770 prefixEnd_7181770 := by exact prefixLift 7181770
  have htrace : WordTrace (prefixWord ++ tailWord_7181770) baseStart_7181770 baseEnd_7181770 := by
    simpa [prefixWord, tailWord_7181770, baseEnd_7181770] using wordTrace_append hprefix tailTrace_7181770
  have hstable : (prefixWord ++ tailWord_7181770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181770).length < 2 ^ (prefixWord ++ tailWord_7181770).sum := by decide
  have hdescent : baseEnd_7181770 < baseStart_7181770 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181793 : List Nat := [1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_7181793 : Nat := 118140960795 + 7181793 * 2 ^ 59
def prefixEnd_7181793 : Nat := 4983230072969 + 3 ^ 40 * 7181793 * 2
def baseEnd_7181793 : Nat := 3687711770095524935559041

theorem tailTrace_7181793 : CollatzResearch.WordTrace tailWord_7181793 prefixEnd_7181793 3687711770095524935559041 := by
  unfold tailWord_7181793
  simp only [CollatzResearch.WordTrace]
  refine ⟨261941510070597988438670033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174627673380398658959113355 261941510070597988438670033)
  ·
    refine ⟨196456132552948491329002525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261941510070597988438670033 196456132552948491329002525)
    ·
      refine ⟨73671049707355684248375947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196456132552948491329002525 73671049707355684248375947)
      ·
        refine ⟨110506574561033526372563921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73671049707355684248375947 110506574561033526372563921)
        ·
          refine ⟨82879930920775144779422941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110506574561033526372563921 82879930920775144779422941)
          ·
            refine ⟨31079974095290679292283603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82879930920775144779422941 31079974095290679292283603)
            ·
              refine ⟨46619961142936018938425405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31079974095290679292283603 46619961142936018938425405)
              ·
                refine ⟨17482485428601007101909527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46619961142936018938425405 17482485428601007101909527)
                ·
                  refine ⟨26223728142901510652864291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17482485428601007101909527 26223728142901510652864291)
                  ·
                    refine ⟨39335592214352265979296437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26223728142901510652864291 39335592214352265979296437)
                    ·
                      refine ⟨3687711770095524935559041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39335592214352265979296437 3687711770095524935559041)
                      ·
                        rfl

theorem cell23_7181793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_7181793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181793 prefixEnd_7181793 := by exact prefixLift 7181793
  have htrace : WordTrace (prefixWord ++ tailWord_7181793) baseStart_7181793 baseEnd_7181793 := by
    simpa [prefixWord, tailWord_7181793, baseEnd_7181793] using wordTrace_append hprefix tailTrace_7181793
  have hstable : (prefixWord ++ tailWord_7181793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181793).length < 2 ^ (prefixWord ++ tailWord_7181793).sum := by decide
  have hdescent : baseEnd_7181793 < baseStart_7181793 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181800 : List Nat := [2, 1, 4, 1, 1, 2, 2, 4, 2, 4]
def baseStart_7181800 : Nat := 118140960795 + 7181800 * 2 ^ 59
def prefixEnd_7181800 : Nat := 4983230072969 + 3 ^ 40 * 7181800 * 2
def baseEnd_7181800 : Nat := 1229238454820035469390503

theorem tailTrace_7181800 : CollatzResearch.WordTrace tailWord_7181800 prefixEnd_7181800 1229238454820035469390503 := by
  unfold tailWord_7181800
  simp only [CollatzResearch.WordTrace]
  refine ⟨130970882690786314317087427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174627843587715085756116569 130970882690786314317087427)
  ·
    refine ⟨196456324036179471475631141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130970882690786314317087427 196456324036179471475631141)
    ·
      refine ⟨36835560756783650901680839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196456324036179471475631141 36835560756783650901680839)
      ·
        refine ⟨55253341135175476352521259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36835560756783650901680839 55253341135175476352521259)
        ·
          refine ⟨82880011702763214528781889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55253341135175476352521259 82880011702763214528781889)
          ·
            refine ⟨62160008777072410896586417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82880011702763214528781889 62160008777072410896586417)
            ·
              refine ⟨46620006582804308172439813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62160008777072410896586417 46620006582804308172439813)
              ·
                refine ⟨8741251234275807782332465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46620006582804308172439813 8741251234275807782332465)
                ·
                  refine ⟨6555938425706855836749349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8741251234275807782332465 6555938425706855836749349)
                  ·
                    refine ⟨1229238454820035469390503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6555938425706855836749349 1229238454820035469390503)
                    ·
                      rfl

theorem cell23_7181800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_7181800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181800 prefixEnd_7181800 := by exact prefixLift 7181800
  have htrace : WordTrace (prefixWord ++ tailWord_7181800) baseStart_7181800 baseEnd_7181800 := by
    simpa [prefixWord, tailWord_7181800, baseEnd_7181800] using wordTrace_append hprefix tailTrace_7181800
  have hstable : (prefixWord ++ tailWord_7181800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181800).length < 2 ^ (prefixWord ++ tailWord_7181800).sum := by decide
  have hdescent : baseEnd_7181800 < baseStart_7181800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181807 : List Nat := [1, 1, 2, 1, 4, 1, 5, 1, 3, 2, 2]
def baseStart_7181807 : Nat := 118140960795 + 7181807 * 2 ^ 59
def prefixEnd_7181807 : Nat := 4983230072969 + 3 ^ 40 * 7181807 * 2
def baseEnd_7181807 : Nat := 3687718958824687880783977

theorem tailTrace_7181807 : CollatzResearch.WordTrace tailWord_7181807 prefixEnd_7181807 3687718958824687880783977 := by
  unfold tailWord_7181807
  simp only [CollatzResearch.WordTrace]
  refine ⟨261942020692547268829679675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174628013795031512553119783 261942020692547268829679675)
  ·
    refine ⟨392913031038820903244519513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261942020692547268829679675 392913031038820903244519513)
    ·
      refine ⟨294684773279115677433389635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392913031038820903244519513 294684773279115677433389635)
      ·
        refine ⟨442027159918673516150084453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294684773279115677433389635 442027159918673516150084453)
        ·
          refine ⟨82880092484751284278140835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442027159918673516150084453 82880092484751284278140835)
          ·
            refine ⟨124320138727126926417211253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82880092484751284278140835 124320138727126926417211253)
            ·
              refine ⟨11655013005668149351613555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124320138727126926417211253 11655013005668149351613555)
              ·
                refine ⟨17482519508502224027420333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11655013005668149351613555 17482519508502224027420333)
                ·
                  refine ⟨6555944815688334010282625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17482519508502224027420333 6555944815688334010282625)
                  ·
                    refine ⟨4916958611766250507711969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6555944815688334010282625 4916958611766250507711969)
                    ·
                      refine ⟨3687718958824687880783977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4916958611766250507711969 3687718958824687880783977)
                      ·
                        rfl

theorem cell23_7181807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 5, 1, 3, 2, 2].length) (baseStart_7181807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181807 prefixEnd_7181807 := by exact prefixLift 7181807
  have htrace : WordTrace (prefixWord ++ tailWord_7181807) baseStart_7181807 baseEnd_7181807 := by
    simpa [prefixWord, tailWord_7181807, baseEnd_7181807] using wordTrace_append hprefix tailTrace_7181807
  have hstable : (prefixWord ++ tailWord_7181807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181807).length < 2 ^ (prefixWord ++ tailWord_7181807).sum := by decide
  have hdescent : baseEnd_7181807 < baseStart_7181807 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181810 : List Nat := [3, 2, 1, 4, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7181810 : Nat := 118140960795 + 7181810 * 2 ^ 59
def prefixEnd_7181810 : Nat := 4983230072969 + 3 ^ 40 * 7181810 * 2
def baseEnd_7181810 : Nat := 3687720499266651369046463

theorem tailTrace_7181810 : CollatzResearch.WordTrace tailWord_7181810 prefixEnd_7181810 3687720499266651369046463 := by
  unfold tailWord_7181810
  simp only [CollatzResearch.WordTrace]
  refine ⟨65485532527884100085509721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174628086741024266894692589 65485532527884100085509721)
  ·
    refine ⟨49114149395913075064132291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65485532527884100085509721 49114149395913075064132291)
    ·
      refine ⟨73671224093869612596198437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49114149395913075064132291 73671224093869612596198437)
      ·
        refine ⟨13813354517600552361787207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73671224093869612596198437 13813354517600552361787207)
        ·
          refine ⟨20720031776400828542680811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13813354517600552361787207 20720031776400828542680811)
          ·
            refine ⟨31080047664601242814021217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20720031776400828542680811 31080047664601242814021217)
            ·
              refine ⟨23310035748450932110515913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31080047664601242814021217 23310035748450932110515913)
              ·
                refine ⟨17482526811338199082886935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23310035748450932110515913 17482526811338199082886935)
                ·
                  refine ⟨26223790217007298624330403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17482526811338199082886935 26223790217007298624330403)
                  ·
                    refine ⟨39335685325510947936495605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26223790217007298624330403 39335685325510947936495605)
                    ·
                      refine ⟨3687720499266651369046463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39335685325510947936495605 3687720499266651369046463)
                      ·
                        rfl

theorem cell23_7181810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7181810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181810 prefixEnd_7181810 := by exact prefixLift 7181810
  have htrace : WordTrace (prefixWord ++ tailWord_7181810) baseStart_7181810 baseEnd_7181810 := by
    simpa [prefixWord, tailWord_7181810, baseEnd_7181810] using wordTrace_append hprefix tailTrace_7181810
  have hstable : (prefixWord ++ tailWord_7181810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181810).length < 2 ^ (prefixWord ++ tailWord_7181810).sum := by decide
  have hdescent : baseEnd_7181810 < baseStart_7181810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181844 : List Nat := [2, 4, 3, 1, 2, 2, 1, 1, 1, 1, 5]
def baseStart_7181844 : Nat := 118140960795 + 7181844 * 2 ^ 59
def prefixEnd_7181844 : Nat := 4983230072969 + 3 ^ 40 * 7181844 * 2
def baseEnd_7181844 : Nat := 3687737957608904236021307

theorem tailTrace_7181844 : CollatzResearch.WordTrace tailWord_7181844 prefixEnd_7181844 3687737957608904236021307 := by
  unfold tailWord_7181844
  simp only [CollatzResearch.WordTrace]
  refine ⟨130971685096706612074388293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174628913462275482765851057 130971685096706612074388293)
  ·
    refine ⟨24557190955632489763947805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130971685096706612074388293 24557190955632489763947805)
    ·
      refine ⟨9208946608362183661480427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24557190955632489763947805 9208946608362183661480427)
      ·
        refine ⟨13813419912543275492220641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9208946608362183661480427 13813419912543275492220641)
        ·
          refine ⟨10360064934407456619165481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13813419912543275492220641 10360064934407456619165481)
          ·
            refine ⟨7770048700805592464374111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10360064934407456619165481 7770048700805592464374111)
            ·
              refine ⟨11655073051208388696561167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770048700805592464374111 11655073051208388696561167)
              ·
                refine ⟨17482609576812583044841751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11655073051208388696561167 17482609576812583044841751)
                ·
                  refine ⟨26223914365218874567262627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17482609576812583044841751 26223914365218874567262627)
                  ·
                    refine ⟨39335871547828311850893941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26223914365218874567262627 39335871547828311850893941)
                    ·
                      refine ⟨3687737957608904236021307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39335871547828311850893941 3687737957608904236021307)
                      ·
                        rfl

theorem cell23_7181844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 2, 1, 1, 1, 1, 5].length) (baseStart_7181844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181844 prefixEnd_7181844 := by exact prefixLift 7181844
  have htrace : WordTrace (prefixWord ++ tailWord_7181844) baseStart_7181844 baseEnd_7181844 := by
    simpa [prefixWord, tailWord_7181844, baseEnd_7181844] using wordTrace_append hprefix tailTrace_7181844
  have hstable : (prefixWord ++ tailWord_7181844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181844).length < 2 ^ (prefixWord ++ tailWord_7181844).sum := by decide
  have hdescent : baseEnd_7181844 < baseStart_7181844 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181857 : List Nat := [1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 3]
def baseStart_7181857 : Nat := 118140960795 + 7181857 * 2 ^ 59
def prefixEnd_7181857 : Nat := 4983230072969 + 3 ^ 40 * 7181857 * 2
def baseEnd_7181857 : Nat := 3687744632857412685158747

theorem tailTrace_7181857 : CollatzResearch.WordTrace tailWord_7181857 prefixEnd_7181857 3687744632857412685158747 := by
  unfold tailWord_7181857
  simp only [CollatzResearch.WordTrace]
  refine ⟨261943844342366127368999825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174629229561577418245999883 261943844342366127368999825)
  ·
    refine ⟨196457883256774595526749869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261943844342366127368999825 196457883256774595526749869)
    ·
      refine ⟨73671706221290473322531201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196457883256774595526749869 73671706221290473322531201)
      ·
        refine ⟨55253779665967854991898401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73671706221290473322531201 55253779665967854991898401)
        ·
          refine ⟨41440334749475891243923801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55253779665967854991898401 41440334749475891243923801)
          ·
            refine ⟨31080251062106918432942851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41440334749475891243923801 31080251062106918432942851)
            ·
              refine ⟨46620376593160377649414277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31080251062106918432942851 46620376593160377649414277)
              ·
                refine ⟨8741320611217570809265177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46620376593160377649414277 8741320611217570809265177)
                ·
                  refine ⟨6555990458413178106948883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8741320611217570809265177 6555990458413178106948883)
                  ·
                    refine ⟨9833985687619767160423325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6555990458413178106948883 9833985687619767160423325)
                    ·
                      refine ⟨3687744632857412685158747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9833985687619767160423325 3687744632857412685158747)
                      ·
                        rfl

theorem cell23_7181857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 2, 1, 4, 2, 1, 3].length) (baseStart_7181857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181857 prefixEnd_7181857 := by exact prefixLift 7181857
  have htrace : WordTrace (prefixWord ++ tailWord_7181857) baseStart_7181857 baseEnd_7181857 := by
    simpa [prefixWord, tailWord_7181857, baseEnd_7181857] using wordTrace_append hprefix tailTrace_7181857
  have hstable : (prefixWord ++ tailWord_7181857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181857).length < 2 ^ (prefixWord ++ tailWord_7181857).sum := by decide
  have hdescent : baseEnd_7181857 < baseStart_7181857 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181893 : List Nat := [1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_7181893 : Nat := 118140960795 + 7181893 * 2 ^ 59
def prefixEnd_7181893 : Nat := 4983230072969 + 3 ^ 40 * 7181893 * 2
def baseEnd_7181893 : Nat := 3687763118160974544308581

theorem tailTrace_7181893 : CollatzResearch.WordTrace tailWord_7181893 prefixEnd_7181893 3687763118160974544308581 := by
  unfold tailWord_7181893
  simp only [CollatzResearch.WordTrace]
  refine ⟨261945157370235705517310333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174630104913490470344873555 261945157370235705517310333)
  ·
    refine ⟨98229434013838389568991375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261945157370235705517310333 98229434013838389568991375)
    ·
      refine ⟨147344151020757584353487063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98229434013838389568991375 147344151020757584353487063)
      ·
        refine ⟨221016226531136376530230595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147344151020757584353487063 221016226531136376530230595)
        ·
          refine ⟨331524339796704564795345893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221016226531136376530230595 331524339796704564795345893)
          ·
            refine ⟨62160813711882105899127355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331524339796704564795345893 62160813711882105899127355)
            ·
              refine ⟨93241220567823158848691033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62160813711882105899127355 93241220567823158848691033)
              ·
                refine ⟨69930915425867369136518275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93241220567823158848691033 69930915425867369136518275)
                ·
                  refine ⟨104896373138801053704777413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69930915425867369136518275 104896373138801053704777413)
                  ·
                    refine ⟨19668069963525197569645765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104896373138801053704777413 19668069963525197569645765)
                    ·
                      refine ⟨3687763118160974544308581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19668069963525197569645765 3687763118160974544308581)
                      ·
                        rfl

theorem cell23_7181893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_7181893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181893 prefixEnd_7181893 := by exact prefixLift 7181893
  have htrace : WordTrace (prefixWord ++ tailWord_7181893) baseStart_7181893 baseEnd_7181893 := by
    simpa [prefixWord, tailWord_7181893, baseEnd_7181893] using wordTrace_append hprefix tailTrace_7181893
  have hstable : (prefixWord ++ tailWord_7181893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181893).length < 2 ^ (prefixWord ++ tailWord_7181893).sum := by decide
  have hdescent : baseEnd_7181893 < baseStart_7181893 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181901 : List Nat := [1, 6, 1, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_7181901 : Nat := 118140960795 + 7181901 * 2 ^ 59
def prefixEnd_7181901 : Nat := 4983230072969 + 3 ^ 40 * 7181901 * 2
def baseEnd_7181901 : Nat := 3687767226006210513008545

theorem tailTrace_7181901 : CollatzResearch.WordTrace tailWord_7181901 prefixEnd_7181901 3687767226006210513008545 := by
  unfold tailWord_7181901
  simp only [CollatzResearch.WordTrace]
  refine ⟨261945449154206722883601557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174630299436137815255734371 261945449154206722883601557)
  ·
    refine ⟨12278692929103440135168823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 261945449154206722883601557 12278692929103440135168823)
    ·
      refine ⟨18418039393655160202753235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12278692929103440135168823 18418039393655160202753235)
      ·
        refine ⟨27627059090482740304129853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18418039393655160202753235 27627059090482740304129853)
        ·
          refine ⟨10360147158931027614048695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27627059090482740304129853 10360147158931027614048695)
          ·
            refine ⟨15540220738396541421073043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360147158931027614048695 15540220738396541421073043)
            ·
              refine ⟨23310331107594812131609565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540220738396541421073043 23310331107594812131609565)
              ·
                refine ⟨8741374165348054549353587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23310331107594812131609565 8741374165348054549353587)
                ·
                  refine ⟨13112061248022081824030381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8741374165348054549353587 13112061248022081824030381)
                  ·
                    refine ⟨4917022968008280684011393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13112061248022081824030381 4917022968008280684011393)
                    ·
                      refine ⟨3687767226006210513008545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917022968008280684011393 3687767226006210513008545)
                      ·
                        rfl

theorem cell23_7181901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_7181901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181901 prefixEnd_7181901 := by exact prefixLift 7181901
  have htrace : WordTrace (prefixWord ++ tailWord_7181901) baseStart_7181901 baseEnd_7181901 := by
    simpa [prefixWord, tailWord_7181901, baseEnd_7181901] using wordTrace_append hprefix tailTrace_7181901
  have hstable : (prefixWord ++ tailWord_7181901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181901).length < 2 ^ (prefixWord ++ tailWord_7181901).sum := by decide
  have hdescent : baseEnd_7181901 < baseStart_7181901 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181943 : List Nat := [1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 5]
def baseStart_7181943 : Nat := 118140960795 + 7181943 * 2 ^ 59
def prefixEnd_7181943 : Nat := 4983230072969 + 3 ^ 40 * 7181943 * 2
def baseEnd_7181943 : Nat := 3687788792193699348683351

theorem tailTrace_7181943 : CollatzResearch.WordTrace tailWord_7181943 prefixEnd_7181943 3687788792193699348683351 := by
  unfold tailWord_7181943
  simp only [CollatzResearch.WordTrace]
  refine ⟨261946981020054564056630483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174631320680036376037753655 261946981020054564056630483)
  ·
    refine ⟨392920471530081846084945725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261946981020054564056630483 392920471530081846084945725)
    ·
      refine ⟨147345176823780692281854647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392920471530081846084945725 147345176823780692281854647)
      ·
        refine ⟨221017765235671038422781971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147345176823780692281854647 221017765235671038422781971)
        ·
          refine ⟨331526647853506557634172957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221017765235671038422781971 331526647853506557634172957)
          ·
            refine ⟨124322492945064959112814859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331526647853506557634172957 124322492945064959112814859)
            ·
              refine ⟨186483739417597438669222289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124322492945064959112814859 186483739417597438669222289)
              ·
                refine ⟨139862804563198079001916717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186483739417597438669222289 139862804563198079001916717)
                ·
                  refine ⟨52448551711199279625718769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139862804563198079001916717 52448551711199279625718769)
                  ·
                    refine ⟨39336413783399459719289077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52448551711199279625718769 39336413783399459719289077)
                    ·
                      refine ⟨3687788792193699348683351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39336413783399459719289077 3687788792193699348683351)
                      ·
                        rfl

theorem cell23_7181943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 5].length) (baseStart_7181943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181943 prefixEnd_7181943 := by exact prefixLift 7181943
  have htrace : WordTrace (prefixWord ++ tailWord_7181943) baseStart_7181943 baseEnd_7181943 := by
    simpa [prefixWord, tailWord_7181943, baseEnd_7181943] using wordTrace_append hprefix tailTrace_7181943
  have hstable : (prefixWord ++ tailWord_7181943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181943).length < 2 ^ (prefixWord ++ tailWord_7181943).sum := by decide
  have hdescent : baseEnd_7181943 < baseStart_7181943 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7181997 : List Nat := [1, 5, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_7181997 : Nat := 118140960795 + 7181997 * 2 ^ 59
def prefixEnd_7181997 : Nat := 4983230072969 + 3 ^ 40 * 7181997 * 2
def baseEnd_7181997 : Nat := 1229272173383014045802701

theorem tailTrace_7181997 : CollatzResearch.WordTrace tailWord_7181997 prefixEnd_7181997 1229272173383014045802701 := by
  unfold tailWord_7181997
  simp only [CollatzResearch.WordTrace]
  refine ⟨261948950561858931279096245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174632633707905954186064163 261948950561858931279096245)
  ·
    refine ⟨24557714115174274807415273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 261948950561858931279096245 24557714115174274807415273)
    ·
      refine ⟨18418285586380706105561455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24557714115174274807415273 18418285586380706105561455)
      ·
        refine ⟨27627428379571059158342183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18418285586380706105561455 27627428379571059158342183)
        ·
          refine ⟨41441142569356588737513275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27627428379571059158342183 41441142569356588737513275)
          ·
            refine ⟨62161713854034883106269913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41441142569356588737513275 62161713854034883106269913)
            ·
              refine ⟨46621285390526162329702435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62161713854034883106269913 46621285390526162329702435)
              ·
                refine ⟨69931928085789243494553653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46621285390526162329702435 69931928085789243494553653)
                ·
                  refine ⟨6556118258042741577614405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69931928085789243494553653 6556118258042741577614405)
                  ·
                    refine ⟨1229272173383014045802701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6556118258042741577614405 1229272173383014045802701)
                    ·
                      rfl

theorem cell23_7181997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_7181997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7181997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7181997 prefixEnd_7181997 := by exact prefixLift 7181997
  have htrace : WordTrace (prefixWord ++ tailWord_7181997) baseStart_7181997 baseEnd_7181997 := by
    simpa [prefixWord, tailWord_7181997, baseEnd_7181997] using wordTrace_append hprefix tailTrace_7181997
  have hstable : (prefixWord ++ tailWord_7181997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7181997).length < 2 ^ (prefixWord ++ tailWord_7181997).sum := by decide
  have hdescent : baseEnd_7181997 < baseStart_7181997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7181997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182007 : List Nat := [1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 3]
def baseStart_7182007 : Nat := 118140960795 + 7182007 * 2 ^ 59
def prefixEnd_7182007 : Nat := 4983230072969 + 3 ^ 40 * 7182007 * 2
def baseEnd_7182007 : Nat := 3687821654955587098283057

theorem tailTrace_7182007 : CollatzResearch.WordTrace tailWord_7182007 prefixEnd_7182007 3687821654955587098283057 := by
  unfold tailWord_7182007
  simp only [CollatzResearch.WordTrace]
  refine ⟨261949315291822702986960275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174632876861215135324640183 261949315291822702986960275)
  ·
    refine ⟨392923972937734054480440413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261949315291822702986960275 392923972937734054480440413)
    ·
      refine ⟨147346489851650270430165155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392923972937734054480440413 147346489851650270430165155)
      ·
        refine ⟨221019734777475405645247733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147346489851650270430165155 221019734777475405645247733)
        ·
          refine ⟨20720600135388319279241975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221019734777475405645247733 20720600135388319279241975)
          ·
            refine ⟨31080900203082478918862963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20720600135388319279241975 31080900203082478918862963)
            ·
              refine ⟨46621350304623718378294445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31080900203082478918862963 46621350304623718378294445)
              ·
                refine ⟨17483006364233894391860417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46621350304623718378294445 17483006364233894391860417)
                ·
                  refine ⟨13112254773175420793895313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17483006364233894391860417 13112254773175420793895313)
                  ·
                    refine ⟨9834191079881565595421485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13112254773175420793895313 9834191079881565595421485)
                    ·
                      refine ⟨3687821654955587098283057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9834191079881565595421485 3687821654955587098283057)
                      ·
                        rfl

theorem cell23_7182007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 2, 2, 3].length) (baseStart_7182007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182007 prefixEnd_7182007 := by exact prefixLift 7182007
  have htrace : WordTrace (prefixWord ++ tailWord_7182007) baseStart_7182007 baseEnd_7182007 := by
    simpa [prefixWord, tailWord_7182007, baseEnd_7182007] using wordTrace_append hprefix tailTrace_7182007
  have hstable : (prefixWord ++ tailWord_7182007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182007).length < 2 ^ (prefixWord ++ tailWord_7182007).sum := by decide
  have hdescent : baseEnd_7182007 < baseStart_7182007 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182030 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_7182030 : Nat := 118140960795 + 7182030 * 2 ^ 59
def prefixEnd_7182030 : Nat := 4983230072969 + 3 ^ 40 * 7182030 * 2
def baseEnd_7182030 : Nat := 3687833465010640508295451

theorem tailTrace_7182030 : CollatzResearch.WordTrace tailWord_7182030 prefixEnd_7182030 3687833465010640508295451 := by
  unfold tailWord_7182030
  simp only [CollatzResearch.WordTrace]
  refine ⟨32743769271342422239380943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174633436113826251943365029 32743769271342422239380943)
  ·
    refine ⟨49115653907013633359071415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32743769271342422239380943 49115653907013633359071415)
    ·
      refine ⟨73673480860520450038607123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49115653907013633359071415 73673480860520450038607123)
      ·
        refine ⟨110510221290780675057910685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73673480860520450038607123 110510221290780675057910685)
        ·
          refine ⟨41441332984042753146716507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110510221290780675057910685 41441332984042753146716507)
          ·
            refine ⟨62161999476064129720074761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41441332984042753146716507 62161999476064129720074761)
            ·
              refine ⟨46621499607048097290056071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62161999476064129720074761 46621499607048097290056071)
              ·
                refine ⟨69932249410572145935084107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46621499607048097290056071 69932249410572145935084107)
                ·
                  refine ⟨104898374115858218902626161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69932249410572145935084107 104898374115858218902626161)
                  ·
                    refine ⟨78673780586893664176969621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104898374115858218902626161 78673780586893664176969621)
                    ·
                      refine ⟨3687833465010640508295451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78673780586893664176969621 3687833465010640508295451)
                      ·
                        rfl

theorem cell23_7182030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_7182030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182030 prefixEnd_7182030 := by exact prefixLift 7182030
  have htrace : WordTrace (prefixWord ++ tailWord_7182030) baseStart_7182030 baseEnd_7182030 := by
    simpa [prefixWord, tailWord_7182030, baseEnd_7182030] using wordTrace_append hprefix tailTrace_7182030
  have hstable : (prefixWord ++ tailWord_7182030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182030).length < 2 ^ (prefixWord ++ tailWord_7182030).sum := by decide
  have hdescent : baseEnd_7182030 < baseStart_7182030 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182038 : List Nat := [5, 2, 1, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_7182038 : Nat := 118140960795 + 7182038 * 2 ^ 59
def prefixEnd_7182038 : Nat := 4983230072969 + 3 ^ 40 * 7182038 * 2
def baseEnd_7182038 : Nat := 3687837572855876476995415

theorem tailTrace_7182038 : CollatzResearch.WordTrace tailWord_7182038 prefixEnd_7182038 3687837572855876476995415 := by
  unfold tailWord_7182038
  simp only [CollatzResearch.WordTrace]
  refine ⟨16371902872169399705083673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174633630636473596854225845 16371902872169399705083673)
  ·
    refine ⟨12278927154127049778812755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 16371902872169399705083673 12278927154127049778812755)
    ·
      refine ⟨18418390731190574668219133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12278927154127049778812755 18418390731190574668219133)
      ·
        refine ⟨6906896524196465500582175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18418390731190574668219133 6906896524196465500582175)
        ·
          refine ⟨10360344786294698250873263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6906896524196465500582175 10360344786294698250873263)
          ·
            refine ⟨15540517179442047376309895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360344786294698250873263 15540517179442047376309895)
            ·
              refine ⟨23310775769163071064464843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540517179442047376309895 23310775769163071064464843)
              ·
                refine ⟨34966163653744606596697265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23310775769163071064464843 34966163653744606596697265)
                ·
                  refine ⟨26224622740308454947522949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34966163653744606596697265 26224622740308454947522949)
                  ·
                    refine ⟨4917116763807835302660553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26224622740308454947522949 4917116763807835302660553)
                    ·
                      refine ⟨3687837572855876476995415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917116763807835302660553 3687837572855876476995415)
                      ·
                        rfl

theorem cell23_7182038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_7182038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182038 prefixEnd_7182038 := by exact prefixLift 7182038
  have htrace : WordTrace (prefixWord ++ tailWord_7182038) baseStart_7182038 baseEnd_7182038 := by
    simpa [prefixWord, tailWord_7182038, baseEnd_7182038] using wordTrace_append hprefix tailTrace_7182038
  have hstable : (prefixWord ++ tailWord_7182038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182038).length < 2 ^ (prefixWord ++ tailWord_7182038).sum := by decide
  have hdescent : baseEnd_7182038 < baseStart_7182038 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182040 : List Nat := [2, 1, 2, 2, 3, 1, 1, 1, 5, 5]
def baseStart_7182040 : Nat := 118140960795 + 7182040 * 2 ^ 59
def prefixEnd_7182040 : Nat := 4983230072969 + 3 ^ 40 * 7182040 * 2
def baseEnd_7182040 : Nat := 1229279533272395156390135

theorem tailTrace_7182040 : CollatzResearch.WordTrace tailWord_7182040 prefixEnd_7182040 1229279533272395156390135 := by
  unfold tailWord_7182040
  simp only [CollatzResearch.WordTrace]
  refine ⟨130975259450351574811455787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174633679267135433081941049 130975259450351574811455787)
  ·
    refine ⟨196462889175527362217183681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130975259450351574811455787 196462889175527362217183681)
    ·
      refine ⟨147347166881645521662887761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196462889175527362217183681 147347166881645521662887761)
      ·
        refine ⟨110510375161234141247165821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147347166881645521662887761 110510375161234141247165821)
        ·
          refine ⟨41441390685462802967687183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110510375161234141247165821 41441390685462802967687183)
          ·
            refine ⟨62162086028194204451530775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41441390685462802967687183 62162086028194204451530775)
            ·
              refine ⟨93243129042291306677296163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62162086028194204451530775 93243129042291306677296163)
              ·
                refine ⟨139864693563436960015944245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93243129042291306677296163 139864693563436960015944245)
                ·
                  refine ⟨13112315021572215001494773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139864693563436960015944245 13112315021572215001494773)
                  ·
                    refine ⟨1229279533272395156390135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13112315021572215001494773 1229279533272395156390135)
                    ·
                      rfl

theorem cell23_7182040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_7182040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182040 prefixEnd_7182040 := by exact prefixLift 7182040
  have htrace : WordTrace (prefixWord ++ tailWord_7182040) baseStart_7182040 baseEnd_7182040 := by
    simpa [prefixWord, tailWord_7182040, baseEnd_7182040] using wordTrace_append hprefix tailTrace_7182040
  have hstable : (prefixWord ++ tailWord_7182040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182040).length < 2 ^ (prefixWord ++ tailWord_7182040).sum := by decide
  have hdescent : baseEnd_7182040 < baseStart_7182040 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182047 : List Nat := [1, 1, 2, 3, 2, 2, 2, 2, 1, 5, 2]
def baseStart_7182047 : Nat := 118140960795 + 7182047 * 2 ^ 59
def prefixEnd_7182047 : Nat := 4983230072969 + 3 ^ 40 * 7182047 * 2
def baseEnd_7182047 : Nat := 3687842194181766941782873

theorem tailTrace_7182047 : CollatzResearch.WordTrace tailWord_7182047 prefixEnd_7182047 3687842194181766941782873 := by
  unfold tailWord_7182047
  simp only [CollatzResearch.WordTrace]
  refine ⟨261950774211677789818416395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174633849474451859878944263 261950774211677789818416395)
  ·
    refine ⟨392926161317516684727624593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261950774211677789818416395 392926161317516684727624593)
    ·
      refine ⟨294694620988137513545718445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392926161317516684727624593 294694620988137513545718445)
      ·
        refine ⟨110510482870551567579644417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294694620988137513545718445 110510482870551567579644417)
        ·
          refine ⟨82882862152913675684733313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110510482870551567579644417 82882862152913675684733313)
          ·
            refine ⟨62162146614685256763549985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82882862152913675684733313 62162146614685256763549985)
            ·
              refine ⟨46621609961013942572662489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62162146614685256763549985 46621609961013942572662489)
              ·
                refine ⟨34966207470760456929496867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46621609961013942572662489 34966207470760456929496867)
                ·
                  refine ⟨52449311206140685394245301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34966207470760456929496867 52449311206140685394245301)
                  ·
                    refine ⟨4917122925575689255710497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52449311206140685394245301 4917122925575689255710497)
                    ·
                      refine ⟨3687842194181766941782873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917122925575689255710497 3687842194181766941782873)
                      ·
                        rfl

theorem cell23_7182047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 2, 1, 5, 2].length) (baseStart_7182047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182047 prefixEnd_7182047 := by exact prefixLift 7182047
  have htrace : WordTrace (prefixWord ++ tailWord_7182047) baseStart_7182047 baseEnd_7182047 := by
    simpa [prefixWord, tailWord_7182047, baseEnd_7182047] using wordTrace_append hprefix tailTrace_7182047
  have hstable : (prefixWord ++ tailWord_7182047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182047).length < 2 ^ (prefixWord ++ tailWord_7182047).sum := by decide
  have hdescent : baseEnd_7182047 < baseStart_7182047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182117 : List Nat := [1, 3, 1, 2, 3, 2, 4, 7]
def baseStart_7182117 : Nat := 118140960795 + 7182117 * 2 ^ 59
def prefixEnd_7182117 : Nat := 4983230072969 + 3 ^ 40 * 7182117 * 2
def baseEnd_7182117 : Nat := 136588079178799321033613

theorem tailTrace_7182117 : CollatzResearch.WordTrace tailWord_7182117 prefixEnd_7182117 136588079178799321033613 := by
  unfold tailWord_7182117
  simp only [CollatzResearch.WordTrace]
  refine ⟨261953327321424191773464605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174635551547616127848976403 261953327321424191773464605)
  ·
    refine ⟨98232497745534071915049227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261953327321424191773464605 98232497745534071915049227)
    ·
      refine ⟨147348746618301107872573841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98232497745534071915049227 147348746618301107872573841)
      ·
        refine ⟨110511559963725830904430381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147348746618301107872573841 110511559963725830904430381)
        ·
          refine ⟨41441834986397186589161393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110511559963725830904430381 41441834986397186589161393)
          ·
            refine ⟨31081376239797889941871045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41441834986397186589161393 31081376239797889941871045)
            ·
              refine ⟨5827758044962104364100821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31081376239797889941871045 5827758044962104364100821)
              ·
                refine ⟨136588079178799321033613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5827758044962104364100821 136588079178799321033613)
                ·
                  rfl

theorem cell23_7182117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 4, 7].length) (baseStart_7182117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182117 prefixEnd_7182117 := by exact prefixLift 7182117
  have htrace : WordTrace (prefixWord ++ tailWord_7182117) baseStart_7182117 baseEnd_7182117 := by
    simpa [prefixWord, tailWord_7182117, baseEnd_7182117] using wordTrace_append hprefix tailTrace_7182117
  have hstable : (prefixWord ++ tailWord_7182117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182117).length < 2 ^ (prefixWord ++ tailWord_7182117).sum := by decide
  have hdescent : baseEnd_7182117 < baseStart_7182117 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182134 : List Nat := [5, 1, 2, 2, 1, 3, 9]
def baseStart_7182134 : Nat := 118140960795 + 7182134 * 2 ^ 59
def prefixEnd_7182134 : Nat := 4983230072969 + 3 ^ 40 * 7182134 * 2
def baseEnd_7182134 : Nat := 45529467493811211128333

theorem tailTrace_7182134 : CollatzResearch.WordTrace tailWord_7182134 prefixEnd_7182134 45529467493811211128333 := by
  unfold tailWord_7182134
  simp only [CollatzResearch.WordTrace]
  refine ⟨16372121710147662729802091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174635964908241735784555637 16372121710147662729802091)
  ·
    refine ⟨24558182565221494094703137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16372121710147662729802091 24558182565221494094703137)
    ·
      refine ⟨18418636923916120571027353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24558182565221494094703137 18418636923916120571027353)
      ·
        refine ⟨13813977692937090428270515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18418636923916120571027353 13813977692937090428270515)
        ·
          refine ⟨20720966539405635642405773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13813977692937090428270515 20720966539405635642405773)
          ·
            refine ⟨7770362452277113365902165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20720966539405635642405773 7770362452277113365902165)
            ·
              refine ⟨45529467493811211128333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7770362452277113365902165 45529467493811211128333)
              ·
                rfl

theorem cell23_7182134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 9].length) (baseStart_7182134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182134 prefixEnd_7182134 := by exact prefixLift 7182134
  have htrace : WordTrace (prefixWord ++ tailWord_7182134) baseStart_7182134 baseEnd_7182134 := by
    simpa [prefixWord, tailWord_7182134, baseEnd_7182134] using wordTrace_append hprefix tailTrace_7182134
  have hstable : (prefixWord ++ tailWord_7182134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182134).length < 2 ^ (prefixWord ++ tailWord_7182134).sum := by decide
  have hdescent : baseEnd_7182134 < baseStart_7182134 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182154 : List Nat := [3, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2]
def baseStart_7182154 : Nat := 118140960795 + 7182154 * 2 ^ 59
def prefixEnd_7182154 : Nat := 4983230072969 + 3 ^ 40 * 7182154 * 2
def baseEnd_7182154 : Nat := 3687897136611798023144881

theorem tailTrace_7182154 : CollatzResearch.WordTrace tailWord_7182154 prefixEnd_7182154 3687897136611798023144881 := by
  unfold tailWord_7182154
  simp only [CollatzResearch.WordTrace]
  refine ⟨65488669205572536773140379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174636451214860098061707677 65488669205572536773140379)
  ·
    refine ⟨98233003808358805159710569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65488669205572536773140379 98233003808358805159710569)
    ·
      refine ⟨73674752856269103869782927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98233003808358805159710569 73674752856269103869782927)
      ·
        refine ⟨110512129284403655804674391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73674752856269103869782927 110512129284403655804674391)
        ·
          refine ⟨165768193926605483707011587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110512129284403655804674391 165768193926605483707011587)
          ·
            refine ⟨248652290889908225560517381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165768193926605483707011587 248652290889908225560517381)
            ·
              refine ⟨46622304541857792292597009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248652290889908225560517381 46622304541857792292597009)
              ·
                refine ⟨34966728406393344219447757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46622304541857792292597009 34966728406393344219447757)
                ·
                  refine ⟨13112523152397504082292909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34966728406393344219447757 13112523152397504082292909)
                  ·
                    refine ⟨4917196182149064030859841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13112523152397504082292909 4917196182149064030859841)
                    ·
                      refine ⟨3687897136611798023144881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917196182149064030859841 3687897136611798023144881)
                      ·
                        rfl

theorem cell23_7182154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 2, 3, 3, 2].length) (baseStart_7182154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182154 prefixEnd_7182154 := by exact prefixLift 7182154
  have htrace : WordTrace (prefixWord ++ tailWord_7182154) baseStart_7182154 baseEnd_7182154 := by
    simpa [prefixWord, tailWord_7182154, baseEnd_7182154] using wordTrace_append hprefix tailTrace_7182154
  have hstable : (prefixWord ++ tailWord_7182154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182154).length < 2 ^ (prefixWord ++ tailWord_7182154).sum := by decide
  have hdescent : baseEnd_7182154 < baseStart_7182154 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182160 : List Nat := [2, 1, 1, 1, 1, 4, 1, 3, 1, 8]
def baseStart_7182160 : Nat := 118140960795 + 7182160 * 2 ^ 59
def prefixEnd_7182160 : Nat := 4983230072969 + 3 ^ 40 * 7182160 * 2
def baseEnd_7182160 : Nat := 1229300072498574999889951

theorem tailTrace_7182160 : CollatzResearch.WordTrace tailWord_7182160 prefixEnd_7182160 1229300072498574999889951 := by
  unfold tailWord_7182160
  simp only [CollatzResearch.WordTrace]
  refine ⟨130977447830134205058639967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174636597106845606744853289 130977447830134205058639967)
  ·
    refine ⟨196466171745201307587959951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130977447830134205058639967 196466171745201307587959951)
    ·
      refine ⟨294699257617801961381939927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196466171745201307587959951 294699257617801961381939927)
      ·
        refine ⟨442048886426702942072909891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294699257617801961381939927 442048886426702942072909891)
        ·
          refine ⟨663073329640054413109364837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442048886426702942072909891 663073329640054413109364837)
          ·
            refine ⟨124326249307510202458005907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 663073329640054413109364837 124326249307510202458005907)
            ·
              refine ⟨186489373961265303687008861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124326249307510202458005907 186489373961265303687008861)
              ·
                refine ⟨69933515235474488882628323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186489373961265303687008861 69933515235474488882628323)
                ·
                  refine ⟨104900272853211733323942485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69933515235474488882628323 104900272853211733323942485)
                  ·
                    refine ⟨1229300072498574999889951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104900272853211733323942485 1229300072498574999889951)
                    ·
                      rfl

theorem cell23_7182160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_7182160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182160 prefixEnd_7182160 := by exact prefixLift 7182160
  have htrace : WordTrace (prefixWord ++ tailWord_7182160) baseStart_7182160 baseEnd_7182160 := by
    simpa [prefixWord, tailWord_7182160, baseEnd_7182160] using wordTrace_append hprefix tailTrace_7182160
  have hstable : (prefixWord ++ tailWord_7182160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182160).length < 2 ^ (prefixWord ++ tailWord_7182160).sum := by decide
  have hdescent : baseEnd_7182160 < baseStart_7182160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182161 : List Nat := [1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 3]
def baseStart_7182161 : Nat := 118140960795 + 7182161 * 2 ^ 59
def prefixEnd_7182161 : Nat := 4983230072969 + 3 ^ 40 * 7182161 * 2
def baseEnd_7182161 : Nat := 3687900730976379495757349

theorem tailTrace_7182161 : CollatzResearch.WordTrace tailWord_7182161 prefixEnd_7182161 3687900730976379495757349 := by
  unfold tailWord_7182161
  simp only [CollatzResearch.WordTrace]
  refine ⟨261954932133264787288066337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174636621422176524858710891 261954932133264787288066337)
  ·
    refine ⟨196466199099948590466049753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261954932133264787288066337 196466199099948590466049753)
    ·
      refine ⟨147349649324961442849537315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196466199099948590466049753 147349649324961442849537315)
      ·
        refine ⟨221024473987442164274305973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147349649324961442849537315 221024473987442164274305973)
        ·
          refine ⟨20721044436322702900716185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221024473987442164274305973 20721044436322702900716185)
          ·
            refine ⟨15540783327242027175537139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20721044436322702900716185 15540783327242027175537139)
            ·
              refine ⟨23311174990863040763305709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15540783327242027175537139 23311174990863040763305709)
              ·
                refine ⟨8741690621573640286239641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23311174990863040763305709 8741690621573640286239641)
                ·
                  refine ⟨6556267966180230214679731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8741690621573640286239641 6556267966180230214679731)
                  ·
                    refine ⟨9834401949270345322019597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6556267966180230214679731 9834401949270345322019597)
                    ·
                      refine ⟨3687900730976379495757349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9834401949270345322019597 3687900730976379495757349)
                      ·
                        rfl

theorem cell23_7182161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_7182161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182161 prefixEnd_7182161 := by exact prefixLift 7182161
  have htrace : WordTrace (prefixWord ++ tailWord_7182161) baseStart_7182161 baseEnd_7182161 := by
    simpa [prefixWord, tailWord_7182161, baseEnd_7182161] using wordTrace_append hprefix tailTrace_7182161
  have hstable : (prefixWord ++ tailWord_7182161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182161).length < 2 ^ (prefixWord ++ tailWord_7182161).sum := by decide
  have hdescent : baseEnd_7182161 < baseStart_7182161 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182188 : List Nat := [2, 2, 1, 1, 4, 3, 3, 1, 1, 3, 2]
def baseStart_7182188 : Nat := 118140960795 + 7182188 * 2 ^ 59
def prefixEnd_7182188 : Nat := 4983230072969 + 3 ^ 40 * 7182188 * 2
def baseEnd_7182188 : Nat := 3687914594954050890119725

theorem tailTrace_7182188 : CollatzResearch.WordTrace tailWord_7182188 prefixEnd_7182188 3687914594954050890119725 := by
  unfold tailWord_7182188
  simp only [CollatzResearch.WordTrace]
  refine ⟨130977958452083485449649609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174637277936111313932866145 130977958452083485449649609)
  ·
    refine ⟨98233468839062614087237207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130977958452083485449649609 98233468839062614087237207)
    ·
      refine ⟨147350203258593921130855811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98233468839062614087237207 147350203258593921130855811)
      ·
        refine ⟨221025304887890881696283717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147350203258593921130855811 221025304887890881696283717)
        ·
          refine ⟨41442244666479540318053197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221025304887890881696283717 41442244666479540318053197)
          ·
            refine ⟨15540841749929827619269949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41442244666479540318053197 15540841749929827619269949)
            ·
              refine ⟨5827815656223685357226231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15540841749929827619269949 5827815656223685357226231)
              ·
                refine ⟨8741723484335528035839347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5827815656223685357226231 8741723484335528035839347)
                ·
                  refine ⟨13112585226503292053759021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8741723484335528035839347 13112585226503292053759021)
                  ·
                    refine ⟨4917219459938734520159633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13112585226503292053759021 4917219459938734520159633)
                    ·
                      refine ⟨3687914594954050890119725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917219459938734520159633 3687914594954050890119725)
                      ·
                        rfl

theorem cell23_7182188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 3, 2].length) (baseStart_7182188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182188 prefixEnd_7182188 := by exact prefixLift 7182188
  have htrace : WordTrace (prefixWord ++ tailWord_7182188) baseStart_7182188 baseEnd_7182188 := by
    simpa [prefixWord, tailWord_7182188, baseEnd_7182188] using wordTrace_append hprefix tailTrace_7182188
  have hstable : (prefixWord ++ tailWord_7182188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182188).length < 2 ^ (prefixWord ++ tailWord_7182188).sum := by decide
  have hdescent : baseEnd_7182188 < baseStart_7182188 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182218 : List Nat := [3, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2]
def baseStart_7182218 : Nat := 118140960795 + 7182218 * 2 ^ 59
def prefixEnd_7182218 : Nat := 4983230072969 + 3 ^ 40 * 7182218 * 2
def baseEnd_7182218 : Nat := 3687929999373685772744587

theorem tailTrace_7182218 : CollatzResearch.WordTrace tailWord_7182218 prefixEnd_7182218 3687929999373685772744587 := by
  unfold tailWord_7182218
  simp only [CollatzResearch.WordTrace]
  refine ⟨65489252773514571505722827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174638007396038857348594205 65489252773514571505722827)
  ·
    refine ⟨98233879160271857258584241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65489252773514571505722827 98233879160271857258584241)
    ·
      refine ⟨73675409370203892943938181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98233879160271857258584241 73675409370203892943938181)
      ·
        refine ⟨13814139256913229926988409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73675409370203892943938181 13814139256913229926988409)
        ·
          refine ⟨10360604442684922445241307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13814139256913229926988409 10360604442684922445241307)
          ·
            refine ⟨15540906664027383667861961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10360604442684922445241307 15540906664027383667861961)
            ·
              refine ⟨11655679998020537750896471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15540906664027383667861961 11655679998020537750896471)
              ·
                refine ⟨17483519997030806626344707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11655679998020537750896471 17483519997030806626344707)
                ·
                  refine ⟨26225279995546209939517061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17483519997030806626344707 26225279995546209939517061)
                  ·
                    refine ⟨4917239999164914363659449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26225279995546209939517061 4917239999164914363659449)
                    ·
                      refine ⟨3687929999373685772744587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917239999164914363659449 3687929999373685772744587)
                      ·
                        rfl

theorem cell23_7182218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 2, 1, 1, 4, 2].length) (baseStart_7182218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182218 prefixEnd_7182218 := by exact prefixLift 7182218
  have htrace : WordTrace (prefixWord ++ tailWord_7182218) baseStart_7182218 baseEnd_7182218 := by
    simpa [prefixWord, tailWord_7182218, baseEnd_7182218] using wordTrace_append hprefix tailTrace_7182218
  have hstable : (prefixWord ++ tailWord_7182218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182218).length < 2 ^ (prefixWord ++ tailWord_7182218).sum := by decide
  have hdescent : baseEnd_7182218 < baseStart_7182218 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182287 : List Nat := [1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 4]
def baseStart_7182287 : Nat := 118140960795 + 7182287 * 2 ^ 59
def prefixEnd_7182287 : Nat := 4983230072969 + 3 ^ 40 * 7182287 * 2
def baseEnd_7182287 : Nat := 3687965429538846002781769

theorem tailTrace_7182287 : CollatzResearch.WordTrace tailWord_7182287 prefixEnd_7182287 3687965429538846002781769 := by
  unfold tailWord_7182287
  simp only [CollatzResearch.WordTrace]
  refine ⟨261959527730808310807153115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174639685153872207204768743 261959527730808310807153115)
  ·
    refine ⟨392939291596212466210729673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261959527730808310807153115 392939291596212466210729673)
    ·
      refine ⟨294704468697159349658047255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392939291596212466210729673 294704468697159349658047255)
      ·
        refine ⟨442056703045739024487070883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294704468697159349658047255 442056703045739024487070883)
        ·
          refine ⟨663085054568608536730606325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442056703045739024487070883 663085054568608536730606325)
          ·
            refine ⟨62164223865807050318494343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 663085054568608536730606325 62164223865807050318494343)
            ·
              refine ⟨93246335798710575477741515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62164223865807050318494343 93246335798710575477741515)
              ·
                refine ⟨139869503698065863216612273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93246335798710575477741515 139869503698065863216612273)
                ·
                  refine ⟨104902127773549397412459205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139869503698065863216612273 104902127773549397412459205)
                  ·
                    refine ⟨19669148957540512014836101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104902127773549397412459205 19669148957540512014836101)
                    ·
                      refine ⟨3687965429538846002781769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19669148957540512014836101 3687965429538846002781769)
                      ·
                        rfl

theorem cell23_7182287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 1, 2, 4, 4].length) (baseStart_7182287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182287 prefixEnd_7182287 := by exact prefixLift 7182287
  have htrace : WordTrace (prefixWord ++ tailWord_7182287) baseStart_7182287 baseEnd_7182287 := by
    simpa [prefixWord, tailWord_7182287, baseEnd_7182287] using wordTrace_append hprefix tailTrace_7182287
  have hstable : (prefixWord ++ tailWord_7182287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182287).length < 2 ^ (prefixWord ++ tailWord_7182287).sum := by decide
  have hdescent : baseEnd_7182287 < baseStart_7182287 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182314 : List Nat := [3, 1, 3, 1, 2, 1, 2, 4, 6]
def baseStart_7182314 : Nat := 118140960795 + 7182314 * 2 ^ 59
def prefixEnd_7182314 : Nat := 4983230072969 + 3 ^ 40 * 7182314 * 2
def baseEnd_7182314 : Nat := 409775477057390821904905

theorem tailTrace_7182314 : CollatzResearch.WordTrace tailWord_7182314 prefixEnd_7182314 409775477057390821904905 := by
  unfold tailWord_7182314
  simp only [CollatzResearch.WordTrace]
  refine ⟨65490128125427623604596499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174640341667806996278923997 65490128125427623604596499)
  ·
    refine ⟨98235192188141435406894749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65490128125427623604596499 98235192188141435406894749)
    ·
      refine ⟨36838197070553038277585531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98235192188141435406894749 36838197070553038277585531)
      ·
        refine ⟨55257295605829557416378297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36838197070553038277585531 55257295605829557416378297)
        ·
          refine ⟨41442971704372168062283723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55257295605829557416378297 41442971704372168062283723)
          ·
            refine ⟨62164457556558252093425585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41442971704372168062283723 62164457556558252093425585)
            ·
              refine ⟨46623343167418689070069189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62164457556558252093425585 46623343167418689070069189)
              ·
                refine ⟨8741876843891004200637973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46623343167418689070069189 8741876843891004200637973)
                ·
                  refine ⟨409775477057390821904905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8741876843891004200637973 409775477057390821904905)
                  ·
                    rfl

theorem cell23_7182314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 2, 4, 6].length) (baseStart_7182314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182314 prefixEnd_7182314 := by exact prefixLift 7182314
  have htrace : WordTrace (prefixWord ++ tailWord_7182314) baseStart_7182314 baseEnd_7182314 := by
    simpa [prefixWord, tailWord_7182314, baseEnd_7182314] using wordTrace_append hprefix tailTrace_7182314
  have hstable : (prefixWord ++ tailWord_7182314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182314).length < 2 ^ (prefixWord ++ tailWord_7182314).sum := by decide
  have hdescent : baseEnd_7182314 < baseStart_7182314 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182318 : List Nat := [4, 1, 2, 1, 3, 3, 1, 1, 3, 4]
def baseStart_7182318 : Nat := 118140960795 + 7182318 * 2 ^ 59
def prefixEnd_7182318 : Nat := 4983230072969 + 3 ^ 40 * 7182318 * 2
def baseEnd_7182318 : Nat := 1229327115813045127164709

theorem tailTrace_7182318 : CollatzResearch.WordTrace tailWord_7182318 prefixEnd_7182318 1229327115813045127164709 := by
  unfold tailWord_7182318
  simp only [CollatzResearch.WordTrace]
  refine ⟨32745082299212000387691451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174640438929130668734354405 32745082299212000387691451)
  ·
    refine ⟨49117623448818000581537177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32745082299212000387691451 49117623448818000581537177)
    ·
      refine ⟨36838217586613500436152883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49117623448818000581537177 36838217586613500436152883)
      ·
        refine ⟨55257326379920250654229325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36838217586613500436152883 55257326379920250654229325)
        ·
          refine ⟨20721497392470093995335997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55257326379920250654229325 20721497392470093995335997)
          ·
            refine ⟨7770561522176285248250999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20721497392470093995335997 7770561522176285248250999)
            ·
              refine ⟨11655842283264427872376499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770561522176285248250999 11655842283264427872376499)
              ·
                refine ⟨17483763424896641808564749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11655842283264427872376499 17483763424896641808564749)
                ·
                  refine ⟨6556411284336240678211781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17483763424896641808564749 6556411284336240678211781)
                  ·
                    refine ⟨1229327115813045127164709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6556411284336240678211781 1229327115813045127164709)
                    ·
                      rfl

theorem cell23_7182318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 3, 1, 1, 3, 4].length) (baseStart_7182318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182318 prefixEnd_7182318 := by exact prefixLift 7182318
  have htrace : WordTrace (prefixWord ++ tailWord_7182318) baseStart_7182318 baseEnd_7182318 := by
    simpa [prefixWord, tailWord_7182318, baseEnd_7182318] using wordTrace_append hprefix tailTrace_7182318
  have hstable : (prefixWord ++ tailWord_7182318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182318).length < 2 ^ (prefixWord ++ tailWord_7182318).sum := by decide
  have hdescent : baseEnd_7182318 < baseStart_7182318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182344 : List Nat := [2, 1, 3, 2, 1, 2, 3, 1, 3, 5]
def baseStart_7182344 : Nat := 118140960795 + 7182344 * 2 ^ 59
def prefixEnd_7182344 : Nat := 4983230072969 + 3 ^ 40 * 7182344 * 2
def baseEnd_7182344 : Nat := 1229331565978717426589669

theorem tailTrace_7182344 : CollatzResearch.WordTrace tailWord_7182344 prefixEnd_7182344 1229331565978717426589669 := by
  unfold tailWord_7182344
  simp only [CollatzResearch.WordTrace]
  refine ⟨130980803345800904770989043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174641071127734539694652057 130980803345800904770989043)
  ·
    refine ⟨196471205018701357156483565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130980803345800904770989043 196471205018701357156483565)
    ·
      refine ⟨73676701882013008933681337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196471205018701357156483565 73676701882013008933681337)
      ·
        refine ⟨55257526411509756700261003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73676701882013008933681337 55257526411509756700261003)
        ·
          refine ⟨82886289617264635050391505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55257526411509756700261003 82886289617264635050391505)
          ·
            refine ⟨62164717212948476287793629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82886289617264635050391505 62164717212948476287793629)
            ·
              refine ⟨23311768954855678607922611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62164717212948476287793629 23311768954855678607922611)
              ·
                refine ⟨34967653432283517911883917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23311768954855678607922611 34967653432283517911883917)
                ·
                  refine ⟨13112870037106319216956469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34967653432283517911883917 13112870037106319216956469)
                  ·
                    refine ⟨1229331565978717426589669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13112870037106319216956469 1229331565978717426589669)
                    ·
                      rfl

theorem cell23_7182344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 1, 3, 5].length) (baseStart_7182344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182344 prefixEnd_7182344 := by exact prefixLift 7182344
  have htrace : WordTrace (prefixWord ++ tailWord_7182344) baseStart_7182344 baseEnd_7182344 := by
    simpa [prefixWord, tailWord_7182344, baseEnd_7182344] using wordTrace_append hprefix tailTrace_7182344
  have hstable : (prefixWord ++ tailWord_7182344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182344).length < 2 ^ (prefixWord ++ tailWord_7182344).sum := by decide
  have hdescent : baseEnd_7182344 < baseStart_7182344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182391 : List Nat := [1, 1, 3, 1, 2, 2, 4, 3, 2, 4]
def baseStart_7182391 : Nat := 118140960795 + 7182391 * 2 ^ 59
def prefixEnd_7182391 : Nat := 4983230072969 + 3 ^ 40 * 7182391 * 2
def baseEnd_7182391 : Nat := 1229339610508971198627097

theorem tailTrace_7182391 : CollatzResearch.WordTrace tailWord_7182391 prefixEnd_7182391 1229339610508971198627097 := by
  unfold tailWord_7182391
  simp only [CollatzResearch.WordTrace]
  refine ⟨261963320922431536568939027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174642213948287691045959351 261963320922431536568939027)
  ·
    refine ⟨392944981383647304853408541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261963320922431536568939027 392944981383647304853408541)
    ·
      refine ⟨147354368018867739320028203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392944981383647304853408541 147354368018867739320028203)
      ·
        refine ⟨221031552028301608980042305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147354368018867739320028203 221031552028301608980042305)
        ·
          refine ⟨165773664021226206735031729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221031552028301608980042305 165773664021226206735031729)
          ·
            refine ⟨124330248015919655051273797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165773664021226206735031729 124330248015919655051273797)
            ·
              refine ⟨23311921502984935322113837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124330248015919655051273797 23311921502984935322113837)
              ·
                refine ⟨8741970563619350745792689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23311921502984935322113837 8741970563619350745792689)
                ·
                  refine ⟨6556477922714513059344517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8741970563619350745792689 6556477922714513059344517)
                  ·
                    refine ⟨1229339610508971198627097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6556477922714513059344517 1229339610508971198627097)
                    ·
                      rfl

theorem cell23_7182391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 4, 3, 2, 4].length) (baseStart_7182391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182391 prefixEnd_7182391 := by exact prefixLift 7182391
  have htrace : WordTrace (prefixWord ++ tailWord_7182391) baseStart_7182391 baseEnd_7182391 := by
    simpa [prefixWord, tailWord_7182391, baseEnd_7182391] using wordTrace_append hprefix tailTrace_7182391
  have hstable : (prefixWord ++ tailWord_7182391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182391).length < 2 ^ (prefixWord ++ tailWord_7182391).sum := by decide
  have hdescent : baseEnd_7182391 < baseStart_7182391 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182448 : List Nat := [2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3]
def baseStart_7182448 : Nat := 118140960795 + 7182448 * 2 ^ 59
def prefixEnd_7182448 : Nat := 4983230072969 + 3 ^ 40 * 7182448 * 2
def baseEnd_7182448 : Nat := 3688048099924219872868529

theorem tailTrace_7182448 : CollatzResearch.WordTrace tailWord_7182448 prefixEnd_7182448 3688048099924219872868529 := by
  unfold tailWord_7182448
  simp only [CollatzResearch.WordTrace]
  refine ⟨130982699941612517651881999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174643599922150023535842665 130982699941612517651881999)
  ·
    refine ⟨196474049912418776477822999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130982699941612517651881999 196474049912418776477822999)
    ·
      refine ⟨294711074868628164716734499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196474049912418776477822999 294711074868628164716734499)
      ·
        refine ⟨442066612302942247075101749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294711074868628164716734499 442066612302942247075101749)
        ·
          refine ⟨41443744903400835663290789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 442066612302942247075101749 41443744903400835663290789)
          ·
            refine ⟨7770702169387656686867023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41443744903400835663290789 7770702169387656686867023)
            ·
              refine ⟨11656053254081485030300535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7770702169387656686867023 11656053254081485030300535)
              ·
                refine ⟨17484079881122227545450803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11656053254081485030300535 17484079881122227545450803)
                ·
                  refine ⟨26226119821683341318176205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17484079881122227545450803 26226119821683341318176205)
                  ·
                    refine ⟨9834794933131252994316077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26226119821683341318176205 9834794933131252994316077)
                    ·
                      refine ⟨3688048099924219872868529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9834794933131252994316077 3688048099924219872868529)
                      ·
                        rfl

theorem cell23_7182448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 1, 1, 1, 3, 3].length) (baseStart_7182448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182448 prefixEnd_7182448 := by exact prefixLift 7182448
  have htrace : WordTrace (prefixWord ++ tailWord_7182448) baseStart_7182448 baseEnd_7182448 := by
    simpa [prefixWord, tailWord_7182448, baseEnd_7182448] using wordTrace_append hprefix tailTrace_7182448
  have hstable : (prefixWord ++ tailWord_7182448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182448).length < 2 ^ (prefixWord ++ tailWord_7182448).sum := by decide
  have hdescent : baseEnd_7182448 < baseStart_7182448 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182561 : List Nat := [1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_7182561 : Nat := 118140960795 + 7182561 * 2 ^ 59
def prefixEnd_7182561 : Nat := 4983230072969 + 3 ^ 40 * 7182561 * 2
def baseEnd_7182561 : Nat := 3688106123238177930755509

theorem tailTrace_7182561 : CollatzResearch.WordTrace tailWord_7182561 prefixEnd_7182561 3688106123238177930755509 := by
  unfold tailWord_7182561
  simp only [CollatzResearch.WordTrace]
  refine ⟨261969521331815655602627537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174646347554543770401751691 261969521331815655602627537)
  ·
    refine ⟨196477140998861741701970653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261969521331815655602627537 196477140998861741701970653)
    ·
      refine ⟨73678927874573153138238995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196477140998861741701970653 73678927874573153138238995)
      ·
        refine ⟨110518391811859729707358493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73678927874573153138238995 110518391811859729707358493)
        ·
          refine ⟨41444396929447398640259435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110518391811859729707358493 41444396929447398640259435)
          ·
            refine ⟨62166595394171097960389153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41444396929447398640259435 62166595394171097960389153)
            ·
              refine ⟨46624946545628323470291865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62166595394171097960389153 46624946545628323470291865)
              ·
                refine ⟨34968709909221242602718899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46624946545628323470291865 34968709909221242602718899)
                ·
                  refine ⟨52453064863831863904078349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34968709909221242602718899 52453064863831863904078349)
                  ·
                    refine ⟨19669899323936948964029381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52453064863831863904078349 19669899323936948964029381)
                    ·
                      refine ⟨3688106123238177930755509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19669899323936948964029381 3688106123238177930755509)
                      ·
                        rfl

theorem cell23_7182561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_7182561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182561 prefixEnd_7182561 := by exact prefixLift 7182561
  have htrace : WordTrace (prefixWord ++ tailWord_7182561) baseStart_7182561 baseEnd_7182561 := by
    simpa [prefixWord, tailWord_7182561, baseEnd_7182561] using wordTrace_append hprefix tailTrace_7182561
  have hstable : (prefixWord ++ tailWord_7182561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182561).length < 2 ^ (prefixWord ++ tailWord_7182561).sum := by decide
  have hdescent : baseEnd_7182561 < baseStart_7182561 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182562 : List Nat := [3, 3, 4, 1, 1, 1, 1, 2, 7]
def baseStart_7182562 : Nat := 118140960795 + 7182562 * 2 ^ 59
def prefixEnd_7182562 : Nat := 4983230072969 + 3 ^ 40 * 7182562 * 2
def baseEnd_7182562 : Nat := 409789626302092491871445

theorem tailTrace_7182562 : CollatzResearch.WordTrace tailWord_7182562 prefixEnd_7182562 409789626302092491871445 := by
  unfold tailWord_7182562
  simp only [CollatzResearch.WordTrace]
  refine ⟨65492389451203008193353485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174646371869874688515609293 65492389451203008193353485)
  ·
    refine ⟨24559646044201128072507557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65492389451203008193353485 24559646044201128072507557)
    ·
      refine ⟨4604933633287711513595167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 24559646044201128072507557 4604933633287711513595167)
      ·
        refine ⟨6907400449931567270392751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4604933633287711513595167 6907400449931567270392751)
        ·
          refine ⟨10361100674897350905589127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907400449931567270392751 10361100674897350905589127)
          ·
            refine ⟨15541651012346026358383691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10361100674897350905589127 15541651012346026358383691)
            ·
              refine ⟨23312476518519039537575537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15541651012346026358383691 23312476518519039537575537)
              ·
                refine ⟨17484357388889279653181653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23312476518519039537575537 17484357388889279653181653)
                ·
                  refine ⟨409789626302092491871445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17484357388889279653181653 409789626302092491871445)
                  ·
                    rfl

theorem cell23_7182562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_7182562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182562 prefixEnd_7182562 := by exact prefixLift 7182562
  have htrace : WordTrace (prefixWord ++ tailWord_7182562) baseStart_7182562 baseEnd_7182562 := by
    simpa [prefixWord, tailWord_7182562, baseEnd_7182562] using wordTrace_append hprefix tailTrace_7182562
  have hstable : (prefixWord ++ tailWord_7182562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182562).length < 2 ^ (prefixWord ++ tailWord_7182562).sum := by decide
  have hdescent : baseEnd_7182562 < baseStart_7182562 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182578 : List Nat := [3, 2, 1, 3, 2, 2, 1, 1, 1, 3, 4]
def baseStart_7182578 : Nat := 118140960795 + 7182578 * 2 ^ 59
def prefixEnd_7182578 : Nat := 4983230072969 + 3 ^ 40 * 7182578 * 2
def baseEnd_7182578 : Nat := 3688114852409304364242931

theorem tailTrace_7182578 : CollatzResearch.WordTrace tailWord_7182578 prefixEnd_7182578 3688114852409304364242931 := by
  unfold tailWord_7182578
  simp only [CollatzResearch.WordTrace]
  refine ⟨65492535343188516876499097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174646760915169378337330925 65492535343188516876499097)
  ·
    refine ⟨49119401507391387657374323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65492535343188516876499097 49119401507391387657374323)
    ·
      refine ⟨73679102261087081486061485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49119401507391387657374323 73679102261087081486061485)
      ·
        refine ⟨27629663347907655557273057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73679102261087081486061485 27629663347907655557273057)
        ·
          refine ⟨20722247510930741667954793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27629663347907655557273057 20722247510930741667954793)
          ·
            refine ⟨15541685633198056250966095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20722247510930741667954793 15541685633198056250966095)
            ·
              refine ⟨23312528449797084376449143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15541685633198056250966095 23312528449797084376449143)
              ·
                refine ⟨34968792674695626564673715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23312528449797084376449143 34968792674695626564673715)
                ·
                  refine ⟨52453189012043439847010573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34968792674695626564673715 52453189012043439847010573)
                  ·
                    refine ⟨19669945879516289942628965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52453189012043439847010573 19669945879516289942628965)
                    ·
                      refine ⟨3688114852409304364242931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19669945879516289942628965 3688114852409304364242931)
                      ·
                        rfl

theorem cell23_7182578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 2, 2, 1, 1, 1, 3, 4].length) (baseStart_7182578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182578 prefixEnd_7182578 := by exact prefixLift 7182578
  have htrace : WordTrace (prefixWord ++ tailWord_7182578) baseStart_7182578 baseEnd_7182578 := by
    simpa [prefixWord, tailWord_7182578, baseEnd_7182578] using wordTrace_append hprefix tailTrace_7182578
  have hstable : (prefixWord ++ tailWord_7182578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182578).length < 2 ^ (prefixWord ++ tailWord_7182578).sum := by decide
  have hdescent : baseEnd_7182578 < baseStart_7182578 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182601 : List Nat := [1, 2, 1, 1, 3, 5, 1, 1, 8]
def baseStart_7182601 : Nat := 118140960795 + 7182601 * 2 ^ 59
def prefixEnd_7182601 : Nat := 4983230072969 + 3 ^ 40 * 7182601 * 2
def baseEnd_7182601 : Nat := 409791851384928641583925

theorem tailTrace_7182601 : CollatzResearch.WordTrace tailWord_7182601 prefixEnd_7182601 409791851384928641583925 := by
  unfold tailWord_7182601
  simp only [CollatzResearch.WordTrace]
  refine ⟨261970980251670742434083657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174647320167780494956055771 261970980251670742434083657)
  ·
    refine ⟨196478235188753056825562743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261970980251670742434083657 196478235188753056825562743)
    ·
      refine ⟨294717352783129585238344115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196478235188753056825562743 294717352783129585238344115)
      ·
        refine ⟨442076029174694377857516173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294717352783129585238344115 442076029174694377857516173)
        ·
          refine ⟨165778510940510391696568565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442076029174694377857516173 165778510940510391696568565)
          ·
            refine ⟨15541735400672849221553303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165778510940510391696568565 15541735400672849221553303)
            ·
              refine ⟨23312603101009273832329955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15541735400672849221553303 23312603101009273832329955)
              ·
                refine ⟨34968904651513910748494933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23312603101009273832329955 34968904651513910748494933)
                ·
                  refine ⟨409791851384928641583925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34968904651513910748494933 409791851384928641583925)
                  ·
                    rfl

theorem cell23_7182601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 8].length) (baseStart_7182601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182601 prefixEnd_7182601 := by exact prefixLift 7182601
  have htrace : WordTrace (prefixWord ++ tailWord_7182601) baseStart_7182601 baseEnd_7182601 := by
    simpa [prefixWord, tailWord_7182601, baseEnd_7182601] using wordTrace_append hprefix tailTrace_7182601
  have hstable : (prefixWord ++ tailWord_7182601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182601).length < 2 ^ (prefixWord ++ tailWord_7182601).sum := by decide
  have hdescent : baseEnd_7182601 < baseStart_7182601 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182622 : List Nat := [4, 3, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_7182622 : Nat := 118140960795 + 7182622 * 2 ^ 59
def prefixEnd_7182622 : Nat := 4983230072969 + 3 ^ 40 * 7182622 * 2
def baseEnd_7182622 : Nat := 1229379148519367397364243

theorem tailTrace_7182622 : CollatzResearch.WordTrace tailWord_7182622 prefixEnd_7182622 1229379148519367397364243 := by
  unfold tailWord_7182622
  simp only [CollatzResearch.WordTrace]
  refine ⟨32746468273074332877574765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174647830789729775347065413 32746468273074332877574765)
  ·
    refine ⟨12279925602402874829090537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 32746468273074332877574765 12279925602402874829090537)
    ·
      refine ⟨9209944201802156121817903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12279925602402874829090537 9209944201802156121817903)
      ·
        refine ⟨13814916302703234182726855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9209944201802156121817903 13814916302703234182726855)
        ·
          refine ⟨20722374454054851274090283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13814916302703234182726855 20722374454054851274090283)
          ·
            refine ⟨31083561681082276911135425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20722374454054851274090283 31083561681082276911135425)
            ·
              refine ⟨23312671260811707683351569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31083561681082276911135425 23312671260811707683351569)
              ·
                refine ⟨17484503445608780762513677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23312671260811707683351569 17484503445608780762513677)
                ·
                  refine ⟨6556688792103292785942629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17484503445608780762513677 6556688792103292785942629)
                  ·
                    refine ⟨1229379148519367397364243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6556688792103292785942629 1229379148519367397364243)
                    ·
                      rfl

theorem cell23_7182622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_7182622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182622 prefixEnd_7182622 := by exact prefixLift 7182622
  have htrace : WordTrace (prefixWord ++ tailWord_7182622) baseStart_7182622 baseEnd_7182622 := by
    simpa [prefixWord, tailWord_7182622, baseEnd_7182622] using wordTrace_append hprefix tailTrace_7182622
  have hstable : (prefixWord ++ tailWord_7182622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182622).length < 2 ^ (prefixWord ++ tailWord_7182622).sum := by decide
  have hdescent : baseEnd_7182622 < baseStart_7182622 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182648 : List Nat := [2, 1, 2, 1, 3, 1, 4, 3, 1, 5]
def baseStart_7182648 : Nat := 118140960795 + 7182648 * 2 ^ 59
def prefixEnd_7182648 : Nat := 4983230072969 + 3 ^ 40 * 7182648 * 2
def baseEnd_7182648 : Nat := 1229383598685039696789203

theorem tailTrace_7182648 : CollatzResearch.WordTrace tailWord_7182648 prefixEnd_7182648 1229383598685039696789203 := by
  unfold tailWord_7182648
  simp only [CollatzResearch.WordTrace]
  refine ⟨130986347241250234730522299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174648462988333646307363065 130986347241250234730522299)
  ·
    refine ⟨196479520861875352095783449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130986347241250234730522299 196479520861875352095783449)
    ·
      refine ⟨147359640646406514071837587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196479520861875352095783449 147359640646406514071837587)
      ·
        refine ⟨221039460969609771107756381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147359640646406514071837587 221039460969609771107756381)
        ·
          refine ⟨82889797863603664165408643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221039460969609771107756381 82889797863603664165408643)
          ·
            refine ⟨124334696795405496248112965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82889797863603664165408643 124334696795405496248112965)
            ·
              refine ⟨23312755649138530546521181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124334696795405496248112965 23312755649138530546521181)
              ·
                refine ⟨8742283368426948954945443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23312755649138530546521181 8742283368426948954945443)
                ·
                  refine ⟨13113425052640423432418165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8742283368426948954945443 13113425052640423432418165)
                  ·
                    refine ⟨1229383598685039696789203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13113425052640423432418165 1229383598685039696789203)
                    ·
                      rfl

theorem cell23_7182648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 4, 3, 1, 5].length) (baseStart_7182648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182648 prefixEnd_7182648 := by exact prefixLift 7182648
  have htrace : WordTrace (prefixWord ++ tailWord_7182648) baseStart_7182648 baseEnd_7182648 := by
    simpa [prefixWord, tailWord_7182648, baseEnd_7182648] using wordTrace_append hprefix tailTrace_7182648
  have hstable : (prefixWord ++ tailWord_7182648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182648).length < 2 ^ (prefixWord ++ tailWord_7182648).sum := by decide
  have hdescent : baseEnd_7182648 < baseStart_7182648 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182655 : List Nat := [1, 1, 2, 2, 4, 1, 3, 2, 2, 3, 2]
def baseStart_7182655 : Nat := 118140960795 + 7182655 * 2 ^ 59
def prefixEnd_7182655 : Nat := 4983230072969 + 3 ^ 40 * 7182655 * 2
def baseEnd_7182655 : Nat := 3688154390419700562980077

theorem tailTrace_7182655 : CollatzResearch.WordTrace tailWord_7182655 prefixEnd_7182655 3688154390419700562980077 := by
  unfold tailWord_7182655
  simp only [CollatzResearch.WordTrace]
  refine ⟨261972949793475109656549419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174648633195650073104366279 261972949793475109656549419)
  ·
    refine ⟨392959424690212664484824129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261972949793475109656549419 392959424690212664484824129)
    ·
      refine ⟨294719568517659498363618097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392959424690212664484824129 294719568517659498363618097)
      ·
        refine ⟨221039676388244623772713573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294719568517659498363618097 221039676388244623772713573)
        ·
          refine ⟨41444939322795866957383795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221039676388244623772713573 41444939322795866957383795)
          ·
            refine ⟨62167408984193800436075693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41444939322795866957383795 62167408984193800436075693)
            ·
              refine ⟨23312778369072675163528385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62167408984193800436075693 23312778369072675163528385)
              ·
                refine ⟨17484583776804506372646289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23312778369072675163528385 17484583776804506372646289)
                ·
                  refine ⟨13113437832603379779484717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17484583776804506372646289 13113437832603379779484717)
                  ·
                    refine ⟨4917539187226267417306769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13113437832603379779484717 4917539187226267417306769)
                    ·
                      refine ⟨3688154390419700562980077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917539187226267417306769 3688154390419700562980077)
                      ·
                        rfl

theorem cell23_7182655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 3, 2, 2, 3, 2].length) (baseStart_7182655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182655 prefixEnd_7182655 := by exact prefixLift 7182655
  have htrace : WordTrace (prefixWord ++ tailWord_7182655) baseStart_7182655 baseEnd_7182655 := by
    simpa [prefixWord, tailWord_7182655, baseEnd_7182655] using wordTrace_append hprefix tailTrace_7182655
  have hstable : (prefixWord ++ tailWord_7182655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182655).length < 2 ^ (prefixWord ++ tailWord_7182655).sum := by decide
  have hdescent : baseEnd_7182655 < baseStart_7182655 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182668 : List Nat := [2, 2, 1, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_7182668 : Nat := 118140960795 + 7182668 * 2 ^ 59
def prefixEnd_7182668 : Nat := 4983230072969 + 3 ^ 40 * 7182668 * 2
def baseEnd_7182668 : Nat := 3688161065668209012117517

theorem tailTrace_7182668 : CollatzResearch.WordTrace tailWord_7182668 prefixEnd_7182668 3688161065668209012117517 := by
  unfold tailWord_7182668
  simp only [CollatzResearch.WordTrace]
  refine ⟨130986711971214006438386329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174648949294952008584515105 130986711971214006438386329)
  ·
    refine ⟨98240033978410504828789747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130986711971214006438386329 98240033978410504828789747)
    ·
      refine ⟨147360050967615757243184621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98240033978410504828789747 147360050967615757243184621)
      ·
        refine ⟨55260019112855908966194233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147360050967615757243184621 55260019112855908966194233)
        ·
          refine ⟨41445014334641931724645675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55260019112855908966194233 41445014334641931724645675)
          ·
            refine ⟨62167521501962897586968513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41445014334641931724645675 62167521501962897586968513)
            ·
              refine ⟨46625641126472173190226385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62167521501962897586968513 46625641126472173190226385)
              ·
                refine ⟨34969230844854129892669789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46625641126472173190226385 34969230844854129892669789)
                ·
                  refine ⟨13113461566820298709751171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34969230844854129892669789 13113461566820298709751171)
                  ·
                    refine ⟨19670192350230448064626757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13113461566820298709751171 19670192350230448064626757)
                    ·
                      refine ⟨3688161065668209012117517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19670192350230448064626757 3688161065668209012117517)
                      ·
                        rfl

theorem cell23_7182668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_7182668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182668 prefixEnd_7182668 := by exact prefixLift 7182668
  have htrace : WordTrace (prefixWord ++ tailWord_7182668) baseStart_7182668 baseEnd_7182668 := by
    simpa [prefixWord, tailWord_7182668, baseEnd_7182668] using wordTrace_append hprefix tailTrace_7182668
  have hstable : (prefixWord ++ tailWord_7182668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182668).length < 2 ^ (prefixWord ++ tailWord_7182668).sum := by decide
  have hdescent : baseEnd_7182668 < baseStart_7182668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182671 : List Nat := [1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 5]
def baseStart_7182671 : Nat := 118140960795 + 7182671 * 2 ^ 59
def prefixEnd_7182671 : Nat := 4983230072969 + 3 ^ 40 * 7182671 * 2
def baseEnd_7182671 : Nat := 3688162606110172500380003

theorem tailTrace_7182671 : CollatzResearch.WordTrace tailWord_7182671 prefixEnd_7182671 3688162606110172500380003 := by
  unfold tailWord_7182671
  simp only [CollatzResearch.WordTrace]
  refine ⟨261973533361417144389131867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174649022240944762926087911 261973533361417144389131867)
  ·
    refine ⟨392960300042125716583697801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261973533361417144389131867 392960300042125716583697801)
    ·
      refine ⟨294720225031594287437773351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392960300042125716583697801 294720225031594287437773351)
      ·
        refine ⟨442080337547391431156660027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294720225031594287437773351 442080337547391431156660027)
        ·
          refine ⟨663120506321087146734990041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442080337547391431156660027 663120506321087146734990041)
          ·
            refine ⟨497340379740815360051242531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663120506321087146734990041 497340379740815360051242531)
            ·
              refine ⟨746010569611223040076863797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497340379740815360051242531 746010569611223040076863797)
              ·
                refine ⟨69938490901052160007205981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 746010569611223040076863797 69938490901052160007205981)
                ·
                  refine ⟨26226934087894560002702243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69938490901052160007205981 26226934087894560002702243)
                  ·
                    refine ⟨39340401131841840004053365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26226934087894560002702243 39340401131841840004053365)
                    ·
                      refine ⟨3688162606110172500380003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39340401131841840004053365 3688162606110172500380003)
                      ·
                        rfl

theorem cell23_7182671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 5, 3, 1, 5].length) (baseStart_7182671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182671 prefixEnd_7182671 := by exact prefixLift 7182671
  have htrace : WordTrace (prefixWord ++ tailWord_7182671) baseStart_7182671 baseEnd_7182671 := by
    simpa [prefixWord, tailWord_7182671, baseEnd_7182671] using wordTrace_append hprefix tailTrace_7182671
  have hstable : (prefixWord ++ tailWord_7182671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182671).length < 2 ^ (prefixWord ++ tailWord_7182671).sum := by decide
  have hdescent : baseEnd_7182671 < baseStart_7182671 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182691 : List Nat := [1, 1, 1, 5, 2, 1, 1, 11]
def baseStart_7182691 : Nat := 118140960795 + 7182691 * 2 ^ 59
def prefixEnd_7182691 : Nat := 4983230072969 + 3 ^ 40 * 7182691 * 2
def baseEnd_7182691 : Nat := 136598995397157867486293

theorem tailTrace_7182691 : CollatzResearch.WordTrace tailWord_7182691 prefixEnd_7182691 136598995397157867486293 := by
  unfold tailWord_7182691
  simp only [CollatzResearch.WordTrace]
  refine ⟨261974262821344687804859927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174649508547563125203239951 261974262821344687804859927)
  ·
    refine ⟨392961394232017031707289891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261974262821344687804859927 392961394232017031707289891)
    ·
      refine ⟨589442091348025547560934837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392961394232017031707289891 589442091348025547560934837)
      ·
        refine ⟨55260196063877395083837641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 589442091348025547560934837 55260196063877395083837641)
        ·
          refine ⟨41445147047908046312878231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55260196063877395083837641 41445147047908046312878231)
          ·
            refine ⟨62167720571862069469317347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41445147047908046312878231 62167720571862069469317347)
            ·
              refine ⟨93251580857793104203976021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62167720571862069469317347 93251580857793104203976021)
              ·
                refine ⟨136598995397157867486293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 93251580857793104203976021 136598995397157867486293)
                ·
                  rfl

theorem cell23_7182691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 11].length) (baseStart_7182691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182691 prefixEnd_7182691 := by exact prefixLift 7182691
  have htrace : WordTrace (prefixWord ++ tailWord_7182691) baseStart_7182691 baseEnd_7182691 := by
    simpa [prefixWord, tailWord_7182691, baseEnd_7182691] using wordTrace_append hprefix tailTrace_7182691
  have hstable : (prefixWord ++ tailWord_7182691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182691).length < 2 ^ (prefixWord ++ tailWord_7182691).sum := by decide
  have hdescent : baseEnd_7182691 < baseStart_7182691 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182711 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 6]
def baseStart_7182711 : Nat := 118140960795 + 7182711 * 2 ^ 59
def prefixEnd_7182711 : Nat := 4983230072969 + 3 ^ 40 * 7182711 * 2
def baseEnd_7182711 : Nat := 3688183145336352343879819

theorem tailTrace_7182711 : CollatzResearch.WordTrace tailWord_7182711 prefixEnd_7182711 3688183145336352343879819 := by
  unfold tailWord_7182711
  simp only [CollatzResearch.WordTrace]
  refine ⟨261974992281272231220587987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174649994854181487480391991 261974992281272231220587987)
  ·
    refine ⟨392962488421908346830881981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261974992281272231220587987 392962488421908346830881981)
    ·
      refine ⟨147360933158215630061580743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392962488421908346830881981 147360933158215630061580743)
      ·
        refine ⟨221041399737323445092371115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147360933158215630061580743 221041399737323445092371115)
        ·
          refine ⟨331562099605985167638556673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221041399737323445092371115 331562099605985167638556673)
          ·
            refine ⟨248671574704488875728917505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331562099605985167638556673 248671574704488875728917505)
            ·
              refine ⟨186503681028366656796688129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248671574704488875728917505 186503681028366656796688129)
              ·
                refine ⟨139877760771274992597516097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186503681028366656796688129 139877760771274992597516097)
                ·
                  refine ⟨104908320578456244448137073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139877760771274992597516097 104908320578456244448137073)
                  ·
                    refine ⟨78681240433842183336102805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104908320578456244448137073 78681240433842183336102805)
                    ·
                      refine ⟨3688183145336352343879819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78681240433842183336102805 3688183145336352343879819)
                      ·
                        rfl

theorem cell23_7182711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_7182711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182711 prefixEnd_7182711 := by exact prefixLift 7182711
  have htrace : WordTrace (prefixWord ++ tailWord_7182711) baseStart_7182711 baseEnd_7182711 := by
    simpa [prefixWord, tailWord_7182711, baseEnd_7182711] using wordTrace_append hprefix tailTrace_7182711
  have hstable : (prefixWord ++ tailWord_7182711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182711).length < 2 ^ (prefixWord ++ tailWord_7182711).sum := by decide
  have hdescent : baseEnd_7182711 < baseStart_7182711 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182745 : List Nat := [1, 2, 1, 2, 1, 4, 1, 3, 3, 3, 2]
def baseStart_7182745 : Nat := 118140960795 + 7182745 * 2 ^ 59
def prefixEnd_7182745 : Nat := 4983230072969 + 3 ^ 40 * 7182745 * 2
def baseEnd_7182745 : Nat := 3688200603678605210854663

theorem tailTrace_7182745 : CollatzResearch.WordTrace tailWord_7182745 prefixEnd_7182745 3688200603678605210854663 := by
  unfold tailWord_7182745
  simp only [CollatzResearch.WordTrace]
  refine ⟨261976232363149055027325689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174650821575432703351550459 261976232363149055027325689)
  ·
    refine ⟨196482174272361791270494267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261976232363149055027325689 196482174272361791270494267)
    ·
      refine ⟨294723261408542686905741401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196482174272361791270494267 294723261408542686905741401)
      ·
        refine ⟨221042446056407015179306051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294723261408542686905741401 221042446056407015179306051)
        ·
          refine ⟨331563669084610522768959077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221042446056407015179306051 331563669084610522768959077)
          ·
            refine ⟨62168187953364473019179827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331563669084610522768959077 62168187953364473019179827)
            ·
              refine ⟨93252281930046709528769741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62168187953364473019179827 93252281930046709528769741)
              ·
                refine ⟨34969605723767516073288653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93252281930046709528769741 34969605723767516073288653)
                ·
                  refine ⟨13113602146412818527483245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34969605723767516073288653 13113602146412818527483245)
                  ·
                    refine ⟨4917600804904806947806217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13113602146412818527483245 4917600804904806947806217)
                    ·
                      refine ⟨3688200603678605210854663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917600804904806947806217 3688200603678605210854663)
                      ·
                        rfl

theorem cell23_7182745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 3, 3, 3, 2].length) (baseStart_7182745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182745 prefixEnd_7182745 := by exact prefixLift 7182745
  have htrace : WordTrace (prefixWord ++ tailWord_7182745) baseStart_7182745 baseEnd_7182745 := by
    simpa [prefixWord, tailWord_7182745, baseEnd_7182745] using wordTrace_append hprefix tailTrace_7182745
  have hstable : (prefixWord ++ tailWord_7182745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182745).length < 2 ^ (prefixWord ++ tailWord_7182745).sum := by decide
  have hdescent : baseEnd_7182745 < baseStart_7182745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182753 : List Nat := [1, 2, 3, 5, 1, 1, 2, 3, 1, 2, 2]
def baseStart_7182753 : Nat := 118140960795 + 7182753 * 2 ^ 59
def prefixEnd_7182753 : Nat := 4983230072969 + 3 ^ 40 * 7182753 * 2
def baseEnd_7182753 : Nat := 3688204711523841179554627

theorem tailTrace_7182753 : CollatzResearch.WordTrace tailWord_7182753 prefixEnd_7182753 3688204711523841179554627 := by
  unfold tailWord_7182753
  simp only [CollatzResearch.WordTrace]
  refine ⟨261976524147120072393616913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174651016098080048262411275 261976524147120072393616913)
  ·
    refine ⟨196482393110340054295212685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261976524147120072393616913 196482393110340054295212685)
    ·
      refine ⟨73680897416377520360704757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196482393110340054295212685 73680897416377520360704757)
      ·
        refine ⟨6907584132785392533816071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 73680897416377520360704757 6907584132785392533816071)
        ·
          refine ⟨10361376199178088800724107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907584132785392533816071 10361376199178088800724107)
          ·
            refine ⟨15542064298767133201086161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10361376199178088800724107 15542064298767133201086161)
            ·
              refine ⟨11656548224075349900814621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15542064298767133201086161 11656548224075349900814621)
              ·
                refine ⟨4371205584028256212805483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11656548224075349900814621 4371205584028256212805483)
                ·
                  refine ⟨6556808376042384319208225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371205584028256212805483 6556808376042384319208225)
                  ·
                    refine ⟨4917606282031788239406169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6556808376042384319208225 4917606282031788239406169)
                    ·
                      refine ⟨3688204711523841179554627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917606282031788239406169 3688204711523841179554627)
                      ·
                        rfl

theorem cell23_7182753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 1, 2, 2].length) (baseStart_7182753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182753 prefixEnd_7182753 := by exact prefixLift 7182753
  have htrace : WordTrace (prefixWord ++ tailWord_7182753) baseStart_7182753 baseEnd_7182753 := by
    simpa [prefixWord, tailWord_7182753, baseEnd_7182753] using wordTrace_append hprefix tailTrace_7182753
  have hstable : (prefixWord ++ tailWord_7182753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182753).length < 2 ^ (prefixWord ++ tailWord_7182753).sum := by decide
  have hdescent : baseEnd_7182753 < baseStart_7182753 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182769 : List Nat := [1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 3]
def baseStart_7182769 : Nat := 118140960795 + 7182769 * 2 ^ 59
def prefixEnd_7182769 : Nat := 4983230072969 + 3 ^ 40 * 7182769 * 2
def baseEnd_7182769 : Nat := 3688212927214313116954553

theorem tailTrace_7182769 : CollatzResearch.WordTrace tailWord_7182769 prefixEnd_7182769 3688212927214313116954553 := by
  unfold tailWord_7182769
  simp only [CollatzResearch.WordTrace]
  refine ⟨261977107715062107126199361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174651405143374738084132907 261977107715062107126199361)
  ·
    refine ⟨196482830786296580344649521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261977107715062107126199361 196482830786296580344649521)
    ·
      refine ⟨147362123089722435258487141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196482830786296580344649521 147362123089722435258487141)
      ·
        refine ⟨27630398079322956610966339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 147362123089722435258487141 27630398079322956610966339)
        ·
          refine ⟨41445597118984434916449509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27630398079322956610966339 41445597118984434916449509)
          ·
            refine ⟨7771049459809581546834283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41445597118984434916449509 7771049459809581546834283)
            ·
              refine ⟨11656574189714372320251425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7771049459809581546834283 11656574189714372320251425)
              ·
                refine ⟨8742430642285779240188569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11656574189714372320251425 8742430642285779240188569)
                ·
                  refine ⟨6556822981714334430141427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8742430642285779240188569 6556822981714334430141427)
                  ·
                    refine ⟨9835234472571501645212141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6556822981714334430141427 9835234472571501645212141)
                    ·
                      refine ⟨3688212927214313116954553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9835234472571501645212141 3688212927214313116954553)
                      ·
                        rfl

theorem cell23_7182769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_7182769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182769 prefixEnd_7182769 := by exact prefixLift 7182769
  have htrace : WordTrace (prefixWord ++ tailWord_7182769) baseStart_7182769 baseEnd_7182769 := by
    simpa [prefixWord, tailWord_7182769, baseEnd_7182769] using wordTrace_append hprefix tailTrace_7182769
  have hstable : (prefixWord ++ tailWord_7182769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182769).length < 2 ^ (prefixWord ++ tailWord_7182769).sum := by decide
  have hdescent : baseEnd_7182769 < baseStart_7182769 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182778 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3]
def baseStart_7182778 : Nat := 118140960795 + 7182778 * 2 ^ 59
def prefixEnd_7182778 : Nat := 4983230072969 + 3 ^ 40 * 7182778 * 2
def baseEnd_7182778 : Nat := 3688217548540203581742011

theorem tailTrace_7182778 : CollatzResearch.WordTrace tailWord_7182778 prefixEnd_7182778 3688217548540203581742011 := by
  unfold tailWord_7182778
  simp only [CollatzResearch.WordTrace]
  refine ⟨65494358993007375415819247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174651623981353001108851325 65494358993007375415819247)
  ·
    refine ⟨98241538489511063123728871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65494358993007375415819247 98241538489511063123728871)
    ·
      refine ⟨147362307734266594685593307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98241538489511063123728871 147362307734266594685593307)
      ·
        refine ⟨221043461601399892028389961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147362307734266594685593307 221043461601399892028389961)
        ·
          refine ⟨165782596201049919021292471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221043461601399892028389961 165782596201049919021292471)
          ·
            refine ⟨248673894301574878531938707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165782596201049919021292471 248673894301574878531938707)
            ·
              refine ⟨373010841452362317797908061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248673894301574878531938707 373010841452362317797908061)
              ·
                refine ⟨139879065544635869174215523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373010841452362317797908061 139879065544635869174215523)
                ·
                  refine ⟨209818598316953803761323285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139879065544635869174215523 209818598316953803761323285)
                  ·
                    refine ⟨9835246796107209551312029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 209818598316953803761323285 9835246796107209551312029)
                    ·
                      refine ⟨3688217548540203581742011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9835246796107209551312029 3688217548540203581742011)
                      ·
                        rfl

theorem cell23_7182778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 1, 6, 3].length) (baseStart_7182778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182778 prefixEnd_7182778 := by exact prefixLift 7182778
  have htrace : WordTrace (prefixWord ++ tailWord_7182778) baseStart_7182778 baseEnd_7182778 := by
    simpa [prefixWord, tailWord_7182778, baseEnd_7182778] using wordTrace_append hprefix tailTrace_7182778
  have hstable : (prefixWord ++ tailWord_7182778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182778).length < 2 ^ (prefixWord ++ tailWord_7182778).sum := by decide
  have hdescent : baseEnd_7182778 < baseStart_7182778 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182792 : List Nat := [2, 1, 3, 1, 3, 2, 3, 1, 1, 4, 2]
def baseStart_7182792 : Nat := 118140960795 + 7182792 * 2 ^ 59
def prefixEnd_7182792 : Nat := 4983230072969 + 3 ^ 40 * 7182792 * 2
def baseEnd_7182792 : Nat := 3688224737269366526966947

theorem tailTrace_7182792 : CollatzResearch.WordTrace tailWord_7182792 prefixEnd_7182792 3688224737269366526966947 := by
  unfold tailWord_7182792
  simp only [CollatzResearch.WordTrace]
  refine ⟨130988973296989391027143315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174651964395985854702857753 130988973296989391027143315)
  ·
    refine ⟨196483459945484086540714973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130988973296989391027143315 196483459945484086540714973)
    ·
      refine ⟨73681297479556532452768115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196483459945484086540714973 73681297479556532452768115)
      ·
        refine ⟨110521946219334798679152173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73681297479556532452768115 110521946219334798679152173)
        ·
          refine ⟨41445729832250549504682065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110521946219334798679152173 41445729832250549504682065)
          ·
            refine ⟨31084297374187912128511549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41445729832250549504682065 31084297374187912128511549)
            ·
              refine ⟨11656611515320467048191831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31084297374187912128511549 11656611515320467048191831)
              ·
                refine ⟨17484917272980700572287747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11656611515320467048191831 17484917272980700572287747)
                ·
                  refine ⟨26227375909471050858431621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17484917272980700572287747 26227375909471050858431621)
                  ·
                    refine ⟨4917632983025822035955929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26227375909471050858431621 4917632983025822035955929)
                    ·
                      refine ⟨3688224737269366526966947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917632983025822035955929 3688224737269366526966947)
                      ·
                        rfl

theorem cell23_7182792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3, 1, 1, 4, 2].length) (baseStart_7182792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182792 prefixEnd_7182792 := by exact prefixLift 7182792
  have htrace : WordTrace (prefixWord ++ tailWord_7182792) baseStart_7182792 baseEnd_7182792 := by
    simpa [prefixWord, tailWord_7182792, baseEnd_7182792] using wordTrace_append hprefix tailTrace_7182792
  have hstable : (prefixWord ++ tailWord_7182792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182792).length < 2 ^ (prefixWord ++ tailWord_7182792).sum := by decide
  have hdescent : baseEnd_7182792 < baseStart_7182792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182832 : List Nat := [2, 1, 1, 1, 3, 3, 5, 2, 5]
def baseStart_7182832 : Nat := 118140960795 + 7182832 * 2 ^ 59
def prefixEnd_7182832 : Nat := 4983230072969 + 3 ^ 40 * 7182832 * 2
def baseEnd_7182832 : Nat := 409805030721727374496307

theorem tailTrace_7182832 : CollatzResearch.WordTrace tailWord_7182832 prefixEnd_7182832 409805030721727374496307 := by
  unfold tailWord_7182832
  simp only [CollatzResearch.WordTrace]
  refine ⟨130989702756916934442871375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174652937009222579257161833 130989702756916934442871375)
  ·
    refine ⟨196484554135375401664307063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130989702756916934442871375 196484554135375401664307063)
    ·
      refine ⟨294726831203063102496460595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196484554135375401664307063 294726831203063102496460595)
      ·
        refine ⟨442090246804594653744690893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294726831203063102496460595 442090246804594653744690893)
        ·
          refine ⟨165783842551722995154259085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442090246804594653744690893 165783842551722995154259085)
          ·
            refine ⟨62168940956896123182847157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 165783842551722995154259085 62168940956896123182847157)
            ·
              refine ⟨5828338214709011548391921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62168940956896123182847157 5828338214709011548391921)
              ·
                refine ⟨4371253661031758661293941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828338214709011548391921 4371253661031758661293941)
                ·
                  refine ⟨409805030721727374496307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4371253661031758661293941 409805030721727374496307)
                  ·
                    rfl

theorem cell23_7182832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 5, 2, 5].length) (baseStart_7182832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182832 prefixEnd_7182832 := by exact prefixLift 7182832
  have htrace : WordTrace (prefixWord ++ tailWord_7182832) baseStart_7182832 baseEnd_7182832 := by
    simpa [prefixWord, tailWord_7182832, baseEnd_7182832] using wordTrace_append hprefix tailTrace_7182832
  have hstable : (prefixWord ++ tailWord_7182832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182832).length < 2 ^ (prefixWord ++ tailWord_7182832).sum := by decide
  have hdescent : baseEnd_7182832 < baseStart_7182832 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182835 : List Nat := [1, 1, 1, 2, 2, 2, 4, 1, 2, 5, 2]
def baseStart_7182835 : Nat := 118140960795 + 7182835 * 2 ^ 59
def prefixEnd_7182835 : Nat := 4983230072969 + 3 ^ 40 * 7182835 * 2
def baseEnd_7182835 : Nat := 3688246816937509858729249

theorem tailTrace_7182835 : CollatzResearch.WordTrace tailWord_7182835 prefixEnd_7182835 3688246816937509858729249 := by
  unfold tailWord_7182835
  simp only [CollatzResearch.WordTrace]
  refine ⟨261979514932823000398101959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174653009955215333598734639 261979514932823000398101959)
  ·
    refine ⟨392969272399234500597152939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261979514932823000398101959 392969272399234500597152939)
    ·
      refine ⟨589453908598851750895729409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392969272399234500597152939 589453908598851750895729409)
      ·
        refine ⟨442090431449138813171797057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589453908598851750895729409 442090431449138813171797057)
        ·
          refine ⟨331567823586854109878847793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442090431449138813171797057 331567823586854109878847793)
          ·
            refine ⟨248675867690140582409135845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331567823586854109878847793 248675867690140582409135845)
            ·
              refine ⟨46626725191901359201712971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248675867690140582409135845 46626725191901359201712971)
              ·
                refine ⟨69940087787852038802569457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46626725191901359201712971 69940087787852038802569457)
                ·
                  refine ⟨52455065840889029101927093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69940087787852038802569457 52455065840889029101927093)
                  ·
                    refine ⟨4917662422583346478305665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52455065840889029101927093 4917662422583346478305665)
                    ·
                      refine ⟨3688246816937509858729249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917662422583346478305665 3688246816937509858729249)
                      ·
                        rfl

theorem cell23_7182835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 4, 1, 2, 5, 2].length) (baseStart_7182835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182835 prefixEnd_7182835 := by exact prefixLift 7182835
  have htrace : WordTrace (prefixWord ++ tailWord_7182835) baseStart_7182835 baseEnd_7182835 := by
    simpa [prefixWord, tailWord_7182835, baseEnd_7182835] using wordTrace_append hprefix tailTrace_7182835
  have hstable : (prefixWord ++ tailWord_7182835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182835).length < 2 ^ (prefixWord ++ tailWord_7182835).sum := by decide
  have hdescent : baseEnd_7182835 < baseStart_7182835 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182862 : List Nat := [4, 1, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_7182862 : Nat := 118140960795 + 7182862 * 2 ^ 59
def prefixEnd_7182862 : Nat := 4983230072969 + 3 ^ 40 * 7182862 * 2
def baseEnd_7182862 : Nat := 1229420226971727084363875

theorem tailTrace_7182862 : CollatzResearch.WordTrace tailWord_7182862 prefixEnd_7182862 1229420226971727084363875 := by
  unfold tailWord_7182862
  simp only [CollatzResearch.WordTrace]
  refine ⟨32747562462965648001166855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174653666469150122672889893 32747562462965648001166855)
  ·
    refine ⟨49121343694448472001750283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32747562462965648001166855 49121343694448472001750283)
    ·
      refine ⟨73682015541672708002625425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49121343694448472001750283 73682015541672708002625425)
      ·
        refine ⟨55261511656254531001969069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73682015541672708002625425 55261511656254531001969069)
        ·
          refine ⟨20723066871095449125738401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55261511656254531001969069 20723066871095449125738401)
          ·
            refine ⟨15542300153321586844303801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20723066871095449125738401 15542300153321586844303801)
            ·
              refine ⟨11656725114991190133227851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15542300153321586844303801 11656725114991190133227851)
              ·
                refine ⟨17485087672486785199841777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11656725114991190133227851 17485087672486785199841777)
                ·
                  refine ⟨13113815754365088899881333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17485087672486785199841777 13113815754365088899881333)
                  ·
                    refine ⟨1229420226971727084363875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13113815754365088899881333 1229420226971727084363875)
                    ·
                      rfl

theorem cell23_7182862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_7182862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182862 prefixEnd_7182862 := by exact prefixLift 7182862
  have htrace : WordTrace (prefixWord ++ tailWord_7182862) baseStart_7182862 baseEnd_7182862 := by
    simpa [prefixWord, tailWord_7182862, baseEnd_7182862] using wordTrace_append hprefix tailTrace_7182862
  have hstable : (prefixWord ++ tailWord_7182862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182862).length < 2 ^ (prefixWord ++ tailWord_7182862).sum := by decide
  have hdescent : baseEnd_7182862 < baseStart_7182862 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182865 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 3, 6, 2]
def baseStart_7182865 : Nat := 118140960795 + 7182865 * 2 ^ 59
def prefixEnd_7182865 : Nat := 4983230072969 + 3 ^ 40 * 7182865 * 2
def baseEnd_7182865 : Nat := 3688262221357144741354111

theorem tailTrace_7182865 : CollatzResearch.WordTrace tailWord_7182865 prefixEnd_7182865 3688262221357144741354111 := by
  unfold tailWord_7182865
  simp only [CollatzResearch.WordTrace]
  refine ⟨261980609122714315521694049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174653739415142877014462699 261980609122714315521694049)
  ·
    refine ⟨196485456842035736641270537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261980609122714315521694049 196485456842035736641270537)
    ·
      refine ⟨147364092631526802480952903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196485456842035736641270537 147364092631526802480952903)
      ·
        refine ⟨221046138947290203721429355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147364092631526802480952903 221046138947290203721429355)
        ·
          refine ⟨331569208420935305582144033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221046138947290203721429355 331569208420935305582144033)
          ·
            refine ⟨248676906315701479186608025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331569208420935305582144033 248676906315701479186608025)
            ·
              refine ⟨186507679736776109389956019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248676906315701479186608025 186507679736776109389956019)
              ·
                refine ⟨279761519605164164084934029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186507679736776109389956019 279761519605164164084934029)
                ·
                  refine ⟨104910569851936561531850261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279761519605164164084934029 104910569851936561531850261)
                  ·
                    refine ⟨4917682961809526321805481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 104910569851936561531850261 4917682961809526321805481)
                    ·
                      refine ⟨3688262221357144741354111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917682961809526321805481 3688262221357144741354111)
                      ·
                        rfl

theorem cell23_7182865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 6, 2].length) (baseStart_7182865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182865 prefixEnd_7182865 := by exact prefixLift 7182865
  have htrace : WordTrace (prefixWord ++ tailWord_7182865) baseStart_7182865 baseEnd_7182865 := by
    simpa [prefixWord, tailWord_7182865, baseEnd_7182865] using wordTrace_append hprefix tailTrace_7182865
  have hstable : (prefixWord ++ tailWord_7182865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182865).length < 2 ^ (prefixWord ++ tailWord_7182865).sum := by decide
  have hdescent : baseEnd_7182865 < baseStart_7182865 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182882 : List Nat := [3, 3, 1, 1, 1, 1, 1, 4, 2, 4, 2]
def baseStart_7182882 : Nat := 118140960795 + 7182882 * 2 ^ 59
def prefixEnd_7182882 : Nat := 4983230072969 + 3 ^ 40 * 7182882 * 2
def baseEnd_7182882 : Nat := 3688270950528271174841533

theorem tailTrace_7182882 : CollatzResearch.WordTrace tailWord_7182882 prefixEnd_7182882 3688270950528271174841533 := by
  unfold tailWord_7182882
  simp only [CollatzResearch.WordTrace]
  refine ⟨65495307290913181856265725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174654152775768484950041933 65495307290913181856265725)
  ·
    refine ⟨24560740234092443196099647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65495307290913181856265725 24560740234092443196099647)
    ·
      refine ⟨36841110351138664794149471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24560740234092443196099647 36841110351138664794149471)
      ·
        refine ⟨55261665526707997191224207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36841110351138664794149471 55261665526707997191224207)
        ·
          refine ⟨82892498290061995786836311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55261665526707997191224207 82892498290061995786836311)
          ·
            refine ⟨124338747435092993680254467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82892498290061995786836311 124338747435092993680254467)
            ·
              refine ⟨186508121152639490520381701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124338747435092993680254467 186508121152639490520381701)
              ·
                refine ⟨34970272716119904472571569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186508121152639490520381701 34970272716119904472571569)
                ·
                  refine ⟨26227704537089928354428677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34970272716119904472571569 26227704537089928354428677)
                  ·
                    refine ⟨4917694600704361566455377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26227704537089928354428677 4917694600704361566455377)
                    ·
                      refine ⟨3688270950528271174841533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917694600704361566455377 3688270950528271174841533)
                      ·
                        rfl

theorem cell23_7182882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 4, 2, 4, 2].length) (baseStart_7182882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182882 prefixEnd_7182882 := by exact prefixLift 7182882
  have htrace : WordTrace (prefixWord ++ tailWord_7182882) baseStart_7182882 baseEnd_7182882 := by
    simpa [prefixWord, tailWord_7182882, baseEnd_7182882] using wordTrace_append hprefix tailTrace_7182882
  have hstable : (prefixWord ++ tailWord_7182882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182882).length < 2 ^ (prefixWord ++ tailWord_7182882).sum := by decide
  have hdescent : baseEnd_7182882 < baseStart_7182882 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182905 : List Nat := [1, 2, 1, 5, 1, 1, 1, 5, 6]
def baseStart_7182905 : Nat := 118140960795 + 7182905 * 2 ^ 59
def prefixEnd_7182905 : Nat := 4983230072969 + 3 ^ 40 * 7182905 * 2
def baseEnd_7182905 : Nat := 409809195620369398317103

theorem tailTrace_7182905 : CollatzResearch.WordTrace tailWord_7182905 prefixEnd_7182905 409809195620369398317103 := by
  unfold tailWord_7182905
  simp only [CollatzResearch.WordTrace]
  refine ⟨261982068042569402353150169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174654712028379601568766779 261982068042569402353150169)
  ·
    refine ⟨196486551031927051764862627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261982068042569402353150169 196486551031927051764862627)
    ·
      refine ⟨294729826547890577647293941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196486551031927051764862627 294729826547890577647293941)
      ·
        refine ⟨27630921238864741654433807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294729826547890577647293941 27630921238864741654433807)
        ·
          refine ⟨41446381858297112481650711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27630921238864741654433807 41446381858297112481650711)
          ·
            refine ⟨62169572787445668722476067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41446381858297112481650711 62169572787445668722476067)
            ·
              refine ⟨93254359181168503083714101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62169572787445668722476067 93254359181168503083714101)
              ·
                refine ⟨8742596173234547164098197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93254359181168503083714101 8742596173234547164098197)
                ·
                  refine ⟨409809195620369398317103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8742596173234547164098197 409809195620369398317103)
                  ·
                    rfl

theorem cell23_7182905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 1, 5, 6].length) (baseStart_7182905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182905 prefixEnd_7182905 := by exact prefixLift 7182905
  have htrace : WordTrace (prefixWord ++ tailWord_7182905) baseStart_7182905 baseEnd_7182905 := by
    simpa [prefixWord, tailWord_7182905, baseEnd_7182905] using wordTrace_append hprefix tailTrace_7182905
  have hstable : (prefixWord ++ tailWord_7182905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182905).length < 2 ^ (prefixWord ++ tailWord_7182905).sum := by decide
  have hdescent : baseEnd_7182905 < baseStart_7182905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182916 : List Nat := [2, 3, 5, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_7182916 : Nat := 118140960795 + 7182916 * 2 ^ 59
def prefixEnd_7182916 : Nat := 4983230072969 + 3 ^ 40 * 7182916 * 2
def baseEnd_7182916 : Nat := 3688288408870524041816377

theorem tailTrace_7182916 : CollatzResearch.WordTrace tailWord_7182916 prefixEnd_7182916 3688288408870524041816377 := by
  unfold tailWord_7182916
  simp only [CollatzResearch.WordTrace]
  refine ⟨130991234622764775615900301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174654979497019700821200401 130991234622764775615900301)
  ·
    refine ⟨49121712983536790855962613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130991234622764775615900301 49121712983536790855962613)
    ·
      refine ⟨4605160592206574142746495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 49121712983536790855962613 4605160592206574142746495)
      ·
        refine ⟨6907740888309861214119743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4605160592206574142746495 6907740888309861214119743)
        ·
          refine ⟨10361611332464791821179615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6907740888309861214119743 10361611332464791821179615)
          ·
            refine ⟨15542416998697187731769423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10361611332464791821179615 15542416998697187731769423)
            ·
              refine ⟨23313625498045781597654135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15542416998697187731769423 23313625498045781597654135)
              ·
                refine ⟨34970438247068672396481203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23313625498045781597654135 34970438247068672396481203)
                ·
                  refine ⟨52455657370603008594721805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34970438247068672396481203 52455657370603008594721805)
                  ·
                    refine ⟨19670871513976128223020677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52455657370603008594721805 19670871513976128223020677)
                    ·
                      refine ⟨3688288408870524041816377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19670871513976128223020677 3688288408870524041816377)
                      ·
                        rfl

theorem cell23_7182916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_7182916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182916 prefixEnd_7182916 := by exact prefixLift 7182916
  have htrace : WordTrace (prefixWord ++ tailWord_7182916) baseStart_7182916 baseEnd_7182916 := by
    simpa [prefixWord, tailWord_7182916, baseEnd_7182916] using wordTrace_append hprefix tailTrace_7182916
  have hstable : (prefixWord ++ tailWord_7182916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182916).length < 2 ^ (prefixWord ++ tailWord_7182916).sum := by decide
  have hdescent : baseEnd_7182916 < baseStart_7182916 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182919 : List Nat := [1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 3]
def baseStart_7182919 : Nat := 118140960795 + 7182919 * 2 ^ 59
def prefixEnd_7182919 : Nat := 4983230072969 + 3 ^ 40 * 7182919 * 2
def baseEnd_7182919 : Nat := 3688289949312487530078863

theorem tailTrace_7182919 : CollatzResearch.WordTrace tailWord_7182919 prefixEnd_7182919 3688289949312487530078863 := by
  unfold tailWord_7182919
  simp only [CollatzResearch.WordTrace]
  refine ⟨261982578664518682744159811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174655052443012455162773207 261982578664518682744159811)
  ·
    refine ⟨392973867996778024116239717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261982578664518682744159811 392973867996778024116239717)
    ·
      refine ⟨73682600249395879521794947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392973867996778024116239717 73682600249395879521794947)
      ·
        refine ⟨110523900374093819282692421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73682600249395879521794947 110523900374093819282692421)
        ·
          refine ⟨20723231320142591115504829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110523900374093819282692421 20723231320142591115504829)
          ·
            refine ⟨7771211745053471668314311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20723231320142591115504829 7771211745053471668314311)
            ·
              refine ⟨11656817617580207502471467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7771211745053471668314311 11656817617580207502471467)
              ·
                refine ⟨17485226426370311253707201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11656817617580207502471467 17485226426370311253707201)
                ·
                  refine ⟨13113919819777733440280401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17485226426370311253707201 13113919819777733440280401)
                  ·
                    refine ⟨9835439864833300080210301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13113919819777733440280401 9835439864833300080210301)
                    ·
                      refine ⟨3688289949312487530078863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9835439864833300080210301 3688289949312487530078863)
                      ·
                        rfl

theorem cell23_7182919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_7182919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182919 prefixEnd_7182919 := by exact prefixLift 7182919
  have htrace : WordTrace (prefixWord ++ tailWord_7182919) baseStart_7182919 baseEnd_7182919 := by
    simpa [prefixWord, tailWord_7182919, baseEnd_7182919] using wordTrace_append hprefix tailTrace_7182919
  have hstable : (prefixWord ++ tailWord_7182919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182919).length < 2 ^ (prefixWord ++ tailWord_7182919).sum := by decide
  have hdescent : baseEnd_7182919 < baseStart_7182919 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182955 : List Nat := [1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 4]
def baseStart_7182955 : Nat := 118140960795 + 7182955 * 2 ^ 59
def prefixEnd_7182955 : Nat := 4983230072969 + 3 ^ 40 * 7182955 * 2
def baseEnd_7182955 : Nat := 3688308434616049389228697

theorem tailTrace_7182955 : CollatzResearch.WordTrace tailWord_7182955 prefixEnd_7182955 3688308434616049389228697 := by
  unfold tailWord_7182955
  simp only [CollatzResearch.WordTrace]
  refine ⟨261983891692388260892470319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174655927794925507261646879 261983891692388260892470319)
  ·
    refine ⟨392975837538582391338705479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261983891692388260892470319 392975837538582391338705479)
    ·
      refine ⟨589463756307873587008058219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392975837538582391338705479 589463756307873587008058219)
      ·
        refine ⟨884195634461810380512087329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589463756307873587008058219 884195634461810380512087329)
        ·
          refine ⟨663146725846357785384065497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884195634461810380512087329 663146725846357785384065497)
          ·
            refine ⟨497360044384768339038049123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663146725846357785384065497 497360044384768339038049123)
            ·
              refine ⟨746040066577152508557073685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497360044384768339038049123 746040066577152508557073685)
              ·
                refine ⟨34970628120804023838612829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 746040066577152508557073685 34970628120804023838612829)
                ·
                  refine ⟨13113985545301508939479811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34970628120804023838612829 13113985545301508939479811)
                  ·
                    refine ⟨19670978317952263409219717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13113985545301508939479811 19670978317952263409219717)
                    ·
                      refine ⟨3688308434616049389228697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19670978317952263409219717 3688308434616049389228697)
                      ·
                        rfl

theorem cell23_7182955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 6, 3, 1, 4].length) (baseStart_7182955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182955 prefixEnd_7182955 := by exact prefixLift 7182955
  have htrace : WordTrace (prefixWord ++ tailWord_7182955) baseStart_7182955 baseEnd_7182955 := by
    simpa [prefixWord, tailWord_7182955, baseEnd_7182955] using wordTrace_append hprefix tailTrace_7182955
  have hstable : (prefixWord ++ tailWord_7182955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182955).length < 2 ^ (prefixWord ++ tailWord_7182955).sum := by decide
  have hdescent : baseEnd_7182955 < baseStart_7182955 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182972 : List Nat := [2, 2, 2, 1, 1, 2, 3, 4, 1, 1, 4]
def baseStart_7182972 : Nat := 118140960795 + 7182972 * 2 ^ 59
def prefixEnd_7182972 : Nat := 4983230072969 + 3 ^ 40 * 7182972 * 2
def baseEnd_7182972 : Nat := 3688317163787175822716119

theorem tailTrace_7182972 : CollatzResearch.WordTrace tailWord_7182972 prefixEnd_7182972 3688317163787175822716119 := by
  unfold tailWord_7182972
  simp only [CollatzResearch.WordTrace]
  refine ⟨130992255866663336397919585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174656341155551115197226113 130992255866663336397919585)
  ·
    refine ⟨98244191899997502298439689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130992255866663336397919585 98244191899997502298439689)
    ·
      refine ⟨73683143924998126723829767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98244191899997502298439689 73683143924998126723829767)
      ·
        refine ⟨110524715887497190085744651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73683143924998126723829767 110524715887497190085744651)
        ·
          refine ⟨165787073831245785128616977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110524715887497190085744651 165787073831245785128616977)
          ·
            refine ⟨124340305373434338846462733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165787073831245785128616977 124340305373434338846462733)
            ·
              refine ⟨46627614515037877067423525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124340305373434338846462733 46627614515037877067423525)
              ·
                refine ⟨8742677721569601950141911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46627614515037877067423525 8742677721569601950141911)
                ·
                  refine ⟨13114016582354402925212867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8742677721569601950141911 13114016582354402925212867)
                  ·
                    refine ⟨19671024873531604387819301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13114016582354402925212867 19671024873531604387819301)
                    ·
                      refine ⟨3688317163787175822716119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19671024873531604387819301 3688317163787175822716119)
                      ·
                        rfl

theorem cell23_7182972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 1, 4].length) (baseStart_7182972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182972 prefixEnd_7182972 := by exact prefixLift 7182972
  have htrace : WordTrace (prefixWord ++ tailWord_7182972) baseStart_7182972 baseEnd_7182972 := by
    simpa [prefixWord, tailWord_7182972, baseEnd_7182972] using wordTrace_append hprefix tailTrace_7182972
  have hstable : (prefixWord ++ tailWord_7182972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182972).length < 2 ^ (prefixWord ++ tailWord_7182972).sum := by decide
  have hdescent : baseEnd_7182972 < baseStart_7182972 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7182985 : List Nat := [1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_7182985 : Nat := 118140960795 + 7182985 * 2 ^ 59
def prefixEnd_7182985 : Nat := 4983230072969 + 3 ^ 40 * 7182985 * 2
def baseEnd_7182985 : Nat := 3688323839035684271853559

theorem tailTrace_7182985 : CollatzResearch.WordTrace tailWord_7182985 prefixEnd_7182985 3688323839035684271853559 := by
  unfold tailWord_7182985
  simp only [CollatzResearch.WordTrace]
  refine ⟨261984985882279576016062409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174656657254853050677374939 261984985882279576016062409)
  ·
    refine ⟨196488739411709682012046807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 261984985882279576016062409 196488739411709682012046807)
    ·
      refine ⟨294733109117564523018070211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196488739411709682012046807 294733109117564523018070211)
      ·
        refine ⟨442099663676346784527105317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294733109117564523018070211 442099663676346784527105317)
        ·
          refine ⟨82893686939315022098832247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442099663676346784527105317 82893686939315022098832247)
          ·
            refine ⟨124340530408972533148248371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82893686939315022098832247 124340530408972533148248371)
            ·
              refine ⟨186510795613458799722372557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124340530408972533148248371 186510795613458799722372557)
              ·
                refine ⟨69941548355047049895889709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186510795613458799722372557 69941548355047049895889709)
                ·
                  refine ⟨26228080633142643710958641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69941548355047049895889709 26228080633142643710958641)
                  ·
                    refine ⟨19671060474856982783218981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26228080633142643710958641 19671060474856982783218981)
                    ·
                      refine ⟨3688323839035684271853559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19671060474856982783218981 3688323839035684271853559)
                      ·
                        rfl

theorem cell23_7182985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_7182985 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7182985 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7182985 prefixEnd_7182985 := by exact prefixLift 7182985
  have htrace : WordTrace (prefixWord ++ tailWord_7182985) baseStart_7182985 baseEnd_7182985 := by
    simpa [prefixWord, tailWord_7182985, baseEnd_7182985] using wordTrace_append hprefix tailTrace_7182985
  have hstable : (prefixWord ++ tailWord_7182985).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7182985).length < 2 ^ (prefixWord ++ tailWord_7182985).sum := by decide
  have hdescent : baseEnd_7182985 < baseStart_7182985 := by decide
  rcases family_descends (prefixWord ++ tailWord_7182985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183045 : List Nat := [1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_7183045 : Nat := 118140960795 + 7183045 * 2 ^ 59
def prefixEnd_7183045 : Nat := 4983230072969 + 3 ^ 40 * 7183045 * 2
def baseEnd_7183045 : Nat := 3688354647874954037103283

theorem tailTrace_7183045 : CollatzResearch.WordTrace tailWord_7183045 prefixEnd_7183045 3688354647874954037103283 := by
  unfold tailWord_7183045
  simp only [CollatzResearch.WordTrace]
  refine ⟨261987174262062206263246589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174658116174708137508831059 261987174262062206263246589)
  ·
    refine ⟨98245190348273327348717471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261987174262062206263246589 98245190348273327348717471)
    ·
      refine ⟨147367785522409991023076207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98245190348273327348717471 147367785522409991023076207)
      ·
        refine ⟨221051678283614986534614311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147367785522409991023076207 221051678283614986534614311)
        ·
          refine ⟨331577517425422479801921467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221051678283614986534614311 331577517425422479801921467)
          ·
            refine ⟨497366276138133719702882201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331577517425422479801921467 497366276138133719702882201)
            ·
              refine ⟨373024707103600289777161651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497366276138133719702882201 373024707103600289777161651)
              ·
                refine ⟨559537060655400434665742477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373024707103600289777161651 559537060655400434665742477)
                ·
                  refine ⟨209826397745775162999653429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559537060655400434665742477 209826397745775162999653429)
                  ·
                    refine ⟨19671224788666421531217509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209826397745775162999653429 19671224788666421531217509)
                    ·
                      refine ⟨3688354647874954037103283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19671224788666421531217509 3688354647874954037103283)
                      ·
                        rfl

theorem cell23_7183045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_7183045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183045 prefixEnd_7183045 := by exact prefixLift 7183045
  have htrace : WordTrace (prefixWord ++ tailWord_7183045) baseStart_7183045 baseEnd_7183045 := by
    simpa [prefixWord, tailWord_7183045, baseEnd_7183045] using wordTrace_append hprefix tailTrace_7183045
  have hstable : (prefixWord ++ tailWord_7183045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183045).length < 2 ^ (prefixWord ++ tailWord_7183045).sum := by decide
  have hdescent : baseEnd_7183045 < baseStart_7183045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183046 : List Nat := [6, 1, 2, 1, 3, 10]
def baseStart_7183046 : Nat := 118140960795 + 7183046 * 2 ^ 59
def prefixEnd_7183046 : Nat := 4983230072969 + 3 ^ 40 * 7183046 * 2
def baseEnd_7183046 : Nat := 15178416301874932235353

theorem tailTrace_7183046 : CollatzResearch.WordTrace tailWord_7183046 prefixEnd_7183046 15178416301874932235353 := by
  unfold tailWord_7183046
  simp only [CollatzResearch.WordTrace]
  refine ⟨8187100335470580732313531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 174658140490039055622688661 8187100335470580732313531)
  ·
    refine ⟨12280650503205871098470297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 8187100335470580732313531 12280650503205871098470297)
    ·
      refine ⟨9210487877404403323852723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 12280650503205871098470297 9210487877404403323852723)
      ·
        refine ⟨13815731816106604985779085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9210487877404403323852723 13815731816106604985779085)
        ·
          refine ⟨5180899431039976869667157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13815731816106604985779085 5180899431039976869667157)
          ·
            refine ⟨15178416301874932235353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 5180899431039976869667157 15178416301874932235353)
            ·
              rfl

theorem cell23_7183046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 10].length) (baseStart_7183046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183046 prefixEnd_7183046 := by exact prefixLift 7183046
  have htrace : WordTrace (prefixWord ++ tailWord_7183046) baseStart_7183046 baseEnd_7183046 := by
    simpa [prefixWord, tailWord_7183046, baseEnd_7183046] using wordTrace_append hprefix tailTrace_7183046
  have hstable : (prefixWord ++ tailWord_7183046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183046).length < 2 ^ (prefixWord ++ tailWord_7183046).sum := by decide
  have hdescent : baseEnd_7183046 < baseStart_7183046 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183082 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3]
def baseStart_7183082 : Nat := 118140960795 + 7183082 * 2 ^ 59
def prefixEnd_7183082 : Nat := 4983230072969 + 3 ^ 40 * 7183082 * 2
def baseEnd_7183082 : Nat := 3688373646659170392340613

theorem tailTrace_7183082 : CollatzResearch.WordTrace tailWord_7183082 prefixEnd_7183082 3688373646659170392340613 := by
  unfold tailWord_7183082
  simp only [CollatzResearch.WordTrace]
  refine ⟨65497130940732040395585875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174659015841952107721562333 65497130940732040395585875)
  ·
    refine ⟨98245696411098060593378813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65497130940732040395585875 98245696411098060593378813)
    ·
      refine ⟨36842136154161772722517055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98245696411098060593378813 36842136154161772722517055)
      ·
        refine ⟨55263204231242659083775583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36842136154161772722517055 55263204231242659083775583)
        ·
          refine ⟨82894806346863988625663375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55263204231242659083775583 82894806346863988625663375)
          ·
            refine ⟨124342209520295982938495063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82894806346863988625663375 124342209520295982938495063)
            ·
              refine ⟨186513314280443974407742595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124342209520295982938495063 186513314280443974407742595)
              ·
                refine ⟨279769971420665961611613893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186513314280443974407742595 279769971420665961611613893)
                ·
                  refine ⟨52456869641374867802177605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279769971420665961611613893 52456869641374867802177605)
                  ·
                    refine ⟨9835663057757787712908301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52456869641374867802177605 9835663057757787712908301)
                    ·
                      refine ⟨3688373646659170392340613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9835663057757787712908301 3688373646659170392340613)
                      ·
                        rfl

theorem cell23_7183082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 4, 4, 3].length) (baseStart_7183082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183082 prefixEnd_7183082 := by exact prefixLift 7183082
  have htrace : WordTrace (prefixWord ++ tailWord_7183082) baseStart_7183082 baseEnd_7183082 := by
    simpa [prefixWord, tailWord_7183082, baseEnd_7183082] using wordTrace_append hprefix tailTrace_7183082
  have hstable : (prefixWord ++ tailWord_7183082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183082).length < 2 ^ (prefixWord ++ tailWord_7183082).sum := by decide
  have hdescent : baseEnd_7183082 < baseStart_7183082 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183095 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 7]
def baseStart_7183095 : Nat := 118140960795 + 7183095 * 2 ^ 59
def prefixEnd_7183095 : Nat := 4983230072969 + 3 ^ 40 * 7183095 * 2
def baseEnd_7183095 : Nat := 3688380321907678841478053

theorem tailTrace_7183095 : CollatzResearch.WordTrace tailWord_7183095 prefixEnd_7183095 3688380321907678841478053 := by
  unfold tailWord_7183095
  simp only [CollatzResearch.WordTrace]
  refine ⟨261988997911881064802566739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174659331941254043201711159 261988997911881064802566739)
  ·
    refine ⟨392983496867821597203850109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261988997911881064802566739 392983496867821597203850109)
    ·
      refine ⟨147368811325433098951443791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392983496867821597203850109 147368811325433098951443791)
      ·
        refine ⟨221053216988149648427165687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147368811325433098951443791 221053216988149648427165687)
        ·
          refine ⟨331579825482224472640748531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221053216988149648427165687 331579825482224472640748531)
          ·
            refine ⟨497369738223336708961122797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331579825482224472640748531 497369738223336708961122797)
            ·
              refine ⟨186513651833751265860421049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497369738223336708961122797 186513651833751265860421049)
              ·
                refine ⟨139885238875313449395315787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186513651833751265860421049 139885238875313449395315787)
                ·
                  refine ⟨209827858312970174092973681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139885238875313449395315787 209827858312970174092973681)
                  ·
                    refine ⟨157370893734727630569730261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209827858312970174092973681 157370893734727630569730261)
                    ·
                      refine ⟨3688380321907678841478053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157370893734727630569730261 3688380321907678841478053)
                      ·
                        rfl

theorem cell23_7183095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 1, 2, 7].length) (baseStart_7183095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183095 prefixEnd_7183095 := by exact prefixLift 7183095
  have htrace : WordTrace (prefixWord ++ tailWord_7183095) baseStart_7183095 baseEnd_7183095 := by
    simpa [prefixWord, tailWord_7183095, baseEnd_7183095] using wordTrace_append hprefix tailTrace_7183095
  have hstable : (prefixWord ++ tailWord_7183095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183095).length < 2 ^ (prefixWord ++ tailWord_7183095).sum := by decide
  have hdescent : baseEnd_7183095 < baseStart_7183095 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183132 : List Nat := [2, 2, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_7183132 : Nat := 118140960795 + 7183132 * 2 ^ 59
def prefixEnd_7183132 : Nat := 4983230072969 + 3 ^ 40 * 7183132 * 2
def baseEnd_7183132 : Nat := 1229466440230631732238461

theorem tailTrace_7183132 : CollatzResearch.WordTrace tailWord_7183132 prefixEnd_7183132 1229466440230631732238461 := by
  unfold tailWord_7183132
  simp only [CollatzResearch.WordTrace]
  refine ⟨130995173706373510060831825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174660231608498013414442433 130995173706373510060831825)
  ·
    refine ⟨98246380279780132545623869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 130995173706373510060831825 98246380279780132545623869)
    ·
      refine ⟨36842392604917549704608951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98246380279780132545623869 36842392604917549704608951)
      ·
        refine ⟨55263588907376324556913427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36842392604917549704608951 55263588907376324556913427)
        ·
          refine ⟨82895383361064486835370141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55263588907376324556913427 82895383361064486835370141)
          ·
            refine ⟨31085768760399182563263803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82895383361064486835370141 31085768760399182563263803)
            ·
              refine ⟨46628653140598773844895705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31085768760399182563263803 46628653140598773844895705)
              ·
                refine ⟨34971489855449080383671779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46628653140598773844895705 34971489855449080383671779)
                ·
                  refine ⟨52457234783173620575507669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34971489855449080383671779 52457234783173620575507669)
                  ·
                    refine ⟨1229466440230631732238461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52457234783173620575507669 1229466440230631732238461)
                    ·
                      rfl

theorem cell23_7183132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_7183132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183132 prefixEnd_7183132 := by exact prefixLift 7183132
  have htrace : WordTrace (prefixWord ++ tailWord_7183132) baseStart_7183132 baseEnd_7183132 := by
    simpa [prefixWord, tailWord_7183132, baseEnd_7183132] using wordTrace_append hprefix tailTrace_7183132
  have hstable : (prefixWord ++ tailWord_7183132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183132).length < 2 ^ (prefixWord ++ tailWord_7183132).sum := by decide
  have hdescent : baseEnd_7183132 < baseStart_7183132 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183152 : List Nat := [2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4]
def baseStart_7183152 : Nat := 118140960795 + 7183152 * 2 ^ 59
def prefixEnd_7183152 : Nat := 4983230072969 + 3 ^ 40 * 7183152 * 2
def baseEnd_7183152 : Nat := 3688409590304985118465291

theorem tailTrace_7183152 : CollatzResearch.WordTrace tailWord_7183152 prefixEnd_7183152 3688409590304985118465291 := by
  unfold tailWord_7183152
  simp only [CollatzResearch.WordTrace]
  refine ⟨130995538436337281768695855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174660717915116375691594473 130995538436337281768695855)
  ·
    refine ⟨196493307654505922653043783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 130995538436337281768695855 196493307654505922653043783)
    ·
      refine ⟨294739961481758883979565675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196493307654505922653043783 294739961481758883979565675)
      ·
        refine ⟨442109942222638325969348513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294739961481758883979565675 442109942222638325969348513)
        ·
          refine ⟨331582456666978744477011385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442109942222638325969348513 331582456666978744477011385)
          ·
            refine ⟨248686842500234058357758539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331582456666978744477011385 248686842500234058357758539)
            ·
              refine ⟨373030263750351087536637809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248686842500234058357758539 373030263750351087536637809)
              ·
                refine ⟨279772697812763315652478357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373030263750351087536637809 279772697812763315652478357)
                ·
                  refine ⟨13114345209973280421209923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 279772697812763315652478357 13114345209973280421209923)
                  ·
                    refine ⟨19671517814959920631814885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13114345209973280421209923 19671517814959920631814885)
                    ·
                      refine ⟨3688409590304985118465291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19671517814959920631814885 3688409590304985118465291)
                      ·
                        rfl

theorem cell23_7183152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 1, 4].length) (baseStart_7183152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183152 prefixEnd_7183152 := by exact prefixLift 7183152
  have htrace : WordTrace (prefixWord ++ tailWord_7183152) baseStart_7183152 baseEnd_7183152 := by
    simpa [prefixWord, tailWord_7183152, baseEnd_7183152] using wordTrace_append hprefix tailTrace_7183152
  have hstable : (prefixWord ++ tailWord_7183152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183152).length < 2 ^ (prefixWord ++ tailWord_7183152).sum := by decide
  have hdescent : baseEnd_7183152 < baseStart_7183152 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183166 : List Nat := [4, 2, 1, 2, 3, 1, 1, 2, 2, 5]
def baseStart_7183166 : Nat := 118140960795 + 7183166 * 2 ^ 59
def prefixEnd_7183166 : Nat := 4983230072969 + 3 ^ 40 * 7183166 * 2
def baseEnd_7183166 : Nat := 1229472259678049354563409

theorem tailTrace_7183166 : CollatzResearch.WordTrace tailWord_7183166 prefixEnd_7183166 1229472259678049354563409 := by
  unfold tailWord_7183166
  simp only [CollatzResearch.WordTrace]
  refine ⟨32748948436827980491050169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174661058329749229285600901 32748948436827980491050169)
  ·
    refine ⟨24561711327620985368287627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32748948436827980491050169 24561711327620985368287627)
    ·
      refine ⟨36842566991431478052431441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24561711327620985368287627 36842566991431478052431441)
      ·
        refine ⟨27631925243573608539323581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36842566991431478052431441 27631925243573608539323581)
        ·
          refine ⟨10361971966340103202246343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27631925243573608539323581 10361971966340103202246343)
          ·
            refine ⟨15542957949510154803369515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10361971966340103202246343 15542957949510154803369515)
            ·
              refine ⟨23314436924265232205054273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15542957949510154803369515 23314436924265232205054273)
              ·
                refine ⟨17485827693198924153790705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23314436924265232205054273 17485827693198924153790705)
                ·
                  refine ⟨13114370769899193115343029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17485827693198924153790705 13114370769899193115343029)
                  ·
                    refine ⟨1229472259678049354563409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13114370769899193115343029 1229472259678049354563409)
                    ·
                      rfl

theorem cell23_7183166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_7183166 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183166 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183166 prefixEnd_7183166 := by exact prefixLift 7183166
  have htrace : WordTrace (prefixWord ++ tailWord_7183166) baseStart_7183166 baseEnd_7183166 := by
    simpa [prefixWord, tailWord_7183166, baseEnd_7183166] using wordTrace_append hprefix tailTrace_7183166
  have hstable : (prefixWord ++ tailWord_7183166).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183166).length < 2 ^ (prefixWord ++ tailWord_7183166).sum := by decide
  have hdescent : baseEnd_7183166 < baseStart_7183166 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183182 : List Nat := [4, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6]
def baseStart_7183182 : Nat := 118140960795 + 7183182 * 2 ^ 59
def prefixEnd_7183182 : Nat := 4983230072969 + 3 ^ 40 * 7183182 * 2
def baseEnd_7183182 : Nat := 3688424994724620001090153

theorem tailTrace_7183182 : CollatzResearch.WordTrace tailWord_7183182 prefixEnd_7183182 3688424994724620001090153 := by
  unfold tailWord_7183182
  simp only [CollatzResearch.WordTrace]
  refine ⟨32749021382820734832622975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174661447375043919107322533 32749021382820734832622975)
  ·
    refine ⟨49123532074231102248934463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32749021382820734832622975 49123532074231102248934463)
    ·
      refine ⟨73685298111346653373401695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49123532074231102248934463 73685298111346653373401695)
      ·
        refine ⟨110527947167019980060102543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73685298111346653373401695 110527947167019980060102543)
        ·
          refine ⟨165791920750529970090153815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110527947167019980060102543 165791920750529970090153815)
          ·
            refine ⟨248687881125794955135230723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165791920750529970090153815 248687881125794955135230723)
            ·
              refine ⟨373031821688692432702846085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248687881125794955135230723 373031821688692432702846085)
              ·
                refine ⟨69943466566629831131783641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 373031821688692432702846085 69943466566629831131783641)
                ·
                  refine ⟨52457599924972373348837731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69943466566629831131783641 52457599924972373348837731)
                  ·
                    refine ⟨78686399887458560023256597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52457599924972373348837731 78686399887458560023256597)
                    ·
                      refine ⟨3688424994724620001090153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78686399887458560023256597 3688424994724620001090153)
                      ·
                        rfl

theorem cell23_7183182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6].length) (baseStart_7183182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183182 prefixEnd_7183182 := by exact prefixLift 7183182
  have htrace : WordTrace (prefixWord ++ tailWord_7183182) baseStart_7183182 baseEnd_7183182 := by
    simpa [prefixWord, tailWord_7183182, baseEnd_7183182] using wordTrace_append hprefix tailTrace_7183182
  have hstable : (prefixWord ++ tailWord_7183182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183182).length < 2 ^ (prefixWord ++ tailWord_7183182).sum := by decide
  have hdescent : baseEnd_7183182 < baseStart_7183182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183189 : List Nat := [1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_7183189 : Nat := 118140960795 + 7183189 * 2 ^ 59
def prefixEnd_7183189 : Nat := 4983230072969 + 3 ^ 40 * 7183189 * 2
def baseEnd_7183189 : Nat := 3688428589089201473702621

theorem tailTrace_7183189 : CollatzResearch.WordTrace tailWord_7183189 prefixEnd_7183189 3688428589089201473702621 := by
  unfold tailWord_7183189
  simp only [CollatzResearch.WordTrace]
  refine ⟨261992426373540518856488621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174661617582360345904325747 261992426373540518856488621)
  ·
    refine ⟨98247159890077694571183233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261992426373540518856488621 98247159890077694571183233)
    ·
      refine ⟨73685369917558270928387425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98247159890077694571183233 73685369917558270928387425)
      ·
        refine ⟨55264027438168703196290569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73685369917558270928387425 55264027438168703196290569)
        ·
          refine ⟨41448020578626527397217927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55264027438168703196290569 41448020578626527397217927)
          ·
            refine ⟨62172030867939791095826891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41448020578626527397217927 62172030867939791095826891)
            ·
              refine ⟨93258046301909686643740337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62172030867939791095826891 93258046301909686643740337)
              ·
                refine ⟨69943534726432264982805253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93258046301909686643740337 69943534726432264982805253)
                ·
                  refine ⟨13114412761206049684275985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69943534726432264982805253 13114412761206049684275985)
                  ·
                    refine ⟨9835809570904537263206989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13114412761206049684275985 9835809570904537263206989)
                    ·
                      refine ⟨3688428589089201473702621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9835809570904537263206989 3688428589089201473702621)
                      ·
                        rfl

theorem cell23_7183189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_7183189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183189 prefixEnd_7183189 := by exact prefixLift 7183189
  have htrace : WordTrace (prefixWord ++ tailWord_7183189) baseStart_7183189 baseEnd_7183189 := by
    simpa [prefixWord, tailWord_7183189, baseEnd_7183189] using wordTrace_append hprefix tailTrace_7183189
  have hstable : (prefixWord ++ tailWord_7183189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183189).length < 2 ^ (prefixWord ++ tailWord_7183189).sum := by decide
  have hdescent : baseEnd_7183189 < baseStart_7183189 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183236 : List Nat := [2, 3, 2, 1, 1, 1, 1, 5, 3, 1, 3]
def baseStart_7183236 : Nat := 118140960795 + 7183236 * 2 ^ 59
def prefixEnd_7183236 : Nat := 4983230072969 + 3 ^ 40 * 7183236 * 2
def baseEnd_7183236 : Nat := 3688452722679962789814905

theorem tailTrace_7183236 : CollatzResearch.WordTrace tailWord_7183236 prefixEnd_7183236 3688452722679962789814905 := by
  unfold tailWord_7183236
  simp only [CollatzResearch.WordTrace]
  refine ⟨130997070302185122941724781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174662760402913497255633041 130997070302185122941724781)
  ·
    refine ⟨49123901363319421103146793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 130997070302185122941724781 49123901363319421103146793)
    ·
      refine ⟨36842926022489565827360095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49123901363319421103146793 36842926022489565827360095)
      ·
        refine ⟨55264389033734348741040143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36842926022489565827360095 55264389033734348741040143)
        ·
          refine ⟨82896583550601523111560215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55264389033734348741040143 82896583550601523111560215)
          ·
            refine ⟨124344875325902284667340323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82896583550601523111560215 124344875325902284667340323)
            ·
              refine ⟨186517312988853427001010485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124344875325902284667340323 186517312988853427001010485)
              ·
                refine ⟨17485998092705008781344733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 186517312988853427001010485 17485998092705008781344733)
                ·
                  refine ⟨6557249284764378293004275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17485998092705008781344733 6557249284764378293004275)
                  ·
                    refine ⟨9835873927146567439506413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6557249284764378293004275 9835873927146567439506413)
                    ·
                      refine ⟨3688452722679962789814905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9835873927146567439506413 3688452722679962789814905)
                      ·
                        rfl

theorem cell23_7183236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_7183236 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183236 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183236 prefixEnd_7183236 := by exact prefixLift 7183236
  have htrace : WordTrace (prefixWord ++ tailWord_7183236) baseStart_7183236 baseEnd_7183236 := by
    simpa [prefixWord, tailWord_7183236, baseEnd_7183236] using wordTrace_append hprefix tailTrace_7183236
  have hstable : (prefixWord ++ tailWord_7183236).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183236).length < 2 ^ (prefixWord ++ tailWord_7183236).sum := by decide
  have hdescent : baseEnd_7183236 < baseStart_7183236 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183239 : List Nat := [1, 1, 4, 2, 3, 1, 1, 2, 3, 5]
def baseStart_7183239 : Nat := 118140960795 + 7183239 * 2 ^ 59
def prefixEnd_7183239 : Nat := 4983230072969 + 3 ^ 40 * 7183239 * 2
def baseEnd_7183239 : Nat := 1229484754373975426025797

theorem tailTrace_7183239 : CollatzResearch.WordTrace tailWord_7183239 prefixEnd_7183239 1229484754373975426025797 := by
  unfold tailWord_7183239
  simp only [CollatzResearch.WordTrace]
  refine ⟨261994250023359377395808771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174662833348906251597205847 261994250023359377395808771)
  ·
    refine ⟨392991375035039066093713157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261994250023359377395808771 392991375035039066093713157)
    ·
      refine ⟨73685882819069824892571217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 392991375035039066093713157 73685882819069824892571217)
      ·
        refine ⟨55264412114302368669428413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73685882819069824892571217 55264412114302368669428413)
        ·
          refine ⟨20724154542863388251035655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55264412114302368669428413 20724154542863388251035655)
          ·
            refine ⟨31086231814295082376553483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20724154542863388251035655 31086231814295082376553483)
            ·
              refine ⟨46629347721442623564830225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31086231814295082376553483 46629347721442623564830225)
              ·
                refine ⟨34972010791081967673622669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46629347721442623564830225 34972010791081967673622669)
                ·
                  refine ⟨13114504046655737877608501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34972010791081967673622669 13114504046655737877608501)
                  ·
                    refine ⟨1229484754373975426025797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13114504046655737877608501 1229484754373975426025797)
                    ·
                      rfl

theorem cell23_7183239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 2, 3, 5].length) (baseStart_7183239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183239 prefixEnd_7183239 := by exact prefixLift 7183239
  have htrace : WordTrace (prefixWord ++ tailWord_7183239) baseStart_7183239 baseEnd_7183239 := by
    simpa [prefixWord, tailWord_7183239, baseEnd_7183239] using wordTrace_append hprefix tailTrace_7183239
  have hstable : (prefixWord ++ tailWord_7183239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183239).length < 2 ^ (prefixWord ++ tailWord_7183239).sum := by decide
  have hdescent : baseEnd_7183239 < baseStart_7183239 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183263 : List Nat := [1, 1, 2, 5, 2, 1, 3, 1, 2, 3, 2]
def baseStart_7183263 : Nat := 118140960795 + 7183263 * 2 ^ 59
def prefixEnd_7183263 : Nat := 4983230072969 + 3 ^ 40 * 7183263 * 2
def baseEnd_7183263 : Nat := 3688466586657634184177281

theorem tailTrace_7183263 : CollatzResearch.WordTrace tailWord_7183263 prefixEnd_7183263 3688466586657634184177281 := by
  unfold tailWord_7183263
  simp only [CollatzResearch.WordTrace]
  refine ⟨261995125375272429494682443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174663416916848286329788295 261995125375272429494682443)
  ·
    refine ⟨392992688062908644242023665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261995125375272429494682443 392992688062908644242023665)
    ·
      refine ⟨294744516047181483181517749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392992688062908644242023665 294744516047181483181517749)
      ·
        refine ⟨27632298379423264048267289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294744516047181483181517749 27632298379423264048267289)
        ·
          refine ⟨20724223784567448036200467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27632298379423264048267289 20724223784567448036200467)
          ·
            refine ⟨31086335676851172054300701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20724223784567448036200467 31086335676851172054300701)
            ·
              refine ⟨11657375878819189520362763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31086335676851172054300701 11657375878819189520362763)
              ·
                refine ⟨17486063818228784280544145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11657375878819189520362763 17486063818228784280544145)
                ·
                  refine ⟨13114547863671588210408109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17486063818228784280544145 13114547863671588210408109)
                  ·
                    refine ⟨4917955448876845578903041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13114547863671588210408109 4917955448876845578903041)
                    ·
                      refine ⟨3688466586657634184177281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4917955448876845578903041 3688466586657634184177281)
                      ·
                        rfl

theorem cell23_7183263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 3, 1, 2, 3, 2].length) (baseStart_7183263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183263 prefixEnd_7183263 := by exact prefixLift 7183263
  have htrace : WordTrace (prefixWord ++ tailWord_7183263) baseStart_7183263 baseEnd_7183263 := by
    simpa [prefixWord, tailWord_7183263, baseEnd_7183263] using wordTrace_append hprefix tailTrace_7183263
  have hstable : (prefixWord ++ tailWord_7183263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183263).length < 2 ^ (prefixWord ++ tailWord_7183263).sum := by decide
  have hdescent : baseEnd_7183263 < baseStart_7183263 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183279 : List Nat := [1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 3]
def baseStart_7183279 : Nat := 118140960795 + 7183279 * 2 ^ 59
def prefixEnd_7183279 : Nat := 4983230072969 + 3 ^ 40 * 7183279 * 2
def baseEnd_7183279 : Nat := 3688474802348106121577207

theorem tailTrace_7183279 : CollatzResearch.WordTrace tailWord_7183279 prefixEnd_7183279 3688474802348106121577207 := by
  unfold tailWord_7183279
  simp only [CollatzResearch.WordTrace]
  refine ⟨261995708943214464227264891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174663805962142976151509927 261995708943214464227264891)
  ·
    refine ⟨392993563414821696340897337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261995708943214464227264891 392993563414821696340897337)
    ·
      refine ⟨294745172561116272255673003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 392993563414821696340897337 294745172561116272255673003)
      ·
        refine ⟨442117758841674408383509505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294745172561116272255673003 442117758841674408383509505)
        ·
          refine ⟨331588319131255806287632129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442117758841674408383509505 331588319131255806287632129)
          ·
            refine ⟨248691239348441854715724097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331588319131255806287632129 248691239348441854715724097)
            ·
              refine ⟨186518429511331391036793073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248691239348441854715724097 186518429511331391036793073)
              ·
                refine ⟨139888822133498543277594805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186518429511331391036793073 139888822133498543277594805)
                ·
                  refine ⟨13114577075015488432274513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139888822133498543277594805 13114577075015488432274513)
                  ·
                    refine ⟨9835932806261616324205885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13114577075015488432274513 9835932806261616324205885)
                    ·
                      refine ⟨3688474802348106121577207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9835932806261616324205885 3688474802348106121577207)
                      ·
                        rfl

theorem cell23_7183279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 5, 2, 3].length) (baseStart_7183279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183279 prefixEnd_7183279 := by exact prefixLift 7183279
  have htrace : WordTrace (prefixWord ++ tailWord_7183279) baseStart_7183279 baseEnd_7183279 := by
    simpa [prefixWord, tailWord_7183279, baseEnd_7183279] using wordTrace_append hprefix tailTrace_7183279
  have hstable : (prefixWord ++ tailWord_7183279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183279).length < 2 ^ (prefixWord ++ tailWord_7183279).sum := by decide
  have hdescent : baseEnd_7183279 < baseStart_7183279 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183316 : List Nat := [2, 4, 1, 2, 1, 2, 4, 7]
def baseStart_7183316 : Nat := 118140960795 + 7183316 * 2 ^ 59
def prefixEnd_7183316 : Nat := 4983230072969 + 3 ^ 40 * 7183316 * 2
def baseEnd_7183316 : Nat := 136610881523419350993131

theorem tailTrace_7183316 : CollatzResearch.WordTrace tailWord_7183316 prefixEnd_7183316 136610881523419350993131 := by
  unfold tailWord_7183316
  simp only [CollatzResearch.WordTrace]
  refine ⟨130998529222040209773180901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174664705629386946364241201 130998529222040209773180901)
  ·
    refine ⟨24562224229132539332471419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 130998529222040209773180901 24562224229132539332471419)
    ·
      refine ⟨36843336343698808998707129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24562224229132539332471419 36843336343698808998707129)
      ·
        refine ⟨27632502257774106749030347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36843336343698808998707129 27632502257774106749030347)
        ·
          refine ⟨41448753386661160123545521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27632502257774106749030347 41448753386661160123545521)
          ·
            refine ⟨31086565039995870092659141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41448753386661160123545521 31086565039995870092659141)
            ·
              refine ⟨5828730944999225642373589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31086565039995870092659141 5828730944999225642373589)
              ·
                refine ⟨136610881523419350993131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5828730944999225642373589 136610881523419350993131)
                ·
                  rfl

theorem cell23_7183316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 4, 7].length) (baseStart_7183316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183316 prefixEnd_7183316 := by exact prefixLift 7183316
  have htrace : WordTrace (prefixWord ++ tailWord_7183316) baseStart_7183316 baseEnd_7183316 := by
    simpa [prefixWord, tailWord_7183316, baseEnd_7183316] using wordTrace_append hprefix tailTrace_7183316
  have hstable : (prefixWord ++ tailWord_7183316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183316).length < 2 ^ (prefixWord ++ tailWord_7183316).sum := by decide
  have hdescent : baseEnd_7183316 < baseStart_7183316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183330 : List Nat := [3, 3, 3, 1, 1, 1, 2, 3, 1, 2, 3]
def baseStart_7183330 : Nat := 118140960795 + 7183330 * 2 ^ 59
def prefixEnd_7183330 : Nat := 4983230072969 + 3 ^ 40 * 7183330 * 2
def baseEnd_7183330 : Nat := 3688500989861485422039473

theorem tailTrace_7183330 : CollatzResearch.WordTrace tailWord_7183330 prefixEnd_7183330 3688500989861485422039473 := by
  unfold tailWord_7183330
  simp only [CollatzResearch.WordTrace]
  refine ⟨65499392266507424984342861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174665046044019799958247629 65499392266507424984342861)
  ·
    refine ⟨24562272099940284369128573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65499392266507424984342861 24562272099940284369128573)
    ·
      refine ⟨9210852037477606638423215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24562272099940284369128573 9210852037477606638423215)
      ·
        refine ⟨13816278056216409957634823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9210852037477606638423215 13816278056216409957634823)
        ·
          refine ⟨20724417084324614936452235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13816278056216409957634823 20724417084324614936452235)
          ·
            refine ⟨31086625626486922404678353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20724417084324614936452235 31086625626486922404678353)
            ·
              refine ⟨23314969219865191803508765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31086625626486922404678353 23314969219865191803508765)
              ·
                refine ⟨8743113457449446926315787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23314969219865191803508765 8743113457449446926315787)
                ·
                  refine ⟨13114670186174170389473681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8743113457449446926315787 13114670186174170389473681)
                  ·
                    refine ⟨9836002639630627792105261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13114670186174170389473681 9836002639630627792105261)
                    ·
                      refine ⟨3688500989861485422039473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9836002639630627792105261 3688500989861485422039473)
                      ·
                        rfl

theorem cell23_7183330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 1, 2, 3].length) (baseStart_7183330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183330 prefixEnd_7183330 := by exact prefixLift 7183330
  have htrace : WordTrace (prefixWord ++ tailWord_7183330) baseStart_7183330 baseEnd_7183330 := by
    simpa [prefixWord, tailWord_7183330, baseEnd_7183330] using wordTrace_append hprefix tailTrace_7183330
  have hstable : (prefixWord ++ tailWord_7183330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183330).length < 2 ^ (prefixWord ++ tailWord_7183330).sum := by decide
  have hdescent : baseEnd_7183330 < baseStart_7183330 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183333 : List Nat := [1, 3, 1, 6, 2, 1, 9]
def baseStart_7183333 : Nat := 118140960795 + 7183333 * 2 ^ 59
def prefixEnd_7183333 : Nat := 4983230072969 + 3 ^ 40 * 7183333 * 2
def baseEnd_7183333 : Nat := 45537068275351221114839

theorem tailTrace_7183333 : CollatzResearch.WordTrace tailWord_7183333 prefixEnd_7183333 45537068275351221114839 := by
  unfold tailWord_7183333
  simp only [CollatzResearch.WordTrace]
  refine ⟨261997678485018831449730653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174665118990012554299820435 261997678485018831449730653)
  ·
    refine ⟨98249129431882061793648995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 261997678485018831449730653 98249129431882061793648995)
    ·
      refine ⟨147373694147823092690473493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98249129431882061793648995 147373694147823092690473493)
      ·
        refine ⟨6908141913179207469865945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147373694147823092690473493 6908141913179207469865945)
        ·
          refine ⟨5181106434884405602399459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6908141913179207469865945 5181106434884405602399459)
          ·
            refine ⟨7771659652326608403599189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181106434884405602399459 7771659652326608403599189)
            ·
              refine ⟨45537068275351221114839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7771659652326608403599189 45537068275351221114839)
              ·
                rfl

theorem cell23_7183333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 9].length) (baseStart_7183333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183333 prefixEnd_7183333 := by exact prefixLift 7183333
  have htrace : WordTrace (prefixWord ++ tailWord_7183333) baseStart_7183333 baseEnd_7183333 := by
    simpa [prefixWord, tailWord_7183333, baseEnd_7183333] using wordTrace_append hprefix tailTrace_7183333
  have hstable : (prefixWord ++ tailWord_7183333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183333).length < 2 ^ (prefixWord ++ tailWord_7183333).sum := by decide
  have hdescent : baseEnd_7183333 < baseStart_7183333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183370 : List Nat := [3, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2]
def baseStart_7183370 : Nat := 118140960795 + 7183370 * 2 ^ 59
def prefixEnd_7183370 : Nat := 4983230072969 + 3 ^ 40 * 7183370 * 2
def baseEnd_7183370 : Nat := 3688521529087665265539289

theorem tailTrace_7183370 : CollatzResearch.WordTrace tailWord_7183370 prefixEnd_7183370 3688521529087665265539289 := by
  unfold tailWord_7183370
  simp only [CollatzResearch.WordTrace]
  refine ⟨65499756996471196692206891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174666018657256524512551709 65499756996471196692206891)
  ·
    refine ⟨98249635494706795038310337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65499756996471196692206891 98249635494706795038310337)
    ·
      refine ⟨73687226621030096278732753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98249635494706795038310337 73687226621030096278732753)
      ·
        refine ⟨55265419965772572209049565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73687226621030096278732753 55265419965772572209049565)
        ·
          refine ⟨20724532487164714578393587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55265419965772572209049565 20724532487164714578393587)
          ·
            refine ⟨31086798730747071867590381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20724532487164714578393587 31086798730747071867590381)
            ·
              refine ⟨11657549524030151950346393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31086798730747071867590381 11657549524030151950346393)
              ·
                refine ⟨8743162143022613962759795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11657549524030151950346393 8743162143022613962759795)
                ·
                  refine ⟨13114743214533920944139693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8743162143022613962759795 13114743214533920944139693)
                  ·
                    refine ⟨4918028705450220354052385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13114743214533920944139693 4918028705450220354052385)
                    ·
                      refine ⟨3688521529087665265539289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918028705450220354052385 3688521529087665265539289)
                      ·
                        rfl

theorem cell23_7183370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 3, 2, 1, 3, 2].length) (baseStart_7183370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183370 prefixEnd_7183370 := by exact prefixLift 7183370
  have htrace : WordTrace (prefixWord ++ tailWord_7183370) baseStart_7183370 baseEnd_7183370 := by
    simpa [prefixWord, tailWord_7183370, baseEnd_7183370] using wordTrace_append hprefix tailTrace_7183370
  have hstable : (prefixWord ++ tailWord_7183370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183370).length < 2 ^ (prefixWord ++ tailWord_7183370).sum := by decide
  have hdescent : baseEnd_7183370 < baseStart_7183370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183379 : List Nat := [1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4]
def baseStart_7183379 : Nat := 118140960795 + 7183379 * 2 ^ 59
def prefixEnd_7183379 : Nat := 4983230072969 + 3 ^ 40 * 7183379 * 2
def baseEnd_7183379 : Nat := 3688526150413555730326747

theorem tailTrace_7183379 : CollatzResearch.WordTrace tailWord_7183379 prefixEnd_7183379 3688526150413555730326747 := by
  unfold tailWord_7183379
  simp only [CollatzResearch.WordTrace]
  refine ⟨261999356242852181305905191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174666237495234787537270127 261999356242852181305905191)
  ·
    refine ⟨392999034364278271958857787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261999356242852181305905191 392999034364278271958857787)
    ·
      refine ⟨589498551546417407938286681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 392999034364278271958857787 589498551546417407938286681)
      ·
        refine ⟨442123913659813055953715011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589498551546417407938286681 442123913659813055953715011)
        ·
          refine ⟨663185870489719583930572517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442123913659813055953715011 663185870489719583930572517)
          ·
            refine ⟨124347350716822421986982347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 663185870489719583930572517 124347350716822421986982347)
            ·
              refine ⟨186521026075233632980473521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124347350716822421986982347 186521026075233632980473521)
              ·
                refine ⟨139890769556425224735355141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186521026075233632980473521 139890769556425224735355141)
                ·
                  refine ⟨26229519291829729637879089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 139890769556425224735355141 26229519291829729637879089)
                  ·
                    refine ⟨19672139468872297228409317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26229519291829729637879089 19672139468872297228409317)
                    ·
                      refine ⟨3688526150413555730326747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19672139468872297228409317 3688526150413555730326747)
                      ·
                        rfl

theorem cell23_7183379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 2, 4, 2, 4].length) (baseStart_7183379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183379 prefixEnd_7183379 := by exact prefixLift 7183379
  have htrace : WordTrace (prefixWord ++ tailWord_7183379) baseStart_7183379 baseEnd_7183379 := by
    simpa [prefixWord, tailWord_7183379, baseEnd_7183379] using wordTrace_append hprefix tailTrace_7183379
  have hstable : (prefixWord ++ tailWord_7183379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183379).length < 2 ^ (prefixWord ++ tailWord_7183379).sum := by decide
  have hdescent : baseEnd_7183379 < baseStart_7183379 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183383 : List Nat := [1, 1, 3, 5, 1, 1, 1, 1, 3, 4, 2]
def baseStart_7183383 : Nat := 118140960795 + 7183383 * 2 ^ 59
def prefixEnd_7183383 : Nat := 4983230072969 + 3 ^ 40 * 7183383 * 2
def baseEnd_7183383 : Nat := 3688528204336173714676729

theorem tailTrace_7183383 : CollatzResearch.WordTrace tailWord_7183383 prefixEnd_7183383 3688528204336173714676729 := by
  unfold tailWord_7183383
  simp only [CollatzResearch.WordTrace]
  refine ⟨261999502134837689989050803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174666334756558459992700535 261999502134837689989050803)
  ·
    refine ⟨392999253202256534983576205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 261999502134837689989050803 392999253202256534983576205)
    ·
      refine ⟨147374719950846200618841077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 392999253202256534983576205 147374719950846200618841077)
      ·
        refine ⟨13816379995391831308016351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147374719950846200618841077 13816379995391831308016351)
        ·
          refine ⟨20724569993087746962024527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13816379995391831308016351 20724569993087746962024527)
          ·
            refine ⟨31086854989631620443036791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20724569993087746962024527 31086854989631620443036791)
            ·
              refine ⟨46630282484447430664555187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31086854989631620443036791 46630282484447430664555187)
              ·
                refine ⟨69945423726671145996832781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46630282484447430664555187 69945423726671145996832781)
                ·
                  refine ⟨26229533897501679748812293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69945423726671145996832781 26229533897501679748812293)
                  ·
                    refine ⟨4918037605781564952902305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26229533897501679748812293 4918037605781564952902305)
                    ·
                      refine ⟨3688528204336173714676729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918037605781564952902305 3688528204336173714676729)
                      ·
                        rfl

theorem cell23_7183383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 4, 2].length) (baseStart_7183383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183383 prefixEnd_7183383 := by exact prefixLift 7183383
  have htrace : WordTrace (prefixWord ++ tailWord_7183383) baseStart_7183383 baseEnd_7183383 := by
    simpa [prefixWord, tailWord_7183383, baseEnd_7183383] using wordTrace_append hprefix tailTrace_7183383
  have hstable : (prefixWord ++ tailWord_7183383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183383).length < 2 ^ (prefixWord ++ tailWord_7183383).sum := by decide
  have hdescent : baseEnd_7183383 < baseStart_7183383 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183406 : List Nat := [4, 1, 3, 1, 1, 1, 2, 3, 7]
def baseStart_7183406 : Nat := 118140960795 + 7183406 * 2 ^ 59
def prefixEnd_7183406 : Nat := 4983230072969 + 3 ^ 40 * 7183406 * 2
def baseEnd_7183406 : Nat := 409837779376803013854347

theorem tailTrace_7183406 : CollatzResearch.WordTrace tailWord_7183406 prefixEnd_7183406 409837779376803013854347 := by
  unfold tailWord_7183406
  simp only [CollatzResearch.WordTrace]
  refine ⟨32750042626719295614642259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174666894009169576611425381 32750042626719295614642259)
  ·
    refine ⟨49125063940078943421963389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32750042626719295614642259 49125063940078943421963389)
    ·
      refine ⟨18421898977529603783236271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49125063940078943421963389 18421898977529603783236271)
      ·
        refine ⟨27632848466294405674854407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18421898977529603783236271 27632848466294405674854407)
        ·
          refine ⟨41449272699441608512281611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27632848466294405674854407 41449272699441608512281611)
          ·
            refine ⟨62173909049162412768422417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41449272699441608512281611 62173909049162412768422417)
            ·
              refine ⟨46630431786871809576316813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62173909049162412768422417 46630431786871809576316813)
              ·
                refine ⟨17486411920076928591118805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46630431786871809576316813 17486411920076928591118805)
                ·
                  refine ⟨409837779376803013854347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17486411920076928591118805 409837779376803013854347)
                  ·
                    rfl

theorem cell23_7183406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 2, 3, 7].length) (baseStart_7183406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183406 prefixEnd_7183406 := by exact prefixLift 7183406
  have htrace : WordTrace (prefixWord ++ tailWord_7183406) baseStart_7183406 baseEnd_7183406 := by
    simpa [prefixWord, tailWord_7183406, baseEnd_7183406] using wordTrace_append hprefix tailTrace_7183406
  have hstable : (prefixWord ++ tailWord_7183406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183406).length < 2 ^ (prefixWord ++ tailWord_7183406).sum := by decide
  have hdescent : baseEnd_7183406 < baseStart_7183406 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183416 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 1, 5, 3]
def baseStart_7183416 : Nat := 118140960795 + 7183416 * 2 ^ 59
def prefixEnd_7183416 : Nat := 4983230072969 + 3 ^ 40 * 7183416 * 2
def baseEnd_7183416 : Nat := 3688545149197772085564077

theorem tailTrace_7183416 : CollatzResearch.WordTrace tailWord_7183416 prefixEnd_7183416 3688545149197772085564077 := by
  unfold tailWord_7183416
  simp only [CollatzResearch.WordTrace]
  refine ⟨131000352871859068312501051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174667137162478757750001401 131000352871859068312501051)
  ·
    refine ⟨196500529307788602468751577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131000352871859068312501051 196500529307788602468751577)
    ·
      refine ⟨147375396980841451851563683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196500529307788602468751577 147375396980841451851563683)
      ·
        refine ⟨221063095471262177777345525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147375396980841451851563683 221063095471262177777345525)
        ·
          refine ⟨20724665200430829166626143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 221063095471262177777345525 20724665200430829166626143)
          ·
            refine ⟨31086997800646243749939215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20724665200430829166626143 31086997800646243749939215)
            ·
              refine ⟨46630496700969365624908823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31086997800646243749939215 46630496700969365624908823)
              ·
                refine ⟨69945745051454048437363235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46630496700969365624908823 69945745051454048437363235)
                ·
                  refine ⟨104918617577181072656044853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69945745051454048437363235 104918617577181072656044853)
                  ·
                    refine ⟨9836120397860725561504205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104918617577181072656044853 9836120397860725561504205)
                    ·
                      refine ⟨3688545149197772085564077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9836120397860725561504205 3688545149197772085564077)
                      ·
                        rfl

theorem cell23_7183416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_7183416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183416 prefixEnd_7183416 := by exact prefixLift 7183416
  have htrace : WordTrace (prefixWord ++ tailWord_7183416) baseStart_7183416 baseEnd_7183416 := by
    simpa [prefixWord, tailWord_7183416, baseEnd_7183416] using wordTrace_append hprefix tailTrace_7183416
  have hstable : (prefixWord ++ tailWord_7183416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183416).length < 2 ^ (prefixWord ++ tailWord_7183416).sum := by decide
  have hdescent : baseEnd_7183416 < baseStart_7183416 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183429 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_7183429 : Nat := 118140960795 + 7183429 * 2 ^ 59
def prefixEnd_7183429 : Nat := 4983230072969 + 3 ^ 40 * 7183429 * 2
def baseEnd_7183429 : Nat := 3688551824446280534701517

theorem tailTrace_7183429 : CollatzResearch.WordTrace tailWord_7183429 prefixEnd_7183429 3688551824446280534701517 := by
  unfold tailWord_7183429
  simp only [CollatzResearch.WordTrace]
  refine ⟨262001179892671039845225341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174667453261780693230150227 262001179892671039845225341)
  ·
    refine ⟨98250442459751639941959503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262001179892671039845225341 98250442459751639941959503)
    ·
      refine ⟨147375663689627459912939255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98250442459751639941959503 147375663689627459912939255)
      ·
        refine ⟨221063495534441189869408883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147375663689627459912939255 221063495534441189869408883)
        ·
          refine ⟨331595243301661784804113325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221063495534441189869408883 331595243301661784804113325)
          ·
            refine ⟨124348216238123169301542497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331595243301661784804113325 124348216238123169301542497)
            ·
              refine ⟨93261162178592376976156873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124348216238123169301542497 93261162178592376976156873)
              ·
                refine ⟨69945871633944282732117655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93261162178592376976156873 69945871633944282732117655)
                ·
                  refine ⟨104918807450916424098176483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69945871633944282732117655 104918807450916424098176483)
                  ·
                    refine ⟨157378211176374636147264725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104918807450916424098176483 157378211176374636147264725)
                    ·
                      refine ⟨3688551824446280534701517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157378211176374636147264725 3688551824446280534701517)
                      ·
                        rfl

theorem cell23_7183429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_7183429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183429 prefixEnd_7183429 := by exact prefixLift 7183429
  have htrace : WordTrace (prefixWord ++ tailWord_7183429) baseStart_7183429 baseEnd_7183429 := by
    simpa [prefixWord, tailWord_7183429, baseEnd_7183429] using wordTrace_append hprefix tailTrace_7183429
  have hstable : (prefixWord ++ tailWord_7183429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183429).length < 2 ^ (prefixWord ++ tailWord_7183429).sum := by decide
  have hdescent : baseEnd_7183429 < baseStart_7183429 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183456 : List Nat := [2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4]
def baseStart_7183456 : Nat := 118140960795 + 7183456 * 2 ^ 59
def prefixEnd_7183456 : Nat := 4983230072969 + 3 ^ 40 * 7183456 * 2
def baseEnd_7183456 : Nat := 3688565688423951929063893

theorem tailTrace_7183456 : CollatzResearch.WordTrace tailWord_7183456 prefixEnd_7183456 3688565688423951929063893 := by
  unfold tailWord_7183456
  simp only [CollatzResearch.WordTrace]
  refine ⟨131001082331786611728229111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174668109775715482304305481 131001082331786611728229111)
  ·
    refine ⟨196501623497679917592343667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131001082331786611728229111 196501623497679917592343667)
    ·
      refine ⟨294752435246519876388515501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196501623497679917592343667 294752435246519876388515501)
      ·
        refine ⟨110532163217444953645693313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294752435246519876388515501 110532163217444953645693313)
        ·
          refine ⟨82899122413083715234269985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110532163217444953645693313 82899122413083715234269985)
          ·
            refine ⟨62174341809812786425702489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82899122413083715234269985 62174341809812786425702489)
            ·
              refine ⟨46630756357359589819276867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62174341809812786425702489 46630756357359589819276867)
              ·
                refine ⟨69946134536039384728915301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46630756357359589819276867 69946134536039384728915301)
                ·
                  refine ⟨13114900225507384636671619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69946134536039384728915301 13114900225507384636671619)
                  ·
                    refine ⟨19672350338261076955007429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13114900225507384636671619 19672350338261076955007429)
                    ·
                      refine ⟨3688565688423951929063893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19672350338261076955007429 3688565688423951929063893)
                      ·
                        rfl

theorem cell23_7183456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 4].length) (baseStart_7183456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183456 prefixEnd_7183456 := by exact prefixLift 7183456
  have htrace : WordTrace (prefixWord ++ tailWord_7183456) baseStart_7183456 baseEnd_7183456 := by
    simpa [prefixWord, tailWord_7183456, baseEnd_7183456] using wordTrace_append hprefix tailTrace_7183456
  have hstable : (prefixWord ++ tailWord_7183456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183456).length < 2 ^ (prefixWord ++ tailWord_7183456).sum := by decide
  have hdescent : baseEnd_7183456 < baseStart_7183456 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183517 : List Nat := [1, 4, 2, 1, 1, 2, 5, 2, 1, 4]
def baseStart_7183517 : Nat := 118140960795 + 7183517 * 2 ^ 59
def prefixEnd_7183517 : Nat := 4983230072969 + 3 ^ 40 * 7183517 * 2
def baseEnd_7183517 : Nat := 1229532336914625396800371

theorem tailTrace_7183517 : CollatzResearch.WordTrace tailWord_7183517 prefixEnd_7183517 1229532336914625396800371 := by
  unfold tailWord_7183517
  simp only [CollatzResearch.WordTrace]
  refine ⟨262004389516352230874428805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174669593010901487249619203 262004389516352230874428805)
  ·
    refine ⟨49125823034316043288955401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262004389516352230874428805 49125823034316043288955401)
    ·
      refine ⟨36844367275737032466716551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49125823034316043288955401 36844367275737032466716551)
      ·
        refine ⟨55266550913605548700074827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36844367275737032466716551 55266550913605548700074827)
        ·
          refine ⟨82899826370408323050112241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55266550913605548700074827 82899826370408323050112241)
          ·
            refine ⟨62174869777806242287584181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82899826370408323050112241 62174869777806242287584181)
            ·
              refine ⟨5828894041669335214461017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62174869777806242287584181 5828894041669335214461017)
              ·
                refine ⟨4371670531252001410845763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5828894041669335214461017 4371670531252001410845763)
                ·
                  refine ⟨6557505796878002116268645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371670531252001410845763 6557505796878002116268645)
                  ·
                    refine ⟨1229532336914625396800371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557505796878002116268645 1229532336914625396800371)
                    ·
                      rfl

theorem cell23_7183517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 5, 2, 1, 4].length) (baseStart_7183517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183517 prefixEnd_7183517 := by exact prefixLift 7183517
  have htrace : WordTrace (prefixWord ++ tailWord_7183517) baseStart_7183517 baseEnd_7183517 := by
    simpa [prefixWord, tailWord_7183517, baseEnd_7183517] using wordTrace_append hprefix tailTrace_7183517
  have hstable : (prefixWord ++ tailWord_7183517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183517).length < 2 ^ (prefixWord ++ tailWord_7183517).sum := by decide
  have hdescent : baseEnd_7183517 < baseStart_7183517 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183530 : List Nat := [3, 1, 5, 1, 1, 2, 1, 3, 6]
def baseStart_7183530 : Nat := 118140960795 + 7183530 * 2 ^ 59
def prefixEnd_7183530 : Nat := 4983230072969 + 3 ^ 40 * 7183530 * 2
def baseEnd_7183530 : Nat := 409844853999153848837617

theorem tailTrace_7183530 : CollatzResearch.WordTrace tailWord_7183530 prefixEnd_7183530 409844853999153848837617 := by
  unfold tailWord_7183530
  simp only [CollatzResearch.WordTrace]
  refine ⟨65501215916326283523663011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174669909110203422729768029 65501215916326283523663011)
  ·
    refine ⟨98251823874489425285494517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65501215916326283523663011 98251823874489425285494517)
    ·
      refine ⟨9211108488233383620515111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98251823874489425285494517 9211108488233383620515111)
      ·
        refine ⟨13816662732350075430772667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211108488233383620515111 13816662732350075430772667)
        ·
          refine ⟨20724994098525113146159001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13816662732350075430772667 20724994098525113146159001)
          ·
            refine ⟨15543745573893834859619251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20724994098525113146159001 15543745573893834859619251)
            ·
              refine ⟨23315618360840752289428877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15543745573893834859619251 23315618360840752289428877)
              ·
                refine ⟨8743356885315282108535829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23315618360840752289428877 8743356885315282108535829)
                ·
                  refine ⟨409844853999153848837617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8743356885315282108535829 409844853999153848837617)
                  ·
                    rfl

theorem cell23_7183530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 1, 3, 6].length) (baseStart_7183530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183530 prefixEnd_7183530 := by exact prefixLift 7183530
  have htrace : WordTrace (prefixWord ++ tailWord_7183530) baseStart_7183530 baseEnd_7183530 := by
    simpa [prefixWord, tailWord_7183530, baseEnd_7183530] using wordTrace_append hprefix tailTrace_7183530
  have hstable : (prefixWord ++ tailWord_7183530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183530).length < 2 ^ (prefixWord ++ tailWord_7183530).sum := by decide
  have hdescent : baseEnd_7183530 < baseStart_7183530 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183583 : List Nat := [1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3]
def baseStart_7183583 : Nat := 118140960795 + 7183583 * 2 ^ 59
def prefixEnd_7183583 : Nat := 4983230072969 + 3 ^ 40 * 7183583 * 2
def baseEnd_7183583 : Nat := 3688630900467072932175809

theorem tailTrace_7183583 : CollatzResearch.WordTrace tailWord_7183583 prefixEnd_7183583 3688630900467072932175809 := by
  unfold tailWord_7183583
  simp only [CollatzResearch.WordTrace]
  refine ⟨262006796734113124146331403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174671197822742082764220935 262006796734113124146331403)
  ·
    refine ⟨393010195101169686219497105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262006796734113124146331403 393010195101169686219497105)
    ·
      refine ⟨294757646325877264664622829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393010195101169686219497105 294757646325877264664622829)
      ·
        refine ⟨110534117372203974249233561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294757646325877264664622829 110534117372203974249233561)
        ·
          refine ⟨82900588029152980686925171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110534117372203974249233561 82900588029152980686925171)
          ·
            refine ⟨124350882043729471030387757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82900588029152980686925171 124350882043729471030387757)
            ·
              refine ⟨46631580766398551636395409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124350882043729471030387757 46631580766398551636395409)
              ·
                refine ⟨34973685574798913727296557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46631580766398551636395409 34973685574798913727296557)
                ·
                  refine ⟨13115132090549592647736209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34973685574798913727296557 13115132090549592647736209)
                  ·
                    refine ⟨9836349067912194485802157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13115132090549592647736209 9836349067912194485802157)
                    ·
                      refine ⟨3688630900467072932175809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9836349067912194485802157 3688630900467072932175809)
                      ·
                        rfl

theorem cell23_7183583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 2, 3, 2, 3].length) (baseStart_7183583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183583 prefixEnd_7183583 := by exact prefixLift 7183583
  have htrace : WordTrace (prefixWord ++ tailWord_7183583) baseStart_7183583 baseEnd_7183583 := by
    simpa [prefixWord, tailWord_7183583, baseEnd_7183583] using wordTrace_append hprefix tailTrace_7183583
  have hstable : (prefixWord ++ tailWord_7183583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183583).length < 2 ^ (prefixWord ++ tailWord_7183583).sum := by decide
  have hdescent : baseEnd_7183583 < baseStart_7183583 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183597 : List Nat := [1, 5, 1, 2, 2, 1, 1, 1, 5, 2, 2]
def baseStart_7183597 : Nat := 118140960795 + 7183597 * 2 ^ 59
def prefixEnd_7183597 : Nat := 4983230072969 + 3 ^ 40 * 7183597 * 2
def baseEnd_7183597 : Nat := 3688638089196235877400745

theorem tailTrace_7183597 : CollatzResearch.WordTrace tailWord_7183597 prefixEnd_7183597 3688638089196235877400745 := by
  unfold tailWord_7183597
  simp only [CollatzResearch.WordTrace]
  refine ⟨262007307356062404537341045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174671538237374936358227363 262007307356062404537341045)
  ·
    refine ⟨24563185064630850425375723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262007307356062404537341045 24563185064630850425375723)
    ·
      refine ⟨36844777596946275638063585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24563185064630850425375723 36844777596946275638063585)
      ·
        refine ⟨27633583197709706728547689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36844777596946275638063585 27633583197709706728547689)
        ·
          refine ⟨20725187398282280046410767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27633583197709706728547689 20725187398282280046410767)
          ·
            refine ⟨31087781097423420069616151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20725187398282280046410767 31087781097423420069616151)
            ·
              refine ⟨46631671646135130104424227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31087781097423420069616151 46631671646135130104424227)
              ·
                refine ⟨69947507469202695156636341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46631671646135130104424227 69947507469202695156636341)
                ·
                  refine ⟨6557578825237752670934657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69947507469202695156636341 6557578825237752670934657)
                  ·
                    refine ⟨4918184118928314503200993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6557578825237752670934657 4918184118928314503200993)
                    ·
                      refine ⟨3688638089196235877400745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918184118928314503200993 3688638089196235877400745)
                      ·
                        rfl

theorem cell23_7183597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 5, 2, 2].length) (baseStart_7183597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183597 prefixEnd_7183597 := by exact prefixLift 7183597
  have htrace : WordTrace (prefixWord ++ tailWord_7183597) baseStart_7183597 baseEnd_7183597 := by
    simpa [prefixWord, tailWord_7183597, baseEnd_7183597] using wordTrace_append hprefix tailTrace_7183597
  have hstable : (prefixWord ++ tailWord_7183597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183597).length < 2 ^ (prefixWord ++ tailWord_7183597).sum := by decide
  have hdescent : baseEnd_7183597 < baseStart_7183597 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183603 : List Nat := [1, 1, 1, 2, 2, 6, 3, 7]
def baseStart_7183603 : Nat := 118140960795 + 7183603 * 2 ^ 59
def prefixEnd_7183603 : Nat := 4983230072969 + 3 ^ 40 * 7183603 * 2
def baseEnd_7183603 : Nat := 136616339632598624219471

theorem tailTrace_7183603 : CollatzResearch.WordTrace tailWord_7183603 prefixEnd_7183603 136616339632598624219471 := by
  unfold tailWord_7183603
  simp only [CollatzResearch.WordTrace]
  refine ⟨262007526194040667562059463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174671684129360445041372975 262007526194040667562059463)
  ·
    refine ⟨393011289291061001343089195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262007526194040667562059463 393011289291061001343089195)
    ·
      refine ⟨589516933936591502014633793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393011289291061001343089195 589516933936591502014633793)
      ·
        refine ⟨442137700452443626510975345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589516933936591502014633793 442137700452443626510975345)
        ·
          refine ⟨331603275339332719883231509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442137700452443626510975345 331603275339332719883231509)
          ·
            refine ⟨15543903531531221244526477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 331603275339332719883231509 15543903531531221244526477)
            ·
              refine ⟨5828963824324207966697429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15543903531531221244526477 5828963824324207966697429)
              ·
                refine ⟨136616339632598624219471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5828963824324207966697429 136616339632598624219471)
                ·
                  rfl

theorem cell23_7183603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 3, 7].length) (baseStart_7183603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183603 prefixEnd_7183603 := by exact prefixLift 7183603
  have htrace : WordTrace (prefixWord ++ tailWord_7183603) baseStart_7183603 baseEnd_7183603 := by
    simpa [prefixWord, tailWord_7183603, baseEnd_7183603] using wordTrace_append hprefix tailTrace_7183603
  have hstable : (prefixWord ++ tailWord_7183603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183603).length < 2 ^ (prefixWord ++ tailWord_7183603).sum := by decide
  have hdescent : baseEnd_7183603 < baseStart_7183603 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183614 : List Nat := [4, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_7183614 : Nat := 118140960795 + 7183614 * 2 ^ 59
def prefixEnd_7183614 : Nat := 4983230072969 + 3 ^ 40 * 7183614 * 2
def baseEnd_7183614 : Nat := 3688646818367362310888167

theorem tailTrace_7183614 : CollatzResearch.WordTrace tailWord_7183614 prefixEnd_7183614 3688646818367362310888167 := by
  unfold tailWord_7183614
  simp only [CollatzResearch.WordTrace]
  refine ⟨32750990924625102055088737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174671951598000544293806597 32750990924625102055088737)
  ·
    refine ⟨24563243193468826541316553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32750990924625102055088737 24563243193468826541316553)
    ·
      refine ⟨18422432395101619905987415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24563243193468826541316553 18422432395101619905987415)
      ·
        refine ⟨27633648592652429858981123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18422432395101619905987415 27633648592652429858981123)
        ·
          refine ⟨41450472888978644788471685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27633648592652429858981123 41450472888978644788471685)
          ·
            refine ⟨7771963666683495897838441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41450472888978644788471685 7771963666683495897838441)
            ·
              refine ⟨5828972750012621923378831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7771963666683495897838441 5828972750012621923378831)
              ·
                refine ⟨8743459125018932885068247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828972750012621923378831 8743459125018932885068247)
                ·
                  refine ⟨13115188687528399327602371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8743459125018932885068247 13115188687528399327602371)
                  ·
                    refine ⟨19672783031292598991403557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13115188687528399327602371 19672783031292598991403557)
                    ·
                      refine ⟨3688646818367362310888167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19672783031292598991403557 3688646818367362310888167)
                      ·
                        rfl

theorem cell23_7183614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_7183614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183614 prefixEnd_7183614 := by exact prefixLift 7183614
  have htrace : WordTrace (prefixWord ++ tailWord_7183614) baseStart_7183614 baseEnd_7183614 := by
    simpa [prefixWord, tailWord_7183614, baseEnd_7183614] using wordTrace_append hprefix tailTrace_7183614
  have hstable : (prefixWord ++ tailWord_7183614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183614).length < 2 ^ (prefixWord ++ tailWord_7183614).sum := by decide
  have hdescent : baseEnd_7183614 < baseStart_7183614 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183617 : List Nat := [1, 2, 4, 1, 1, 3, 4, 1, 1, 2, 3]
def baseStart_7183617 : Nat := 118140960795 + 7183617 * 2 ^ 59
def prefixEnd_7183617 : Nat := 4983230072969 + 3 ^ 40 * 7183617 * 2
def baseEnd_7183617 : Nat := 3688648358809325799150653

theorem tailTrace_7183617 : CollatzResearch.WordTrace tailWord_7183617 prefixEnd_7183617 3688648358809325799150653 := by
  unfold tailWord_7183617
  simp only [CollatzResearch.WordTrace]
  refine ⟨262008036815989947953069105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174672024543993298635379403 262008036815989947953069105)
  ·
    refine ⟨196506027611992460964801829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262008036815989947953069105 196506027611992460964801829)
    ·
      refine ⟨36844880177248586430900343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196506027611992460964801829 36844880177248586430900343)
      ·
        refine ⟨55267320265872879646350515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36844880177248586430900343 55267320265872879646350515)
        ·
          refine ⟨82900980398809319469525773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55267320265872879646350515 82900980398809319469525773)
          ·
            refine ⟨31087867649553494801072165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82900980398809319469525773 31087867649553494801072165)
            ·
              refine ⟨5828975184291280275201031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31087867649553494801072165 5828975184291280275201031)
              ·
                refine ⟨8743462776436920412801547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5828975184291280275201031 8743462776436920412801547)
                ·
                  refine ⟨13115194164655380619202321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8743462776436920412801547 13115194164655380619202321)
                  ·
                    refine ⟨9836395623491535464401741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13115194164655380619202321 9836395623491535464401741)
                    ·
                      refine ⟨3688648358809325799150653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9836395623491535464401741 3688648358809325799150653)
                      ·
                        rfl

theorem cell23_7183617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 4, 1, 1, 2, 3].length) (baseStart_7183617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183617 prefixEnd_7183617 := by exact prefixLift 7183617
  have htrace : WordTrace (prefixWord ++ tailWord_7183617) baseStart_7183617 baseEnd_7183617 := by
    simpa [prefixWord, tailWord_7183617, baseEnd_7183617] using wordTrace_append hprefix tailTrace_7183617
  have hstable : (prefixWord ++ tailWord_7183617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183617).length < 2 ^ (prefixWord ++ tailWord_7183617).sum := by decide
  have hdescent : baseEnd_7183617 < baseStart_7183617 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183624 : List Nat := [2, 1, 3, 2, 5, 1, 1, 2, 2, 4]
def baseStart_7183624 : Nat := 118140960795 + 7183624 * 2 ^ 59
def prefixEnd_7183624 : Nat := 4983230072969 + 3 ^ 40 * 7183624 * 2
def baseEnd_7183624 : Nat := 1229550651057969090587707

theorem tailTrace_7183624 : CollatzResearch.WordTrace tailWord_7183624 prefixEnd_7183624 1229550651057969090587707 := by
  unfold tailWord_7183624
  simp only [CollatzResearch.WordTrace]
  refine ⟨131004146063482294074286963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174672194751309725432382617 131004146063482294074286963)
  ·
    refine ⟨196506219095223441111430445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131004146063482294074286963 196506219095223441111430445)
    ·
      refine ⟨73689832160708790416786417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196506219095223441111430445 73689832160708790416786417)
      ·
        refine ⟨55267374120531592812589813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73689832160708790416786417 55267374120531592812589813)
        ·
          refine ⟨5181316323799836826180295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 55267374120531592812589813 5181316323799836826180295)
          ·
            refine ⟨7771974485699755239270443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181316323799836826180295 7771974485699755239270443)
            ·
              refine ⟨11657961728549632858905665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7771974485699755239270443 11657961728549632858905665)
              ·
                refine ⟨8743471296412224644179249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11657961728549632858905665 8743471296412224644179249)
                ·
                  refine ⟨6557603472309168483134437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8743471296412224644179249 6557603472309168483134437)
                  ·
                    refine ⟨1229550651057969090587707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557603472309168483134437 1229550651057969090587707)
                    ·
                      rfl

theorem cell23_7183624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_7183624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183624 prefixEnd_7183624 := by exact prefixLift 7183624
  have htrace : WordTrace (prefixWord ++ tailWord_7183624) baseStart_7183624 baseEnd_7183624 := by
    simpa [prefixWord, tailWord_7183624, baseEnd_7183624] using wordTrace_append hprefix tailTrace_7183624
  have hstable : (prefixWord ++ tailWord_7183624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183624).length < 2 ^ (prefixWord ++ tailWord_7183624).sum := by decide
  have hdescent : baseEnd_7183624 < baseStart_7183624 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183647 : List Nat := [1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 3]
def baseStart_7183647 : Nat := 118140960795 + 7183647 * 2 ^ 59
def prefixEnd_7183647 : Nat := 4983230072969 + 3 ^ 40 * 7183647 * 2
def baseEnd_7183647 : Nat := 3688663763228960681775515

theorem tailTrace_7183647 : CollatzResearch.WordTrace tailWord_7183647 prefixEnd_7183647 3688663763228960681775515 := by
  unfold tailWord_7183647
  simp only [CollatzResearch.WordTrace]
  refine ⟨262009131005881263076661195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174672754003920842051107463 262009131005881263076661195)
  ·
    refine ⟨393013696508821894614991793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262009131005881263076661195 393013696508821894614991793)
    ·
      refine ⟨294760272381616420961243845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393013696508821894614991793 294760272381616420961243845)
      ·
        refine ⟨55267551071553078930233221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 294760272381616420961243845 55267551071553078930233221)
        ·
          refine ⟨10362665825916202299418729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55267551071553078930233221 10362665825916202299418729)
          ·
            refine ⟨7771999369437151724564047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10362665825916202299418729 7771999369437151724564047)
            ·
              refine ⟨11657999054155727586846071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7771999369437151724564047 11657999054155727586846071)
              ·
                refine ⟨17486998581233591380269107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11657999054155727586846071 17486998581233591380269107)
                ·
                  refine ⟨26230497871850387070403661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17486998581233591380269107 26230497871850387070403661)
                  ·
                    refine ⟨9836436701943895151401373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26230497871850387070403661 9836436701943895151401373)
                    ·
                      refine ⟨3688663763228960681775515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9836436701943895151401373 3688663763228960681775515)
                      ·
                        rfl

theorem cell23_7183647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 1, 1, 1, 3, 3].length) (baseStart_7183647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183647 prefixEnd_7183647 := by exact prefixLift 7183647
  have htrace : WordTrace (prefixWord ++ tailWord_7183647) baseStart_7183647 baseEnd_7183647 := by
    simpa [prefixWord, tailWord_7183647, baseEnd_7183647] using wordTrace_append hprefix tailTrace_7183647
  have hstable : (prefixWord ++ tailWord_7183647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183647).length < 2 ^ (prefixWord ++ tailWord_7183647).sum := by decide
  have hdescent : baseEnd_7183647 < baseStart_7183647 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183687 : List Nat := [1, 1, 4, 1, 2, 3, 2, 1, 4, 2, 2]
def baseStart_7183687 : Nat := 118140960795 + 7183687 * 2 ^ 59
def prefixEnd_7183687 : Nat := 4983230072969 + 3 ^ 40 * 7183687 * 2
def baseEnd_7183687 : Nat := 3688684302455140525275331

theorem tailTrace_7183687 : CollatzResearch.WordTrace tailWord_7183687 prefixEnd_7183687 3688684302455140525275331 := by
  unfold tailWord_7183687
  simp only [CollatzResearch.WordTrace]
  refine ⟨262010589925736349908117315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174673726617157566605411543 262010589925736349908117315)
  ·
    refine ⟨393015884888604524862175973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262010589925736349908117315 393015884888604524862175973)
    ·
      refine ⟨73690478416613348411657995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393015884888604524862175973 73690478416613348411657995)
      ·
        refine ⟨110535717624920022617486993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73690478416613348411657995 110535717624920022617486993)
        ·
          refine ⟨82901788218690016963115245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110535717624920022617486993 82901788218690016963115245)
          ·
            refine ⟨31088170582008756361168217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82901788218690016963115245 31088170582008756361168217)
            ·
              refine ⟨23316127936506567270876163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31088170582008756361168217 23316127936506567270876163)
              ·
                refine ⟨34974191904759850906314245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23316127936506567270876163 34974191904759850906314245)
                ·
                  refine ⟨6557660982142472044933921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34974191904759850906314245 6557660982142472044933921)
                  ·
                    refine ⟨4918245736606854033700441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6557660982142472044933921 4918245736606854033700441)
                    ·
                      refine ⟨3688684302455140525275331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918245736606854033700441 3688684302455140525275331)
                      ·
                        rfl

theorem cell23_7183687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 4, 2, 2].length) (baseStart_7183687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183687 prefixEnd_7183687 := by exact prefixLift 7183687
  have htrace : WordTrace (prefixWord ++ tailWord_7183687) baseStart_7183687 baseEnd_7183687 := by
    simpa [prefixWord, tailWord_7183687, baseEnd_7183687] using wordTrace_append hprefix tailTrace_7183687
  have hstable : (prefixWord ++ tailWord_7183687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183687).length < 2 ^ (prefixWord ++ tailWord_7183687).sum := by decide
  have hdescent : baseEnd_7183687 < baseStart_7183687 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183800 : List Nat := [2, 1, 2, 1, 2, 2, 5, 2, 6]
def baseStart_7183800 : Nat := 118140960795 + 7183800 * 2 ^ 59
def prefixEnd_7183800 : Nat := 4983230072969 + 3 ^ 40 * 7183800 * 2
def baseEnd_7183800 : Nat := 409860258418788731462479

theorem tailTrace_7183800 : CollatzResearch.WordTrace tailWord_7183800 prefixEnd_7183800 409860258418788731462479 := by
  unfold tailWord_7183800
  simp only [CollatzResearch.WordTrace]
  refine ⟨131007355687163485103490427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174676474249551313471320569 131007355687163485103490427)
  ·
    refine ⟨196511033530745227655235641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131007355687163485103490427 196511033530745227655235641)
    ·
      refine ⟨147383275148058920741426731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196511033530745227655235641 147383275148058920741426731)
      ·
        refine ⟨221074912722088381112140097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147383275148058920741426731 221074912722088381112140097)
        ·
          refine ⟨165806184541566285834105073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221074912722088381112140097 165806184541566285834105073)
          ·
            refine ⟨124354638406174714375578805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165806184541566285834105073 124354638406174714375578805)
            ·
              refine ⟨11658247350578879472710513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124354638406174714375578805 11658247350578879472710513)
              ·
                refine ⟨8743685512934159604532885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11658247350578879472710513 8743685512934159604532885)
                ·
                  refine ⟨409860258418788731462479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8743685512934159604532885 409860258418788731462479)
                  ·
                    rfl

theorem cell23_7183800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 5, 2, 6].length) (baseStart_7183800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183800 prefixEnd_7183800 := by exact prefixLift 7183800
  have htrace : WordTrace (prefixWord ++ tailWord_7183800) baseStart_7183800 baseEnd_7183800 := by
    simpa [prefixWord, tailWord_7183800, baseEnd_7183800] using wordTrace_append hprefix tailTrace_7183800
  have hstable : (prefixWord ++ tailWord_7183800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183800).length < 2 ^ (prefixWord ++ tailWord_7183800).sum := by decide
  have hdescent : baseEnd_7183800 < baseStart_7183800 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183804 : List Nat := [2, 2, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_7183804 : Nat := 118140960795 + 7183804 * 2 ^ 59
def prefixEnd_7183804 : Nat := 4983230072969 + 3 ^ 40 * 7183804 * 2
def baseEnd_7183804 : Nat := 1229581459897238855837431

theorem tailTrace_7183804 : CollatzResearch.WordTrace tailWord_7183804 prefixEnd_7183804 1229581459897238855837431 := by
  unfold tailWord_7183804
  simp only [CollatzResearch.WordTrace]
  refine ⟨131007428633156239445063233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174676571510874985926750977 131007428633156239445063233)
  ·
    refine ⟨98255571474867179583797425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131007428633156239445063233 98255571474867179583797425)
    ·
      refine ⟨73691678606150384687848069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98255571474867179583797425 73691678606150384687848069)
      ·
        refine ⟨13817189738653197128971513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 73691678606150384687848069 13817189738653197128971513)
        ·
          refine ⟨10362892303989897846728635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13817189738653197128971513 10362892303989897846728635)
          ·
            refine ⟨15544338455984846770092953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10362892303989897846728635 15544338455984846770092953)
            ·
              refine ⟨11658253841988635077569715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15544338455984846770092953 11658253841988635077569715)
              ·
                refine ⟨17487380762982952616354573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11658253841988635077569715 17487380762982952616354573)
                ·
                  refine ⟨6557767786118607231132965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17487380762982952616354573 6557767786118607231132965)
                  ·
                    refine ⟨1229581459897238855837431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6557767786118607231132965 1229581459897238855837431)
                    ·
                      rfl

theorem cell23_7183804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_7183804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183804 prefixEnd_7183804 := by exact prefixLift 7183804
  have htrace : WordTrace (prefixWord ++ tailWord_7183804) baseStart_7183804 baseEnd_7183804 := by
    simpa [prefixWord, tailWord_7183804, baseEnd_7183804] using wordTrace_append hprefix tailTrace_7183804
  have hstable : (prefixWord ++ tailWord_7183804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183804).length < 2 ^ (prefixWord ++ tailWord_7183804).sum := by decide
  have hdescent : baseEnd_7183804 < baseStart_7183804 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183823 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 7]
def baseStart_7183823 : Nat := 118140960795 + 7183823 * 2 ^ 59
def prefixEnd_7183823 : Nat := 4983230072969 + 3 ^ 40 * 7183823 * 2
def baseEnd_7183823 : Nat := 3688754135824151993174705

theorem tailTrace_7183823 : CollatzResearch.WordTrace tailWord_7183823 prefixEnd_7183823 3688754135824151993174705 := by
  unfold tailWord_7183823
  simp only [CollatzResearch.WordTrace]
  refine ⟨262015550253243645135068123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174677033502162430090045415 262015550253243645135068123)
  ·
    refine ⟨393023325379865467702602185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262015550253243645135068123 393023325379865467702602185)
    ·
      refine ⟨294767494034899100776951639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393023325379865467702602185 294767494034899100776951639)
      ·
        refine ⟨442151241052348651165427459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294767494034899100776951639 442151241052348651165427459)
        ·
          refine ⟨663226861578522976748141189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442151241052348651165427459 663226861578522976748141189)
          ·
            refine ⟨124355036545973058140276473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 663226861578522976748141189 124355036545973058140276473)
            ·
              refine ⟨93266277409479793605207355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124355036545973058140276473 93266277409479793605207355)
              ·
                refine ⟨139899416114219690407811033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93266277409479793605207355 139899416114219690407811033)
                ·
                  refine ⟨104924562085664767805858275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139899416114219690407811033 104924562085664767805858275)
                  ·
                    refine ⟨157386843128497151708787413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104924562085664767805858275 157386843128497151708787413)
                    ·
                      refine ⟨3688754135824151993174705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157386843128497151708787413 3688754135824151993174705)
                      ·
                        rfl

theorem cell23_7183823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 1, 7].length) (baseStart_7183823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183823 prefixEnd_7183823 := by exact prefixLift 7183823
  have htrace : WordTrace (prefixWord ++ tailWord_7183823) baseStart_7183823 baseEnd_7183823 := by
    simpa [prefixWord, tailWord_7183823, baseEnd_7183823] using wordTrace_append hprefix tailTrace_7183823
  have hstable : (prefixWord ++ tailWord_7183823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183823).length < 2 ^ (prefixWord ++ tailWord_7183823).sum := by decide
  have hdescent : baseEnd_7183823 < baseStart_7183823 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183847 : List Nat := [1, 1, 5, 2, 1, 2, 2, 3, 1, 5]
def baseStart_7183847 : Nat := 118140960795 + 7183847 * 2 ^ 59
def prefixEnd_7183847 : Nat := 4983230072969 + 3 ^ 40 * 7183847 * 2
def baseEnd_7183847 : Nat := 1229588819786619966424865

theorem tailTrace_7183847 : CollatzResearch.WordTrace tailWord_7183847 prefixEnd_7183847 1229588819786619966424865 := by
  unfold tailWord_7183847
  simp only [CollatzResearch.WordTrace]
  refine ⟨262016425605156697233941795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174677617070104464822627863 262016425605156697233941795)
  ·
    refine ⟨393024638407735045850912693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262016425605156697233941795 393024638407735045850912693)
    ·
      refine ⟨36846059850725160548523065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 393024638407735045850912693 36846059850725160548523065)
      ·
        refine ⟨27634544888043870411392299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36846059850725160548523065 27634544888043870411392299)
        ·
          refine ⟨41451817332065805617088449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27634544888043870411392299 41451817332065805617088449)
          ·
            refine ⟨31088862999049354212816337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41451817332065805617088449 31088862999049354212816337)
            ·
              refine ⟨23316647249287015659612253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31088862999049354212816337 23316647249287015659612253)
              ·
                refine ⟨8743742718482630872354595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23316647249287015659612253 8743742718482630872354595)
                ·
                  refine ⟨13115614077723946308531893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8743742718482630872354595 13115614077723946308531893)
                  ·
                    refine ⟨1229588819786619966424865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13115614077723946308531893 1229588819786619966424865)
                    ·
                      rfl

theorem cell23_7183847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 2, 3, 1, 5].length) (baseStart_7183847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183847 prefixEnd_7183847 := by exact prefixLift 7183847
  have htrace : WordTrace (prefixWord ++ tailWord_7183847) baseStart_7183847 baseEnd_7183847 := by
    simpa [prefixWord, tailWord_7183847, baseEnd_7183847] using wordTrace_append hprefix tailTrace_7183847
  have hstable : (prefixWord ++ tailWord_7183847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183847).length < 2 ^ (prefixWord ++ tailWord_7183847).sum := by decide
  have hdescent : baseEnd_7183847 < baseStart_7183847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183854 : List Nat := [4, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2]
def baseStart_7183854 : Nat := 118140960795 + 7183854 * 2 ^ 59
def prefixEnd_7183854 : Nat := 4983230072969 + 3 ^ 40 * 7183854 * 2
def baseEnd_7183854 : Nat := 3688770053724441371887063

theorem tailTrace_7183854 : CollatzResearch.WordTrace tailWord_7183854 prefixEnd_7183854 3688770053724441371887063 := by
  unfold tailWord_7183854
  simp only [CollatzResearch.WordTrace]
  refine ⟨32752085114516417178680827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174677787277420891619631077 32752085114516417178680827)
  ·
    refine ⟨49128127671774625768021241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32752085114516417178680827 49128127671774625768021241)
    ·
      refine ⟨36846095753830969326015931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49128127671774625768021241 36846095753830969326015931)
      ·
        refine ⟨55269143630746453989023897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36846095753830969326015931 55269143630746453989023897)
        ·
          refine ⟨41451857723059840491767923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55269143630746453989023897 41451857723059840491767923)
          ·
            refine ⟨62177786584589760737651885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41451857723059840491767923 62177786584589760737651885)
            ·
              refine ⟨23316669969221160276619457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62177786584589760737651885 23316669969221160276619457)
              ·
                refine ⟨17487502476915870207464593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23316669969221160276619457 17487502476915870207464593)
                ·
                  refine ⟨13115626857686902655598445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17487502476915870207464593 13115626857686902655598445)
                  ·
                    refine ⟨4918360071632588495849417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13115626857686902655598445 4918360071632588495849417)
                    ·
                      refine ⟨3688770053724441371887063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918360071632588495849417 3688770053724441371887063)
                      ·
                        rfl

theorem cell23_7183854_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_7183854 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183854 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183854 prefixEnd_7183854 := by exact prefixLift 7183854
  have htrace : WordTrace (prefixWord ++ tailWord_7183854) baseStart_7183854 baseEnd_7183854 := by
    simpa [prefixWord, tailWord_7183854, baseEnd_7183854] using wordTrace_append hprefix tailTrace_7183854
  have hstable : (prefixWord ++ tailWord_7183854).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183854).length < 2 ^ (prefixWord ++ tailWord_7183854).sum := by decide
  have hdescent : baseEnd_7183854 < baseStart_7183854 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183854) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183861 : List Nat := [1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_7183861 : Nat := 118140960795 + 7183861 * 2 ^ 59
def prefixEnd_7183861 : Nat := 4983230072969 + 3 ^ 40 * 7183861 * 2
def baseEnd_7183861 : Nat := 3688773648089022844499531

theorem tailTrace_7183861 : CollatzResearch.WordTrace tailWord_7183861 prefixEnd_7183861 3688773648089022844499531 := by
  unfold tailWord_7183861
  simp only [CollatzResearch.WordTrace]
  refine ⟨262016936227105977624951437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174677957484737318416634291 262016936227105977624951437)
  ·
    refine ⟨98256351085164741609356789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262016936227105977624951437 98256351085164741609356789)
    ·
      refine ⟨9211532914234194525877199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 98256351085164741609356789 9211532914234194525877199)
      ·
        refine ⟨13817299371351291788815799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9211532914234194525877199 13817299371351291788815799)
        ·
          refine ⟨20725949057026937683223699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13817299371351291788815799 20725949057026937683223699)
          ·
            refine ⟨31088923585540406524835549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20725949057026937683223699 31088923585540406524835549)
            ·
              refine ⟨11658346344577652446813331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31088923585540406524835549 11658346344577652446813331)
              ·
                refine ⟨17487519516866478670219997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11658346344577652446813331 17487519516866478670219997)
                ·
                  refine ⟨6557819818824929501332499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17487519516866478670219997 6557819818824929501332499)
                  ·
                    refine ⟨9836729728237394251998749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6557819818824929501332499 9836729728237394251998749)
                    ·
                      refine ⟨3688773648089022844499531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9836729728237394251998749 3688773648089022844499531)
                      ·
                        rfl

theorem cell23_7183861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_7183861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183861 prefixEnd_7183861 := by exact prefixLift 7183861
  have htrace : WordTrace (prefixWord ++ tailWord_7183861) baseStart_7183861 baseEnd_7183861 := by
    simpa [prefixWord, tailWord_7183861, baseEnd_7183861] using wordTrace_append hprefix tailTrace_7183861
  have hstable : (prefixWord ++ tailWord_7183861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183861).length < 2 ^ (prefixWord ++ tailWord_7183861).sum := by decide
  have hdescent : baseEnd_7183861 < baseStart_7183861 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183880 : List Nat := [2, 1, 3, 2, 1, 1, 4, 1, 1, 1, 6]
def baseStart_7183880 : Nat := 118140960795 + 7183880 * 2 ^ 59
def prefixEnd_7183880 : Nat := 4983230072969 + 3 ^ 40 * 7183880 * 2
def baseEnd_7183880 : Nat := 3688783404221458270161943

theorem tailTrace_7183880 : CollatzResearch.WordTrace tailWord_7183880 prefixEnd_7183880 3688783404221458270161943 := by
  unfold tailWord_7183880
  simp only [CollatzResearch.WordTrace]
  refine ⟨131008814607018571934946547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174678419476024762579928729 131008814607018571934946547)
  ·
    refine ⟨196513221910527857902419821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131008814607018571934946547 196513221910527857902419821)
    ·
      refine ⟨73692458216447946713407433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196513221910527857902419821 73692458216447946713407433)
      ·
        refine ⟨55269343662335960035055575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73692458216447946713407433 55269343662335960035055575)
        ·
          refine ⟨82904015493503940052583363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55269343662335960035055575 82904015493503940052583363)
          ·
            refine ⟨124356023240255910078875045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82904015493503940052583363 124356023240255910078875045)
            ·
              refine ⟨23316754357547983139789071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124356023240255910078875045 23316754357547983139789071)
              ·
                refine ⟨34975131536321974709683607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23316754357547983139789071 34975131536321974709683607)
                ·
                  refine ⟨52462697304482962064525411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34975131536321974709683607 52462697304482962064525411)
                  ·
                    refine ⟨78694045956724443096788117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52462697304482962064525411 78694045956724443096788117)
                    ·
                      refine ⟨3688783404221458270161943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78694045956724443096788117 3688783404221458270161943)
                      ·
                        rfl

theorem cell23_7183880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 1, 1, 1, 6].length) (baseStart_7183880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183880 prefixEnd_7183880 := by exact prefixLift 7183880
  have htrace : WordTrace (prefixWord ++ tailWord_7183880) baseStart_7183880 baseEnd_7183880 := by
    simpa [prefixWord, tailWord_7183880, baseEnd_7183880] using wordTrace_append hprefix tailTrace_7183880
  have hstable : (prefixWord ++ tailWord_7183880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183880).length < 2 ^ (prefixWord ++ tailWord_7183880).sum := by decide
  have hdescent : baseEnd_7183880 < baseStart_7183880 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183904 : List Nat := [2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7183904 : Nat := 118140960795 + 7183904 * 2 ^ 59
def prefixEnd_7183904 : Nat := 4983230072969 + 3 ^ 40 * 7183904 * 2
def baseEnd_7183904 : Nat := 3688795727757166176261833

theorem tailTrace_7183904 : CollatzResearch.WordTrace tailWord_7183904 prefixEnd_7183904 3688795727757166176261833 := by
  unfold tailWord_7183904
  simp only [CollatzResearch.WordTrace]
  refine ⟨131009252282975097984383383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174679003043966797312511177 131009252282975097984383383)
  ·
    refine ⟨196513878424462646976575075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131009252282975097984383383 196513878424462646976575075)
    ·
      refine ⟨294770817636693970464862613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196513878424462646976575075 294770817636693970464862613)
      ·
        refine ⟨13817382076720029865540435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 294770817636693970464862613 13817382076720029865540435)
        ·
          refine ⟨20726073115080044798310653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13817382076720029865540435 20726073115080044798310653)
          ·
            refine ⟨7772277418155016799366495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20726073115080044798310653 7772277418155016799366495)
            ·
              refine ⟨11658416127232525199049743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7772277418155016799366495 11658416127232525199049743)
              ·
                refine ⟨17487624190848787798574615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11658416127232525199049743 17487624190848787798574615)
                ·
                  refine ⟨26231436286273181697861923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17487624190848787798574615 26231436286273181697861923)
                  ·
                    refine ⟨39347154429409772546792885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26231436286273181697861923 39347154429409772546792885)
                    ·
                      refine ⟨3688795727757166176261833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39347154429409772546792885 3688795727757166176261833)
                      ·
                        rfl

theorem cell23_7183904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7183904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183904 prefixEnd_7183904 := by exact prefixLift 7183904
  have htrace : WordTrace (prefixWord ++ tailWord_7183904) baseStart_7183904 baseEnd_7183904 := by
    simpa [prefixWord, tailWord_7183904, baseEnd_7183904] using wordTrace_append hprefix tailTrace_7183904
  have hstable : (prefixWord ++ tailWord_7183904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183904).length < 2 ^ (prefixWord ++ tailWord_7183904).sum := by decide
  have hdescent : baseEnd_7183904 < baseStart_7183904 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183912 : List Nat := [2, 1, 5, 2, 3, 1, 2, 2, 1, 1, 3]
def baseStart_7183912 : Nat := 118140960795 + 7183912 * 2 ^ 59
def prefixEnd_7183912 : Nat := 4983230072969 + 3 ^ 40 * 7183912 * 2
def baseEnd_7183912 : Nat := 3688799835602402144961797

theorem tailTrace_7183912 : CollatzResearch.WordTrace tailWord_7183912 prefixEnd_7183912 3688799835602402144961797 := by
  unfold tailWord_7183912
  simp only [CollatzResearch.WordTrace]
  refine ⟨131009398174960606667528995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174679197566614142223371993 131009398174960606667528995)
  ·
    refine ⟨196514097262440910001293493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131009398174960606667528995 196514097262440910001293493)
    ·
      refine ⟨18423196618353835312621265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196514097262440910001293493 18423196618353835312621265)
      ·
        refine ⟨13817397463765376484465949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18423196618353835312621265 13817397463765376484465949)
        ·
          refine ⟨5181524048912016181674731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13817397463765376484465949 5181524048912016181674731)
          ·
            refine ⟨7772286073368024272512097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181524048912016181674731 7772286073368024272512097)
            ·
              refine ⟨5829214555026018204384073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7772286073368024272512097 5829214555026018204384073)
              ·
                refine ⟨4371910916269513653288055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5829214555026018204384073 4371910916269513653288055)
                ·
                  refine ⟨6557866374404270479932083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4371910916269513653288055 6557866374404270479932083)
                  ·
                    refine ⟨9836799561606405719898125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6557866374404270479932083 9836799561606405719898125)
                    ·
                      refine ⟨3688799835602402144961797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9836799561606405719898125 3688799835602402144961797)
                      ·
                        rfl

theorem cell23_7183912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_7183912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183912 prefixEnd_7183912 := by exact prefixLift 7183912
  have htrace : WordTrace (prefixWord ++ tailWord_7183912) baseStart_7183912 baseEnd_7183912 := by
    simpa [prefixWord, tailWord_7183912, baseEnd_7183912] using wordTrace_append hprefix tailTrace_7183912
  have hstable : (prefixWord ++ tailWord_7183912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183912).length < 2 ^ (prefixWord ++ tailWord_7183912).sum := by decide
  have hdescent : baseEnd_7183912 < baseStart_7183912 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183950 : List Nat := [4, 1, 1, 1, 1, 2, 1, 1, 3, 8]
def baseStart_7183950 : Nat := 118140960795 + 7183950 * 2 ^ 59
def prefixEnd_7183950 : Nat := 4983230072969 + 3 ^ 40 * 7183950 * 2
def baseEnd_7183950 : Nat := 1229606449289090998762207

theorem tailTrace_7183950 : CollatzResearch.WordTrace tailWord_7183950 prefixEnd_7183950 1229606449289090998762207 := by
  unfold tailWord_7183950
  simp only [CollatzResearch.WordTrace]
  refine ⟨32752522790472943228117663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174680121549189030549960869 32752522790472943228117663)
  ·
    refine ⟨49128784185709414842176495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32752522790472943228117663 49128784185709414842176495)
    ·
      refine ⟨73693176278564122263264743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49128784185709414842176495 73693176278564122263264743)
      ·
        refine ⟨110539764417846183394897115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73693176278564122263264743 110539764417846183394897115)
        ·
          refine ⟨165809646626769275092345673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110539764417846183394897115 165809646626769275092345673)
          ·
            refine ⟨124357234970076956319259255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165809646626769275092345673 124357234970076956319259255)
            ·
              refine ⟨186535852455115434478888883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124357234970076956319259255 186535852455115434478888883)
              ·
                refine ⟨279803778682673151718333325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186535852455115434478888883 279803778682673151718333325)
                ·
                  refine ⟨104926417006002431894374997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 279803778682673151718333325 104926417006002431894374997)
                  ·
                    refine ⟨1229606449289090998762207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104926417006002431894374997 1229606449289090998762207)
                    ·
                      rfl

theorem cell23_7183950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_7183950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183950 prefixEnd_7183950 := by exact prefixLift 7183950
  have htrace : WordTrace (prefixWord ++ tailWord_7183950) baseStart_7183950 baseEnd_7183950 := by
    simpa [prefixWord, tailWord_7183950, baseEnd_7183950] using wordTrace_append hprefix tailTrace_7183950
  have hstable : (prefixWord ++ tailWord_7183950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183950).length < 2 ^ (prefixWord ++ tailWord_7183950).sum := by decide
  have hdescent : baseEnd_7183950 < baseStart_7183950 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183960 : List Nat := [2, 1, 2, 2, 1, 2, 1, 3, 1, 3, 5]
def baseStart_7183960 : Nat := 118140960795 + 7183960 * 2 ^ 59
def prefixEnd_7183960 : Nat := 4983230072969 + 3 ^ 40 * 7183960 * 2
def baseEnd_7183960 : Nat := 3688824482673817957161575

theorem tailTrace_7183960 : CollatzResearch.WordTrace tailWord_7183960 prefixEnd_7183960 3688824482673817957161575 := by
  unfold tailWord_7183960
  simp only [CollatzResearch.WordTrace]
  refine ⟨131010273526873658766402667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174680364702498211688536889 131010273526873658766402667)
  ·
    refine ⟨196515410290310488149604001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131010273526873658766402667 196515410290310488149604001)
    ·
      refine ⟨147386557717732866112203001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196515410290310488149604001 147386557717732866112203001)
      ·
        refine ⟨110539918288299649584152251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147386557717732866112203001 110539918288299649584152251)
        ·
          refine ⟨165809877432449474376228377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110539918288299649584152251 165809877432449474376228377)
          ·
            refine ⟨124357408074337105782171283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165809877432449474376228377 124357408074337105782171283)
            ·
              refine ⟨186536112111505658673256925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124357408074337105782171283 186536112111505658673256925)
              ·
                refine ⟨69951042041814622002471347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186536112111505658673256925 69951042041814622002471347)
                ·
                  refine ⟨104926563062721933003707021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69951042041814622002471347 104926563062721933003707021)
                  ·
                    refine ⟨39347461148520724876390133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104926563062721933003707021 39347461148520724876390133)
                    ·
                      refine ⟨3688824482673817957161575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39347461148520724876390133 3688824482673817957161575)
                      ·
                        rfl

theorem cell23_7183960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_7183960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183960 prefixEnd_7183960 := by exact prefixLift 7183960
  have htrace : WordTrace (prefixWord ++ tailWord_7183960) baseStart_7183960 baseEnd_7183960 := by
    simpa [prefixWord, tailWord_7183960, baseEnd_7183960] using wordTrace_append hprefix tailTrace_7183960
  have hstable : (prefixWord ++ tailWord_7183960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183960).length < 2 ^ (prefixWord ++ tailWord_7183960).sum := by decide
  have hdescent : baseEnd_7183960 < baseStart_7183960 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7183997 : List Nat := [1, 4, 1, 1, 4, 1, 2, 2, 7]
def baseStart_7183997 : Nat := 118140960795 + 7183997 * 2 ^ 59
def prefixEnd_7183997 : Nat := 4983230072969 + 3 ^ 40 * 7183997 * 2
def baseEnd_7183997 : Nat := 409871497939781590266545

theorem tailTrace_7183997 : CollatzResearch.WordTrace tailWord_7183997 prefixEnd_7183997 409871497939781590266545 := by
  unfold tailWord_7183997
  simp only [CollatzResearch.WordTrace]
  refine ⟨262021896554613272851902245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174681264369742181901268163 262021896554613272851902245)
  ·
    refine ⟨49129105603989988659731671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262021896554613272851902245 49129105603989988659731671)
    ·
      refine ⟨73693658405984982989597507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49129105603989988659731671 73693658405984982989597507)
      ·
        refine ⟨110540487608977474484396261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73693658405984982989597507 110540487608977474484396261)
        ·
          refine ⟨20726341426683276465824299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110540487608977474484396261 20726341426683276465824299)
          ·
            refine ⟨31089512140024914698736449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20726341426683276465824299 31089512140024914698736449)
            ·
              refine ⟨23317134105018686024052337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31089512140024914698736449 23317134105018686024052337)
              ·
                refine ⟨17487850578764014518039253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23317134105018686024052337 17487850578764014518039253)
                ·
                  refine ⟨409871497939781590266545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17487850578764014518039253 409871497939781590266545)
                  ·
                    rfl

theorem cell23_7183997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 2, 2, 7].length) (baseStart_7183997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7183997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7183997 prefixEnd_7183997 := by exact prefixLift 7183997
  have htrace : WordTrace (prefixWord ++ tailWord_7183997) baseStart_7183997 baseEnd_7183997 := by
    simpa [prefixWord, tailWord_7183997, baseEnd_7183997] using wordTrace_append hprefix tailTrace_7183997
  have hstable : (prefixWord ++ tailWord_7183997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7183997).length < 2 ^ (prefixWord ++ tailWord_7183997).sum := by decide
  have hdescent : baseEnd_7183997 < baseStart_7183997 := by decide
  rcases family_descends (prefixWord ++ tailWord_7183997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184031 : List Nat := [1, 1, 2, 7, 1, 2, 1, 1, 7]
def baseStart_7184031 : Nat := 118140960795 + 7184031 * 2 ^ 59
def prefixEnd_7184031 : Nat := 4983230072969 + 3 ^ 40 * 7184031 * 2
def baseEnd_7184031 : Nat := 409873437755587464374861

theorem tailTrace_7184031 : CollatzResearch.WordTrace tailWord_7184031 prefixEnd_7184031 409873437755587464374861 := by
  unfold tailWord_7184031
  simp only [CollatzResearch.WordTrace]
  refine ⟨262023136636490096658639947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174682091090993397772426631 262023136636490096658639947)
  ·
    refine ⟨393034704954735144987959921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262023136636490096658639947 393034704954735144987959921)
    ·
      refine ⟨294776028716051358740969941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393034704954735144987959921 294776028716051358740969941)
      ·
        refine ⟨6908813173032453720491483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 294776028716051358740969941 6908813173032453720491483)
        ·
          refine ⟨10363219759548680580737225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6908813173032453720491483 10363219759548680580737225)
          ·
            refine ⟨7772414819661510435552919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10363219759548680580737225 7772414819661510435552919)
            ·
              refine ⟨11658622229492265653329379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7772414819661510435552919 11658622229492265653329379)
              ·
                refine ⟨17487933344238398479994069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11658622229492265653329379 17487933344238398479994069)
                ·
                  refine ⟨409873437755587464374861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 17487933344238398479994069 409873437755587464374861)
                  ·
                    rfl

theorem cell23_7184031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 2, 1, 1, 7].length) (baseStart_7184031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184031 prefixEnd_7184031 := by exact prefixLift 7184031
  have htrace : WordTrace (prefixWord ++ tailWord_7184031) baseStart_7184031 baseEnd_7184031 := by
    simpa [prefixWord, tailWord_7184031, baseEnd_7184031] using wordTrace_append hprefix tailTrace_7184031
  have hstable : (prefixWord ++ tailWord_7184031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184031).length < 2 ^ (prefixWord ++ tailWord_7184031).sum := by decide
  have hdescent : baseEnd_7184031 < baseStart_7184031 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184047 : List Nat := [1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 4]
def baseStart_7184047 : Nat := 118140960795 + 7184047 * 2 ^ 59
def prefixEnd_7184047 : Nat := 4983230072969 + 3 ^ 40 * 7184047 * 2
def baseEnd_7184047 : Nat := 3688869155490759116773675

theorem tailTrace_7184047 : CollatzResearch.WordTrace tailWord_7184047 prefixEnd_7184047 3688869155490759116773675 := by
  unfold tailWord_7184047
  simp only [CollatzResearch.WordTrace]
  refine ⟨262023720204432131391222395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174682480136288087594148263 262023720204432131391222395)
  ·
    refine ⟨393035580306648197086833593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262023720204432131391222395 393035580306648197086833593)
    ·
      refine ⟨294776685229986147815125195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393035580306648197086833593 294776685229986147815125195)
      ·
        refine ⟨442165027844979221722687793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294776685229986147815125195 442165027844979221722687793)
        ·
          refine ⟨331623770883734416292015845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442165027844979221722687793 331623770883734416292015845)
          ·
            refine ⟨62179457040700203054752971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331623770883734416292015845 62179457040700203054752971)
            ·
              refine ⟨93269185561050304582129457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62179457040700203054752971 93269185561050304582129457)
              ·
                refine ⟨69951889170787728436597093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93269185561050304582129457 69951889170787728436597093)
                ·
                  refine ⟨13115979219522699081861955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69951889170787728436597093 13115979219522699081861955)
                  ·
                    refine ⟨19673968829284048622792933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13115979219522699081861955 19673968829284048622792933)
                    ·
                      refine ⟨3688869155490759116773675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19673968829284048622792933 3688869155490759116773675)
                      ·
                        rfl

theorem cell23_7184047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 2, 4, 1, 4].length) (baseStart_7184047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184047 prefixEnd_7184047 := by exact prefixLift 7184047
  have htrace : WordTrace (prefixWord ++ tailWord_7184047) baseStart_7184047 baseEnd_7184047 := by
    simpa [prefixWord, tailWord_7184047, baseEnd_7184047] using wordTrace_append hprefix tailTrace_7184047
  have hstable : (prefixWord ++ tailWord_7184047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184047).length < 2 ^ (prefixWord ++ tailWord_7184047).sum := by decide
  have hdescent : baseEnd_7184047 < baseStart_7184047 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184064 : List Nat := [2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4]
def baseStart_7184064 : Nat := 118140960795 + 7184064 * 2 ^ 59
def prefixEnd_7184064 : Nat := 4983230072969 + 3 ^ 40 * 7184064 * 2
def baseEnd_7184064 : Nat := 3688877884661885550261097

theorem tailTrace_7184064 : CollatzResearch.WordTrace tailWord_7184064 prefixEnd_7184064 3688877884661885550261097 := by
  unfold tailWord_7184064
  simp only [CollatzResearch.WordTrace]
  refine ⟨131012170122685271647295623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174682893496913695529727497 131012170122685271647295623)
  ·
    refine ⟨196518255184027907470943435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131012170122685271647295623 196518255184027907470943435)
    ·
      refine ⟨294777382776041861206415153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196518255184027907470943435 294777382776041861206415153)
      ·
        refine ⟨221083037082031395904811365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294777382776041861206415153 221083037082031395904811365)
        ·
          refine ⟨41453069452880886732152131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221083037082031395904811365 41453069452880886732152131)
          ·
            refine ⟨62179604179321330098228197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41453069452880886732152131 62179604179321330098228197)
            ·
              refine ⟨11658675783622749393417787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62179604179321330098228197 11658675783622749393417787)
              ·
                refine ⟨17488013675434124090126681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11658675783622749393417787 17488013675434124090126681)
                ·
                  refine ⟨13116010256575593067595011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17488013675434124090126681 13116010256575593067595011)
                  ·
                    refine ⟨19674015384863389601392517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13116010256575593067595011 19674015384863389601392517)
                    ·
                      refine ⟨3688877884661885550261097, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19674015384863389601392517 3688877884661885550261097)
                      ·
                        rfl

theorem cell23_7184064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 4].length) (baseStart_7184064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184064 prefixEnd_7184064 := by exact prefixLift 7184064
  have htrace : WordTrace (prefixWord ++ tailWord_7184064) baseStart_7184064 baseEnd_7184064 := by
    simpa [prefixWord, tailWord_7184064, baseEnd_7184064] using wordTrace_append hprefix tailTrace_7184064
  have hstable : (prefixWord ++ tailWord_7184064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184064).length < 2 ^ (prefixWord ++ tailWord_7184064).sum := by decide
  have hdescent : baseEnd_7184064 < baseStart_7184064 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184104 : List Nat := [2, 1, 4, 1, 3, 1, 2, 3, 6]
def baseStart_7184104 : Nat := 118140960795 + 7184104 * 2 ^ 59
def prefixEnd_7184104 : Nat := 4983230072969 + 3 ^ 40 * 7184104 * 2
def baseEnd_7184104 : Nat := 409877602654229488195657

theorem tailTrace_7184104 : CollatzResearch.WordTrace tailWord_7184104 prefixEnd_7184104 409877602654229488195657 := by
  unfold tailWord_7184104
  simp only [CollatzResearch.WordTrace]
  refine ⟨131012899582612815063023683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174683866110150420084031577 131012899582612815063023683)
  ·
    refine ⟨196519349373919222594535525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131012899582612815063023683 196519349373919222594535525)
    ·
      refine ⟨36847378007609854236475411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196519349373919222594535525 36847378007609854236475411)
      ·
        refine ⟨55271067011414781354713117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36847378007609854236475411 55271067011414781354713117)
        ·
          refine ⟨20726650129280543008017419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 55271067011414781354713117 20726650129280543008017419)
          ·
            refine ⟨31089975193920814512026129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20726650129280543008017419 31089975193920814512026129)
            ·
              refine ⟨23317481395440610884019597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31089975193920814512026129 23317481395440610884019597)
              ·
                refine ⟨8744055523290229081507349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23317481395440610884019597 8744055523290229081507349)
                ·
                  refine ⟨409877602654229488195657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8744055523290229081507349 409877602654229488195657)
                  ·
                    rfl

theorem cell23_7184104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 2, 3, 6].length) (baseStart_7184104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184104 prefixEnd_7184104 := by exact prefixLift 7184104
  have htrace : WordTrace (prefixWord ++ tailWord_7184104) baseStart_7184104 baseEnd_7184104 := by
    simpa [prefixWord, tailWord_7184104, baseEnd_7184104] using wordTrace_append hprefix tailTrace_7184104
  have hstable : (prefixWord ++ tailWord_7184104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184104).length < 2 ^ (prefixWord ++ tailWord_7184104).sum := by decide
  have hdescent : baseEnd_7184104 < baseStart_7184104 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184118 : List Nat := [5, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_7184118 : Nat := 118140960795 + 7184118 * 2 ^ 59
def prefixEnd_7184118 : Nat := 4983230072969 + 3 ^ 40 * 7184118 * 2
def baseEnd_7184118 : Nat := 3688905612617228338985849

theorem tailTrace_7184118 : CollatzResearch.WordTrace tailWord_7184118 prefixEnd_7184118 3688905612617228338985849 := by
  unfold tailWord_7184118
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376644361698431907316063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174684206524783273678038005 16376644361698431907316063)
  ·
    refine ⟨24564966542547647860974095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16376644361698431907316063 24564966542547647860974095)
    ·
      refine ⟨36847449813821471791461143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24564966542547647860974095 36847449813821471791461143)
      ·
        refine ⟨55271174720732207687191715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36847449813821471791461143 55271174720732207687191715)
        ·
          refine ⟨82906762081098311530787573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55271174720732207687191715 82906762081098311530787573)
          ·
            refine ⟨7772508945102966706011335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 82906762081098311530787573 7772508945102966706011335)
            ·
              refine ⟨11658763417654450059017003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7772508945102966706011335 11658763417654450059017003)
              ·
                refine ⟨17488145126481675088525505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11658763417654450059017003 17488145126481675088525505)
                ·
                  refine ⟨13116108844861256316394129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17488145126481675088525505 13116108844861256316394129)
                  ·
                    refine ⟨9837081633645942237295597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13116108844861256316394129 9837081633645942237295597)
                    ·
                      refine ⟨3688905612617228338985849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9837081633645942237295597 3688905612617228338985849)
                      ·
                        rfl

theorem cell23_7184118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_7184118 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184118 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184118 prefixEnd_7184118 := by exact prefixLift 7184118
  have htrace : WordTrace (prefixWord ++ tailWord_7184118) baseStart_7184118 baseEnd_7184118 := by
    simpa [prefixWord, tailWord_7184118, baseEnd_7184118] using wordTrace_append hprefix tailTrace_7184118
  have hstable : (prefixWord ++ tailWord_7184118).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184118).length < 2 ^ (prefixWord ++ tailWord_7184118).sum := by decide
  have hdescent : baseEnd_7184118 < baseStart_7184118 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184182 : List Nat := [5, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3]
def baseStart_7184182 : Nat := 118140960795 + 7184182 * 2 ^ 59
def prefixEnd_7184182 : Nat := 4983230072969 + 3 ^ 40 * 7184182 * 2
def baseEnd_7184182 : Nat := 3688938475379116088585555

theorem tailTrace_7184182 : CollatzResearch.WordTrace tailWord_7184182 prefixEnd_7184182 3688938475379116088585555 := by
  unfold tailWord_7184182
  simp only [CollatzResearch.WordTrace]
  refine ⟨16376790253683940590461675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174685762705962032964924533 16376790253683940590461675)
  ·
    refine ⟨24565185380525910885692513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16376790253683940590461675 24565185380525910885692513)
    ·
      refine ⟨18423889035394433164269385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24565185380525910885692513 18423889035394433164269385)
      ·
        refine ⟨13817916776545824873202039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18423889035394433164269385 13817916776545824873202039)
        ·
          refine ⟨20726875164818737309803059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13817916776545824873202039 20726875164818737309803059)
          ·
            refine ⟨31090312747228105964704589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20726875164818737309803059 31090312747228105964704589)
            ·
              refine ⟨11658867280210539736764221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31090312747228105964704589 11658867280210539736764221)
              ·
                refine ⟨4372075230078952401286583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11658867280210539736764221 4372075230078952401286583)
                ·
                  refine ⟨6558112845118428601929875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372075230078952401286583 6558112845118428601929875)
                  ·
                    refine ⟨9837169267677642902894813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6558112845118428601929875 9837169267677642902894813)
                    ·
                      refine ⟨3688938475379116088585555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9837169267677642902894813 3688938475379116088585555)
                      ·
                        rfl

theorem cell23_7184182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3].length) (baseStart_7184182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184182 prefixEnd_7184182 := by exact prefixLift 7184182
  have htrace : WordTrace (prefixWord ++ tailWord_7184182) baseStart_7184182 baseEnd_7184182 := by
    simpa [prefixWord, tailWord_7184182, baseEnd_7184182] using wordTrace_append hprefix tailTrace_7184182
  have hstable : (prefixWord ++ tailWord_7184182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184182).length < 2 ^ (prefixWord ++ tailWord_7184182).sum := by decide
  have hdescent : baseEnd_7184182 < baseStart_7184182 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184191 : List Nat := [1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 5]
def baseStart_7184191 : Nat := 118140960795 + 7184191 * 2 ^ 59
def prefixEnd_7184191 : Nat := 4983230072969 + 3 ^ 40 * 7184191 * 2
def baseEnd_7184191 : Nat := 3688943096705006553373013

theorem tailTrace_7184191 : CollatzResearch.WordTrace tailWord_7184191 prefixEnd_7184191 3688943096705006553373013 := by
  unfold tailWord_7184191
  simp only [CollatzResearch.WordTrace]
  refine ⟨262028972315910443984464427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174685981543940295989642951 262028972315910443984464427)
  ·
    refine ⟨393043458473865665976696641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262028972315910443984464427 393043458473865665976696641)
    ·
      refine ⟨294782593855399249482522481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393043458473865665976696641 294782593855399249482522481)
      ·
        refine ⟨221086945391549437111891861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294782593855399249482522481 221086945391549437111891861)
        ·
          refine ⟨10363450565228879864619931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 221086945391549437111891861 10363450565228879864619931)
          ·
            refine ⟨15545175847843319796929897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363450565228879864619931 15545175847843319796929897)
            ·
              refine ⟨11658881885882489847697423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15545175847843319796929897 11658881885882489847697423)
              ·
                refine ⟨17488322828823734771546135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11658881885882489847697423 17488322828823734771546135)
                ·
                  refine ⟨26232484243235602157319203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17488322828823734771546135 26232484243235602157319203)
                  ·
                    refine ⟨39348726364853403235978805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26232484243235602157319203 39348726364853403235978805)
                    ·
                      refine ⟨3688943096705006553373013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39348726364853403235978805 3688943096705006553373013)
                      ·
                        rfl

theorem cell23_7184191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 2, 1, 1, 1, 5].length) (baseStart_7184191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184191 prefixEnd_7184191 := by exact prefixLift 7184191
  have htrace : WordTrace (prefixWord ++ tailWord_7184191) baseStart_7184191 baseEnd_7184191 := by
    simpa [prefixWord, tailWord_7184191, baseEnd_7184191] using wordTrace_append hprefix tailTrace_7184191
  have hstable : (prefixWord ++ tailWord_7184191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184191).length < 2 ^ (prefixWord ++ tailWord_7184191).sum := by decide
  have hdescent : baseEnd_7184191 < baseStart_7184191 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184215 : List Nat := [1, 1, 3, 2, 5, 2, 2, 1, 2, 4]
def baseStart_7184215 : Nat := 118140960795 + 7184215 * 2 ^ 59
def prefixEnd_7184215 : Nat := 4983230072969 + 3 ^ 40 * 7184215 * 2
def baseEnd_7184215 : Nat := 1229651806746904819824301

theorem tailTrace_7184215 : CollatzResearch.WordTrace tailWord_7184215 prefixEnd_7184215 1229651806746904819824301 := by
  unfold tailWord_7184215
  simp only [CollatzResearch.WordTrace]
  refine ⟨262029847667823496083338099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174686565111882330722225399 262029847667823496083338099)
  ·
    refine ⟨393044771501735244125007149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262029847667823496083338099 393044771501735244125007149)
    ·
      refine ⟨147391789313150716546877681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393044771501735244125007149 147391789313150716546877681)
      ·
        refine ⟨110543841984863037410158261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147391789313150716546877681 110543841984863037410158261)
        ·
          refine ⟨10363485186080909757202337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110543841984863037410158261 10363485186080909757202337)
          ·
            refine ⟨7772613889560682317901753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10363485186080909757202337 7772613889560682317901753)
            ·
              refine ⟨5829460417170511738426315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7772613889560682317901753 5829460417170511738426315)
              ·
                refine ⟨8744190625755767607639473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829460417170511738426315 8744190625755767607639473)
                ·
                  refine ⟨6558142969316825705729605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8744190625755767607639473 6558142969316825705729605)
                  ·
                    refine ⟨1229651806746904819824301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6558142969316825705729605 1229651806746904819824301)
                    ·
                      rfl

theorem cell23_7184215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 5, 2, 2, 1, 2, 4].length) (baseStart_7184215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184215 prefixEnd_7184215 := by exact prefixLift 7184215
  have htrace : WordTrace (prefixWord ++ tailWord_7184215) baseStart_7184215 baseEnd_7184215 := by
    simpa [prefixWord, tailWord_7184215, baseEnd_7184215] using wordTrace_append hprefix tailTrace_7184215
  have hstable : (prefixWord ++ tailWord_7184215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184215).length < 2 ^ (prefixWord ++ tailWord_7184215).sum := by decide
  have hdescent : baseEnd_7184215 < baseStart_7184215 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184238 : List Nat := [4, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3]
def baseStart_7184238 : Nat := 118140960795 + 7184238 * 2 ^ 59
def prefixEnd_7184238 : Nat := 4983230072969 + 3 ^ 40 * 7184238 * 2
def baseEnd_7184238 : Nat := 3688967230295767869485297

theorem tailTrace_7184238 : CollatzResearch.WordTrace tailWord_7184238 prefixEnd_7184238 3688967230295767869485297 := by
  unfold tailWord_7184238
  simp only [CollatzResearch.WordTrace]
  refine ⟨32753835818342521376428171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174687124364493447340950245 32753835818342521376428171)
  ·
    refine ⟨49130753727513782064642257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32753835818342521376428171 49130753727513782064642257)
    ·
      refine ⟨36848065295635336548481693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49130753727513782064642257 36848065295635336548481693)
      ·
        refine ⟨13818024485863251205680635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36848065295635336548481693 13818024485863251205680635)
        ·
          refine ⟨20727036728794876808520953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13818024485863251205680635 20727036728794876808520953)
          ·
            refine ⟨15545277546596157606390715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20727036728794876808520953 15545277546596157606390715)
            ·
              refine ⟨23317916319894236409586073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15545277546596157606390715 23317916319894236409586073)
              ·
                refine ⟨17488437239920677307189555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23317916319894236409586073 17488437239920677307189555)
                ·
                  refine ⟨26232655859881015960784333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17488437239920677307189555 26232655859881015960784333)
                  ·
                    refine ⟨9837245947455380985294125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26232655859881015960784333 9837245947455380985294125)
                    ·
                      refine ⟨3688967230295767869485297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9837245947455380985294125 3688967230295767869485297)
                      ·
                        rfl

theorem cell23_7184238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3].length) (baseStart_7184238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184238 prefixEnd_7184238 := by exact prefixLift 7184238
  have htrace : WordTrace (prefixWord ++ tailWord_7184238) baseStart_7184238 baseEnd_7184238 := by
    simpa [prefixWord, tailWord_7184238, baseEnd_7184238] using wordTrace_append hprefix tailTrace_7184238
  have hstable : (prefixWord ++ tailWord_7184238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184238).length < 2 ^ (prefixWord ++ tailWord_7184238).sum := by decide
  have hdescent : baseEnd_7184238 < baseStart_7184238 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184261 : List Nat := [1, 3, 1, 1, 3, 2, 1, 2, 3, 4, 2]
def baseStart_7184261 : Nat := 118140960795 + 7184261 * 2 ^ 59
def prefixEnd_7184261 : Nat := 4983230072969 + 3 ^ 40 * 7184261 * 2
def baseEnd_7184261 : Nat := 3688979040350821279497691

theorem tailTrace_7184261 : CollatzResearch.WordTrace tailWord_7184261 prefixEnd_7184261 3688979040350821279497691 := by
  unfold tailWord_7184261
  simp only [CollatzResearch.WordTrace]
  refine ⟨262031525425656845939512637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174687683617104563959675091 262031525425656845939512637)
  ·
    refine ⟨98261822034621317227317239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262031525425656845939512637 98261822034621317227317239)
    ·
      refine ⟨147392733051931975840975859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98261822034621317227317239 147392733051931975840975859)
      ·
        refine ⟨221089099577897963761463789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147392733051931975840975859 221089099577897963761463789)
        ·
          refine ⟨82908412341711736410548921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221089099577897963761463789 82908412341711736410548921)
          ·
            refine ⟨62181309256283802307911691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82908412341711736410548921 62181309256283802307911691)
            ·
              refine ⟨93271963884425703461867537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62181309256283802307911691 93271963884425703461867537)
              ·
                refine ⟨69953972913319277596400653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93271963884425703461867537 69953972913319277596400653)
                ·
                  refine ⟨26232739842494729098650245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69953972913319277596400653 26232739842494729098650245)
                  ·
                    refine ⟨4918638720467761705996921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26232739842494729098650245 4918638720467761705996921)
                    ·
                      refine ⟨3688979040350821279497691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918638720467761705996921 3688979040350821279497691)
                      ·
                        rfl

theorem cell23_7184261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 2, 3, 4, 2].length) (baseStart_7184261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184261 prefixEnd_7184261 := by exact prefixLift 7184261
  have htrace : WordTrace (prefixWord ++ tailWord_7184261) baseStart_7184261 baseEnd_7184261 := by
    simpa [prefixWord, tailWord_7184261, baseEnd_7184261] using wordTrace_append hprefix tailTrace_7184261
  have hstable : (prefixWord ++ tailWord_7184261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184261).length < 2 ^ (prefixWord ++ tailWord_7184261).sum := by decide
  have hdescent : baseEnd_7184261 < baseStart_7184261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184318 : List Nat := [4, 2, 1, 1, 1, 3, 2, 4, 5]
def baseStart_7184318 : Nat := 118140960795 + 7184318 * 2 ^ 59
def prefixEnd_7184318 : Nat := 4983230072969 + 3 ^ 40 * 7184318 * 2
def baseEnd_7184318 : Nat := 409889812083125284053881

theorem tailTrace_7184318 : CollatzResearch.WordTrace tailWord_7184318 prefixEnd_7184318 409889812083125284053881 := by
  unfold tailWord_7184318
  simp only [CollatzResearch.WordTrace]
  refine ⟨32754200548306293084292201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174689069590966896449558405 32754200548306293084292201)
  ·
    refine ⟨24565650411229719813219151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32754200548306293084292201 24565650411229719813219151)
    ·
      refine ⟨36848475616844579719828727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24565650411229719813219151 36848475616844579719828727)
      ·
        refine ⟨55272713425266869579743091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36848475616844579719828727 55272713425266869579743091)
        ·
          refine ⟨82909070137900304369614637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55272713425266869579743091 82909070137900304369614637)
          ·
            refine ⟨31090901301712614138605489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82909070137900304369614637 31090901301712614138605489)
            ·
              refine ⟨23318175976284460603954117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31090901301712614138605489 23318175976284460603954117)
              ·
                refine ⟨4372157995553336363241397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 23318175976284460603954117 4372157995553336363241397)
                ·
                  refine ⟨409889812083125284053881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4372157995553336363241397 409889812083125284053881)
                  ·
                    rfl

theorem cell23_7184318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 2, 4, 5].length) (baseStart_7184318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184318 prefixEnd_7184318 := by exact prefixLift 7184318
  have htrace : WordTrace (prefixWord ++ tailWord_7184318) baseStart_7184318 baseEnd_7184318 := by
    simpa [prefixWord, tailWord_7184318, baseEnd_7184318] using wordTrace_append hprefix tailTrace_7184318
  have hstable : (prefixWord ++ tailWord_7184318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184318).length < 2 ^ (prefixWord ++ tailWord_7184318).sum := by decide
  have hdescent : baseEnd_7184318 < baseStart_7184318 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184344 : List Nat := [2, 1, 2, 2, 2, 2, 1, 1, 2, 8]
def baseStart_7184344 : Nat := 118140960795 + 7184344 * 2 ^ 59
def prefixEnd_7184344 : Nat := 4983230072969 + 3 ^ 40 * 7184344 * 2
def baseEnd_7184344 : Nat := 1229673886415048151586603

theorem tailTrace_7184344 : CollatzResearch.WordTrace tailWord_7184344 prefixEnd_7184344 1229673886415048151586603 := by
  unfold tailWord_7184344
  simp only [CollatzResearch.WordTrace]
  refine ⟨131017276342178075557392043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174689701789570767409856057 131017276342178075557392043)
  ·
    refine ⟨196525914513267113336088065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131017276342178075557392043 196525914513267113336088065)
    ·
      refine ⟨147394435884950335002066049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196525914513267113336088065 147394435884950335002066049)
      ·
        refine ⟨110545826913712751251549537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147394435884950335002066049 110545826913712751251549537)
        ·
          refine ⟨82909370185284563438662153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110545826913712751251549537 82909370185284563438662153)
          ·
            refine ⟨62182027638963422578996615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82909370185284563438662153 62182027638963422578996615)
            ·
              refine ⟨93273041458445133868494923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62182027638963422578996615 93273041458445133868494923)
              ·
                refine ⟨139909562187667700802742385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93273041458445133868494923 139909562187667700802742385)
                ·
                  refine ⟨104932171640750775602056789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139909562187667700802742385 104932171640750775602056789)
                  ·
                    refine ⟨1229673886415048151586603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 104932171640750775602056789 1229673886415048151586603)
                    ·
                      rfl

theorem cell23_7184344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_7184344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184344 prefixEnd_7184344 := by exact prefixLift 7184344
  have htrace : WordTrace (prefixWord ++ tailWord_7184344) baseStart_7184344 baseEnd_7184344 := by
    simpa [prefixWord, tailWord_7184344, baseEnd_7184344] using wordTrace_append hprefix tailTrace_7184344
  have hstable : (prefixWord ++ tailWord_7184344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184344).length < 2 ^ (prefixWord ++ tailWord_7184344).sum := by decide
  have hdescent : baseEnd_7184344 < baseStart_7184344 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184351 : List Nat := [1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 4]
def baseStart_7184351 : Nat := 118140960795 + 7184351 * 2 ^ 59
def prefixEnd_7184351 : Nat := 4983230072969 + 3 ^ 40 * 7184351 * 2
def baseEnd_7184351 : Nat := 3689025253609725927372277

theorem tailTrace_7184351 : CollatzResearch.WordTrace tailWord_7184351 prefixEnd_7184351 3689025253609725927372277 := by
  unfold tailWord_7184351
  simp only [CollatzResearch.WordTrace]
  refine ⟨262034807995330791310288907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174689871996887194206859271 262034807995330791310288907)
  ·
    refine ⟨393052211992996186965433361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262034807995330791310288907 393052211992996186965433361)
    ·
      refine ⟨294789158994747140224075021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393052211992996186965433361 294789158994747140224075021)
      ·
        refine ⟨110545934623030177584028133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294789158994747140224075021 110545934623030177584028133)
        ·
          refine ⟨20727362741818158297005275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110545934623030177584028133 20727362741818158297005275)
          ·
            refine ⟨31091044112727237445507913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20727362741818158297005275 31091044112727237445507913)
            ·
              refine ⟨23318283084545428084130935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31091044112727237445507913 23318283084545428084130935)
              ·
                refine ⟨34977424626818142126196403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23318283084545428084130935 34977424626818142126196403)
                ·
                  refine ⟨52466136940227213189294605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34977424626818142126196403 52466136940227213189294605)
                  ·
                    refine ⟨19674801352585204945985477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52466136940227213189294605 19674801352585204945985477)
                    ·
                      refine ⟨3689025253609725927372277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19674801352585204945985477 3689025253609725927372277)
                      ·
                        rfl

theorem cell23_7184351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_7184351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184351 prefixEnd_7184351 := by exact prefixLift 7184351
  have htrace : WordTrace (prefixWord ++ tailWord_7184351) baseStart_7184351 baseEnd_7184351 := by
    simpa [prefixWord, tailWord_7184351, baseEnd_7184351] using wordTrace_append hprefix tailTrace_7184351
  have hstable : (prefixWord ++ tailWord_7184351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184351).length < 2 ^ (prefixWord ++ tailWord_7184351).sum := by decide
  have hdescent : baseEnd_7184351 < baseStart_7184351 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184364 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_7184364 : Nat := 118140960795 + 7184364 * 2 ^ 59
def prefixEnd_7184364 : Nat := 4983230072969 + 3 ^ 40 * 7184364 * 2
def baseEnd_7184364 : Nat := 3689031928858234376509717

theorem tailTrace_7184364 : CollatzResearch.WordTrace tailWord_7184364 prefixEnd_7184364 3689031928858234376509717 := by
  unfold tailWord_7184364
  simp only [CollatzResearch.WordTrace]
  refine ⟨131017641072141847265256073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174690188096189129687008097 131017641072141847265256073)
  ·
    refine ⟨98263230804106385448942055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131017641072141847265256073 98263230804106385448942055)
    ·
      refine ⟨147394846206159578173413083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98263230804106385448942055 147394846206159578173413083)
      ·
        refine ⟨221092269309239367260119625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147394846206159578173413083 221092269309239367260119625)
        ·
          refine ⟨165819201981929525445089719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 221092269309239367260119625 165819201981929525445089719)
          ·
            refine ⟨248728802972894288167634579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165819201981929525445089719 248728802972894288167634579)
            ·
              refine ⟨373093204459341432251451869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248728802972894288167634579 373093204459341432251451869)
              ·
                refine ⟨139909951672253037094294451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 373093204459341432251451869 139909951672253037094294451)
                ·
                  refine ⟨209864927508379555641441677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139909951672253037094294451 209864927508379555641441677)
                  ·
                    refine ⟨78699347815642333365540629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 209864927508379555641441677 78699347815642333365540629)
                    ·
                      refine ⟨3689031928858234376509717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78699347815642333365540629 3689031928858234376509717)
                      ·
                        rfl

theorem cell23_7184364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_7184364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184364 prefixEnd_7184364 := by exact prefixLift 7184364
  have htrace : WordTrace (prefixWord ++ tailWord_7184364) baseStart_7184364 baseEnd_7184364 := by
    simpa [prefixWord, tailWord_7184364, baseEnd_7184364] using wordTrace_append hprefix tailTrace_7184364
  have hstable : (prefixWord ++ tailWord_7184364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184364).length < 2 ^ (prefixWord ++ tailWord_7184364).sum := by decide
  have hdescent : baseEnd_7184364 < baseStart_7184364 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184365 : List Nat := [1, 5, 1, 4, 1, 1, 1, 2, 2, 5]
def baseStart_7184365 : Nat := 118140960795 + 7184365 * 2 ^ 59
def prefixEnd_7184365 : Nat := 4983230072969 + 3 ^ 40 * 7184365 * 2
def baseEnd_7184365 : Nat := 1229677480779629624199071

theorem tailTrace_7184365 : CollatzResearch.WordTrace tailWord_7184365 prefixEnd_7184365 1229677480779629624199071 := by
  unfold tailWord_7184365
  simp only [CollatzResearch.WordTrace]
  refine ⟨262035318617280071701298549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174690212411520047800865699 262035318617280071701298549)
  ·
    refine ⟨24565811120370006721996739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262035318617280071701298549 24565811120370006721996739)
    ·
      refine ⟨36848716680555010082995109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24565811120370006721996739 36848716680555010082995109)
      ·
        refine ⟨6909134377604064390561583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 36848716680555010082995109 6909134377604064390561583)
        ·
          refine ⟨10363701566406096585842375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909134377604064390561583 10363701566406096585842375)
          ·
            refine ⟨15545552349609144878763563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363701566406096585842375 15545552349609144878763563)
            ·
              refine ⟨23318328524413717318145345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15545552349609144878763563 23318328524413717318145345)
              ·
                refine ⟨17488746393310287988609009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23318328524413717318145345 17488746393310287988609009)
                ·
                  refine ⟨13116559794982715991456757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17488746393310287988609009 13116559794982715991456757)
                  ·
                    refine ⟨1229677480779629624199071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13116559794982715991456757 1229677480779629624199071)
                    ·
                      rfl

theorem cell23_7184365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 1, 2, 2, 5].length) (baseStart_7184365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184365 prefixEnd_7184365 := by exact prefixLift 7184365
  have htrace : WordTrace (prefixWord ++ tailWord_7184365) baseStart_7184365 baseEnd_7184365 := by
    simpa [prefixWord, tailWord_7184365, baseEnd_7184365] using wordTrace_append hprefix tailTrace_7184365
  have hstable : (prefixWord ++ tailWord_7184365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184365).length < 2 ^ (prefixWord ++ tailWord_7184365).sum := by decide
  have hdescent : baseEnd_7184365 < baseStart_7184365 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184405 : List Nat := [1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_7184405 : Nat := 118140960795 + 7184405 * 2 ^ 59
def prefixEnd_7184405 : Nat := 4983230072969 + 3 ^ 40 * 7184405 * 2
def baseEnd_7184405 : Nat := 3689052981565068716097029

theorem tailTrace_7184405 : CollatzResearch.WordTrace tailWord_7184405 prefixEnd_7184405 3689052981565068716097029 := by
  unfold tailWord_7184405
  simp only [CollatzResearch.WordTrace]
  refine ⟨262036777537135158532754669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174691185024756772355169779 262036777537135158532754669)
  ·
    refine ⟨98263791576425684449783001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262036777537135158532754669 98263791576425684449783001)
    ·
      refine ⟨73697843682319263337337251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98263791576425684449783001 73697843682319263337337251)
      ·
        refine ⟨110546765523478895006005877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73697843682319263337337251 110546765523478895006005877)
        ·
          refine ⟨10363759267826146406813051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110546765523478895006005877 10363759267826146406813051)
          ·
            refine ⟨15545638901739219610219577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10363759267826146406813051 15545638901739219610219577)
            ·
              refine ⟨11659229176304414707664683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15545638901739219610219577 11659229176304414707664683)
              ·
                refine ⟨17488843764456622061497025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11659229176304414707664683 17488843764456622061497025)
                ·
                  refine ⟨13116632823342466546122769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17488843764456622061497025 13116632823342466546122769)
                  ·
                    refine ⟨9837474617506849909592077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13116632823342466546122769 9837474617506849909592077)
                    ·
                      refine ⟨3689052981565068716097029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9837474617506849909592077 3689052981565068716097029)
                      ·
                        rfl

theorem cell23_7184405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_7184405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184405 prefixEnd_7184405 := by exact prefixLift 7184405
  have htrace : WordTrace (prefixWord ++ tailWord_7184405) baseStart_7184405 baseEnd_7184405 := by
    simpa [prefixWord, tailWord_7184405, baseEnd_7184405] using wordTrace_append hprefix tailTrace_7184405
  have hstable : (prefixWord ++ tailWord_7184405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184405).length < 2 ^ (prefixWord ++ tailWord_7184405).sum := by decide
  have hdescent : baseEnd_7184405 < baseStart_7184405 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184428 : List Nat := [2, 2, 1, 1, 1, 2, 2, 3, 4, 3, 2]
def baseStart_7184428 : Nat := 118140960795 + 7184428 * 2 ^ 59
def prefixEnd_7184428 : Nat := 4983230072969 + 3 ^ 40 * 7184428 * 2
def baseEnd_7184428 : Nat := 3689064791620122126109423

theorem tailTrace_7184428 : CollatzResearch.WordTrace tailWord_7184428 prefixEnd_7184428 3689064791620122126109423 := by
  unfold tailWord_7184428
  simp only [CollatzResearch.WordTrace]
  refine ⟨131018808208025916730420969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174691744277367888973894625 131018808208025916730420969)
  ·
    refine ⟨98264106156019437547815727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131018808208025916730420969 98264106156019437547815727)
    ·
      refine ⟨147396159234029156321723591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98264106156019437547815727 147396159234029156321723591)
      ·
        refine ⟨221094238851043734482585387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147396159234029156321723591 221094238851043734482585387)
        ·
          refine ⟨331641358276565601723878081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221094238851043734482585387 331641358276565601723878081)
          ·
            refine ⟨248731018707424201292908561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331641358276565601723878081 248731018707424201292908561)
            ·
              refine ⟨186548264030568150969681421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248731018707424201292908561 186548264030568150969681421)
              ·
                refine ⟨69955599011463056613630533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 186548264030568150969681421 69955599011463056613630533)
                ·
                  refine ⟨13116674814649323115055725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 69955599011463056613630533 13116674814649323115055725)
                  ·
                    refine ⟨4918753055493496168145897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13116674814649323115055725 4918753055493496168145897)
                    ·
                      refine ⟨3689064791620122126109423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918753055493496168145897 3689064791620122126109423)
                      ·
                        rfl

theorem cell23_7184428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 3, 2].length) (baseStart_7184428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184428 prefixEnd_7184428 := by exact prefixLift 7184428
  have htrace : WordTrace (prefixWord ++ tailWord_7184428) baseStart_7184428 baseEnd_7184428 := by
    simpa [prefixWord, tailWord_7184428, baseEnd_7184428] using wordTrace_append hprefix tailTrace_7184428
  have hstable : (prefixWord ++ tailWord_7184428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184428).length < 2 ^ (prefixWord ++ tailWord_7184428).sum := by decide
  have hdescent : baseEnd_7184428 < baseStart_7184428 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184438 : List Nat := [5, 1, 2, 1, 1, 1, 1, 1, 5, 5]
def baseStart_7184438 : Nat := 118140960795 + 7184438 * 2 ^ 59
def prefixEnd_7184438 : Nat := 4983230072969 + 3 ^ 40 * 7184438 * 2
def baseEnd_7184438 : Nat := 1229689975475555695661459

theorem tailTrace_7184438 : CollatzResearch.WordTrace tailWord_7184438 prefixEnd_7184438 1229689975475555695661459 := by
  unfold tailWord_7184438
  simp only [CollatzResearch.WordTrace]
  refine ⟨16377373821625975323044123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174691987430677070112470645 16377373821625975323044123)
  ·
    refine ⟨24566060732438962984566185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16377373821625975323044123 24566060732438962984566185)
    ·
      refine ⟨18424545549329222238424639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24566060732438962984566185 18424545549329222238424639)
      ·
        refine ⟨27636818323993833357636959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18424545549329222238424639 27636818323993833357636959)
        ·
          refine ⟨41455227485990750036455439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27636818323993833357636959 41455227485990750036455439)
          ·
            refine ⟨62182841228986125054683159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41455227485990750036455439 62182841228986125054683159)
            ·
              refine ⟨93274261843479187582024739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62182841228986125054683159 93274261843479187582024739)
              ·
                refine ⟨139911392765218781373037109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93274261843479187582024739 139911392765218781373037109)
                ·
                  refine ⟨13116693071739260753722229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139911392765218781373037109 13116693071739260753722229)
                  ·
                    refine ⟨1229689975475555695661459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13116693071739260753722229 1229689975475555695661459)
                    ·
                      rfl

theorem cell23_7184438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 1, 1, 5, 5].length) (baseStart_7184438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184438 prefixEnd_7184438 := by exact prefixLift 7184438
  have htrace : WordTrace (prefixWord ++ tailWord_7184438) baseStart_7184438 baseEnd_7184438 := by
    simpa [prefixWord, tailWord_7184438, baseEnd_7184438] using wordTrace_append hprefix tailTrace_7184438
  have hstable : (prefixWord ++ tailWord_7184438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184438).length < 2 ^ (prefixWord ++ tailWord_7184438).sum := by decide
  have hdescent : baseEnd_7184438 < baseStart_7184438 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184458 : List Nat := [3, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4]
def baseStart_7184458 : Nat := 118140960795 + 7184458 * 2 ^ 59
def prefixEnd_7184458 : Nat := 4983230072969 + 3 ^ 40 * 7184458 * 2
def baseEnd_7184458 : Nat := 3689080196039757008734285

theorem tailTrace_7184458 : CollatzResearch.WordTrace tailWord_7184458 prefixEnd_7184458 3689080196039757008734285 := by
  unfold tailWord_7184458
  simp only [CollatzResearch.WordTrace]
  refine ⟨65509677651485787146108507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174692473737295432389622685 65509677651485787146108507)
  ·
    refine ⟨98264516477228680719162761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65509677651485787146108507 98264516477228680719162761)
    ·
      refine ⟨73698387357921510539372071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98264516477228680719162761 73698387357921510539372071)
      ·
        refine ⟨110547581036882265809058107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73698387357921510539372071 110547581036882265809058107)
        ·
          refine ⟨165821371555323398713587161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110547581036882265809058107 165821371555323398713587161)
          ·
            refine ⟨124366028666492549035190371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 165821371555323398713587161 124366028666492549035190371)
            ·
              refine ⟨186549042999738823552785557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124366028666492549035190371 186549042999738823552785557)
              ·
                refine ⟨8744486390612757354036823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 186549042999738823552785557 8744486390612757354036823)
                ·
                  refine ⟨13116729585919136031055235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8744486390612757354036823 13116729585919136031055235)
                  ·
                    refine ⟨19675094378878704046582853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13116729585919136031055235 19675094378878704046582853)
                    ·
                      refine ⟨3689080196039757008734285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19675094378878704046582853 3689080196039757008734285)
                      ·
                        rfl

theorem cell23_7184458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 6, 1, 1, 4].length) (baseStart_7184458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184458 prefixEnd_7184458 := by exact prefixLift 7184458
  have htrace : WordTrace (prefixWord ++ tailWord_7184458) baseStart_7184458 baseEnd_7184458 := by
    simpa [prefixWord, tailWord_7184458, baseEnd_7184458] using wordTrace_append hprefix tailTrace_7184458
  have hstable : (prefixWord ++ tailWord_7184458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184458).length < 2 ^ (prefixWord ++ tailWord_7184458).sum := by decide
  have hdescent : baseEnd_7184458 < baseStart_7184458 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184462 : List Nat := [4, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2]
def baseStart_7184462 : Nat := 118140960795 + 7184462 * 2 ^ 59
def prefixEnd_7184462 : Nat := 4983230072969 + 3 ^ 40 * 7184462 * 2
def baseEnd_7184462 : Nat := 3689082249962374993084267

theorem tailTrace_7184462 : CollatzResearch.WordTrace tailWord_7184462 prefixEnd_7184462 3689082249962374993084267 := by
  unfold tailWord_7184462
  simp only [CollatzResearch.WordTrace]
  refine ⟨32754857062241082158447455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174692570998619104845053093 32754857062241082158447455)
  ·
    refine ⟨49132285593361623237671183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32754857062241082158447455 49132285593361623237671183)
    ·
      refine ⟨73698428390042434856506775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49132285593361623237671183 73698428390042434856506775)
      ·
        refine ⟨110547642585063652284760163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73698428390042434856506775 110547642585063652284760163)
        ·
          refine ⟨165821463877595478427140245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110547642585063652284760163 165821463877595478427140245)
          ·
            refine ⟨7772881119262288051272199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 165821463877595478427140245 7772881119262288051272199)
            ·
              refine ⟨11659321678893432076908299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7772881119262288051272199 11659321678893432076908299)
              ·
                refine ⟨17488982518340148115362449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11659321678893432076908299 17488982518340148115362449)
                ·
                  refine ⟨13116736888755111086521837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17488982518340148115362449 13116736888755111086521837)
                  ·
                    refine ⟨4918776333283166657445689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13116736888755111086521837 4918776333283166657445689)
                    ·
                      refine ⟨3689082249962374993084267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918776333283166657445689 3689082249962374993084267)
                      ·
                        rfl

theorem cell23_7184462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 1, 1, 2, 3, 2].length) (baseStart_7184462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184462 prefixEnd_7184462 := by exact prefixLift 7184462
  have htrace : WordTrace (prefixWord ++ tailWord_7184462) baseStart_7184462 baseEnd_7184462 := by
    simpa [prefixWord, tailWord_7184462, baseEnd_7184462] using wordTrace_append hprefix tailTrace_7184462
  have hstable : (prefixWord ++ tailWord_7184462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184462).length < 2 ^ (prefixWord ++ tailWord_7184462).sum := by decide
  have hdescent : baseEnd_7184462 < baseStart_7184462 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184468 : List Nat := [2, 4, 1, 1, 1, 1, 1, 4, 4, 4]
def baseStart_7184468 : Nat := 118140960795 + 7184468 * 2 ^ 59
def prefixEnd_7184468 : Nat := 4983230072969 + 3 ^ 40 * 7184468 * 2
def baseEnd_7184468 : Nat := 1229695110282100656536413

theorem tailTrace_7184468 : CollatzResearch.WordTrace tailWord_7184468 prefixEnd_7184468 1229695110282100656536413 := by
  unfold tailWord_7184468
  simp only [CollatzResearch.WordTrace]
  refine ⟨131019537667953460146149029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174692716890604613528198705 131019537667953460146149029)
  ·
    refine ⟨24566163312741273777402943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131019537667953460146149029 24566163312741273777402943)
    ·
      refine ⟨36849244969111910666104415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24566163312741273777402943 36849244969111910666104415)
      ·
        refine ⟨55273867453667865999156623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36849244969111910666104415 55273867453667865999156623)
        ·
          refine ⟨82910801180501798998734935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55273867453667865999156623 82910801180501798998734935)
          ·
            refine ⟨124366201770752698498102403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82910801180501798998734935 124366201770752698498102403)
            ·
              refine ⟨186549302656129047747153605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124366201770752698498102403 186549302656129047747153605)
              ·
                refine ⟨34977994248024196452591301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186549302656129047747153605 34977994248024196452591301)
                ·
                  refine ⟨6558373921504536834860869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34977994248024196452591301 6558373921504536834860869)
                  ·
                    refine ⟨1229695110282100656536413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6558373921504536834860869 1229695110282100656536413)
                    ·
                      rfl

theorem cell23_7184468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 4, 4, 4].length) (baseStart_7184468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184468 prefixEnd_7184468 := by exact prefixLift 7184468
  have htrace : WordTrace (prefixWord ++ tailWord_7184468) baseStart_7184468 baseEnd_7184468 := by
    simpa [prefixWord, tailWord_7184468, baseEnd_7184468] using wordTrace_append hprefix tailTrace_7184468
  have hstable : (prefixWord ++ tailWord_7184468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184468).length < 2 ^ (prefixWord ++ tailWord_7184468).sum := by decide
  have hdescent : baseEnd_7184468 < baseStart_7184468 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184485 : List Nat := [1, 3, 1, 3, 2, 2, 3, 2, 2, 4]
def baseStart_7184485 : Nat := 118140960795 + 7184485 * 2 ^ 59
def prefixEnd_7184485 : Nat := 4983230072969 + 3 ^ 40 * 7184485 * 2
def baseEnd_7184485 : Nat := 1229698020005809467698887

theorem tailTrace_7184485 : CollatzResearch.WordTrace tailWord_7184485 prefixEnd_7184485 1229698020005809467698887 := by
  unfold tailWord_7184485
  simp only [CollatzResearch.WordTrace]
  refine ⟨262039695376845332195666909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174693130251230221463777939 262039695376845332195666909)
  ·
    refine ⟨98264885766316999573375091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262039695376845332195666909 98264885766316999573375091)
    ·
      refine ⟨147397328649475499360062637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98264885766316999573375091 147397328649475499360062637)
      ·
        refine ⟨55273998243553312260023489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147397328649475499360062637 55273998243553312260023489)
        ·
          refine ⟨41455498682664984195017617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55273998243553312260023489 41455498682664984195017617)
          ·
            refine ⟨31091624011998738146263213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41455498682664984195017617 31091624011998738146263213)
            ·
              refine ⟨11659359004499526804848705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 31091624011998738146263213 11659359004499526804848705)
              ·
                refine ⟨8744519253374645103636529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11659359004499526804848705 8744519253374645103636529)
                ·
                  refine ⟨6558389440030983827727397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8744519253374645103636529 6558389440030983827727397)
                  ·
                    refine ⟨1229698020005809467698887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6558389440030983827727397 1229698020005809467698887)
                    ·
                      rfl

theorem cell23_7184485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_7184485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184485 prefixEnd_7184485 := by exact prefixLift 7184485
  have htrace : WordTrace (prefixWord ++ tailWord_7184485) baseStart_7184485 baseEnd_7184485 := by
    simpa [prefixWord, tailWord_7184485, baseEnd_7184485] using wordTrace_append hprefix tailTrace_7184485
  have hstable : (prefixWord ++ tailWord_7184485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184485).length < 2 ^ (prefixWord ++ tailWord_7184485).sum := by decide
  have hdescent : baseEnd_7184485 < baseStart_7184485 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184491 : List Nat := [1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 3]
def baseStart_7184491 : Nat := 118140960795 + 7184491 * 2 ^ 59
def prefixEnd_7184491 : Nat := 4983230072969 + 3 ^ 40 * 7184491 * 2
def baseEnd_7184491 : Nat := 3689097140901355379621633

theorem tailTrace_7184491 : CollatzResearch.WordTrace tailWord_7184491 prefixEnd_7184491 3689097140901355379621633 := by
  unfold tailWord_7184491
  simp only [CollatzResearch.WordTrace]
  refine ⟨262039914214823595220385327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174693276143215730146923551 262039914214823595220385327)
  ·
    refine ⟨393059871322235392830577991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262039914214823595220385327 393059871322235392830577991)
    ·
      refine ⟨589589806983353089245866987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393059871322235392830577991 589589806983353089245866987)
      ·
        refine ⟨884384710475029633868800481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589589806983353089245866987 884384710475029633868800481)
        ·
          refine ⟨663288532856272225401600361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884384710475029633868800481 663288532856272225401600361)
          ·
            refine ⟨497466399642204169051200271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663288532856272225401600361 497466399642204169051200271)
            ·
              refine ⟨746199599463306253576800407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497466399642204169051200271 746199599463306253576800407)
              ·
                refine ⟨1119299399194959380365200611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 746199599463306253576800407 1119299399194959380365200611)
                ·
                  refine ⟨1678949098792439070547800917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1119299399194959380365200611 1678949098792439070547800917)
                  ·
                    refine ⟨9837592375736947678991021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 1678949098792439070547800917 9837592375736947678991021)
                    ·
                      refine ⟨3689097140901355379621633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9837592375736947678991021 3689097140901355379621633)
                      ·
                        rfl

theorem cell23_7184491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 9, 3].length) (baseStart_7184491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184491 prefixEnd_7184491 := by exact prefixLift 7184491
  have htrace : WordTrace (prefixWord ++ tailWord_7184491) baseStart_7184491 baseEnd_7184491 := by
    simpa [prefixWord, tailWord_7184491, baseEnd_7184491] using wordTrace_append hprefix tailTrace_7184491
  have hstable : (prefixWord ++ tailWord_7184491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184491).length < 2 ^ (prefixWord ++ tailWord_7184491).sum := by decide
  have hdescent : baseEnd_7184491 < baseStart_7184491 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184492 : List Nat := [2, 2, 1, 1, 3, 4, 2, 1, 3, 2, 2]
def baseStart_7184492 : Nat := 118140960795 + 7184492 * 2 ^ 59
def prefixEnd_7184492 : Nat := 4983230072969 + 3 ^ 40 * 7184492 * 2
def baseEnd_7184492 : Nat := 3689097654382009875709129

theorem tailTrace_7184492 : CollatzResearch.WordTrace tailWord_7184492 prefixEnd_7184492 3689097654382009875709129 := by
  unfold tailWord_7184492
  simp only [CollatzResearch.WordTrace]
  refine ⟨131019975343909986195585865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174693300458546648260781153 131019975343909986195585865)
  ·
    refine ⟨98264981507932489646689399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131019975343909986195585865 98264981507932489646689399)
    ·
      refine ⟨147397472261898734470034099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98264981507932489646689399 147397472261898734470034099)
      ·
        refine ⟨221096208392848101705051149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147397472261898734470034099 221096208392848101705051149)
        ·
          refine ⟨82911078147318038139394181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221096208392848101705051149 82911078147318038139394181)
          ·
            refine ⟨15545827152622132151136409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82911078147318038139394181 15545827152622132151136409)
            ·
              refine ⟨11659370364466599113352307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15545827152622132151136409 11659370364466599113352307)
              ·
                refine ⟨17489055546699898670028461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11659370364466599113352307 17489055546699898670028461)
                ·
                  refine ⟨6558395830012462001260673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17489055546699898670028461 6558395830012462001260673)
                  ·
                    refine ⟨4918796872509346500945505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6558395830012462001260673 4918796872509346500945505)
                    ·
                      refine ⟨3689097654382009875709129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918796872509346500945505 3689097654382009875709129)
                      ·
                        rfl

theorem cell23_7184492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 2, 2].length) (baseStart_7184492 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184492 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184492 prefixEnd_7184492 := by exact prefixLift 7184492
  have htrace : WordTrace (prefixWord ++ tailWord_7184492) baseStart_7184492 baseEnd_7184492 := by
    simpa [prefixWord, tailWord_7184492, baseEnd_7184492] using wordTrace_append hprefix tailTrace_7184492
  have hstable : (prefixWord ++ tailWord_7184492).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184492).length < 2 ^ (prefixWord ++ tailWord_7184492).sum := by decide
  have hdescent : baseEnd_7184492 < baseStart_7184492 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184505 : List Nat := [1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 4]
def baseStart_7184505 : Nat := 118140960795 + 7184505 * 2 ^ 59
def prefixEnd_7184505 : Nat := 4983230072969 + 3 ^ 40 * 7184505 * 2
def baseEnd_7184505 : Nat := 3689104329630518324846569

theorem tailTrace_7184505 : CollatzResearch.WordTrace tailWord_7184505 prefixEnd_7184505 3689104329630518324846569 := by
  unfold tailWord_7184505
  simp only [CollatzResearch.WordTrace]
  refine ⟨262040424836772875611394969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174693616557848583740929979 262040424836772875611394969)
  ·
    refine ⟨196530318627579656708546227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262040424836772875611394969 196530318627579656708546227)
    ·
      refine ⟨294795477941369485062819341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196530318627579656708546227 294795477941369485062819341)
      ·
        refine ⟨110548304228013556898557253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294795477941369485062819341 110548304228013556898557253)
        ·
          refine ⟨20727807042752541918479485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110548304228013556898557253 20727807042752541918479485)
          ·
            refine ⟨7772927641032203219429807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20727807042752541918479485 7772927641032203219429807)
            ·
              refine ⟨11659391461548304829144711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7772927641032203219429807 11659391461548304829144711)
              ·
                refine ⟨17489087192322457243717067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11659391461548304829144711 17489087192322457243717067)
                ·
                  refine ⟨26233630788483685865575601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17489087192322457243717067 26233630788483685865575601)
                  ·
                    refine ⟨19675223091362764399181701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26233630788483685865575601 19675223091362764399181701)
                    ·
                      refine ⟨3689104329630518324846569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19675223091362764399181701 3689104329630518324846569)
                      ·
                        rfl

theorem cell23_7184505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 2, 4].length) (baseStart_7184505 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184505 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184505 prefixEnd_7184505 := by exact prefixLift 7184505
  have htrace : WordTrace (prefixWord ++ tailWord_7184505) baseStart_7184505 baseEnd_7184505 := by
    simpa [prefixWord, tailWord_7184505, baseEnd_7184505] using wordTrace_append hprefix tailTrace_7184505
  have hstable : (prefixWord ++ tailWord_7184505).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184505).length < 2 ^ (prefixWord ++ tailWord_7184505).sum := by decide
  have hdescent : baseEnd_7184505 < baseStart_7184505 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184521 : List Nat := [1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 5]
def baseStart_7184521 : Nat := 118140960795 + 7184521 * 2 ^ 59
def prefixEnd_7184521 : Nat := 4983230072969 + 3 ^ 40 * 7184521 * 2
def baseEnd_7184521 : Nat := 3689112545320990262246495

theorem tailTrace_7184521 : CollatzResearch.WordTrace tailWord_7184521 prefixEnd_7184521 3689112545320990262246495 := by
  unfold tailWord_7184521
  simp only [CollatzResearch.WordTrace]
  refine ⟨262041008404714910343977417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174694005603143273562651611 262041008404714910343977417)
  ·
    refine ⟨196530756303536182757983063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262041008404714910343977417 196530756303536182757983063)
    ·
      refine ⟨294796134455304274136974595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196530756303536182757983063 294796134455304274136974595)
      ·
        refine ⟨442194201682956411205461893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294796134455304274136974595 442194201682956411205461893)
        ·
          refine ⟨82911412815554327101024105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442194201682956411205461893 82911412815554327101024105)
          ·
            refine ⟨62183559611665745325768079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82911412815554327101024105 62183559611665745325768079)
            ·
              refine ⟨93275339417498617988652119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62183559611665745325768079 93275339417498617988652119)
              ·
                refine ⟨139913009126247926982978179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93275339417498617988652119 139913009126247926982978179)
                ·
                  refine ⟨209869513689371890474467269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139913009126247926982978179 209869513689371890474467269)
                  ·
                    refine ⟨39350533816757229463962613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 209869513689371890474467269 39350533816757229463962613)
                    ·
                      refine ⟨3689112545320990262246495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39350533816757229463962613 3689112545320990262246495)
                      ·
                        rfl

theorem cell23_7184521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 1, 1, 4, 5].length) (baseStart_7184521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184521 prefixEnd_7184521 := by exact prefixLift 7184521
  have htrace : WordTrace (prefixWord ++ tailWord_7184521) baseStart_7184521 baseEnd_7184521 := by
    simpa [prefixWord, tailWord_7184521, baseEnd_7184521] using wordTrace_append hprefix tailTrace_7184521
  have hstable : (prefixWord ++ tailWord_7184521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184521).length < 2 ^ (prefixWord ++ tailWord_7184521).sum := by decide
  have hdescent : baseEnd_7184521 < baseStart_7184521 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184531 : List Nat := [1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4]
def baseStart_7184531 : Nat := 118140960795 + 7184531 * 2 ^ 59
def prefixEnd_7184531 : Nat := 4983230072969 + 3 ^ 40 * 7184531 * 2
def baseEnd_7184531 : Nat := 3689117680127535223121449

theorem tailTrace_7184531 : CollatzResearch.WordTrace tailWord_7184531 prefixEnd_7184531 3689117680127535223121449 := by
  unfold tailWord_7184531
  simp only [CollatzResearch.WordTrace]
  refine ⟨262041373134678682051841447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174694248756452454701227631 262041373134678682051841447)
  ·
    refine ⟨393062059702018023077762171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262041373134678682051841447 393062059702018023077762171)
    ·
      refine ⟨589593089553027034616643257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393062059702018023077762171 589593089553027034616643257)
      ·
        refine ⟨442194817164770275962482443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589593089553027034616643257 442194817164770275962482443)
        ·
          refine ⟨663292225747155413943723665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442194817164770275962482443 663292225747155413943723665)
          ·
            refine ⟨497469169310366560457792749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663292225747155413943723665 497469169310366560457792749)
            ·
              refine ⟨186550938491387460171672281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497469169310366560457792749 186550938491387460171672281)
              ·
                refine ⟨139913203868540595128754211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 186550938491387460171672281 139913203868540595128754211)
                ·
                  refine ⟨209869805802810892693131317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139913203868540595128754211 209869805802810892693131317)
                  ·
                    refine ⟨19675294294013521189981061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 209869805802810892693131317 19675294294013521189981061)
                    ·
                      refine ⟨3689117680127535223121449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19675294294013521189981061 3689117680127535223121449)
                      ·
                        rfl

theorem cell23_7184531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 5, 4].length) (baseStart_7184531 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184531 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184531 prefixEnd_7184531 := by exact prefixLift 7184531
  have htrace : WordTrace (prefixWord ++ tailWord_7184531) baseStart_7184531 baseEnd_7184531 := by
    simpa [prefixWord, tailWord_7184531, baseEnd_7184531] using wordTrace_append hprefix tailTrace_7184531
  have hstable : (prefixWord ++ tailWord_7184531).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184531).length < 2 ^ (prefixWord ++ tailWord_7184531).sum := by decide
  have hdescent : baseEnd_7184531 < baseStart_7184531 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184532 : List Nat := [2, 4, 2, 3, 2, 1, 9]
def baseStart_7184532 : Nat := 118140960795 + 7184532 * 2 ^ 59
def prefixEnd_7184532 : Nat := 4983230072969 + 3 ^ 40 * 7184532 * 2
def baseEnd_7184532 : Nat := 45544669056891231101345

theorem tailTrace_7184532 : CollatzResearch.WordTrace tailWord_7184532 prefixEnd_7184532 45544669056891231101345 := by
  unfold tailWord_7184532
  simp only [CollatzResearch.WordTrace]
  refine ⟨131020704803837529611313925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174694273071783372815085233 131020704803837529611313925)
  ·
    refine ⟨24566382150719536802121361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 131020704803837529611313925 24566382150719536802121361)
    ·
      refine ⟨18424786613039652601591021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24566382150719536802121361 18424786613039652601591021)
      ·
        refine ⟨6909294979889869725596633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 18424786613039652601591021 6909294979889869725596633)
        ·
          refine ⟨5181971234917402294197475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6909294979889869725596633 5181971234917402294197475)
          ·
            refine ⟨7772956852376103441296213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5181971234917402294197475 7772956852376103441296213)
            ·
              refine ⟨45544669056891231101345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7772956852376103441296213 45544669056891231101345)
              ·
                rfl

theorem cell23_7184532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 9].length) (baseStart_7184532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184532 prefixEnd_7184532 := by exact prefixLift 7184532
  have htrace : WordTrace (prefixWord ++ tailWord_7184532) baseStart_7184532 baseEnd_7184532 := by
    simpa [prefixWord, tailWord_7184532, baseEnd_7184532] using wordTrace_append hprefix tailTrace_7184532
  have hstable : (prefixWord ++ tailWord_7184532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184532).length < 2 ^ (prefixWord ++ tailWord_7184532).sum := by decide
  have hdescent : baseEnd_7184532 < baseStart_7184532 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184571 : List Nat := [1, 1, 1, 1, 1, 2, 6, 1, 9]
def baseStart_7184571 : Nat := 118140960795 + 7184571 * 2 ^ 59
def prefixEnd_7184571 : Nat := 4983230072969 + 3 ^ 40 * 7184571 * 2
def baseEnd_7184571 : Nat := 409904246594857229624585

theorem tailTrace_7184571 : CollatzResearch.WordTrace tailWord_7184571 prefixEnd_7184571 409904246594857229624585 := by
  unfold tailWord_7184571
  simp only [CollatzResearch.WordTrace]
  refine ⟨262042832054533768883297567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174695221369689179255531711 262042832054533768883297567)
  ·
    refine ⟨393064248081800653324946351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262042832054533768883297567 393064248081800653324946351)
    ·
      refine ⟨589596372122700979987419527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393064248081800653324946351 589596372122700979987419527)
      ·
        refine ⟨884394558184051469981129291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589596372122700979987419527 884394558184051469981129291)
        ·
          refine ⟨1326591837276077204971693937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884394558184051469981129291 1326591837276077204971693937)
          ·
            refine ⟨994943877957057903728770453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1326591837276077204971693937 994943877957057903728770453)
            ·
              refine ⟨46637994279237089237286115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 994943877957057903728770453 46637994279237089237286115)
              ·
                refine ⟨69956991418855633855929173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46637994279237089237286115 69956991418855633855929173)
                ·
                  refine ⟨409904246594857229624585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 69956991418855633855929173 409904246594857229624585)
                  ·
                    rfl

theorem cell23_7184571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 1, 9].length) (baseStart_7184571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184571 prefixEnd_7184571 := by exact prefixLift 7184571
  have htrace : WordTrace (prefixWord ++ tailWord_7184571) baseStart_7184571 baseEnd_7184571 := by
    simpa [prefixWord, tailWord_7184571, baseEnd_7184571] using wordTrace_append hprefix tailTrace_7184571
  have hstable : (prefixWord ++ tailWord_7184571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184571).length < 2 ^ (prefixWord ++ tailWord_7184571).sum := by decide
  have hdescent : baseEnd_7184571 < baseStart_7184571 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184615 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 3]
def baseStart_7184615 : Nat := 118140960795 + 7184615 * 2 ^ 59
def prefixEnd_7184615 : Nat := 4983230072969 + 3 ^ 40 * 7184615 * 2
def baseEnd_7184615 : Nat := 3689160812502512894471063

theorem tailTrace_7184615 : CollatzResearch.WordTrace tailWord_7184615 prefixEnd_7184615 3689160812502512894471063 := by
  unfold tailWord_7184615
  simp only [CollatzResearch.WordTrace]
  refine ⟨262044436866374364397899299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174696291244249576265266199 262044436866374364397899299)
  ·
    refine ⟨393066655299561546596848949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262044436866374364397899299 393066655299561546596848949)
    ·
      refine ⟨36849998934333894993454589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 393066655299561546596848949 36849998934333894993454589)
      ·
        refine ⟨13818749600375210622545471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36849998934333894993454589 13818749600375210622545471)
        ·
          refine ⟨20728124400562815933818207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13818749600375210622545471 20728124400562815933818207)
          ·
            refine ⟨31092186600844223900727311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728124400562815933818207 31092186600844223900727311)
            ·
              refine ⟨46638279901266335851090967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31092186600844223900727311 46638279901266335851090967)
              ·
                refine ⟨69957419851899503776636451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46638279901266335851090967 69957419851899503776636451)
                ·
                  refine ⟨104936129777849255664954677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69957419851899503776636451 104936129777849255664954677)
                  ·
                    refine ⟨9837762166673367718589501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104936129777849255664954677 9837762166673367718589501)
                    ·
                      refine ⟨3689160812502512894471063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9837762166673367718589501 3689160812502512894471063)
                      ·
                        rfl

theorem cell23_7184615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_7184615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184615 prefixEnd_7184615 := by exact prefixLift 7184615
  have htrace : WordTrace (prefixWord ++ tailWord_7184615) baseStart_7184615 baseEnd_7184615 := by
    simpa [prefixWord, tailWord_7184615, baseEnd_7184615] using wordTrace_append hprefix tailTrace_7184615
  have hstable : (prefixWord ++ tailWord_7184615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184615).length < 2 ^ (prefixWord ++ tailWord_7184615).sum := by decide
  have hdescent : baseEnd_7184615 < baseStart_7184615 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184618 : List Nat := [3, 1, 3, 1, 1, 2, 2, 2, 1, 7]
def baseStart_7184618 : Nat := 118140960795 + 7184618 * 2 ^ 59
def prefixEnd_7184618 : Nat := 4983230072969 + 3 ^ 40 * 7184618 * 2
def baseEnd_7184618 : Nat := 1229720784314825460911183

theorem tailTrace_7184618 : CollatzResearch.WordTrace tailWord_7184618 prefixEnd_7184618 1229720784314825460911183 := by
  unfold tailWord_7184618
  simp only [CollatzResearch.WordTrace]
  refine ⟨65511136571340873977564627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174696364190242330606839005 65511136571340873977564627)
  ·
    refine ⟨98266704857011310966346941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65511136571340873977564627 98266704857011310966346941)
    ·
      refine ⟨36850014321379241612380103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98266704857011310966346941 36850014321379241612380103)
      ·
        refine ⟨55275021482068862418570155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36850014321379241612380103 55275021482068862418570155)
        ·
          refine ⟨82912532223103293627855233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55275021482068862418570155 82912532223103293627855233)
          ·
            refine ⟨62184399167327470220891425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82912532223103293627855233 62184399167327470220891425)
            ·
              refine ⟨46638299375495602665668569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62184399167327470220891425 46638299375495602665668569)
              ·
                refine ⟨34978724531621701999251427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46638299375495602665668569 34978724531621701999251427)
                ·
                  refine ⟨52468086797432552998877141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34978724531621701999251427 52468086797432552998877141)
                  ·
                    refine ⟨1229720784314825460911183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52468086797432552998877141 1229720784314825460911183)
                    ·
                      rfl

theorem cell23_7184618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 2, 1, 7].length) (baseStart_7184618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184618 prefixEnd_7184618 := by exact prefixLift 7184618
  have htrace : WordTrace (prefixWord ++ tailWord_7184618) baseStart_7184618 baseEnd_7184618 := by
    simpa [prefixWord, tailWord_7184618, baseEnd_7184618] using wordTrace_append hprefix tailTrace_7184618
  have hstable : (prefixWord ++ tailWord_7184618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184618).length < 2 ^ (prefixWord ++ tailWord_7184618).sum := by decide
  have hdescent : baseEnd_7184618 < baseStart_7184618 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184668 : List Nat := [2, 2, 3, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_7184668 : Nat := 118140960795 + 7184668 * 2 ^ 59
def prefixEnd_7184668 : Nat := 4983230072969 + 3 ^ 40 * 7184668 * 2
def baseEnd_7184668 : Nat := 3689188026977201187108319

theorem tailTrace_7184668 : CollatzResearch.WordTrace tailWord_7184668 prefixEnd_7184668 3689188026977201187108319 := by
  unfold tailWord_7184668
  simp only [CollatzResearch.WordTrace]
  refine ⟨131023184967591177224789329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174697579956788236299719105 131023184967591177224789329)
  ·
    refine ⟨98267388725693382918591997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131023184967591177224789329 98267388725693382918591997)
    ·
      refine ⟨36850270772135018594471999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98267388725693382918591997 36850270772135018594471999)
      ·
        refine ⟨55275406158202527891707999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36850270772135018594471999 55275406158202527891707999)
        ·
          refine ⟨82913109237303791837561999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55275406158202527891707999 82913109237303791837561999)
          ·
            refine ⟨124369663855955687756342999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82913109237303791837561999 124369663855955687756342999)
            ·
              refine ⟨186554495783933531634514499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 124369663855955687756342999 186554495783933531634514499)
              ·
                refine ⟨279831743675900297451771749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186554495783933531634514499 279831743675900297451771749)
                ·
                  refine ⟨52468451939231305772207203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 279831743675900297451771749 52468451939231305772207203)
                  ·
                    refine ⟨78702677908846958658310805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52468451939231305772207203 78702677908846958658310805)
                    ·
                      refine ⟨3689188026977201187108319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78702677908846958658310805 3689188026977201187108319)
                      ·
                        rfl

theorem cell23_7184668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_7184668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184668 prefixEnd_7184668 := by exact prefixLift 7184668
  have htrace : WordTrace (prefixWord ++ tailWord_7184668) baseStart_7184668 baseEnd_7184668 := by
    simpa [prefixWord, tailWord_7184668, baseEnd_7184668] using wordTrace_append hprefix tailTrace_7184668
  have hstable : (prefixWord ++ tailWord_7184668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184668).length < 2 ^ (prefixWord ++ tailWord_7184668).sum := by decide
  have hdescent : baseEnd_7184668 < baseStart_7184668 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184672 : List Nat := [2, 1, 1, 5, 2, 1, 2, 1, 2, 4, 2]
def baseStart_7184672 : Nat := 118140960795 + 7184672 * 2 ^ 59
def prefixEnd_7184672 : Nat := 4983230072969 + 3 ^ 40 * 7184672 * 2
def baseEnd_7184672 : Nat := 3689190080899819171458301

theorem tailTrace_7184672 : CollatzResearch.WordTrace tailWord_7184672 prefixEnd_7184672 3689190080899819171458301 := by
  unfold tailWord_7184672
  simp only [CollatzResearch.WordTrace]
  refine ⟨131023257913583931566362135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174697677218111908755149513 131023257913583931566362135)
  ·
    refine ⟨196534886870375897349543203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131023257913583931566362135 196534886870375897349543203)
    ·
      refine ⟨294802330305563846024314805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196534886870375897349543203 294802330305563846024314805)
      ·
        refine ⟨27637718466146610564779513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 294802330305563846024314805 27637718466146610564779513)
        ·
          refine ⟨20728288849609957923584635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27637718466146610564779513 20728288849609957923584635)
          ·
            refine ⟨31092433274414936885376953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728288849609957923584635 31092433274414936885376953)
            ·
              refine ⟨23319324955811202664032715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31092433274414936885376953 23319324955811202664032715)
              ·
                refine ⟨34978987433716803996049073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23319324955811202664032715 34978987433716803996049073)
                ·
                  refine ⟨26234240575287602997036805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34978987433716803996049073 26234240575287602997036805)
                  ·
                    refine ⟨4918920107866425561944401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26234240575287602997036805 4918920107866425561944401)
                    ·
                      refine ⟨3689190080899819171458301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918920107866425561944401 3689190080899819171458301)
                      ·
                        rfl

theorem cell23_7184672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 1, 2, 4, 2].length) (baseStart_7184672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184672 prefixEnd_7184672 := by exact prefixLift 7184672
  have htrace : WordTrace (prefixWord ++ tailWord_7184672) baseStart_7184672 baseEnd_7184672 := by
    simpa [prefixWord, tailWord_7184672, baseEnd_7184672] using wordTrace_append hprefix tailTrace_7184672
  have hstable : (prefixWord ++ tailWord_7184672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184672).length < 2 ^ (prefixWord ++ tailWord_7184672).sum := by decide
  have hdescent : baseEnd_7184672 < baseStart_7184672 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184692 : List Nat := [2, 5, 1, 1, 1, 2, 2, 1, 1, 4, 3]
def baseStart_7184692 : Nat := 118140960795 + 7184692 * 2 ^ 59
def prefixEnd_7184692 : Nat := 4983230072969 + 3 ^ 40 * 7184692 * 2
def baseEnd_7184692 : Nat := 3689200350512909093208209

theorem tailTrace_7184692 : CollatzResearch.WordTrace tailWord_7184692 prefixEnd_7184692 3689200350512909093208209 := by
  unfold tailWord_7184692
  simp only [CollatzResearch.WordTrace]
  refine ⟨131023622643547703274226165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174698163524730271032301553 131023622643547703274226165)
  ·
    refine ⟨12283464622832597181958703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131023622643547703274226165 12283464622832597181958703)
    ·
      refine ⟨18425196934248895772938055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12283464622832597181958703 18425196934248895772938055)
      ·
        refine ⟨27637795401373343659407083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18425196934248895772938055 27637795401373343659407083)
        ·
          refine ⟨41456693102060015489110625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27637795401373343659407083 41456693102060015489110625)
          ·
            refine ⟨31092519826545011616832969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41456693102060015489110625 31092519826545011616832969)
            ·
              refine ⟨23319389869908758712624727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31092519826545011616832969 23319389869908758712624727)
              ·
                refine ⟨34979084804863138068937091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23319389869908758712624727 34979084804863138068937091)
                ·
                  refine ⟨52468627207294707103405637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34979084804863138068937091 52468627207294707103405637)
                  ·
                    refine ⟨9837867601367757581888557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52468627207294707103405637 9837867601367757581888557)
                    ·
                      refine ⟨3689200350512909093208209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9837867601367757581888557 3689200350512909093208209)
                      ·
                        rfl

theorem cell23_7184692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_7184692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184692 prefixEnd_7184692 := by exact prefixLift 7184692
  have htrace : WordTrace (prefixWord ++ tailWord_7184692) baseStart_7184692 baseEnd_7184692 := by
    simpa [prefixWord, tailWord_7184692, baseEnd_7184692] using wordTrace_append hprefix tailTrace_7184692
  have hstable : (prefixWord ++ tailWord_7184692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184692).length < 2 ^ (prefixWord ++ tailWord_7184692).sum := by decide
  have hdescent : baseEnd_7184692 < baseStart_7184692 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184715 : List Nat := [1, 1, 1, 1, 3, 1, 1, 4, 3, 5, 2]
def baseStart_7184715 : Nat := 118140960795 + 7184715 * 2 ^ 59
def prefixEnd_7184715 : Nat := 4983230072969 + 3 ^ 40 * 7184715 * 2
def baseEnd_7184715 : Nat := 3689212160567962503220603

theorem tailTrace_7184715 : CollatzResearch.WordTrace tailWord_7184715 prefixEnd_7184715 3689212160567962503220603 := by
  unfold tailWord_7184715
  simp only [CollatzResearch.WordTrace]
  refine ⟨262048084166012081476539599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174698722777341387651026399 262048084166012081476539599)
  ·
    refine ⟨393072126249018122214809399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262048084166012081476539599 393072126249018122214809399)
    ·
      refine ⟨589608189373527183322214099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393072126249018122214809399 589608189373527183322214099)
      ·
        refine ⟨884412284060290774983321149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589608189373527183322214099 884412284060290774983321149)
        ·
          refine ⟨331654606522609040618745431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 884412284060290774983321149 331654606522609040618745431)
          ·
            refine ⟨497481909783913560928118147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331654606522609040618745431 497481909783913560928118147)
            ·
              refine ⟨746222864675870341392177221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497481909783913560928118147 746222864675870341392177221)
              ·
                refine ⟨139916787126725689011033229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746222864675870341392177221 139916787126725689011033229)
                ·
                  refine ⟨52468795172522133379137461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139916787126725689011033229 52468795172522133379137461)
                  ·
                    refine ⟨4918949547423950004294137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 52468795172522133379137461 4918949547423950004294137)
                    ·
                      refine ⟨3689212160567962503220603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918949547423950004294137 3689212160567962503220603)
                      ·
                        rfl

theorem cell23_7184715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 5, 2].length) (baseStart_7184715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184715 prefixEnd_7184715 := by exact prefixLift 7184715
  have htrace : WordTrace (prefixWord ++ tailWord_7184715) baseStart_7184715 baseEnd_7184715 := by
    simpa [prefixWord, tailWord_7184715, baseEnd_7184715] using wordTrace_append hprefix tailTrace_7184715
  have hstable : (prefixWord ++ tailWord_7184715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184715).length < 2 ^ (prefixWord ++ tailWord_7184715).sum := by decide
  have hdescent : baseEnd_7184715 < baseStart_7184715 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184745 : List Nat := [1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 4]
def baseStart_7184745 : Nat := 118140960795 + 7184745 * 2 ^ 59
def prefixEnd_7184745 : Nat := 4983230072969 + 3 ^ 40 * 7184745 * 2
def baseEnd_7184745 : Nat := 3689227564987597385845465

theorem tailTrace_7184745 : CollatzResearch.WordTrace tailWord_7184745 prefixEnd_7184745 3689227564987597385845465 := by
  unfold tailWord_7184745
  simp only [CollatzResearch.WordTrace]
  refine ⟨262049178355903396600131689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174699452237268931066754459 262049178355903396600131689)
  ·
    refine ⟨196536883766927547450098767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262049178355903396600131689 196536883766927547450098767)
    ·
      refine ⟨294805325650391321175148151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196536883766927547450098767 294805325650391321175148151)
      ·
        refine ⟨442207988475586981762722227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294805325650391321175148151 442207988475586981762722227)
        ·
          refine ⟨663311982713380472644083341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442207988475586981762722227 663311982713380472644083341)
          ·
            refine ⟨248741993517517677241531253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663311982713380472644083341 248741993517517677241531253)
            ·
              refine ⟨23319561892267282241393555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 248741993517517677241531253 23319561892267282241393555)
              ·
                refine ⟨34979342838400923362090333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23319561892267282241393555 34979342838400923362090333)
                ·
                  refine ⟨13117253564400346260783875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34979342838400923362090333 13117253564400346260783875)
                  ·
                    refine ⟨19675880346600519391175813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13117253564400346260783875 19675880346600519391175813)
                    ·
                      refine ⟨3689227564987597385845465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19675880346600519391175813 3689227564987597385845465)
                      ·
                        rfl

theorem cell23_7184745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 1, 4].length) (baseStart_7184745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184745 prefixEnd_7184745 := by exact prefixLift 7184745
  have htrace : WordTrace (prefixWord ++ tailWord_7184745) baseStart_7184745 baseEnd_7184745 := by
    simpa [prefixWord, tailWord_7184745, baseEnd_7184745] using wordTrace_append hprefix tailTrace_7184745
  have hstable : (prefixWord ++ tailWord_7184745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184745).length < 2 ^ (prefixWord ++ tailWord_7184745).sum := by decide
  have hdescent : baseEnd_7184745 < baseStart_7184745 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184749 : List Nat := [1, 5, 1, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_7184749 : Nat := 118140960795 + 7184749 * 2 ^ 59
def prefixEnd_7184749 : Nat := 4983230072969 + 3 ^ 40 * 7184749 * 2
def baseEnd_7184749 : Nat := 3689229618910215370195447

theorem tailTrace_7184749 : CollatzResearch.WordTrace tailWord_7184749 prefixEnd_7184749 3689229618910215370195447 := by
  unfold tailWord_7184749
  simp only [CollatzResearch.WordTrace]
  refine ⟨262049324247888905283277301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174699549498592603522184867 262049324247888905283277301)
  ·
    refine ⟨24567124148239584870307247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262049324247888905283277301 24567124148239584870307247)
    ·
      refine ⟨36850686222359377305460871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24567124148239584870307247 36850686222359377305460871)
      ·
        refine ⟨55276029333539065958191307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36850686222359377305460871 55276029333539065958191307)
        ·
          refine ⟨82914044000308598937286961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55276029333539065958191307 82914044000308598937286961)
          ·
            refine ⟨62185533000231449202965221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82914044000308598937286961 62185533000231449202965221)
            ·
              refine ⟨11659787437543396725555979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62185533000231449202965221 11659787437543396725555979)
              ·
                refine ⟨17489681156315095088333969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11659787437543396725555979 17489681156315095088333969)
                ·
                  refine ⟨13117260867236321316250477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17489681156315095088333969 13117260867236321316250477)
                  ·
                    refine ⟨4918972825213620493593929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13117260867236321316250477 4918972825213620493593929)
                    ·
                      refine ⟨3689229618910215370195447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4918972825213620493593929 3689229618910215370195447)
                      ·
                        rfl

theorem cell23_7184749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_7184749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184749 prefixEnd_7184749 := by exact prefixLift 7184749
  have htrace : WordTrace (prefixWord ++ tailWord_7184749) baseStart_7184749 baseEnd_7184749 := by
    simpa [prefixWord, tailWord_7184749, baseEnd_7184749] using wordTrace_append hprefix tailTrace_7184749
  have hstable : (prefixWord ++ tailWord_7184749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184749).length < 2 ^ (prefixWord ++ tailWord_7184749).sum := by decide
  have hdescent : baseEnd_7184749 < baseStart_7184749 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184775 : List Nat := [1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 4]
def baseStart_7184775 : Nat := 118140960795 + 7184775 * 2 ^ 59
def prefixEnd_7184775 : Nat := 4983230072969 + 3 ^ 40 * 7184775 * 2
def baseEnd_7184775 : Nat := 3689242969407232268470327

theorem tailTrace_7184775 : CollatzResearch.WordTrace tailWord_7184775 prefixEnd_7184775 3689242969407232268470327 := by
  unfold tailWord_7184775
  simp only [CollatzResearch.WordTrace]
  refine ⟨262050272545794711723723779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174700181697196474482482519 262050272545794711723723779)
  ·
    refine ⟨393075408818692067585585669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262050272545794711723723779 393075408818692067585585669)
    ·
      refine ⟨73701639153504762672297313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393075408818692067585585669 73701639153504762672297313)
      ·
        refine ⟨55276229365128572004222985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73701639153504762672297313 55276229365128572004222985)
        ·
          refine ⟨41457172023846429003167239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55276229365128572004222985 41457172023846429003167239)
          ·
            refine ⟨62185758035769643504750859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41457172023846429003167239 62185758035769643504750859)
            ·
              refine ⟨93278637053654465257126289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62185758035769643504750859 93278637053654465257126289)
              ·
                refine ⟨69958977790240848942844717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93278637053654465257126289 69958977790240848942844717)
                ·
                  refine ⟨26234616671340318353566769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 69958977790240848942844717 26234616671340318353566769)
                  ·
                    refine ⟨19675962503505238765175077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26234616671340318353566769 19675962503505238765175077)
                    ·
                      refine ⟨3689242969407232268470327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19675962503505238765175077 3689242969407232268470327)
                      ·
                        rfl

theorem cell23_7184775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_7184775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184775 prefixEnd_7184775 := by exact prefixLift 7184775
  have htrace : WordTrace (prefixWord ++ tailWord_7184775) baseStart_7184775 baseEnd_7184775 := by
    simpa [prefixWord, tailWord_7184775, baseEnd_7184775] using wordTrace_append hprefix tailTrace_7184775
  have hstable : (prefixWord ++ tailWord_7184775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184775).length < 2 ^ (prefixWord ++ tailWord_7184775).sum := by decide
  have hdescent : baseEnd_7184775 < baseStart_7184775 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184790 : List Nat := [5, 3, 1, 2, 1, 1, 1, 2, 3, 1, 3]
def baseStart_7184790 : Nat := 118140960795 + 7184790 * 2 ^ 59
def prefixEnd_7184790 : Nat := 4983230072969 + 3 ^ 40 * 7184790 * 2
def baseEnd_7184790 : Nat := 3689250671617049709782759

theorem tailTrace_7184790 : CollatzResearch.WordTrace tailWord_7184790 prefixEnd_7184790 3689250671617049709782759 := by
  unfold tailWord_7184790
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378176227546273080344989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174700546427160246190346549 16378176227546273080344989)
  ·
    refine ⟨6141816085329852405129371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 16378176227546273080344989 6141816085329852405129371)
    ·
      refine ⟨9212724127994778607694057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6141816085329852405129371 9212724127994778607694057)
      ·
        refine ⟨6909543095996083955770543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 9212724127994778607694057 6909543095996083955770543)
        ·
          refine ⟨10364314643994125933655815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909543095996083955770543 10364314643994125933655815)
          ·
            refine ⟨15546471965991188900483723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10364314643994125933655815 15546471965991188900483723)
            ·
              refine ⟨23319707948986783350725585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546471965991188900483723 23319707948986783350725585)
              ·
                refine ⟨17489780961740087513044189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23319707948986783350725585 17489780961740087513044189)
                ·
                  refine ⟨6558667860652532817391571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17489780961740087513044189 6558667860652532817391571)
                  ·
                    refine ⟨9838001790978799226087357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6558667860652532817391571 9838001790978799226087357)
                    ·
                      refine ⟨3689250671617049709782759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838001790978799226087357 3689250671617049709782759)
                      ·
                        rfl

theorem cell23_7184790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_7184790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184790 prefixEnd_7184790 := by exact prefixLift 7184790
  have htrace : WordTrace (prefixWord ++ tailWord_7184790) baseStart_7184790 baseEnd_7184790 := by
    simpa [prefixWord, tailWord_7184790, baseEnd_7184790] using wordTrace_append hprefix tailTrace_7184790
  have hstable : (prefixWord ++ tailWord_7184790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184790).length < 2 ^ (prefixWord ++ tailWord_7184790).sum := by decide
  have hdescent : baseEnd_7184790 < baseStart_7184790 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184792 : List Nat := [2, 1, 2, 5, 1, 1, 1, 3, 1, 2, 4]
def baseStart_7184792 : Nat := 118140960795 + 7184792 * 2 ^ 59
def prefixEnd_7184792 : Nat := 4983230072969 + 3 ^ 40 * 7184792 * 2
def baseEnd_7184792 : Nat := 3689251698578358701957749

theorem tailTrace_7184792 : CollatzResearch.WordTrace tailWord_7184792 prefixEnd_7184792 3689251698578358701957749 := by
  unfold tailWord_7184792
  simp only [CollatzResearch.WordTrace]
  refine ⟨131025446293366561813546315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174700595057822082418061753 131025446293366561813546315)
  ·
    refine ⟨196538169440049842720319473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131025446293366561813546315 196538169440049842720319473)
    ·
      refine ⟨147403627080037382040239605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196538169440049842720319473 147403627080037382040239605)
      ·
        refine ⟨13819090038753504566272463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 147403627080037382040239605 13819090038753504566272463)
        ·
          refine ⟨20728635058130256849408695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13819090038753504566272463 20728635058130256849408695)
          ·
            refine ⟨31092952587195385274113043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20728635058130256849408695 31092952587195385274113043)
            ·
              refine ⟨46639428880793077911169565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31092952587195385274113043 46639428880793077911169565)
              ·
                refine ⟨17489785830297404216688587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46639428880793077911169565 17489785830297404216688587)
                ·
                  refine ⟨26234678745446106325032881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17489785830297404216688587 26234678745446106325032881)
                  ·
                    refine ⟨19676009059084579743774661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26234678745446106325032881 19676009059084579743774661)
                    ·
                      refine ⟨3689251698578358701957749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19676009059084579743774661 3689251698578358701957749)
                      ·
                        rfl

theorem cell23_7184792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_7184792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184792 prefixEnd_7184792 := by exact prefixLift 7184792
  have htrace : WordTrace (prefixWord ++ tailWord_7184792) baseStart_7184792 baseEnd_7184792 := by
    simpa [prefixWord, tailWord_7184792, baseEnd_7184792] using wordTrace_append hprefix tailTrace_7184792
  have hstable : (prefixWord ++ tailWord_7184792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184792).length < 2 ^ (prefixWord ++ tailWord_7184792).sum := by decide
  have hdescent : baseEnd_7184792 < baseStart_7184792 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184802 : List Nat := [3, 3, 1, 2, 1, 1, 5, 7]
def baseStart_7184802 : Nat := 118140960795 + 7184802 * 2 ^ 59
def prefixEnd_7184802 : Nat := 4983230072969 + 3 ^ 40 * 7184802 * 2
def baseEnd_7184802 : Nat := 136639141977218654178989

theorem tailTrace_7184802 : CollatzResearch.WordTrace tailWord_7184802 prefixEnd_7184802 136639141977218654178989 := by
  unfold tailWord_7184802
  simp only [CollatzResearch.WordTrace]
  refine ⟨65512814329174223833739165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174700838211131263556637773 65512814329174223833739165)
  ·
    refine ⟨24567305373440333937652187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65512814329174223833739165 24567305373440333937652187)
    ·
      refine ⟨36850958060160500906478281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24567305373440333937652187 36850958060160500906478281)
      ·
        refine ⟨27638218545120375679858711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36850958060160500906478281 27638218545120375679858711)
        ·
          refine ⟨41457327817680563519788067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27638218545120375679858711 41457327817680563519788067)
          ·
            refine ⟨62185991726520845279682101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41457327817680563519788067 62185991726520845279682101)
            ·
              refine ⟨5829936724361329244970197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62185991726520845279682101 5829936724361329244970197)
              ·
                refine ⟨136639141977218654178989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5829936724361329244970197 136639141977218654178989)
                ·
                  rfl

theorem cell23_7184802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 5, 7].length) (baseStart_7184802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184802 prefixEnd_7184802 := by exact prefixLift 7184802
  have htrace : WordTrace (prefixWord ++ tailWord_7184802) baseStart_7184802 baseEnd_7184802 := by
    simpa [prefixWord, tailWord_7184802, baseEnd_7184802] using wordTrace_append hprefix tailTrace_7184802
  have hstable : (prefixWord ++ tailWord_7184802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184802).length < 2 ^ (prefixWord ++ tailWord_7184802).sum := by decide
  have hdescent : baseEnd_7184802 < baseStart_7184802 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184810 : List Nat := [3, 1, 6, 1, 1, 2, 2, 1, 1, 5]
def baseStart_7184810 : Nat := 118140960795 + 7184810 * 2 ^ 59
def prefixEnd_7184810 : Nat := 4983230072969 + 3 ^ 40 * 7184810 * 2
def baseEnd_7184810 : Nat := 1229753647076713210510889

theorem tailTrace_7184810 : CollatzResearch.WordTrace tailWord_7184810 prefixEnd_7184810 1229753647076713210510889 := by
  unfold tailWord_7184810
  simp only [CollatzResearch.WordTrace]
  refine ⟨65512887275166978175311971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174701032733778608467498589 65512887275166978175311971)
  ·
    refine ⟨98269330912750467262967957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65512887275166978175311971 98269330912750467262967957)
    ·
      refine ⟨4606374886535178152951623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 98269330912750467262967957 4606374886535178152951623)
      ·
        refine ⟨6909562329802767229427435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4606374886535178152951623 6909562329802767229427435)
        ·
          refine ⟨10364343494704150844141153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6909562329802767229427435 10364343494704150844141153)
          ·
            refine ⟨7773257621028113133105865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10364343494704150844141153 7773257621028113133105865)
            ·
              refine ⟨5829943215771084849829399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7773257621028113133105865 5829943215771084849829399)
              ·
                refine ⟨8744914823656627274744099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829943215771084849829399 8744914823656627274744099)
                ·
                  refine ⟨13117372235484940912116149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8744914823656627274744099 13117372235484940912116149)
                  ·
                    refine ⟨1229753647076713210510889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13117372235484940912116149 1229753647076713210510889)
                    ·
                      rfl

theorem cell23_7184810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 1, 2, 2, 1, 1, 5].length) (baseStart_7184810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184810 prefixEnd_7184810 := by exact prefixLift 7184810
  have htrace : WordTrace (prefixWord ++ tailWord_7184810) baseStart_7184810 baseEnd_7184810 := by
    simpa [prefixWord, tailWord_7184810, baseEnd_7184810] using wordTrace_append hprefix tailTrace_7184810
  have hstable : (prefixWord ++ tailWord_7184810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184810).length < 2 ^ (prefixWord ++ tailWord_7184810).sum := by decide
  have hdescent : baseEnd_7184810 < baseStart_7184810 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184812 : List Nat := [2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 3]
def baseStart_7184812 : Nat := 118140960795 + 7184812 * 2 ^ 59
def prefixEnd_7184812 : Nat := 4983230072969 + 3 ^ 40 * 7184812 * 2
def baseEnd_7184812 : Nat := 3689261968191448623707657

theorem tailTrace_7184812 : CollatzResearch.WordTrace tailWord_7184812 prefixEnd_7184812 3689261968191448623707657 := by
  unfold tailWord_7184812
  simp only [CollatzResearch.WordTrace]
  refine ⟨131025811023330333521410345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174701081364440444695213793 131025811023330333521410345)
  ·
    refine ⟨98269358267497750141057759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131025811023330333521410345 98269358267497750141057759)
    ·
      refine ⟨147404037401246625211586639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98269358267497750141057759 147404037401246625211586639)
      ·
        refine ⟨221106056101869937817379959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147404037401246625211586639 221106056101869937817379959)
        ·
          refine ⟨331659084152804906726069939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221106056101869937817379959 331659084152804906726069939)
          ·
            refine ⟨497488626229207360089104909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331659084152804906726069939 497488626229207360089104909)
            ·
              refine ⟨186558234835952760033414341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 497488626229207360089104909 186558234835952760033414341)
              ·
                refine ⟨34979669031741142506265189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186558234835952760033414341 34979669031741142506265189)
                ·
                  refine ⟨6558687943451464219924723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34979669031741142506265189 6558687943451464219924723)
                  ·
                    refine ⟨9838031915177196329887085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6558687943451464219924723 9838031915177196329887085)
                    ·
                      refine ⟨3689261968191448623707657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838031915177196329887085 3689261968191448623707657)
                      ·
                        rfl

theorem cell23_7184812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 3].length) (baseStart_7184812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184812 prefixEnd_7184812 := by exact prefixLift 7184812
  have htrace : WordTrace (prefixWord ++ tailWord_7184812) baseStart_7184812 baseEnd_7184812 := by
    simpa [prefixWord, tailWord_7184812, baseEnd_7184812] using wordTrace_append hprefix tailTrace_7184812
  have hstable : (prefixWord ++ tailWord_7184812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184812).length < 2 ^ (prefixWord ++ tailWord_7184812).sum := by decide
  have hdescent : baseEnd_7184812 < baseStart_7184812 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184813 : List Nat := [1, 5, 2, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_7184813 : Nat := 118140960795 + 7184813 * 2 ^ 59
def prefixEnd_7184813 : Nat := 4983230072969 + 3 ^ 40 * 7184813 * 2
def baseEnd_7184813 : Nat := 3689262481672103119795153

theorem tailTrace_7184813 : CollatzResearch.WordTrace tailWord_7184813 prefixEnd_7184813 3689262481672103119795153 := by
  unfold tailWord_7184813
  simp only [CollatzResearch.WordTrace]
  refine ⟨262051658519657044213607093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174701105679771362809071395 262051658519657044213607093)
  ·
    refine ⟨24567342986217847895025665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262051658519657044213607093 24567342986217847895025665)
    ·
      refine ⟨18425507239663385921269249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 24567342986217847895025665 18425507239663385921269249)
      ·
        refine ⟨13819130429747539440951937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18425507239663385921269249 13819130429747539440951937)
        ·
          refine ⟨10364347822310654580713953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13819130429747539440951937 10364347822310654580713953)
          ·
            refine ⟨7773260866732990935535465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10364347822310654580713953 7773260866732990935535465)
            ·
              refine ⟨5829945650049743201651599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7773260866732990935535465 5829945650049743201651599)
              ·
                refine ⟨8744918475074614802477399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5829945650049743201651599 8744918475074614802477399)
                ·
                  refine ⟨13117377712611922203716099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8744918475074614802477399 13117377712611922203716099)
                  ·
                    refine ⟨19676066568917883305574149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13117377712611922203716099 19676066568917883305574149)
                    ·
                      refine ⟨3689262481672103119795153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19676066568917883305574149 3689262481672103119795153)
                      ·
                        rfl

theorem cell23_7184813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_7184813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184813 prefixEnd_7184813 := by exact prefixLift 7184813
  have htrace : WordTrace (prefixWord ++ tailWord_7184813) baseStart_7184813 baseEnd_7184813 := by
    simpa [prefixWord, tailWord_7184813, baseEnd_7184813] using wordTrace_append hprefix tailTrace_7184813
  have hstable : (prefixWord ++ tailWord_7184813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184813).length < 2 ^ (prefixWord ++ tailWord_7184813).sum := by decide
  have hdescent : baseEnd_7184813 < baseStart_7184813 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184829 : List Nat := [1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 3]
def baseStart_7184829 : Nat := 118140960795 + 7184829 * 2 ^ 59
def prefixEnd_7184829 : Nat := 4983230072969 + 3 ^ 40 * 7184829 * 2
def baseEnd_7184829 : Nat := 3689270697362575057195079

theorem tailTrace_7184829 : CollatzResearch.WordTrace tailWord_7184829 prefixEnd_7184829 3689270697362575057195079 := by
  unfold tailWord_7184829
  simp only [CollatzResearch.WordTrace]
  refine ⟨262052242087599078946189541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174701494725066052630793027 262052242087599078946189541)
  ·
    refine ⟨49134795391424827302410539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262052242087599078946189541 49134795391424827302410539)
    ·
      refine ⟨73702193087137240953615809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49134795391424827302410539 73702193087137240953615809)
      ·
        refine ⟨55276644815352930715211857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73702193087137240953615809 55276644815352930715211857)
        ·
          refine ⟨41457483611514698036408893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55276644815352930715211857 41457483611514698036408893)
          ·
            refine ⟨15546556354318011763653335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 41457483611514698036408893 15546556354318011763653335)
            ·
              refine ⟨23319834531477017645480003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546556354318011763653335 23319834531477017645480003)
              ·
                refine ⟨34979751797215526468220005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23319834531477017645480003 34979751797215526468220005)
                ·
                  refine ⟨6558703461977911212791251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34979751797215526468220005 6558703461977911212791251)
                  ·
                    refine ⟨9838055192966866819186877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6558703461977911212791251 9838055192966866819186877)
                    ·
                      refine ⟨3689270697362575057195079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838055192966866819186877 3689270697362575057195079)
                      ·
                        rfl

theorem cell23_7184829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 3, 1, 1, 4, 1, 3].length) (baseStart_7184829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184829 prefixEnd_7184829 := by exact prefixLift 7184829
  have htrace : WordTrace (prefixWord ++ tailWord_7184829) baseStart_7184829 baseEnd_7184829 := by
    simpa [prefixWord, tailWord_7184829, baseEnd_7184829] using wordTrace_append hprefix tailTrace_7184829
  have hstable : (prefixWord ++ tailWord_7184829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184829).length < 2 ^ (prefixWord ++ tailWord_7184829).sum := by decide
  have hdescent : baseEnd_7184829 < baseStart_7184829 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184872 : List Nat := [2, 1, 4, 1, 1, 4, 1, 1, 2, 1, 5]
def baseStart_7184872 : Nat := 118140960795 + 7184872 * 2 ^ 59
def prefixEnd_7184872 : Nat := 4983230072969 + 3 ^ 40 * 7184872 * 2
def baseEnd_7184872 : Nat := 3689292777030718388957381

theorem tailTrace_7184872 : CollatzResearch.WordTrace tailWord_7184872 prefixEnd_7184872 3689292777030718388957381 := by
  unfold tailWord_7184872
  simp only [CollatzResearch.WordTrace]
  refine ⟨131026905213221648645002435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174702540284295531526669913 131026905213221648645002435)
  ·
    refine ⟨196540357819832472967503653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131026905213221648645002435 196540357819832472967503653)
    ·
      refine ⟨36851317091218588681406935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196540357819832472967503653 36851317091218588681406935)
      ·
        refine ⟨55276975636827883022110403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36851317091218588681406935 55276975636827883022110403)
        ·
          refine ⟨82915463455241824533165605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55276975636827883022110403 82915463455241824533165605)
          ·
            refine ⟨15546649397857842099968551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82915463455241824533165605 15546649397857842099968551)
            ·
              refine ⟨23319974096786763149952827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546649397857842099968551 23319974096786763149952827)
              ·
                refine ⟨34979961145180144724929241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23319974096786763149952827 34979961145180144724929241)
                ·
                  refine ⟨26234970858885108543696931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34979961145180144724929241 26234970858885108543696931)
                  ·
                    refine ⟨39352456288327662815545397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26234970858885108543696931 39352456288327662815545397)
                    ·
                      refine ⟨3689292777030718388957381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39352456288327662815545397 3689292777030718388957381)
                      ·
                        rfl

theorem cell23_7184872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_7184872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184872 prefixEnd_7184872 := by exact prefixLift 7184872
  have htrace : WordTrace (prefixWord ++ tailWord_7184872) baseStart_7184872 baseEnd_7184872 := by
    simpa [prefixWord, tailWord_7184872, baseEnd_7184872] using wordTrace_append hprefix tailTrace_7184872
  have hstable : (prefixWord ++ tailWord_7184872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184872).length < 2 ^ (prefixWord ++ tailWord_7184872).sum := by decide
  have hdescent : baseEnd_7184872 < baseStart_7184872 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184886 : List Nat := [5, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2]
def baseStart_7184886 : Nat := 118140960795 + 7184886 * 2 ^ 59
def prefixEnd_7184886 : Nat := 4983230072969 + 3 ^ 40 * 7184886 * 2
def baseEnd_7184886 : Nat := 3689299965759881334182317

theorem tailTrace_7184886 : CollatzResearch.WordTrace tailWord_7184886 prefixEnd_7184886 3689299965759881334182317 := by
  unfold tailWord_7184886
  simp only [CollatzResearch.WordTrace]
  refine ⟨16378395065524536105063407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 174702880698928385120676341 16378395065524536105063407)
  ·
    refine ⟨24567592598286804157595111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 16378395065524536105063407 24567592598286804157595111)
    ·
      refine ⟨36851388897430206236392667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24567592598286804157595111 36851388897430206236392667)
      ·
        refine ⟨55277083346145309354589001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36851388897430206236392667 55277083346145309354589001)
        ·
          refine ⟨41457812509608982015941751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55277083346145309354589001 41457812509608982015941751)
          ·
            refine ⟨62186718764413473023912627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41457812509608982015941751 62186718764413473023912627)
            ·
              refine ⟨93280078146620209535868941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62186718764413473023912627 93280078146620209535868941)
              ·
                refine ⟨34980029304982578575950853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93280078146620209535868941 34980029304982578575950853)
                ·
                  refine ⟨6558755494684233482990785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34980029304982578575950853 6558755494684233482990785)
                  ·
                    refine ⟨4919066621013175112243089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6558755494684233482990785 4919066621013175112243089)
                    ·
                      refine ⟨3689299965759881334182317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919066621013175112243089 3689299965759881334182317)
                      ·
                        rfl

theorem cell23_7184886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_7184886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184886 prefixEnd_7184886 := by exact prefixLift 7184886
  have htrace : WordTrace (prefixWord ++ tailWord_7184886) baseStart_7184886 baseEnd_7184886 := by
    simpa [prefixWord, tailWord_7184886, baseEnd_7184886] using wordTrace_append hprefix tailTrace_7184886
  have hstable : (prefixWord ++ tailWord_7184886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184886).length < 2 ^ (prefixWord ++ tailWord_7184886).sum := by decide
  have hdescent : baseEnd_7184886 < baseStart_7184886 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184903 : List Nat := [1, 1, 4, 3, 3, 1, 1, 3, 2, 2, 2]
def baseStart_7184903 : Nat := 118140960795 + 7184903 * 2 ^ 59
def prefixEnd_7184903 : Nat := 4983230072969 + 3 ^ 40 * 7184903 * 2
def baseEnd_7184903 : Nat := 3689308694931007767669739

theorem tailTrace_7184903 : CollatzResearch.WordTrace tailWord_7184903 prefixEnd_7184903 3689308694931007767669739 := by
  unfold tailWord_7184903
  simp only [CollatzResearch.WordTrace]
  refine ⟨262054941089330989584383363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174703294059553993056255575 262054941089330989584383363)
  ·
    refine ⟨393082411633996484376575045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262054941089330989584383363 393082411633996484376575045)
    ·
      refine ⟨73702952181374340820607821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393082411633996484376575045 73702952181374340820607821)
      ·
        refine ⟨27638607068015377807727933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73702952181374340820607821 27638607068015377807727933)
        ·
          refine ⟨10364477650505766677897975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27638607068015377807727933 10364477650505766677897975)
          ·
            refine ⟨15546716475758650016846963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10364477650505766677897975 15546716475758650016846963)
            ·
              refine ⟨23320074713637975025270445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15546716475758650016846963 23320074713637975025270445)
              ·
                refine ⟨8745028017614240634476417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23320074713637975025270445 8745028017614240634476417)
                ·
                  refine ⟨6558771013210680475857313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8745028017614240634476417 6558771013210680475857313)
                  ·
                    refine ⟨4919078259908010356892985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6558771013210680475857313 4919078259908010356892985)
                    ·
                      refine ⟨3689308694931007767669739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919078259908010356892985 3689308694931007767669739)
                      ·
                        rfl

theorem cell23_7184903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 3, 2, 2, 2].length) (baseStart_7184903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184903 prefixEnd_7184903 := by exact prefixLift 7184903
  have htrace : WordTrace (prefixWord ++ tailWord_7184903) baseStart_7184903 baseEnd_7184903 := by
    simpa [prefixWord, tailWord_7184903, baseEnd_7184903] using wordTrace_append hprefix tailTrace_7184903
  have hstable : (prefixWord ++ tailWord_7184903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184903).length < 2 ^ (prefixWord ++ tailWord_7184903).sum := by decide
  have hdescent : baseEnd_7184903 < baseStart_7184903 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184905 : List Nat := [1, 2, 1, 1, 3, 1, 2, 4, 1, 7]
def baseStart_7184905 : Nat := 118140960795 + 7184905 * 2 ^ 59
def prefixEnd_7184905 : Nat := 4983230072969 + 3 ^ 40 * 7184905 * 2
def baseEnd_7184905 : Nat := 1229769907297438919948243

theorem tailTrace_7184905 : CollatzResearch.WordTrace tailWord_7184905 prefixEnd_7184905 1229769907297438919948243 := by
  unfold tailWord_7184905
  simp only [CollatzResearch.WordTrace]
  refine ⟨262055014035323743925956169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174703342690215829283970779 262055014035323743925956169)
  ·
    refine ⟨196541260526492807944467127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262055014035323743925956169 196541260526492807944467127)
    ·
      refine ⟨294811890789739211916700691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196541260526492807944467127 294811890789739211916700691)
      ·
        refine ⟨442217836184608817875051037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294811890789739211916700691 442217836184608817875051037)
        ·
          refine ⟨165831688569228306703144139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 442217836184608817875051037 165831688569228306703144139)
          ·
            refine ⟨248747532853842460054716209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 165831688569228306703144139 248747532853842460054716209)
            ·
              refine ⟨186560649640381845041037157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248747532853842460054716209 186560649640381845041037157)
              ·
                refine ⟨34980121807571595945194467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 186560649640381845041037157 34980121807571595945194467)
                ·
                  refine ⟨52470182711357393917791701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34980121807571595945194467 52470182711357393917791701)
                  ·
                    refine ⟨1229769907297438919948243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 52470182711357393917791701 1229769907297438919948243)
                    ·
                      rfl

theorem cell23_7184905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 4, 1, 7].length) (baseStart_7184905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184905 prefixEnd_7184905 := by exact prefixLift 7184905
  have htrace : WordTrace (prefixWord ++ tailWord_7184905) baseStart_7184905 baseEnd_7184905 := by
    simpa [prefixWord, tailWord_7184905, baseEnd_7184905] using wordTrace_append hprefix tailTrace_7184905
  have hstable : (prefixWord ++ tailWord_7184905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184905).length < 2 ^ (prefixWord ++ tailWord_7184905).sum := by decide
  have hdescent : baseEnd_7184905 < baseStart_7184905 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184915 : List Nat := [1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7]
def baseStart_7184915 : Nat := 118140960795 + 7184915 * 2 ^ 59
def prefixEnd_7184915 : Nat := 4983230072969 + 3 ^ 40 * 7184915 * 2
def baseEnd_7184915 : Nat := 3689314856698861720719683

theorem tailTrace_7184915 : CollatzResearch.WordTrace tailWord_7184915 prefixEnd_7184915 3689314856698861720719683 := by
  unfold tailWord_7184915
  simp only [CollatzResearch.WordTrace]
  refine ⟨262055378765287515633820199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174703585843525010422546799 262055378765287515633820199)
  ·
    refine ⟨393083068147931273450730299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262055378765287515633820199 393083068147931273450730299)
    ·
      refine ⟨589624602221896910176095449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393083068147931273450730299 589624602221896910176095449)
      ·
        refine ⟨442218451666422682632071587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589624602221896910176095449 442218451666422682632071587)
        ·
          refine ⟨663327677499634023948107381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442218451666422682632071587 663327677499634023948107381)
          ·
            refine ⟨62186969765590689745135067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 663327677499634023948107381 62186969765590689745135067)
            ·
              refine ⟨93280454648386034617702601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62186969765590689745135067 93280454648386034617702601)
              ·
                refine ⟨69960340986289525963276951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93280454648386034617702601 69960340986289525963276951)
                ·
                  refine ⟨104940511479434288944915427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69960340986289525963276951 104940511479434288944915427)
                  ·
                    refine ⟨157410767219151433417373141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 104940511479434288944915427 157410767219151433417373141)
                    ·
                      refine ⟨3689314856698861720719683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157410767219151433417373141 3689314856698861720719683)
                      ·
                        rfl

theorem cell23_7184915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 1, 1, 7].length) (baseStart_7184915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184915 prefixEnd_7184915 := by exact prefixLift 7184915
  have htrace : WordTrace (prefixWord ++ tailWord_7184915) baseStart_7184915 baseEnd_7184915 := by
    simpa [prefixWord, tailWord_7184915, baseEnd_7184915] using wordTrace_append hprefix tailTrace_7184915
  have hstable : (prefixWord ++ tailWord_7184915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184915).length < 2 ^ (prefixWord ++ tailWord_7184915).sum := by decide
  have hdescent : baseEnd_7184915 < baseStart_7184915 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184922 : List Nat := [3, 1, 1, 3, 1, 1, 3, 3, 2, 5]
def baseStart_7184922 : Nat := 118140960795 + 7184922 * 2 ^ 59
def prefixEnd_7184922 : Nat := 4983230072969 + 3 ^ 40 * 7184922 * 2
def baseEnd_7184922 : Nat := 1229772817021147731110717

theorem tailTrace_7184922 : CollatzResearch.WordTrace tailWord_7184922 prefixEnd_7184922 1229772817021147731110717 := by
  unfold tailWord_7184922
  simp only [CollatzResearch.WordTrace]
  refine ⟨65513908519065538957331255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174703756050841437219550013 65513908519065538957331255)
  ·
    refine ⟨98270862778598308435996883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65513908519065538957331255 98270862778598308435996883)
    ·
      refine ⟨147406294167897462653995325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98270862778598308435996883 147406294167897462653995325)
      ·
        refine ⟨55277360312961548495248247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 147406294167897462653995325 55277360312961548495248247)
        ·
          refine ⟨82916040469442322742872371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55277360312961548495248247 82916040469442322742872371)
          ·
            refine ⟨124374060704163484114308557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82916040469442322742872371 124374060704163484114308557)
            ·
              refine ⟨46640272764061306542865709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124374060704163484114308557 46640272764061306542865709)
              ·
                refine ⟨17490102286522989953574641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46640272764061306542865709 17490102286522989953574641)
                ·
                  refine ⟨13117576714892242465180981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17490102286522989953574641 13117576714892242465180981)
                  ·
                    refine ⟨1229772817021147731110717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13117576714892242465180981 1229772817021147731110717)
                    ·
                      rfl

theorem cell23_7184922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 3, 2, 5].length) (baseStart_7184922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184922 prefixEnd_7184922 := by exact prefixLift 7184922
  have htrace : WordTrace (prefixWord ++ tailWord_7184922) baseStart_7184922 baseEnd_7184922 := by
    simpa [prefixWord, tailWord_7184922, baseEnd_7184922] using wordTrace_append hprefix tailTrace_7184922
  have hstable : (prefixWord ++ tailWord_7184922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184922).length < 2 ^ (prefixWord ++ tailWord_7184922).sum := by decide
  have hdescent : baseEnd_7184922 < baseStart_7184922 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7184959 : List Nat := [1, 1, 2, 2, 3, 2, 3, 1, 2, 4, 2]
def baseStart_7184959 : Nat := 118140960795 + 7184959 * 2 ^ 59
def prefixEnd_7184959 : Nat := 4983230072969 + 3 ^ 40 * 7184959 * 2
def baseEnd_7184959 : Nat := 3689337449847659548569481

theorem tailTrace_7184959 : CollatzResearch.WordTrace tailWord_7184959 prefixEnd_7184959 3689337449847659548569481 := by
  unfold tailWord_7184959
  simp only [CollatzResearch.WordTrace]
  refine ⟨262056983577128111148421931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174704655718085407432281287 262056983577128111148421931)
  ·
    refine ⟨393085475365692166722632897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262056983577128111148421931 393085475365692166722632897)
    ·
      refine ⟨294814106524269125041974673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393085475365692166722632897 294814106524269125041974673)
      ·
        refine ⟨221110579893201843781481005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294814106524269125041974673 221110579893201843781481005)
        ·
          refine ⟨82916467459950691418055377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221110579893201843781481005 82916467459950691418055377)
          ·
            refine ⟨62187350594963018563541533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82916467459950691418055377 62187350594963018563541533)
            ·
              refine ⟨23320256473111131961328075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62187350594963018563541533 23320256473111131961328075)
              ·
                refine ⟨34980384709666697941992113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23320256473111131961328075 34980384709666697941992113)
                ·
                  refine ⟨26235288532250023456494085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34980384709666697941992113 26235288532250023456494085)
                  ·
                    refine ⟨4919116599796879398092641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26235288532250023456494085 4919116599796879398092641)
                    ·
                      refine ⟨3689337449847659548569481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919116599796879398092641 3689337449847659548569481)
                      ·
                        rfl

theorem cell23_7184959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 4, 2].length) (baseStart_7184959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7184959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7184959 prefixEnd_7184959 := by exact prefixLift 7184959
  have htrace : WordTrace (prefixWord ++ tailWord_7184959) baseStart_7184959 baseEnd_7184959 := by
    simpa [prefixWord, tailWord_7184959, baseEnd_7184959] using wordTrace_append hprefix tailTrace_7184959
  have hstable : (prefixWord ++ tailWord_7184959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7184959).length < 2 ^ (prefixWord ++ tailWord_7184959).sum := by decide
  have hdescent : baseEnd_7184959 < baseStart_7184959 := by decide
  rcases family_descends (prefixWord ++ tailWord_7184959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185002 : List Nat := [3, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8]
def baseStart_7185002 : Nat := 118140960795 + 7185002 * 2 ^ 59
def prefixEnd_7185002 : Nat := 4983230072969 + 3 ^ 40 * 7185002 * 2
def baseEnd_7185002 : Nat := 3689359529515802880331783

theorem tailTrace_7185002 : CollatzResearch.WordTrace tailWord_7185002 prefixEnd_7185002 3689359529515802880331783 := by
  unfold tailWord_7185002
  simp only [CollatzResearch.WordTrace]
  refine ⟨65514637978993082373059315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174705701277314886328158173 65514637978993082373059315)
  ·
    refine ⟨98271956968489623559588973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65514637978993082373059315 98271956968489623559588973)
    ·
      refine ⟨36851983863183608834845865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98271956968489623559588973 36851983863183608834845865)
      ·
        refine ⟨27638987897387706626134399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36851983863183608834845865 27638987897387706626134399)
        ·
          refine ⟨41458481846081559939201599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27638987897387706626134399 41458481846081559939201599)
          ·
            refine ⟨62187722769122339908802399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41458481846081559939201599 62187722769122339908802399)
            ·
              refine ⟨93281584153683509863203599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62187722769122339908802399 93281584153683509863203599)
              ·
                refine ⟨139922376230525264794805399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93281584153683509863203599 139922376230525264794805399)
                ·
                  refine ⟨209883564345787897192208099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 139922376230525264794805399 209883564345787897192208099)
                  ·
                    refine ⟨314825346518681845788312149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 209883564345787897192208099 314825346518681845788312149)
                    ·
                      refine ⟨3689359529515802880331783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 314825346518681845788312149 3689359529515802880331783)
                      ·
                        rfl

theorem cell23_7185002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_7185002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185002 prefixEnd_7185002 := by exact prefixLift 7185002
  have htrace : WordTrace (prefixWord ++ tailWord_7185002) baseStart_7185002 baseEnd_7185002 := by
    simpa [prefixWord, tailWord_7185002, baseEnd_7185002] using wordTrace_append hprefix tailTrace_7185002
  have hstable : (prefixWord ++ tailWord_7185002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185002).length < 2 ^ (prefixWord ++ tailWord_7185002).sum := by decide
  have hdescent : baseEnd_7185002 < baseStart_7185002 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185019 : List Nat := [1, 1, 1, 1, 1, 4, 2, 1, 6, 3, 2]
def baseStart_7185019 : Nat := 118140960795 + 7185019 * 2 ^ 59
def prefixEnd_7185019 : Nat := 4983230072969 + 3 ^ 40 * 7185019 * 2
def baseEnd_7185019 : Nat := 3689368258686929313819205

theorem tailTrace_7185019 : CollatzResearch.WordTrace tailWord_7185019 prefixEnd_7185019 3689368258686929313819205 := by
  unfold tailWord_7185019
  simp only [CollatzResearch.WordTrace]
  refine ⟨262059171956910741395606111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174706114637940494263737407 262059171956910741395606111)
  ·
    refine ⟨393088757935366112093409167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262059171956910741395606111 393088757935366112093409167)
    ·
      refine ⟨589633136903049168140113751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393088757935366112093409167 589633136903049168140113751)
      ·
        refine ⟨884449705354573752210170627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589633136903049168140113751 884449705354573752210170627)
        ·
          refine ⟨1326674558031860628315255941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884449705354573752210170627 1326674558031860628315255941)
          ·
            refine ⟨248751479630973867809110489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1326674558031860628315255941 248751479630973867809110489)
            ·
              refine ⟨186563609723230400856832867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 248751479630973867809110489 186563609723230400856832867)
              ·
                refine ⟨279845414584845601285249301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 186563609723230400856832867 279845414584845601285249301)
                ·
                  refine ⟨13117753808664637560246061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 279845414584845601285249301 13117753808664637560246061)
                  ·
                    refine ⟨4919157678249239085092273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13117753808664637560246061 4919157678249239085092273)
                    ·
                      refine ⟨3689368258686929313819205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919157678249239085092273 3689368258686929313819205)
                      ·
                        rfl

theorem cell23_7185019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 3, 2].length) (baseStart_7185019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185019 prefixEnd_7185019 := by exact prefixLift 7185019
  have htrace : WordTrace (prefixWord ++ tailWord_7185019) baseStart_7185019 baseEnd_7185019 := by
    simpa [prefixWord, tailWord_7185019, baseEnd_7185019] using wordTrace_append hprefix tailTrace_7185019
  have hstable : (prefixWord ++ tailWord_7185019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185019).length < 2 ^ (prefixWord ++ tailWord_7185019).sum := by decide
  have hdescent : baseEnd_7185019 < baseStart_7185019 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185029 : List Nat := [1, 3, 1, 1, 4, 2, 1, 4, 1, 5]
def baseStart_7185029 : Nat := 118140960795 + 7185029 * 2 ^ 59
def prefixEnd_7185029 : Nat := 4983230072969 + 3 ^ 40 * 7185029 * 2
def baseEnd_7185029 : Nat := 1229791131164491424898053

theorem tailTrace_7185029 : CollatzResearch.WordTrace tailWord_7185029 prefixEnd_7185029 1229791131164491424898053 := by
  unfold tailWord_7185029
  simp only [CollatzResearch.WordTrace]
  refine ⟨262059536686874513103470141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174706357791249675402313427 262059536686874513103470141)
  ·
    refine ⟨98272326257577942413801303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262059536686874513103470141 98272326257577942413801303)
    ·
      refine ⟨147408489386366913620701955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98272326257577942413801303 147408489386366913620701955)
      ·
        refine ⟨221112734079550370431052933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147408489386366913620701955 221112734079550370431052933)
        ·
          refine ⟨41458637639915694455822425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 221112734079550370431052933 41458637639915694455822425)
          ·
            refine ⟨31093978229936770841866819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41458637639915694455822425 31093978229936770841866819)
            ·
              refine ⟨46640967344905156262800229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31093978229936770841866819 46640967344905156262800229)
              ·
                refine ⟨8745181377169716799275043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 46640967344905156262800229 8745181377169716799275043)
                ·
                  refine ⟨13117772065754575198912565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745181377169716799275043 13117772065754575198912565)
                  ·
                    refine ⟨1229791131164491424898053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13117772065754575198912565 1229791131164491424898053)
                    ·
                      rfl

theorem cell23_7185029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_7185029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185029 prefixEnd_7185029 := by exact prefixLift 7185029
  have htrace : WordTrace (prefixWord ++ tailWord_7185029) baseStart_7185029 baseEnd_7185029 := by
    simpa [prefixWord, tailWord_7185029, baseEnd_7185029] using wordTrace_append hprefix tailTrace_7185029
  have hstable : (prefixWord ++ tailWord_7185029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185029).length < 2 ^ (prefixWord ++ tailWord_7185029).sum := by decide
  have hdescent : baseEnd_7185029 < baseStart_7185029 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185049 : List Nat := [1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 4]
def baseStart_7185049 : Nat := 118140960795 + 7185049 * 2 ^ 59
def prefixEnd_7185049 : Nat := 4983230072969 + 3 ^ 40 * 7185049 * 2
def baseEnd_7185049 : Nat := 3689383663106564196444067

theorem tailTrace_7185049 : CollatzResearch.WordTrace tailWord_7185049 prefixEnd_7185049 3689383663106564196444067 := by
  unfold tailWord_7185049
  simp only [CollatzResearch.WordTrace]
  refine ⟨262060266146802056519198201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174706844097868037679465467 262060266146802056519198201)
  ·
    refine ⟨196545199610101542389398651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262060266146802056519198201 196545199610101542389398651)
    ·
      refine ⟨294817799415152313584097977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196545199610101542389398651 294817799415152313584097977)
      ·
        refine ⟨221113349561364235188073483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 294817799415152313584097977 221113349561364235188073483)
        ·
          refine ⟨331670024342046352782110225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221113349561364235188073483 331670024342046352782110225)
          ·
            refine ⟨248752518256534764586582669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331670024342046352782110225 248752518256534764586582669)
            ·
              refine ⟨93282194346200536719968501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 248752518256534764586582669 93282194346200536719968501)
              ·
                refine ⟨8745205719956300317497047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93282194346200536719968501 8745205719956300317497047)
                ·
                  refine ⟨13117808579934450476245571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745205719956300317497047 13117808579934450476245571)
                  ·
                    refine ⟨19676712869901675714368357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13117808579934450476245571 19676712869901675714368357)
                    ·
                      refine ⟨3689383663106564196444067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19676712869901675714368357 3689383663106564196444067)
                      ·
                        rfl

theorem cell23_7185049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 5, 1, 1, 4].length) (baseStart_7185049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185049 prefixEnd_7185049 := by exact prefixLift 7185049
  have htrace : WordTrace (prefixWord ++ tailWord_7185049) baseStart_7185049 baseEnd_7185049 := by
    simpa [prefixWord, tailWord_7185049, baseEnd_7185049] using wordTrace_append hprefix tailTrace_7185049
  have hstable : (prefixWord ++ tailWord_7185049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185049).length < 2 ^ (prefixWord ++ tailWord_7185049).sum := by decide
  have hdescent : baseEnd_7185049 < baseStart_7185049 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185060 : List Nat := [2, 3, 1, 2, 2, 1, 5, 2, 1, 1, 3]
def baseStart_7185060 : Nat := 118140960795 + 7185060 * 2 ^ 59
def prefixEnd_7185060 : Nat := 4983230072969 + 3 ^ 40 * 7185060 * 2
def baseEnd_7185060 : Nat := 3689389311393763653406517

theorem tailTrace_7185060 : CollatzResearch.WordTrace tailWord_7185060 prefixEnd_7185060 3689389311393763653406517 := by
  unfold tailWord_7185060
  simp only [CollatzResearch.WordTrace]
  refine ⟨131030333674881102698924317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174707111566508136931899089 131030333674881102698924317)
  ·
    refine ⟨49136375128080413512096619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131030333674881102698924317 49136375128080413512096619)
    ·
      refine ⟨73704562692120620268144929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49136375128080413512096619 73704562692120620268144929)
      ·
        refine ⟨55278422019090465201108697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73704562692120620268144929 55278422019090465201108697)
        ·
          refine ⟨41458816514317848900831523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55278422019090465201108697 41458816514317848900831523)
          ·
            refine ⟨62188224771476773351247285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41458816514317848900831523 62188224771476773351247285)
            ·
              refine ⟨5830146072325947501679433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 62188224771476773351247285 5830146072325947501679433)
              ·
                refine ⟨4372609554244460626259575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5830146072325947501679433 4372609554244460626259575)
                ·
                  refine ⟨6558914331366690939389363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372609554244460626259575 6558914331366690939389363)
                  ·
                    refine ⟨9838371497050036409084045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6558914331366690939389363 9838371497050036409084045)
                    ·
                      refine ⟨3689389311393763653406517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838371497050036409084045 3689389311393763653406517)
                      ·
                        rfl

theorem cell23_7185060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 5, 2, 1, 1, 3].length) (baseStart_7185060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185060 prefixEnd_7185060 := by exact prefixLift 7185060
  have htrace : WordTrace (prefixWord ++ tailWord_7185060) baseStart_7185060 baseEnd_7185060 := by
    simpa [prefixWord, tailWord_7185060, baseEnd_7185060] using wordTrace_append hprefix tailTrace_7185060
  have hstable : (prefixWord ++ tailWord_7185060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185060).length < 2 ^ (prefixWord ++ tailWord_7185060).sum := by decide
  have hdescent : baseEnd_7185060 < baseStart_7185060 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185086 : List Nat := [4, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3]
def baseStart_7185086 : Nat := 118140960795 + 7185086 * 2 ^ 59
def prefixEnd_7185086 : Nat := 4983230072969 + 3 ^ 40 * 7185086 * 2
def baseEnd_7185086 : Nat := 3689402661890780551681397

theorem tailTrace_7185086 : CollatzResearch.WordTrace tailWord_7185086 prefixEnd_7185086 3689402661890780551681397 := by
  unfold tailWord_7185086
  simp only [CollatzResearch.WordTrace]
  refine ⟨32757701955958501479786889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174707743765112007892196741 32757701955958501479786889)
  ·
    refine ⟨24568276466968876109840167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32757701955958501479786889 24568276466968876109840167)
    ·
      refine ⟨36852414700453314164760251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24568276466968876109840167 36852414700453314164760251)
      ·
        refine ⟨55278622050679971247140377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36852414700453314164760251 55278622050679971247140377)
        ·
          refine ⟨41458966538009978435355283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55278622050679971247140377 41458966538009978435355283)
          ·
            refine ⟨62188449807014967653032925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41458966538009978435355283 62188449807014967653032925)
            ·
              refine ⟨23320668677630612869887347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62188449807014967653032925 23320668677630612869887347)
              ·
                refine ⟨34981003016445919304831021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23320668677630612869887347 34981003016445919304831021)
                ·
                  refine ⟨13117876131167219739311633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34981003016445919304831021 13117876131167219739311633)
                  ·
                    refine ⟨9838407098375414804483725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13117876131167219739311633 9838407098375414804483725)
                    ·
                      refine ⟨3689402661890780551681397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838407098375414804483725 3689402661890780551681397)
                      ·
                        rfl

theorem cell23_7185086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 1, 3, 2, 3].length) (baseStart_7185086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185086 prefixEnd_7185086 := by exact prefixLift 7185086
  have htrace : WordTrace (prefixWord ++ tailWord_7185086) baseStart_7185086 baseEnd_7185086 := by
    simpa [prefixWord, tailWord_7185086, baseEnd_7185086] using wordTrace_append hprefix tailTrace_7185086
  have hstable : (prefixWord ++ tailWord_7185086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185086).length < 2 ^ (prefixWord ++ tailWord_7185086).sum := by decide
  have hdescent : baseEnd_7185086 < baseStart_7185086 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185133 : List Nat := [1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_7185133 : Nat := 118140960795 + 7185133 * 2 ^ 59
def prefixEnd_7185133 : Nat := 4983230072969 + 3 ^ 40 * 7185133 * 2
def baseEnd_7185133 : Nat := 3689426795481541867793681

theorem tailTrace_7185133 : CollatzResearch.WordTrace tailWord_7185133 prefixEnd_7185133 3689426795481541867793681 := by
  unfold tailWord_7185133
  simp only [CollatzResearch.WordTrace]
  refine ⟨262063329878497738865256053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174708886585665159243504035 262063329878497738865256053)
  ·
    refine ⟨24568437176109163018617755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262063329878497738865256053 24568437176109163018617755)
    ·
      refine ⟨36852655764163744527926633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24568437176109163018617755 36852655764163744527926633)
      ·
        refine ⟨27639491823122808395944975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36852655764163744527926633 27639491823122808395944975)
        ·
          refine ⟨41459237734684212593917463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27639491823122808395944975 41459237734684212593917463)
          ·
            refine ⟨62188856602026318890876195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41459237734684212593917463 62188856602026318890876195)
            ·
              refine ⟨93283284903039478336314293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62188856602026318890876195 93283284903039478336314293)
              ·
                refine ⟨8745307959659951094029465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 93283284903039478336314293 8745307959659951094029465)
                ·
                  refine ⟨6558980969744963320522099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8745307959659951094029465 6558980969744963320522099)
                  ·
                    refine ⟨9838471454617444980783149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6558980969744963320522099 9838471454617444980783149)
                    ·
                      refine ⟨3689426795481541867793681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838471454617444980783149 3689426795481541867793681)
                      ·
                        rfl

theorem cell23_7185133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_7185133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185133 prefixEnd_7185133 := by exact prefixLift 7185133
  have htrace : WordTrace (prefixWord ++ tailWord_7185133) baseStart_7185133 baseEnd_7185133 := by
    simpa [prefixWord, tailWord_7185133, baseEnd_7185133] using wordTrace_append hprefix tailTrace_7185133
  have hstable : (prefixWord ++ tailWord_7185133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185133).length < 2 ^ (prefixWord ++ tailWord_7185133).sum := by decide
  have hdescent : baseEnd_7185133 < baseStart_7185133 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185140 : List Nat := [2, 6, 1, 1, 2, 1, 3, 7]
def baseStart_7185140 : Nat := 118140960795 + 7185140 * 2 ^ 59
def prefixEnd_7185140 : Nat := 4983230072969 + 3 ^ 40 * 7185140 * 2
def baseEnd_7185140 : Nat := 136645569994300864459487

theorem tailTrace_7185140 : CollatzResearch.WordTrace tailWord_7185140 prefixEnd_7185140 136645569994300864459487 := by
  unfold tailWord_7185140
  simp only [CollatzResearch.WordTrace]
  refine ⟨131031792594736189530380437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174709056792981586040507249 131031792594736189530380437)
  ·
    refine ⟨6142115277878258884236583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 131031792594736189530380437 6142115277878258884236583)
    ·
      refine ⟨9213172916817388326354875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6142115277878258884236583 9213172916817388326354875)
      ·
        refine ⟨13819759375226082489532313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9213172916817388326354875 13819759375226082489532313)
        ·
          refine ⟨10364819531419561867149235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13819759375226082489532313 10364819531419561867149235)
          ·
            refine ⟨15547229297129342800723853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10364819531419561867149235 15547229297129342800723853)
            ·
              refine ⟨5830210986423503550271445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15547229297129342800723853 5830210986423503550271445)
              ·
                refine ⟨136645569994300864459487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 5830210986423503550271445 136645569994300864459487)
                ·
                  rfl

theorem cell23_7185140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 3, 7].length) (baseStart_7185140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185140 prefixEnd_7185140 := by exact prefixLift 7185140
  have htrace : WordTrace (prefixWord ++ tailWord_7185140) baseStart_7185140 baseEnd_7185140 := by
    simpa [prefixWord, tailWord_7185140, baseEnd_7185140] using wordTrace_append hprefix tailTrace_7185140
  have hstable : (prefixWord ++ tailWord_7185140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185140).length < 2 ^ (prefixWord ++ tailWord_7185140).sum := by decide
  have hdescent : baseEnd_7185140 < baseStart_7185140 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185160 : List Nat := [2, 1, 3, 2, 2, 2, 4, 1, 1, 3, 2]
def baseStart_7185160 : Nat := 118140960795 + 7185160 * 2 ^ 59
def prefixEnd_7185160 : Nat := 4983230072969 + 3 ^ 40 * 7185160 * 2
def baseEnd_7185160 : Nat := 3689440659459213262156057

theorem tailTrace_7185160 : CollatzResearch.WordTrace tailWord_7185160 prefixEnd_7185160 3689440659459213262156057 := by
  unfold tailWord_7185160
  simp only [CollatzResearch.WordTrace]
  refine ⟨131032157324699961238244467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174709543099599948317659289 131032157324699961238244467)
  ·
    refine ⟨196548235987049941857366701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131032157324699961238244467 196548235987049941857366701)
    ·
      refine ⟨73705588495143728196512513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196548235987049941857366701 73705588495143728196512513)
      ·
        refine ⟨55279191371357796147384385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73705588495143728196512513 55279191371357796147384385)
        ·
          refine ⟨41459393528518347110538289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55279191371357796147384385 41459393528518347110538289)
          ·
            refine ⟨31094545146388760332903717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41459393528518347110538289 31094545146388760332903717)
            ·
              refine ⟨5830227214947892562419447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 31094545146388760332903717 5830227214947892562419447)
              ·
                refine ⟨8745340822421838843629171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5830227214947892562419447 8745340822421838843629171)
                ·
                  refine ⟨13118011233632758265443757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745340822421838843629171 13118011233632758265443757)
                  ·
                    refine ⟨4919254212612284349541409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13118011233632758265443757 4919254212612284349541409)
                    ·
                      refine ⟨3689440659459213262156057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919254212612284349541409 3689440659459213262156057)
                      ·
                        rfl

theorem cell23_7185160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 4, 1, 1, 3, 2].length) (baseStart_7185160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185160 prefixEnd_7185160 := by exact prefixLift 7185160
  have htrace : WordTrace (prefixWord ++ tailWord_7185160) baseStart_7185160 baseEnd_7185160 := by
    simpa [prefixWord, tailWord_7185160, baseEnd_7185160] using wordTrace_append hprefix tailTrace_7185160
  have hstable : (prefixWord ++ tailWord_7185160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185160).length < 2 ^ (prefixWord ++ tailWord_7185160).sum := by decide
  have hdescent : baseEnd_7185160 < baseStart_7185160 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185169 : List Nat := [1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 4]
def baseStart_7185169 : Nat := 118140960795 + 7185169 * 2 ^ 59
def prefixEnd_7185169 : Nat := 4983230072969 + 3 ^ 40 * 7185169 * 2
def baseEnd_7185169 : Nat := 3689445280785103726943515

theorem tailTrace_7185169 : CollatzResearch.WordTrace tailWord_7185169 prefixEnd_7185169 3689445280785103726943515 := by
  unfold tailWord_7185169
  simp only [CollatzResearch.WordTrace]
  refine ⟨262064642906367317013566561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174709761937578211342377707 262064642906367317013566561)
  ·
    refine ⟨196548482179775487760174921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262064642906367317013566561 196548482179775487760174921)
    ·
      refine ⟨147411361634831615820131191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196548482179775487760174921 147411361634831615820131191)
      ·
        refine ⟨221117042452247423730196787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147411361634831615820131191 221117042452247423730196787)
        ·
          refine ⟨331675563678371135595295181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221117042452247423730196787 331675563678371135595295181)
          ·
            refine ⟨124378336379389175848235693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331675563678371135595295181 124378336379389175848235693)
            ·
              refine ⟨46641876142270940943088385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 124378336379389175848235693 46641876142270940943088385)
              ·
                refine ⟨34981407106703205707316289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46641876142270940943088385 34981407106703205707316289)
                ·
                  refine ⟨26236055330027404280487217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34981407106703205707316289 26236055330027404280487217)
                  ·
                    refine ⟨19677041497520553210365413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26236055330027404280487217 19677041497520553210365413)
                    ·
                      refine ⟨3689445280785103726943515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19677041497520553210365413 3689445280785103726943515)
                      ·
                        rfl

theorem cell23_7185169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_7185169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185169 prefixEnd_7185169 := by exact prefixLift 7185169
  have htrace : WordTrace (prefixWord ++ tailWord_7185169) baseStart_7185169 baseEnd_7185169 := by
    simpa [prefixWord, tailWord_7185169, baseEnd_7185169] using wordTrace_append hprefix tailTrace_7185169
  have hstable : (prefixWord ++ tailWord_7185169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185169).length < 2 ^ (prefixWord ++ tailWord_7185169).sum := by decide
  have hdescent : baseEnd_7185169 < baseStart_7185169 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185173 : List Nat := [1, 3, 2, 1, 2, 2, 3, 1, 4, 2, 2]
def baseStart_7185173 : Nat := 118140960795 + 7185173 * 2 ^ 59
def prefixEnd_7185173 : Nat := 4983230072969 + 3 ^ 40 * 7185173 * 2
def baseEnd_7185173 : Nat := 3689447334707721711293497

theorem tailTrace_7185173 : CollatzResearch.WordTrace tailWord_7185173 prefixEnd_7185173 3689447334707721711293497 := by
  unfold tailWord_7185173
  simp only [CollatzResearch.WordTrace]
  refine ⟨262064788798352825696712173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174709859198901883797808115 262064788798352825696712173)
  ·
    refine ⟨98274295799382309636267065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262064788798352825696712173 98274295799382309636267065)
    ·
      refine ⟨73705721849536732227200299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98274295799382309636267065 73705721849536732227200299)
      ·
        refine ⟨110558582774305098340800449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73705721849536732227200299 110558582774305098340800449)
        ·
          refine ⟨82918937080728823755600337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 110558582774305098340800449 82918937080728823755600337)
          ·
            refine ⟨62189202810546617816700253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82918937080728823755600337 62189202810546617816700253)
            ·
              refine ⟨23320951053954981681262595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62189202810546617816700253 23320951053954981681262595)
              ·
                refine ⟨34981426580932472521893893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23320951053954981681262595 34981426580932472521893893)
                ·
                  refine ⟨6559017483924838597855105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34981426580932472521893893 6559017483924838597855105)
                  ·
                    refine ⟨4919263112943628948391329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6559017483924838597855105 4919263112943628948391329)
                    ·
                      refine ⟨3689447334707721711293497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919263112943628948391329 3689447334707721711293497)
                      ·
                        rfl

theorem cell23_7185173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 1, 4, 2, 2].length) (baseStart_7185173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185173 prefixEnd_7185173 := by exact prefixLift 7185173
  have htrace : WordTrace (prefixWord ++ tailWord_7185173) baseStart_7185173 baseEnd_7185173 := by
    simpa [prefixWord, tailWord_7185173, baseEnd_7185173] using wordTrace_append hprefix tailTrace_7185173
  have hstable : (prefixWord ++ tailWord_7185173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185173).length < 2 ^ (prefixWord ++ tailWord_7185173).sum := by decide
  have hdescent : baseEnd_7185173 < baseStart_7185173 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185186 : List Nat := [3, 3, 1, 1, 2, 2, 2, 1, 2, 2, 4]
def baseStart_7185186 : Nat := 118140960795 + 7185186 * 2 ^ 59
def prefixEnd_7185186 : Nat := 4983230072969 + 3 ^ 40 * 7185186 * 2
def baseEnd_7185186 : Nat := 3689454009956230160430937

theorem tailTrace_7185186 : CollatzResearch.WordTrace tailWord_7185186 prefixEnd_7185186 3689454009956230160430937 := by
  unfold tailWord_7185186
  simp only [CollatzResearch.WordTrace]
  refine ⟨65516315736826432229233853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174710175298203819277956941 65516315736826432229233853)
  ·
    refine ⟨24568618401309912085962695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65516315736826432229233853 24568618401309912085962695)
    ·
      refine ⟨36852927601964868128944043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24568618401309912085962695 36852927601964868128944043)
      ·
        refine ⟨55279391402947302193416065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36852927601964868128944043 55279391402947302193416065)
        ·
          refine ⟨41459543552210476645062049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55279391402947302193416065 41459543552210476645062049)
          ·
            refine ⟨31094657664157857483796537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41459543552210476645062049 31094657664157857483796537)
            ·
              refine ⟨23320993248118393112847403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31094657664157857483796537 23320993248118393112847403)
              ·
                refine ⟨34981489872177589669271105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23320993248118393112847403 34981489872177589669271105)
                ·
                  refine ⟨26236117404133192251953329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34981489872177589669271105 26236117404133192251953329)
                  ·
                    refine ⟨19677088053099894188964997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26236117404133192251953329 19677088053099894188964997)
                    ·
                      refine ⟨3689454009956230160430937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19677088053099894188964997 3689454009956230160430937)
                      ·
                        rfl

theorem cell23_7185186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 2, 4].length) (baseStart_7185186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185186 prefixEnd_7185186 := by exact prefixLift 7185186
  have htrace : WordTrace (prefixWord ++ tailWord_7185186) baseStart_7185186 baseEnd_7185186 := by
    simpa [prefixWord, tailWord_7185186, baseEnd_7185186] using wordTrace_append hprefix tailTrace_7185186
  have hstable : (prefixWord ++ tailWord_7185186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185186).length < 2 ^ (prefixWord ++ tailWord_7185186).sum := by decide
  have hdescent : baseEnd_7185186 < baseStart_7185186 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185219 : List Nat := [1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5]
def baseStart_7185219 : Nat := 118140960795 + 7185219 * 2 ^ 59
def prefixEnd_7185219 : Nat := 4983230072969 + 3 ^ 40 * 7185219 * 2
def baseEnd_7185219 : Nat := 3689470954817828531318285

theorem tailTrace_7185219 : CollatzResearch.WordTrace tailWord_7185219 prefixEnd_7185219 3689470954817828531318285 := by
  unfold tailWord_7185219
  simp only [CollatzResearch.WordTrace]
  refine ⟨262066466556186175552886711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174710977704124117035257807 262066466556186175552886711)
  ·
    refine ⟨393099699834279263329330067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262066466556186175552886711 393099699834279263329330067)
    ·
      refine ⟨589649549751418894993995101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393099699834279263329330067 589649549751418894993995101)
      ·
        refine ⟨221118581156782085622748163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 589649549751418894993995101 221118581156782085622748163)
        ·
          refine ⟨331677871735173128434122245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221118581156782085622748163 331677871735173128434122245)
          ·
            refine ⟨62189600950344961581397921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 331677871735173128434122245 62189600950344961581397921)
            ·
              refine ⟨46642200712758721186048441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62189600950344961581397921 46642200712758721186048441)
              ·
                refine ⟨34981650534569040889536331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46642200712758721186048441 34981650534569040889536331)
                ·
                  refine ⟨52472475801853561334304497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34981650534569040889536331 52472475801853561334304497)
                  ·
                    refine ⟨39354356851390171000728373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 52472475801853561334304497 39354356851390171000728373)
                    ·
                      refine ⟨3689470954817828531318285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39354356851390171000728373 3689470954817828531318285)
                      ·
                        rfl

theorem cell23_7185219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 2, 1, 2, 5].length) (baseStart_7185219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185219 prefixEnd_7185219 := by exact prefixLift 7185219
  have htrace : WordTrace (prefixWord ++ tailWord_7185219) baseStart_7185219 baseEnd_7185219 := by
    simpa [prefixWord, tailWord_7185219, baseEnd_7185219] using wordTrace_append hprefix tailTrace_7185219
  have hstable : (prefixWord ++ tailWord_7185219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185219).length < 2 ^ (prefixWord ++ tailWord_7185219).sum := by decide
  have hdescent : baseEnd_7185219 < baseStart_7185219 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185259 : List Nat := [1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4]
def baseStart_7185259 : Nat := 118140960795 + 7185259 * 2 ^ 59
def prefixEnd_7185259 : Nat := 4983230072969 + 3 ^ 40 * 7185259 * 2
def baseEnd_7185259 : Nat := 3689491494044008374818101

theorem tailTrace_7185259 : CollatzResearch.WordTrace tailWord_7185259 prefixEnd_7185259 3689491494044008374818101 := by
  unfold tailWord_7185259
  simp only [CollatzResearch.WordTrace]
  refine ⟨262067925476041262384342831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174711950317360841589561887 262067925476041262384342831)
  ·
    refine ⟨393101888214061893576514247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262067925476041262384342831 393101888214061893576514247)
    ·
      refine ⟨589652832321092840364771371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393101888214061893576514247 589652832321092840364771371)
      ·
        refine ⟨884479248481639260547157057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589652832321092840364771371 884479248481639260547157057)
        ·
          refine ⟨663359436361229445410367793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 884479248481639260547157057 663359436361229445410367793)
          ·
            refine ⟨497519577270922084057775845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663359436361229445410367793 497519577270922084057775845)
            ·
              refine ⟨93284920738297890760832971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 497519577270922084057775845 93284920738297890760832971)
              ·
                refine ⟨139927381107446836141249457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93284920738297890760832971 139927381107446836141249457)
                ·
                  refine ⟨104945535830585127105937093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139927381107446836141249457 104945535830585127105937093)
                  ·
                    refine ⟨19677287968234711332363205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 104945535830585127105937093 19677287968234711332363205)
                    ·
                      refine ⟨3689491494044008374818101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19677287968234711332363205 3689491494044008374818101)
                      ·
                        rfl

theorem cell23_7185259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 4, 4].length) (baseStart_7185259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185259 prefixEnd_7185259 := by exact prefixLift 7185259
  have htrace : WordTrace (prefixWord ++ tailWord_7185259) baseStart_7185259 baseEnd_7185259 := by
    simpa [prefixWord, tailWord_7185259, baseEnd_7185259] using wordTrace_append hprefix tailTrace_7185259
  have hstable : (prefixWord ++ tailWord_7185259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185259).length < 2 ^ (prefixWord ++ tailWord_7185259).sum := by decide
  have hdescent : baseEnd_7185259 < baseStart_7185259 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185266 : List Nat := [3, 2, 1, 2, 1, 1, 2, 3, 1, 4, 3]
def baseStart_7185266 : Nat := 118140960795 + 7185266 * 2 ^ 59
def prefixEnd_7185266 : Nat := 4983230072969 + 3 ^ 40 * 7185266 * 2
def baseEnd_7185266 : Nat := 3689495088408589847430569

theorem tailTrace_7185266 : CollatzResearch.WordTrace tailWord_7185266 prefixEnd_7185266 3689495088408589847430569 := by
  unfold tailWord_7185266
  simp only [CollatzResearch.WordTrace]
  refine ⟨65517045196753975644961913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174712120524677268386565101 65517045196753975644961913)
  ·
    refine ⟨49137783897565481733721435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65517045196753975644961913 49137783897565481733721435)
    ·
      refine ⟨73706675846348222600582153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49137783897565481733721435 73706675846348222600582153)
      ·
        refine ⟨55280006884761166950436615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73706675846348222600582153 55280006884761166950436615)
        ·
          refine ⟨82920010327141750425654923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55280006884761166950436615 82920010327141750425654923)
          ·
            refine ⟨124380015490712625638482385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82920010327141750425654923 124380015490712625638482385)
            ·
              refine ⟨93285011618034469228861789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124380015490712625638482385 93285011618034469228861789)
              ·
                refine ⟨34981879356762925960823171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93285011618034469228861789 34981879356762925960823171)
                ·
                  refine ⟨52472819035144388941234757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34981879356762925960823171 52472819035144388941234757)
                  ·
                    refine ⟨9838653569089572926481517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52472819035144388941234757 9838653569089572926481517)
                    ·
                      refine ⟨3689495088408589847430569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838653569089572926481517 3689495088408589847430569)
                      ·
                        rfl

theorem cell23_7185266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 3, 1, 4, 3].length) (baseStart_7185266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185266 prefixEnd_7185266 := by exact prefixLift 7185266
  have htrace : WordTrace (prefixWord ++ tailWord_7185266) baseStart_7185266 baseEnd_7185266 := by
    simpa [prefixWord, tailWord_7185266, baseEnd_7185266] using wordTrace_append hprefix tailTrace_7185266
  have hstable : (prefixWord ++ tailWord_7185266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185266).length < 2 ^ (prefixWord ++ tailWord_7185266).sum := by decide
  have hdescent : baseEnd_7185266 < baseStart_7185266 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185316 : List Nat := [2, 3, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_7185316 : Nat := 118140960795 + 7185316 * 2 ^ 59
def prefixEnd_7185316 : Nat := 4983230072969 + 3 ^ 40 * 7185316 * 2
def baseEnd_7185316 : Nat := 1229840254147104883935113

theorem tailTrace_7185316 : CollatzResearch.WordTrace tailWord_7185316 prefixEnd_7185316 1229840254147104883935113 := by
  unfold tailWord_7185316
  simp only [CollatzResearch.WordTrace]
  refine ⟨131035002218417380559583901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174713336291223174079445201 131035002218417380559583901)
  ·
    refine ⟨49138125831906517709843963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131035002218417380559583901 49138125831906517709843963)
    ·
      refine ⟨73707188747859776564765945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49138125831906517709843963 73707188747859776564765945)
      ·
        refine ⟨55280391560894832423574459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73707188747859776564765945 55280391560894832423574459)
        ·
          refine ⟨82920587341342248635361689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55280391560894832423574459 82920587341342248635361689)
          ·
            refine ⟨62190440506006686476521267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82920587341342248635361689 62190440506006686476521267)
            ·
              refine ⟨93285660759010029714781901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62190440506006686476521267 93285660759010029714781901)
              ·
                refine ⟨34982122784628761143043213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 93285660759010029714781901 34982122784628761143043213)
                ·
                  refine ⟨13118296044235785428641205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 34982122784628761143043213 13118296044235785428641205)
                  ·
                    refine ⟨1229840254147104883935113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13118296044235785428641205 1229840254147104883935113)
                    ·
                      rfl

theorem cell23_7185316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_7185316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185316 prefixEnd_7185316 := by exact prefixLift 7185316
  have htrace : WordTrace (prefixWord ++ tailWord_7185316) baseStart_7185316 baseEnd_7185316 := by
    simpa [prefixWord, tailWord_7185316, baseEnd_7185316] using wordTrace_append hprefix tailTrace_7185316
  have hstable : (prefixWord ++ tailWord_7185316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185316).length < 2 ^ (prefixWord ++ tailWord_7185316).sum := by decide
  have hdescent : baseEnd_7185316 < baseStart_7185316 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185333 : List Nat := [1, 3, 3, 2, 1, 1, 3, 3, 1, 5]
def baseStart_7185333 : Nat := 118140960795 + 7185333 * 2 ^ 59
def prefixEnd_7185333 : Nat := 4983230072969 + 3 ^ 40 * 7185333 * 2
def baseEnd_7185333 : Nat := 1229843163870813695097587

theorem tailTrace_7185333 : CollatzResearch.WordTrace tailWord_7185333 prefixEnd_7185333 1229843163870813695097587 := by
  unfold tailWord_7185333
  simp only [CollatzResearch.WordTrace]
  refine ⟨262070624477773173022536653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174713749651848782015024435 262070624477773173022536653)
  ·
    refine ⟨98276484179164939883451245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262070624477773173022536653 98276484179164939883451245)
    ·
      refine ⟨36853681567186852456294217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 98276484179164939883451245 36853681567186852456294217)
      ·
        refine ⟨27640261175390139342220663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36853681567186852456294217 27640261175390139342220663)
        ·
          refine ⟨41460391763085209013330995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27640261175390139342220663 41460391763085209013330995)
          ·
            refine ⟨62190587644627813519996493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41460391763085209013330995 62190587644627813519996493)
            ·
              refine ⟨23321470366735430069998685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62190587644627813519996493 23321470366735430069998685)
              ·
                refine ⟨8745551387525786276249507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23321470366735430069998685 8745551387525786276249507)
                ·
                  refine ⟨13118327081288679414374261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745551387525786276249507 13118327081288679414374261)
                  ·
                    refine ⟨1229843163870813695097587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13118327081288679414374261 1229843163870813695097587)
                    ·
                      rfl

theorem cell23_7185333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_7185333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185333 prefixEnd_7185333 := by exact prefixLift 7185333
  have htrace : WordTrace (prefixWord ++ tailWord_7185333) baseStart_7185333 baseEnd_7185333 := by
    simpa [prefixWord, tailWord_7185333, baseEnd_7185333] using wordTrace_append hprefix tailTrace_7185333
  have hstable : (prefixWord ++ tailWord_7185333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185333).length < 2 ^ (prefixWord ++ tailWord_7185333).sum := by decide
  have hdescent : baseEnd_7185333 < baseStart_7185333 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185370 : List Nat := [3, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4]
def baseStart_7185370 : Nat := 118140960795 + 7185370 * 2 ^ 59
def prefixEnd_7185370 : Nat := 4983230072969 + 3 ^ 40 * 7185370 * 2
def baseEnd_7185370 : Nat := 3689548490396657440530091

theorem tailTrace_7185370 : CollatzResearch.WordTrace tailWord_7185370 prefixEnd_7185370 3689548490396657440530091 := by
  unfold tailWord_7185370
  simp only [CollatzResearch.WordTrace]
  refine ⟨65517993494659782085408391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174714649319092752227755709 65517993494659782085408391)
  ·
    refine ⟨98276990241989673128112587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65517993494659782085408391 98276990241989673128112587)
    ·
      refine ⟨147415485362984509692168881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98276990241989673128112587 147415485362984509692168881)
      ·
        refine ⟨110561614022238382269126661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147415485362984509692168881 110561614022238382269126661)
        ·
          refine ⟨20730302629169696675461249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110561614022238382269126661 20730302629169696675461249)
          ·
            refine ⟨15547726971877272506595937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20730302629169696675461249 15547726971877272506595937)
            ·
              refine ⟨11660795228907954379946953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15547726971877272506595937 11660795228907954379946953)
              ·
                refine ⟨8745596421680965784960215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11660795228907954379946953 8745596421680965784960215)
                ·
                  refine ⟨13118394632521448677440323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8745596421680965784960215 13118394632521448677440323)
                  ·
                    refine ⟨19677591948782173016160485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13118394632521448677440323 19677591948782173016160485)
                    ·
                      refine ⟨3689548490396657440530091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19677591948782173016160485 3689548490396657440530091)
                      ·
                        rfl

theorem cell23_7185370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_7185370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185370 prefixEnd_7185370 := by exact prefixLift 7185370
  have htrace : WordTrace (prefixWord ++ tailWord_7185370) baseStart_7185370 baseEnd_7185370 := by
    simpa [prefixWord, tailWord_7185370, baseEnd_7185370] using wordTrace_append hprefix tailTrace_7185370
  have hstable : (prefixWord ++ tailWord_7185370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185370).length < 2 ^ (prefixWord ++ tailWord_7185370).sum := by decide
  have hdescent : baseEnd_7185370 < baseStart_7185370 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185381 : List Nat := [1, 3, 1, 6, 1, 2, 1, 3, 1, 1, 3]
def baseStart_7185381 : Nat := 118140960795 + 7185381 * 2 ^ 59
def prefixEnd_7185381 : Nat := 4983230072969 + 3 ^ 40 * 7185381 * 2
def baseEnd_7185381 : Nat := 3689554138683856897492541

theorem tailTrace_7185381 : CollatzResearch.WordTrace tailWord_7185381 prefixEnd_7185381 3689554138683856897492541 := by
  unfold tailWord_7185381
  simp only [CollatzResearch.WordTrace]
  refine ⟨262072375181599277220283997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174714916787732851480189331 262072375181599277220283997)
  ·
    refine ⟨98277140693099728957606499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262072375181599277220283997 98277140693099728957606499)
    ·
      refine ⟨147415711039649593436409749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98277140693099728957606499 147415711039649593436409749)
      ·
        refine ⟨6910111454983574692331707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 147415711039649593436409749 6910111454983574692331707)
        ·
          refine ⟨10365167182475362038497561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6910111454983574692331707 10365167182475362038497561)
          ·
            refine ⟨7773875386856521528873171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10365167182475362038497561 7773875386856521528873171)
            ·
              refine ⟨11660813080284782293309757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7773875386856521528873171 11660813080284782293309757)
              ·
                refine ⟨4372804905106793359991159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11660813080284782293309757 4372804905106793359991159)
                ·
                  refine ⟨6559207357660190039986739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4372804905106793359991159 6559207357660190039986739)
                  ·
                    refine ⟨9838811036490285059980109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6559207357660190039986739 9838811036490285059980109)
                    ·
                      refine ⟨3689554138683856897492541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838811036490285059980109 3689554138683856897492541)
                      ·
                        rfl

theorem cell23_7185381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 2, 1, 3, 1, 1, 3].length) (baseStart_7185381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185381 prefixEnd_7185381 := by exact prefixLift 7185381
  have htrace : WordTrace (prefixWord ++ tailWord_7185381) baseStart_7185381 baseEnd_7185381 := by
    simpa [prefixWord, tailWord_7185381, baseEnd_7185381] using wordTrace_append hprefix tailTrace_7185381
  have hstable : (prefixWord ++ tailWord_7185381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185381).length < 2 ^ (prefixWord ++ tailWord_7185381).sum := by decide
  have hdescent : baseEnd_7185381 < baseStart_7185381 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185390 : List Nat := [4, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5]
def baseStart_7185390 : Nat := 118140960795 + 7185390 * 2 ^ 59
def prefixEnd_7185390 : Nat := 4983230072969 + 3 ^ 40 * 7185390 * 2
def baseEnd_7185390 : Nat := 3689558760009747362279999

theorem tailTrace_7185390 : CollatzResearch.WordTrace tailWord_7185390 prefixEnd_7185390 3689558760009747362279999 := by
  unfold tailWord_7185390
  simp only [CollatzResearch.WordTrace]
  refine ⟨32759087929820833969670203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174715135625711114504907749 32759087929820833969670203)
  ·
    refine ⟨49138631894731250954505305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32759087929820833969670203 49138631894731250954505305)
    ·
      refine ⟨36853973921048438215878979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49138631894731250954505305 36853973921048438215878979)
      ·
        refine ⟨55280960881572657323818469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36853973921048438215878979 55280960881572657323818469)
        ·
          refine ⟨10365180165294873248215963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55280960881572657323818469 10365180165294873248215963)
          ·
            refine ⟨15547770247942309872323945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365180165294873248215963 15547770247942309872323945)
            ·
              refine ⟨11660827685956732404242959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15547770247942309872323945 11660827685956732404242959)
              ·
                refine ⟨17491241528935098606364439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11660827685956732404242959 17491241528935098606364439)
                ·
                  refine ⟨26236862293402647909546659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17491241528935098606364439 26236862293402647909546659)
                  ·
                    refine ⟨39355293440103971864319989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26236862293402647909546659 39355293440103971864319989)
                    ·
                      refine ⟨3689558760009747362279999, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39355293440103971864319989 3689558760009747362279999)
                      ·
                        rfl

theorem cell23_7185390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5].length) (baseStart_7185390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185390 prefixEnd_7185390 := by exact prefixLift 7185390
  have htrace : WordTrace (prefixWord ++ tailWord_7185390) baseStart_7185390 baseEnd_7185390 := by
    simpa [prefixWord, tailWord_7185390, baseEnd_7185390] using wordTrace_append hprefix tailTrace_7185390
  have hstable : (prefixWord ++ tailWord_7185390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185390).length < 2 ^ (prefixWord ++ tailWord_7185390).sum := by decide
  have hdescent : baseEnd_7185390 < baseStart_7185390 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185460 : List Nat := [2, 5, 1, 2, 1, 1, 1, 1, 2, 3, 4]
def baseStart_7185460 : Nat := 118140960795 + 7185460 * 2 ^ 59
def prefixEnd_7185460 : Nat := 4983230072969 + 3 ^ 40 * 7185460 * 2
def baseEnd_7185460 : Nat := 3689594703655562088404677

theorem tailTrace_7185460 : CollatzResearch.WordTrace tailWord_7185460 prefixEnd_7185460 3689594703655562088404677 := by
  unfold tailWord_7185460
  simp only [CollatzResearch.WordTrace]
  refine ⟨131037628274156536856204917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174716837698875382474939889 131037628274156536856204917)
  ·
    refine ⟨12284777650702175330269211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 131037628274156536856204917 12284777650702175330269211)
    ·
      refine ⟨18427166476053262995403817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12284777650702175330269211 18427166476053262995403817)
      ·
        refine ⟨13820374857039947246552863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 18427166476053262995403817 13820374857039947246552863)
        ·
          refine ⟨20730562285559920869829295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13820374857039947246552863 20730562285559920869829295)
          ·
            refine ⟨31095843428339881304743943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20730562285559920869829295 31095843428339881304743943)
            ·
              refine ⟨46643765142509821957115915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31095843428339881304743943 46643765142509821957115915)
              ·
                refine ⟨69965647713764732935673873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 46643765142509821957115915 69965647713764732935673873)
                ·
                  refine ⟨52474235785323549701755405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 69965647713764732935673873 52474235785323549701755405)
                  ·
                    refine ⟨19677838419496331138158277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52474235785323549701755405 19677838419496331138158277)
                    ·
                      refine ⟨3689594703655562088404677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19677838419496331138158277 3689594703655562088404677)
                      ·
                        rfl

theorem cell23_7185460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_7185460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185460 prefixEnd_7185460 := by exact prefixLift 7185460
  have htrace : WordTrace (prefixWord ++ tailWord_7185460) baseStart_7185460 baseEnd_7185460 := by
    simpa [prefixWord, tailWord_7185460, baseEnd_7185460] using wordTrace_append hprefix tailTrace_7185460
  have hstable : (prefixWord ++ tailWord_7185460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185460).length < 2 ^ (prefixWord ++ tailWord_7185460).sum := by decide
  have hdescent : baseEnd_7185460 < baseStart_7185460 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185470 : List Nat := [4, 2, 1, 3, 1, 2, 1, 1, 2, 6]
def baseStart_7185470 : Nat := 118140960795 + 7185470 * 2 ^ 59
def prefixEnd_7185470 : Nat := 4983230072969 + 3 ^ 40 * 7185470 * 2
def baseEnd_7185470 : Nat := 1229866612820702349759877

theorem tailTrace_7185470 : CollatzResearch.WordTrace tailWord_7185470 prefixEnd_7185470 1229866612820702349759877 := by
  unfold tailWord_7185470
  simp only [CollatzResearch.WordTrace]
  refine ⟨32759452659784605677534233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174717080852184563613515909 32759452659784605677534233)
  ·
    refine ⟨24569589494838454258150675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32759452659784605677534233 24569589494838454258150675)
    ·
      refine ⟨36854384242257681387226013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24569589494838454258150675 36854384242257681387226013)
      ·
        refine ⟨13820394090846630520209755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 36854384242257681387226013 13820394090846630520209755)
        ·
          refine ⟨20730591136269945780314633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13820394090846630520209755 20730591136269945780314633)
          ·
            refine ⟨15547943352202459335235975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20730591136269945780314633 15547943352202459335235975)
            ·
              refine ⟨23321915028303689002853963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15547943352202459335235975 23321915028303689002853963)
              ·
                refine ⟨34982872542455533504280945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23321915028303689002853963 34982872542455533504280945)
                ·
                  refine ⟨26237154406841650128210709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34982872542455533504280945 26237154406841650128210709)
                  ·
                    refine ⟨1229866612820702349759877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26237154406841650128210709 1229866612820702349759877)
                    ·
                      rfl

theorem cell23_7185470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 2, 6].length) (baseStart_7185470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185470 prefixEnd_7185470 := by exact prefixLift 7185470
  have htrace : WordTrace (prefixWord ++ tailWord_7185470) baseStart_7185470 baseEnd_7185470 := by
    simpa [prefixWord, tailWord_7185470, baseEnd_7185470] using wordTrace_append hprefix tailTrace_7185470
  have hstable : (prefixWord ++ tailWord_7185470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185470).length < 2 ^ (prefixWord ++ tailWord_7185470).sum := by decide
  have hdescent : baseEnd_7185470 < baseStart_7185470 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185477 : List Nat := [1, 3, 1, 1, 1, 3, 4, 3, 2, 2, 2]
def baseStart_7185477 : Nat := 118140960795 + 7185477 * 2 ^ 59
def prefixEnd_7185477 : Nat := 4983230072969 + 3 ^ 40 * 7185477 * 2
def baseEnd_7185477 : Nat := 3689603432826688521892099

theorem tailTrace_7185477 : CollatzResearch.WordTrace tailWord_7185477 prefixEnd_7185477 3689603432826688521892099 := by
  unfold tailWord_7185477
  simp only [CollatzResearch.WordTrace]
  refine ⟨262075876589251485615778685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174717251059500990410519123 262075876589251485615778685)
  ·
    refine ⟨98278453720969307105917007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262075876589251485615778685 98278453720969307105917007)
    ·
      refine ⟨147417680581453960658875511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98278453720969307105917007 147417680581453960658875511)
      ·
        refine ⟨221126520872180940988313267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147417680581453960658875511 221126520872180940988313267)
        ·
          refine ⟨331689781308271411482469901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221126520872180940988313267 331689781308271411482469901)
          ·
            refine ⟨124383667990601779305926213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 331689781308271411482469901 124383667990601779305926213)
            ·
              refine ⟨23321937748237833619861165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 124383667990601779305926213 23321937748237833619861165)
              ·
                refine ⟨8745726655589187607447937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23321937748237833619861165 8745726655589187607447937)
                ·
                  refine ⟨6559294991691890705585953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8745726655589187607447937 6559294991691890705585953)
                  ·
                    refine ⟨4919471243768918029189465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6559294991691890705585953 4919471243768918029189465)
                    ·
                      refine ⟨3689603432826688521892099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919471243768918029189465 3689603432826688521892099)
                      ·
                        rfl

theorem cell23_7185477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 2, 2, 2].length) (baseStart_7185477 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185477 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185477 prefixEnd_7185477 := by exact prefixLift 7185477
  have htrace : WordTrace (prefixWord ++ tailWord_7185477) baseStart_7185477 baseEnd_7185477 := by
    simpa [prefixWord, tailWord_7185477, baseEnd_7185477] using wordTrace_append hprefix tailTrace_7185477
  have hstable : (prefixWord ++ tailWord_7185477).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185477).length < 2 ^ (prefixWord ++ tailWord_7185477).sum := by decide
  have hdescent : baseEnd_7185477 < baseStart_7185477 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185493 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_7185493 : Nat := 118140960795 + 7185493 * 2 ^ 59
def prefixEnd_7185493 : Nat := 4983230072969 + 3 ^ 40 * 7185493 * 2
def baseEnd_7185493 : Nat := 3689611648517160459292025

theorem tailTrace_7185493 : CollatzResearch.WordTrace tailWord_7185493 prefixEnd_7185493 3689611648517160459292025 := by
  unfold tailWord_7185493
  simp only [CollatzResearch.WordTrace]
  refine ⟨262076460157193520348361133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174717640104795680232240755 262076460157193520348361133)
  ·
    refine ⟨98278672558947570130635425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262076460157193520348361133 98278672558947570130635425)
    ·
      refine ⟨73709004419210677597976569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98278672558947570130635425 73709004419210677597976569)
      ·
        refine ⟨55281753314408008198482427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73709004419210677597976569 55281753314408008198482427)
        ·
          refine ⟨82922629971612012297723641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55281753314408008198482427 82922629971612012297723641)
          ·
            refine ⟨62191972478709009223292731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82922629971612012297723641 62191972478709009223292731)
            ·
              refine ⟨93287958718063513834939097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62191972478709009223292731 93287958718063513834939097)
              ·
                refine ⟨69965969038547635376204323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93287958718063513834939097 69965969038547635376204323)
                ·
                  refine ⟨104948953557821453064306485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 69965969038547635376204323 104948953557821453064306485)
                  ·
                    refine ⟨9838964396045761224778733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104948953557821453064306485 9838964396045761224778733)
                    ·
                      refine ⟨3689611648517160459292025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9838964396045761224778733 3689611648517160459292025)
                      ·
                        rfl

theorem cell23_7185493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_7185493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185493 prefixEnd_7185493 := by exact prefixLift 7185493
  have htrace : WordTrace (prefixWord ++ tailWord_7185493) baseStart_7185493 baseEnd_7185493 := by
    simpa [prefixWord, tailWord_7185493, baseEnd_7185493] using wordTrace_append hprefix tailTrace_7185493
  have hstable : (prefixWord ++ tailWord_7185493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185493).length < 2 ^ (prefixWord ++ tailWord_7185493).sum := by decide
  have hdescent : baseEnd_7185493 < baseStart_7185493 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185533 : List Nat := [1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 4]
def baseStart_7185533 : Nat := 118140960795 + 7185533 * 2 ^ 59
def prefixEnd_7185533 : Nat := 4983230072969 + 3 ^ 40 * 7185533 * 2
def baseEnd_7185533 : Nat := 3689632187743340302791841

theorem tailTrace_7185533 : CollatzResearch.WordTrace tailWord_7185533 prefixEnd_7185533 3689632187743340302791841 := by
  unfold tailWord_7185533
  simp only [CollatzResearch.WordTrace]
  refine ⟨262077919077048607179817253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174718612718032404786544835 262077919077048607179817253)
  ·
    refine ⟨49139609826946613846215735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262077919077048607179817253 49139609826946613846215735)
    ·
      refine ⟨73709414740419920769323603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49139609826946613846215735 73709414740419920769323603)
      ·
        refine ⟨110564122110629881153985405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73709414740419920769323603 110564122110629881153985405)
        ·
          refine ⟨41461545791486205432744527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110564122110629881153985405 41461545791486205432744527)
          ·
            refine ⟨62192318687229308149116791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41461545791486205432744527 62192318687229308149116791)
            ·
              refine ⟨93288478030843962223675187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62192318687229308149116791 93288478030843962223675187)
              ·
                refine ⟨139932717046265943335512781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93288478030843962223675187 139932717046265943335512781)
                ·
                  refine ⟨52474768892349728750817293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 139932717046265943335512781 52474768892349728750817293)
                  ·
                    refine ⟨19678038334631148281556485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52474768892349728750817293 19678038334631148281556485)
                    ·
                      refine ⟨3689632187743340302791841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19678038334631148281556485 3689632187743340302791841)
                      ·
                        rfl

theorem cell23_7185533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_7185533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185533 prefixEnd_7185533 := by exact prefixLift 7185533
  have htrace : WordTrace (prefixWord ++ tailWord_7185533) baseStart_7185533 baseEnd_7185533 := by
    simpa [prefixWord, tailWord_7185533, baseEnd_7185533] using wordTrace_append hprefix tailTrace_7185533
  have hstable : (prefixWord ++ tailWord_7185533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185533).length < 2 ^ (prefixWord ++ tailWord_7185533).sum := by decide
  have hdescent : baseEnd_7185533 < baseStart_7185533 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185550 : List Nat := [4, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4]
def baseStart_7185550 : Nat := 118140960795 + 7185550 * 2 ^ 59
def prefixEnd_7185550 : Nat := 4983230072969 + 3 ^ 40 * 7185550 * 2
def baseEnd_7185550 : Nat := 3689640916914466736279263

theorem tailTrace_7185550 : CollatzResearch.WordTrace tailWord_7185550 prefixEnd_7185550 3689640916914466736279263 := by
  unfold tailWord_7185550
  simp only [CollatzResearch.WordTrace]
  refine ⟨32759817389748377385398263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174719026078658012722124069 32759817389748377385398263)
  ·
    refine ⟨49139726084622566078097395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32759817389748377385398263 49139726084622566078097395)
    ·
      refine ⟨73709589126933849117146093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49139726084622566078097395 73709589126933849117146093)
      ·
        refine ⟨27641095922600193418929785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 73709589126933849117146093 27641095922600193418929785)
        ·
          refine ⟨20730821941950145064197339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27641095922600193418929785 20730821941950145064197339)
          ·
            refine ⟨31096232912925217596296009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 20730821941950145064197339 31096232912925217596296009)
            ·
              refine ⟨23322174684693913197222007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31096232912925217596296009 23322174684693913197222007)
              ·
                refine ⟨34983262027040869795833011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23322174684693913197222007 34983262027040869795833011)
                ·
                  refine ⟨52474893040561304693749517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34983262027040869795833011 52474893040561304693749517)
                  ·
                    refine ⟨19678084890210489260156069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 52474893040561304693749517 19678084890210489260156069)
                    ·
                      refine ⟨3689640916914466736279263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19678084890210489260156069 3689640916914466736279263)
                      ·
                        rfl

theorem cell23_7185550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 2, 1, 1, 3, 4].length) (baseStart_7185550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185550 prefixEnd_7185550 := by exact prefixLift 7185550
  have htrace : WordTrace (prefixWord ++ tailWord_7185550) baseStart_7185550 baseEnd_7185550 := by
    simpa [prefixWord, tailWord_7185550, baseEnd_7185550] using wordTrace_append hprefix tailTrace_7185550
  have hstable : (prefixWord ++ tailWord_7185550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185550).length < 2 ^ (prefixWord ++ tailWord_7185550).sum := by decide
  have hdescent : baseEnd_7185550 < baseStart_7185550 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185567 : List Nat := [1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 4]
def baseStart_7185567 : Nat := 118140960795 + 7185567 * 2 ^ 59
def prefixEnd_7185567 : Nat := 4983230072969 + 3 ^ 40 * 7185567 * 2
def baseEnd_7185567 : Nat := 3689649646085593169766685

theorem tailTrace_7185567 : CollatzResearch.WordTrace tailWord_7185567 prefixEnd_7185567 3689649646085593169766685 := by
  unfold tailWord_7185567
  simp only [CollatzResearch.WordTrace]
  refine ⟨262079159158925430986554955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174719439439283620657703303 262079159158925430986554955)
  ·
    refine ⟨393118738738388146479832433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262079159158925430986554955 393118738738388146479832433)
    ·
      refine ⟨294839054053791109859874325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393118738738388146479832433 294839054053791109859874325)
      ·
        refine ⟨13820580658771458274681609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 294839054053791109859874325 13820580658771458274681609)
        ·
          refine ⟨10365435494078593706011207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13820580658771458274681609 10365435494078593706011207)
          ·
            refine ⟨15548153241117890559016811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365435494078593706011207 15548153241117890559016811)
            ·
              refine ⟨23322229861676835838525217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15548153241117890559016811 23322229861676835838525217)
              ·
                refine ⟨17491672396257626878893913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23322229861676835838525217 17491672396257626878893913)
                ·
                  refine ⟨13118754297193220159170435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17491672396257626878893913 13118754297193220159170435)
                  ·
                    refine ⟨19678131445789830238755653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13118754297193220159170435 19678131445789830238755653)
                    ·
                      refine ⟨3689649646085593169766685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19678131445789830238755653 3689649646085593169766685)
                      ·
                        rfl

theorem cell23_7185567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 1, 4].length) (baseStart_7185567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185567 prefixEnd_7185567 := by exact prefixLift 7185567
  have htrace : WordTrace (prefixWord ++ tailWord_7185567) baseStart_7185567 baseEnd_7185567 := by
    simpa [prefixWord, tailWord_7185567, baseEnd_7185567] using wordTrace_append hprefix tailTrace_7185567
  have hstable : (prefixWord ++ tailWord_7185567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185567).length < 2 ^ (prefixWord ++ tailWord_7185567).sum := by decide
  have hdescent : baseEnd_7185567 < baseStart_7185567 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185573 : List Nat := [1, 3, 1, 2, 1, 4, 2, 1, 8]
def baseStart_7185573 : Nat := 118140960795 + 7185573 * 2 ^ 59
def prefixEnd_7185573 : Nat := 4983230072969 + 3 ^ 40 * 7185573 * 2
def baseEnd_7185573 : Nat := 409961414107724460699073

theorem tailTrace_7185573 : CollatzResearch.WordTrace tailWord_7185573 prefixEnd_7185573 409961414107724460699073 := by
  unfold tailWord_7185573
  simp only [CollatzResearch.WordTrace]
  refine ⟨262079377996903694011273373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174719585331269129340848915 262079377996903694011273373)
  ·
    refine ⟨98279766748838885254227515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262079377996903694011273373 98279766748838885254227515)
    ·
      refine ⟨147419650123258327881341273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98279766748838885254227515 147419650123258327881341273)
      ·
        refine ⟨110564737592443745911005955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 147419650123258327881341273 110564737592443745911005955)
        ·
          refine ⟨165847106388665618866508933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110564737592443745911005955 165847106388665618866508933)
          ·
            refine ⟨31096332447874803537470425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165847106388665618866508933 31096332447874803537470425)
            ·
              refine ⟨23322249335906102653102819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31096332447874803537470425 23322249335906102653102819)
              ·
                refine ⟨34983374003859153979654229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23322249335906102653102819 34983374003859153979654229)
                ·
                  refine ⟨409961414107724460699073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 34983374003859153979654229 409961414107724460699073)
                  ·
                    rfl

theorem cell23_7185573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 2, 1, 8].length) (baseStart_7185573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185573 prefixEnd_7185573 := by exact prefixLift 7185573
  have htrace : WordTrace (prefixWord ++ tailWord_7185573) baseStart_7185573 baseEnd_7185573 := by
    simpa [prefixWord, tailWord_7185573, baseEnd_7185573] using wordTrace_append hprefix tailTrace_7185573
  have hstable : (prefixWord ++ tailWord_7185573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185573).length < 2 ^ (prefixWord ++ tailWord_7185573).sum := by decide
  have hdescent : baseEnd_7185573 < baseStart_7185573 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185604 : List Nat := [2, 3, 3, 1, 3, 1, 2, 1, 2, 2, 3]
def baseStart_7185604 : Nat := 118140960795 + 7185604 * 2 ^ 59
def prefixEnd_7185604 : Nat := 4983230072969 + 3 ^ 40 * 7185604 * 2
def baseEnd_7185604 : Nat := 3689668644869809525004015

theorem tailTrace_7185604 : CollatzResearch.WordTrace tailWord_7185604 prefixEnd_7185604 3689668644869809525004015 := by
  unfold tailWord_7185604
  simp only [CollatzResearch.WordTrace]
  refine ⟨131040254329895693152825933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174720339106527590870434577 131040254329895693152825933)
  ·
    refine ⟨49140095373710884932309725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 131040254329895693152825933 49140095373710884932309725)
    ·
      refine ⟨18427535765141581849616147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 49140095373710884932309725 18427535765141581849616147)
      ·
        refine ⟨27641303647712372774424221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18427535765141581849616147 27641303647712372774424221)
        ·
          refine ⟨10365488867892139790409083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27641303647712372774424221 10365488867892139790409083)
          ·
            refine ⟨15548233301838209685613625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365488867892139790409083 15548233301838209685613625)
            ·
              refine ⟨11661174976378657264210219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15548233301838209685613625 11661174976378657264210219)
              ·
                refine ⟨17491762464567985896315329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11661174976378657264210219 17491762464567985896315329)
                ·
                  refine ⟨13118821848425989422236497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 17491762464567985896315329 13118821848425989422236497)
                  ·
                    refine ⟨9839116386319492066677373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13118821848425989422236497 9839116386319492066677373)
                    ·
                      refine ⟨3689668644869809525004015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9839116386319492066677373 3689668644869809525004015)
                      ·
                        rfl

theorem cell23_7185604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 2, 2, 3].length) (baseStart_7185604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185604 prefixEnd_7185604 := by exact prefixLift 7185604
  have htrace : WordTrace (prefixWord ++ tailWord_7185604) baseStart_7185604 baseEnd_7185604 := by
    simpa [prefixWord, tailWord_7185604, baseEnd_7185604] using wordTrace_append hprefix tailTrace_7185604
  have hstable : (prefixWord ++ tailWord_7185604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185604).length < 2 ^ (prefixWord ++ tailWord_7185604).sum := by decide
  have hdescent : baseEnd_7185604 < baseStart_7185604 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185640 : List Nat := [2, 1, 4, 1, 2, 1, 1, 1, 5, 1, 4]
def baseStart_7185640 : Nat := 118140960795 + 7185640 * 2 ^ 59
def prefixEnd_7185640 : Nat := 4983230072969 + 3 ^ 40 * 7185640 * 2
def baseEnd_7185640 : Nat := 3689687130173371384153849

theorem tailTrace_7185640 : CollatzResearch.WordTrace tailWord_7185640 prefixEnd_7185640 3689687130173371384153849 := by
  unfold tailWord_7185640
  simp only [CollatzResearch.WordTrace]
  refine ⟨131040910843830482226981187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174721214458440642969308249 131040910843830482226981187)
  ·
    refine ⟨196561366265745723340471781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131040910843830482226981187 196561366265745723340471781)
    ·
      refine ⟨36855256174827323126338459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196561366265745723340471781 36855256174827323126338459)
      ·
        refine ⟨55282884262240984689507689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36855256174827323126338459 55282884262240984689507689)
        ·
          refine ⟨41462163196680738517130767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55282884262240984689507689 41462163196680738517130767)
          ·
            refine ⟨62193244795021107775696151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41462163196680738517130767 62193244795021107775696151)
            ·
              refine ⟨93289867192531661663544227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62193244795021107775696151 93289867192531661663544227)
              ·
                refine ⟨139934800788797492495316341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93289867192531661663544227 139934800788797492495316341)
                ·
                  refine ⟨13118887573949764921435907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 139934800788797492495316341 13118887573949764921435907)
                  ·
                    refine ⟨19678331360924647382153861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13118887573949764921435907 19678331360924647382153861)
                    ·
                      refine ⟨3689687130173371384153849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19678331360924647382153861 3689687130173371384153849)
                      ·
                        rfl

theorem cell23_7185640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_7185640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185640 prefixEnd_7185640 := by exact prefixLift 7185640
  have htrace : WordTrace (prefixWord ++ tailWord_7185640) baseStart_7185640 baseEnd_7185640 := by
    simpa [prefixWord, tailWord_7185640, baseEnd_7185640] using wordTrace_append hprefix tailTrace_7185640
  have hstable : (prefixWord ++ tailWord_7185640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185640).length < 2 ^ (prefixWord ++ tailWord_7185640).sum := by decide
  have hdescent : baseEnd_7185640 < baseStart_7185640 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185683 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6]
def baseStart_7185683 : Nat := 118140960795 + 7185683 * 2 ^ 59
def prefixEnd_7185683 : Nat := 4983230072969 + 3 ^ 40 * 7185683 * 2
def baseEnd_7185683 : Nat := 3689709209841514715916151

theorem tailTrace_7185683 : CollatzResearch.WordTrace tailWord_7185683 prefixEnd_7185683 3689709209841514715916151 := by
  unfold tailWord_7185683
  simp only [CollatzResearch.WordTrace]
  refine ⟨262083390026505182797777703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174722260017670121865185135 262083390026505182797777703)
  ·
    refine ⟨393125085039757774196666555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262083390026505182797777703 393125085039757774196666555)
    ·
      refine ⟨589687627559636661294999833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393125085039757774196666555 589687627559636661294999833)
      ·
        refine ⟨442265720669727495971249875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589687627559636661294999833 442265720669727495971249875)
        ·
          refine ⟨663398581004591243956874813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442265720669727495971249875 663398581004591243956874813)
          ·
            refine ⟨248774467876721716483828055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663398581004591243956874813 248774467876721716483828055)
            ·
              refine ⟨373161701815082574725742083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248774467876721716483828055 373161701815082574725742083)
              ·
                refine ⟨559742552722623862088613125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373161701815082574725742083 559742552722623862088613125)
                ·
                  refine ⟨104951728635491974141614961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 559742552722623862088613125 104951728635491974141614961)
                  ·
                    refine ⟨78713796476618980606211221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 104951728635491974141614961 78713796476618980606211221)
                    ·
                      refine ⟨3689709209841514715916151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78713796476618980606211221 3689709209841514715916151)
                      ·
                        rfl

theorem cell23_7185683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_7185683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185683 prefixEnd_7185683 := by exact prefixLift 7185683
  have htrace : WordTrace (prefixWord ++ tailWord_7185683) baseStart_7185683 baseEnd_7185683 := by
    simpa [prefixWord, tailWord_7185683, baseEnd_7185683] using wordTrace_append hprefix tailTrace_7185683
  have hstable : (prefixWord ++ tailWord_7185683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185683).length < 2 ^ (prefixWord ++ tailWord_7185683).sum := by decide
  have hdescent : baseEnd_7185683 < baseStart_7185683 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185704 : List Nat := [2, 1, 5, 1, 2, 3, 1, 1, 1, 2, 4]
def baseStart_7185704 : Nat := 118140960795 + 7185704 * 2 ^ 59
def prefixEnd_7185704 : Nat := 4983230072969 + 3 ^ 40 * 7185704 * 2
def baseEnd_7185704 : Nat := 3689719992935259133753555

theorem tailTrace_7185704 : CollatzResearch.WordTrace tailWord_7185704 prefixEnd_7185704 3689719992935259133753555 := by
  unfold tailWord_7185704
  simp only [CollatzResearch.WordTrace]
  refine ⟨131042077979714551692146083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174722770639619402256194777 131042077979714551692146083)
  ·
    refine ⟨196563116969571827538219125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131042077979714551692146083 196563116969571827538219125)
    ·
      refine ⟨18427792215897358831708043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 196563116969571827538219125 18427792215897358831708043)
      ·
        refine ⟨27641688323846038247562065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18427792215897358831708043 27641688323846038247562065)
        ·
          refine ⟨20731266242884528685671549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27641688323846038247562065 20731266242884528685671549)
          ·
            refine ⟨7774224841081698257126831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20731266242884528685671549 7774224841081698257126831)
            ·
              refine ⟨11661337261622547385690247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774224841081698257126831 11661337261622547385690247)
              ·
                refine ⟨17492005892433821078535371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11661337261622547385690247 17492005892433821078535371)
                ·
                  refine ⟨26238008838650731617803057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17492005892433821078535371 26238008838650731617803057)
                  ·
                    refine ⟨19678506628988048713352293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26238008838650731617803057 19678506628988048713352293)
                    ·
                      refine ⟨3689719992935259133753555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19678506628988048713352293 3689719992935259133753555)
                      ·
                        rfl

theorem cell23_7185704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 1, 1, 1, 2, 4].length) (baseStart_7185704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185704 prefixEnd_7185704 := by exact prefixLift 7185704
  have htrace : WordTrace (prefixWord ++ tailWord_7185704) baseStart_7185704 baseEnd_7185704 := by
    simpa [prefixWord, tailWord_7185704, baseEnd_7185704] using wordTrace_append hprefix tailTrace_7185704
  have hstable : (prefixWord ++ tailWord_7185704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185704).length < 2 ^ (prefixWord ++ tailWord_7185704).sum := by decide
  have hdescent : baseEnd_7185704 < baseStart_7185704 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185768 : List Nat := [2, 1, 4, 2, 3, 2, 1, 2, 1, 3, 2]
def baseStart_7185768 : Nat := 118140960795 + 7185768 * 2 ^ 59
def prefixEnd_7185768 : Nat := 4983230072969 + 3 ^ 40 * 7185768 * 2
def baseEnd_7185768 : Nat := 3689752855697146883353261

theorem tailTrace_7185768 : CollatzResearch.WordTrace tailWord_7185768 prefixEnd_7185768 3689752855697146883353261 := by
  unfold tailWord_7185768
  simp only [CollatzResearch.WordTrace]
  refine ⟨131043245115598621157310979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174724326820798161543081305 131043245115598621157310979)
  ·
    refine ⟨196564867673397931735966469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131043245115598621157310979 196564867673397931735966469)
    ·
      refine ⟨36855912688762112200493713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 196564867673397931735966469 36855912688762112200493713)
      ·
        refine ⟨27641934516571584150370285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 36855912688762112200493713 27641934516571584150370285)
        ·
          refine ⟨10365725443714344056388857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27641934516571584150370285 10365725443714344056388857)
          ·
            refine ⟨7774294082785758042291643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 10365725443714344056388857 7774294082785758042291643)
            ·
              refine ⟨11661441124178637063437465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774294082785758042291643 11661441124178637063437465)
              ·
                refine ⟨8746080843133977797578099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11661441124178637063437465 8746080843133977797578099)
                ·
                  refine ⟨13119121264700966696367149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8746080843133977797578099 13119121264700966696367149)
                  ·
                    refine ⟨4919670474262862511137681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 13119121264700966696367149 4919670474262862511137681)
                    ·
                      refine ⟨3689752855697146883353261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919670474262862511137681 3689752855697146883353261)
                      ·
                        rfl

theorem cell23_7185768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_7185768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185768 prefixEnd_7185768 := by exact prefixLift 7185768
  have htrace : WordTrace (prefixWord ++ tailWord_7185768) baseStart_7185768 baseEnd_7185768 := by
    simpa [prefixWord, tailWord_7185768, baseEnd_7185768] using wordTrace_append hprefix tailTrace_7185768
  have hstable : (prefixWord ++ tailWord_7185768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185768).length < 2 ^ (prefixWord ++ tailWord_7185768).sum := by decide
  have hdescent : baseEnd_7185768 < baseStart_7185768 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185781 : List Nat := [1, 3, 4, 1, 3, 1, 1, 2, 1, 4, 2]
def baseStart_7185781 : Nat := 118140960795 + 7185781 * 2 ^ 59
def prefixEnd_7185781 : Nat := 4983230072969 + 3 ^ 40 * 7185781 * 2
def baseEnd_7185781 : Nat := 3689759530945655332490701

theorem tailTrace_7185781 : CollatzResearch.WordTrace tailWord_7185781 prefixEnd_7185781 3689759530945655332490701 := by
  unfold tailWord_7185781
  simp only [CollatzResearch.WordTrace]
  refine ⟨262086964380150145534845197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174724642920100097023230131 262086964380150145534845197)
  ·
    refine ⟨98282611642556304575566949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262086964380150145534845197 98282611642556304575566949)
    ·
      refine ⟨18427989682979307107918803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98282611642556304575566949 18427989682979307107918803)
      ·
        refine ⟨27641984524468960661878205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18427989682979307107918803 27641984524468960661878205)
        ·
          refine ⟨10365744196675860248204327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 27641984524468960661878205 10365744196675860248204327)
          ·
            refine ⟨15548616295013790372306491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10365744196675860248204327 15548616295013790372306491)
            ·
              refine ⟨23322924442520685558459737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15548616295013790372306491 23322924442520685558459737)
              ·
                refine ⟨17492193331890514168844803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 23322924442520685558459737 17492193331890514168844803)
                ·
                  refine ⟨26238289997835771253267205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17492193331890514168844803 26238289997835771253267205)
                  ·
                    refine ⟨4919679374594207109987601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26238289997835771253267205 4919679374594207109987601)
                    ·
                      refine ⟨3689759530945655332490701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919679374594207109987601 3689759530945655332490701)
                      ·
                        rfl

theorem cell23_7185781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 4, 2].length) (baseStart_7185781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185781 prefixEnd_7185781 := by exact prefixLift 7185781
  have htrace : WordTrace (prefixWord ++ tailWord_7185781) baseStart_7185781 baseEnd_7185781 := by
    simpa [prefixWord, tailWord_7185781, baseEnd_7185781] using wordTrace_append hprefix tailTrace_7185781
  have hstable : (prefixWord ++ tailWord_7185781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185781).length < 2 ^ (prefixWord ++ tailWord_7185781).sum := by decide
  have hdescent : baseEnd_7185781 < baseStart_7185781 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185787 : List Nat := [1, 1, 1, 1, 1, 6, 2, 5, 5]
def baseStart_7185787 : Nat := 118140960795 + 7185787 * 2 ^ 59
def prefixEnd_7185787 : Nat := 4983230072969 + 3 ^ 40 * 7185787 * 2
def baseEnd_7185787 : Nat := 409973623536620256557297

theorem tailTrace_7185787 : CollatzResearch.WordTrace tailWord_7185787 prefixEnd_7185787 409973623536620256557297 := by
  unfold tailWord_7185787
  simp only [CollatzResearch.WordTrace]
  refine ⟨262087183218128408559563615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174724788812085605706375743 262087183218128408559563615)
  ·
    refine ⟨393130774827192612839345423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262087183218128408559563615 393130774827192612839345423)
    ·
      refine ⟨589696162240788919259018135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393130774827192612839345423 589696162240788919259018135)
      ·
        refine ⟨884544243361183378888527203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 589696162240788919259018135 884544243361183378888527203)
        ·
          refine ⟨1326816365041775068332790805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 884544243361183378888527203 1326816365041775068332790805)
          ·
            refine ⟨62194517111333206328099569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1326816365041775068332790805 62194517111333206328099569)
            ·
              refine ⟨46645887833499904746074677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 62194517111333206328099569 46645887833499904746074677)
              ·
                refine ⟨4373051984390616069944501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 46645887833499904746074677 4373051984390616069944501)
                ·
                  refine ⟨409973623536620256557297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4373051984390616069944501 409973623536620256557297)
                  ·
                    rfl

theorem cell23_7185787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 2, 5, 5].length) (baseStart_7185787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185787 prefixEnd_7185787 := by exact prefixLift 7185787
  have htrace : WordTrace (prefixWord ++ tailWord_7185787) baseStart_7185787 baseEnd_7185787 := by
    simpa [prefixWord, tailWord_7185787, baseEnd_7185787] using wordTrace_append hprefix tailTrace_7185787
  have hstable : (prefixWord ++ tailWord_7185787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185787).length < 2 ^ (prefixWord ++ tailWord_7185787).sum := by decide
  have hdescent : baseEnd_7185787 < baseStart_7185787 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185840 : List Nat := [2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5]
def baseStart_7185840 : Nat := 118140960795 + 7185840 * 2 ^ 59
def prefixEnd_7185840 : Nat := 4983230072969 + 3 ^ 40 * 7185840 * 2
def baseEnd_7185840 : Nat := 3689789826304270601652929

theorem tailTrace_7185840 : CollatzResearch.WordTrace tailWord_7185840 prefixEnd_7185840 3689789826304270601652929 := by
  unfold tailWord_7185840
  simp only [CollatzResearch.WordTrace]
  refine ⟨131044558143468199305621487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174726077524624265740828649 131044558143468199305621487)
  ·
    refine ⟨196566837215202298958432231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131044558143468199305621487 196566837215202298958432231)
    ·
      refine ⟨294850255822803448437648347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196566837215202298958432231 294850255822803448437648347)
      ·
        refine ⟨442275383734205172656472521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294850255822803448437648347 442275383734205172656472521)
        ·
          refine ⟨331706537800653879492354391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 442275383734205172656472521 331706537800653879492354391)
          ·
            refine ⟨497559806700980819238531587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331706537800653879492354391 497559806700980819238531587)
            ·
              refine ⟨746339710051471228857797381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 497559806700980819238531587 746339710051471228857797381)
              ·
                refine ⟨139938695634650855410837009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 746339710051471228857797381 139938695634650855410837009)
                ·
                  refine ⟨104954021725988141558127757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139938695634650855410837009 104954021725988141558127757)
                  ·
                    refine ⟨39357758147245553084297909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 104954021725988141558127757 39357758147245553084297909)
                    ·
                      refine ⟨3689789826304270601652929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39357758147245553084297909 3689789826304270601652929)
                      ·
                        rfl

theorem cell23_7185840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 5].length) (baseStart_7185840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185840 prefixEnd_7185840 := by exact prefixLift 7185840
  have htrace : WordTrace (prefixWord ++ tailWord_7185840) baseStart_7185840 baseEnd_7185840 := by
    simpa [prefixWord, tailWord_7185840, baseEnd_7185840] using wordTrace_append hprefix tailTrace_7185840
  have hstable : (prefixWord ++ tailWord_7185840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185840).length < 2 ^ (prefixWord ++ tailWord_7185840).sum := by decide
  have hdescent : baseEnd_7185840 < baseStart_7185840 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185847 : List Nat := [1, 1, 3, 1, 3, 2, 1, 2, 5, 4]
def baseStart_7185847 : Nat := 118140960795 + 7185847 * 2 ^ 59
def prefixEnd_7185847 : Nat := 4983230072969 + 3 ^ 40 * 7185847 * 2
def baseEnd_7185847 : Nat := 1229931140222950691421799

theorem tailTrace_7185847 : CollatzResearch.WordTrace tailWord_7185847 prefixEnd_7185847 1229931140222950691421799 := by
  unfold tailWord_7185847
  simp only [CollatzResearch.WordTrace]
  refine ⟨262089371597911038806747795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174726247731940692537831863 262089371597911038806747795)
  ·
    refine ⟨393134057396866558210121693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262089371597911038806747795 393134057396866558210121693)
    ·
      refine ⟨147425271523824959328795635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 393134057396866558210121693 147425271523824959328795635)
      ·
        refine ⟨221137907285737438993193453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147425271523824959328795635 221137907285737438993193453)
        ·
          refine ⟨82926715232151539622447545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 221137907285737438993193453 82926715232151539622447545)
          ·
            refine ⟨62195036424113654716835659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82926715232151539622447545 62195036424113654716835659)
            ·
              refine ⟨93292554636170482075253489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62195036424113654716835659 93292554636170482075253489)
              ·
                refine ⟨69969415977127861556440117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 93292554636170482075253489 69969415977127861556440117)
                ·
                  refine ⟨6559632747855737020916261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 69969415977127861556440117 6559632747855737020916261)
                  ·
                    refine ⟨1229931140222950691421799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6559632747855737020916261 1229931140222950691421799)
                    ·
                      rfl

theorem cell23_7185847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 2, 5, 4].length) (baseStart_7185847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185847 prefixEnd_7185847 := by exact prefixLift 7185847
  have htrace : WordTrace (prefixWord ++ tailWord_7185847) baseStart_7185847 baseEnd_7185847 := by
    simpa [prefixWord, tailWord_7185847, baseEnd_7185847] using wordTrace_append hprefix tailTrace_7185847
  have hstable : (prefixWord ++ tailWord_7185847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185847).length < 2 ^ (prefixWord ++ tailWord_7185847).sum := by decide
  have hdescent : baseEnd_7185847 < baseStart_7185847 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185864 : List Nat := [2, 1, 3, 1, 3, 1, 4, 1, 3, 4]
def baseStart_7185864 : Nat := 118140960795 + 7185864 * 2 ^ 59
def prefixEnd_7185864 : Nat := 4983230072969 + 3 ^ 40 * 7185864 * 2
def baseEnd_7185864 : Nat := 1229934049946659502584273

theorem tailTrace_7185864 : CollatzResearch.WordTrace tailWord_7185864 prefixEnd_7185864 1229934049946659502584273 := by
  unfold tailWord_7185864
  simp only [CollatzResearch.WordTrace]
  refine ⟨131044995819424725355058323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174726661092566300473411097 131044995819424725355058323)
  ·
    refine ⟨196567493729137088032587485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131044995819424725355058323 196567493729137088032587485)
    ·
      refine ⟨73712810148426408012220307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196567493729137088032587485 73712810148426408012220307)
      ·
        refine ⟨110569215222639612018330461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73712810148426408012220307 110569215222639612018330461)
        ·
          refine ⟨41463455708489854506873923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110569215222639612018330461 41463455708489854506873923)
          ·
            refine ⟨62195183562734781760310885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41463455708489854506873923 62195183562734781760310885)
            ·
              refine ⟨11661596918012771580058291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 62195183562734781760310885 11661596918012771580058291)
              ·
                refine ⟨17492395377019157370087437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11661596918012771580058291 17492395377019157370087437)
                ·
                  refine ⟨6559648266382184013782789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 17492395377019157370087437 6559648266382184013782789)
                  ·
                    refine ⟨1229934049946659502584273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6559648266382184013782789 1229934049946659502584273)
                    ·
                      rfl

theorem cell23_7185864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 4, 1, 3, 4].length) (baseStart_7185864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185864 prefixEnd_7185864 := by exact prefixLift 7185864
  have htrace : WordTrace (prefixWord ++ tailWord_7185864) baseStart_7185864 baseEnd_7185864 := by
    simpa [prefixWord, tailWord_7185864, baseEnd_7185864] using wordTrace_append hprefix tailTrace_7185864
  have hstable : (prefixWord ++ tailWord_7185864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185864).length < 2 ^ (prefixWord ++ tailWord_7185864).sum := by decide
  have hdescent : baseEnd_7185864 < baseStart_7185864 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185887 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 3]
def baseStart_7185887 : Nat := 118140960795 + 7185887 * 2 ^ 59
def prefixEnd_7185887 : Nat := 4983230072969 + 3 ^ 40 * 7185887 * 2
def baseEnd_7185887 : Nat := 3689813959895031917765213

theorem tailTrace_7185887 : CollatzResearch.WordTrace tailWord_7185887 prefixEnd_7185887 3689813959895031917765213 := by
  unfold tailWord_7185887
  simp only [CollatzResearch.WordTrace]
  refine ⟨262090830517766125638203915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174727220345177417092135943 262090830517766125638203915)
  ·
    refine ⟨393136245776649188457305873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262090830517766125638203915 393136245776649188457305873)
    ·
      refine ⟨294852184332486891342979405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393136245776649188457305873 294852184332486891342979405)
      ·
        refine ⟨110569569124682584253617277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294852184332486891342979405 110569569124682584253617277)
        ·
          refine ⟨41463588421755969095106479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110569569124682584253617277 41463588421755969095106479)
          ·
            refine ⟨62195382632633953642659719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41463588421755969095106479 62195382632633953642659719)
            ·
              refine ⟨93293073948950930463989579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 62195382632633953642659719 93293073948950930463989579)
              ·
                refine ⟨139939610923426395695984369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93293073948950930463989579 139939610923426395695984369)
                ·
                  refine ⟨104954708192569796771988277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 139939610923426395695984369 104954708192569796771988277)
                  ·
                    refine ⟨9839503893053418447373901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 104954708192569796771988277 9839503893053418447373901)
                    ·
                      refine ⟨3689813959895031917765213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9839503893053418447373901 3689813959895031917765213)
                      ·
                        rfl

theorem cell23_7185887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 2, 5, 3].length) (baseStart_7185887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185887 prefixEnd_7185887 := by exact prefixLift 7185887
  have htrace : WordTrace (prefixWord ++ tailWord_7185887) baseStart_7185887 baseEnd_7185887 := by
    simpa [prefixWord, tailWord_7185887, baseEnd_7185887] using wordTrace_append hprefix tailTrace_7185887
  have hstable : (prefixWord ++ tailWord_7185887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185887).length < 2 ^ (prefixWord ++ tailWord_7185887).sum := by decide
  have hdescent : baseEnd_7185887 < baseStart_7185887 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185937 : List Nat := [1, 2, 2, 1, 1, 2, 4, 3, 1, 6]
def baseStart_7185937 : Nat := 118140960795 + 7185937 * 2 ^ 59
def prefixEnd_7185937 : Nat := 4983230072969 + 3 ^ 40 * 7185937 * 2
def baseEnd_7185937 : Nat := 1229946544642585574046661

theorem tailTrace_7185937 : CollatzResearch.WordTrace tailWord_7185937 prefixEnd_7185937 1229946544642585574046661 := by
  unfold tailWord_7185937
  simp only [CollatzResearch.WordTrace]
  refine ⟨262092654167584984177524065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174728436111723322785016043 262092654167584984177524065)
  ·
    refine ⟨196569490625688738133143049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262092654167584984177524065 196569490625688738133143049)
    ·
      refine ⟨147427117969266553599857287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 196569490625688738133143049 147427117969266553599857287)
      ·
        refine ⟨221140676953899830399785931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147427117969266553599857287 221140676953899830399785931)
        ·
          refine ⟨331711015430849745599678897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221140676953899830399785931 331711015430849745599678897)
          ·
            refine ⟨248783261573137309199759173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 331711015430849745599678897 248783261573137309199759173)
            ·
              refine ⟨46646861544963245474954845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 248783261573137309199759173 46646861544963245474954845)
              ·
                refine ⟨17492573079361217053108067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 46646861544963245474954845 17492573079361217053108067)
                ·
                  refine ⟨26238859619041825579662101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17492573079361217053108067 26238859619041825579662101)
                  ·
                    refine ⟨1229946544642585574046661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 26238859619041825579662101 1229946544642585574046661)
                    ·
                      rfl

theorem cell23_7185937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_7185937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185937 prefixEnd_7185937 := by exact prefixLift 7185937
  have htrace : WordTrace (prefixWord ++ tailWord_7185937) baseStart_7185937 baseEnd_7185937 := by
    simpa [prefixWord, tailWord_7185937, baseEnd_7185937] using wordTrace_append hprefix tailTrace_7185937
  have hstable : (prefixWord ++ tailWord_7185937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185937).length < 2 ^ (prefixWord ++ tailWord_7185937).sum := by decide
  have hdescent : baseEnd_7185937 < baseStart_7185937 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185941 : List Nat := [1, 3, 2, 1, 3, 4, 1, 2, 1, 5]
def baseStart_7185941 : Nat := 118140960795 + 7185941 * 2 ^ 59
def prefixEnd_7185941 : Nat := 4983230072969 + 3 ^ 40 * 7185941 * 2
def baseEnd_7185941 : Nat := 1229947229283458235496655

theorem tailTrace_7185941 : CollatzResearch.WordTrace tailWord_7185941 prefixEnd_7185941 1229947229283458235496655 := by
  unfold tailWord_7185941
  simp only [CollatzResearch.WordTrace]
  refine ⟨262092800059570492860669677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174728533373046995240446451 262092800059570492860669677)
  ·
    refine ⟨98284800022338934822751129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262092800059570492860669677 98284800022338934822751129)
    ·
      refine ⟨73713600016754201117063347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98284800022338934822751129 73713600016754201117063347)
      ·
        refine ⟨110570400025131301675595021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73713600016754201117063347 110570400025131301675595021)
        ·
          refine ⟨41463900009424238128348133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 110570400025131301675595021 41463900009424238128348133)
          ·
            refine ⟨7774481251767044649065275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 41463900009424238128348133 7774481251767044649065275)
            ·
              refine ⟨11661721877650566973597913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774481251767044649065275 11661721877650566973597913)
              ·
                refine ⟨8746291408237925230198435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11661721877650566973597913 8746291408237925230198435)
                ·
                  refine ⟨13119437112356887845297653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8746291408237925230198435 13119437112356887845297653)
                  ·
                    refine ⟨1229947229283458235496655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 13119437112356887845297653 1229947229283458235496655)
                    ·
                      rfl

theorem cell23_7185941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_7185941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185941 prefixEnd_7185941 := by exact prefixLift 7185941
  have htrace : WordTrace (prefixWord ++ tailWord_7185941) baseStart_7185941 baseEnd_7185941 := by
    simpa [prefixWord, tailWord_7185941, baseEnd_7185941] using wordTrace_append hprefix tailTrace_7185941
  have hstable : (prefixWord ++ tailWord_7185941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185941).length < 2 ^ (prefixWord ++ tailWord_7185941).sum := by decide
  have hdescent : baseEnd_7185941 < baseStart_7185941 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185954 : List Nat := [3, 3, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_7185954 : Nat := 118140960795 + 7185954 * 2 ^ 59
def prefixEnd_7185954 : Nat := 4983230072969 + 3 ^ 40 * 7185954 * 2
def baseEnd_7185954 : Nat := 1229949454366294385209135

theorem tailTrace_7185954 : CollatzResearch.WordTrace tailWord_7185954 prefixEnd_7185954 1229949454366294385209135 := by
  unfold tailWord_7185954
  simp only [CollatzResearch.WordTrace]
  refine ⟨65523318552130849020223229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174728849472348930720595277 65523318552130849020223229)
  ·
    refine ⟨24571244457049068382583711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 65523318552130849020223229 24571244457049068382583711)
    ·
      refine ⟨36856866685573602573875567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24571244457049068382583711 36856866685573602573875567)
      ·
        refine ⟨55285300028360403860813351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36856866685573602573875567 55285300028360403860813351)
        ·
          refine ⟨82927950042540605791220027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55285300028360403860813351 82927950042540605791220027)
          ·
            refine ⟨124391925063810908686830041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82927950042540605791220027 124391925063810908686830041)
            ·
              refine ⟨93293943797858181515122531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 124391925063810908686830041 93293943797858181515122531)
              ·
                refine ⟨139940915696787272272683797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93293943797858181515122531 139940915696787272272683797)
                ·
                  refine ⟨6559730423286903387782053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139940915696787272272683797 6559730423286903387782053)
                  ·
                    refine ⟨1229949454366294385209135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6559730423286903387782053 1229949454366294385209135)
                    ·
                      rfl

theorem cell23_7185954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_7185954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185954 prefixEnd_7185954 := by exact prefixLift 7185954
  have htrace : WordTrace (prefixWord ++ tailWord_7185954) baseStart_7185954 baseEnd_7185954 := by
    simpa [prefixWord, tailWord_7185954, baseEnd_7185954] using wordTrace_append hprefix tailTrace_7185954
  have hstable : (prefixWord ++ tailWord_7185954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185954).length < 2 ^ (prefixWord ++ tailWord_7185954).sum := by decide
  have hdescent : baseEnd_7185954 < baseStart_7185954 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185971 : List Nat := [1, 1, 1, 2, 4, 4, 2, 2, 2, 4]
def baseStart_7185971 : Nat := 118140960795 + 7185971 * 2 ^ 59
def prefixEnd_7185971 : Nat := 4983230072969 + 3 ^ 40 * 7185971 * 2
def baseEnd_7185971 : Nat := 1229952364090003196371609

theorem tailTrace_7185971 : CollatzResearch.WordTrace tailWord_7185971 prefixEnd_7185971 1229952364090003196371609 := by
  unfold tailWord_7185971
  simp only [CollatzResearch.WordTrace]
  refine ⟨262093894249461807984261767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174729262832974538656174511 262093894249461807984261767)
  ·
    refine ⟨393140841374192711976392651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262093894249461807984261767 393140841374192711976392651)
    ·
      refine ⟨589711262061289067964588977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393140841374192711976392651 589711262061289067964588977)
      ·
        refine ⟨442283446545966800973441733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589711262061289067964588977 442283446545966800973441733)
        ·
          refine ⟨82928146227368775182520325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 442283446545966800973441733 82928146227368775182520325)
          ·
            refine ⟨15549027417631645346722561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 82928146227368775182520325 15549027417631645346722561)
            ·
              refine ⟨11661770563223734010041921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15549027417631645346722561 11661770563223734010041921)
              ·
                refine ⟨8746327922417800507531441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11661770563223734010041921 8746327922417800507531441)
                ·
                  refine ⟨6559745941813350380648581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8746327922417800507531441 6559745941813350380648581)
                  ·
                    refine ⟨1229952364090003196371609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6559745941813350380648581 1229952364090003196371609)
                    ·
                      rfl

theorem cell23_7185971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 4, 2, 2, 2, 4].length) (baseStart_7185971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185971 prefixEnd_7185971 := by exact prefixLift 7185971
  have htrace : WordTrace (prefixWord ++ tailWord_7185971) baseStart_7185971 baseEnd_7185971 := by
    simpa [prefixWord, tailWord_7185971, baseEnd_7185971] using wordTrace_append hprefix tailTrace_7185971
  have hstable : (prefixWord ++ tailWord_7185971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185971).length < 2 ^ (prefixWord ++ tailWord_7185971).sum := by decide
  have hdescent : baseEnd_7185971 < baseStart_7185971 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7185991 : List Nat := [1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 4]
def baseStart_7185991 : Nat := 118140960795 + 7185991 * 2 ^ 59
def prefixEnd_7185991 : Nat := 4983230072969 + 3 ^ 40 * 7185991 * 2
def baseEnd_7185991 : Nat := 3689867361883099510864735

theorem tailTrace_7185991 : CollatzResearch.WordTrace tailWord_7185991 prefixEnd_7185991 3689867361883099510864735 := by
  unfold tailWord_7185991
  simp only [CollatzResearch.WordTrace]
  refine ⟨262094623709389351399989827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174729749139592900933326551 262094623709389351399989827)
  ·
    refine ⟨393141935564084027099984741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262094623709389351399989827 393141935564084027099984741)
    ·
      refine ⟨73714112918265755081247139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 393141935564084027099984741 73714112918265755081247139)
      ·
        refine ⟨110571169377398632621870709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73714112918265755081247139 110571169377398632621870709)
        ·
          refine ⟨10366047129131121808300379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 110571169377398632621870709 10366047129131121808300379)
          ·
            refine ⟨15549070693696682712450569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10366047129131121808300379 15549070693696682712450569)
            ·
              refine ⟨11661803020272512034337927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15549070693696682712450569 11661803020272512034337927)
              ·
                refine ⟨17492704530408768051506891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11661803020272512034337927 17492704530408768051506891)
                ·
                  refine ⟨26239056795613152077260337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17492704530408768051506891 26239056795613152077260337)
                  ·
                    refine ⟨19679292596709864057945253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 26239056795613152077260337 19679292596709864057945253)
                    ·
                      refine ⟨3689867361883099510864735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19679292596709864057945253 3689867361883099510864735)
                      ·
                        rfl

theorem cell23_7185991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_7185991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7185991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7185991 prefixEnd_7185991 := by exact prefixLift 7185991
  have htrace : WordTrace (prefixWord ++ tailWord_7185991) baseStart_7185991 baseEnd_7185991 := by
    simpa [prefixWord, tailWord_7185991, baseEnd_7185991] using wordTrace_append hprefix tailTrace_7185991
  have hstable : (prefixWord ++ tailWord_7185991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7185991).length < 2 ^ (prefixWord ++ tailWord_7185991).sum := by decide
  have hdescent : baseEnd_7185991 < baseStart_7185991 := by decide
  rcases family_descends (prefixWord ++ tailWord_7185991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186012 : List Nat := [2, 2, 4, 1, 2, 2, 2, 3, 1, 2, 2]
def baseStart_7186012 : Nat := 118140960795 + 7186012 * 2 ^ 59
def prefixEnd_7186012 : Nat := 4983230072969 + 3 ^ 40 * 7186012 * 2
def baseEnd_7186012 : Nat := 3689878144976843928702139

theorem tailTrace_7186012 : CollatzResearch.WordTrace tailWord_7186012 prefixEnd_7186012 3689878144976843928702139 := by
  unfold tailWord_7186012
  simp only [CollatzResearch.WordTrace]
  refine ⟨131047694821156635993252145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174730259761542181324336193 131047694821156635993252145)
  ·
    refine ⟨98285771115867476994939109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 131047694821156635993252145 98285771115867476994939109)
    ·
      refine ⟨18428582084225151936551083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 98285771115867476994939109 18428582084225151936551083)
      ·
        refine ⟨27642873126337727904826625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18428582084225151936551083 27642873126337727904826625)
        ·
          refine ⟨20732154844753295928619969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 27642873126337727904826625 20732154844753295928619969)
          ·
            refine ⟨15549116133564971946464977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20732154844753295928619969 15549116133564971946464977)
            ·
              refine ⟨11661837100173728959848733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15549116133564971946464977 11661837100173728959848733)
              ·
                refine ⟨4373188912565148359943275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11661837100173728959848733 4373188912565148359943275)
                ·
                  refine ⟨6559783368847722539914913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4373188912565148359943275 6559783368847722539914913)
                  ·
                    refine ⟨4919837526635791904936185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6559783368847722539914913 4919837526635791904936185)
                    ·
                      refine ⟨3689878144976843928702139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919837526635791904936185 3689878144976843928702139)
                      ·
                        rfl

theorem cell23_7186012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_7186012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186012 prefixEnd_7186012 := by exact prefixLift 7186012
  have htrace : WordTrace (prefixWord ++ tailWord_7186012) baseStart_7186012 baseEnd_7186012 := by
    simpa [prefixWord, tailWord_7186012, baseEnd_7186012] using wordTrace_append hprefix tailTrace_7186012
  have hstable : (prefixWord ++ tailWord_7186012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186012).length < 2 ^ (prefixWord ++ tailWord_7186012).sum := by decide
  have hdescent : baseEnd_7186012 < baseStart_7186012 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186045 : List Nat := [1, 4, 1, 1, 4, 2, 3, 1, 2, 1, 3]
def baseStart_7186045 : Nat := 118140960795 + 7186045 * 2 ^ 59
def prefixEnd_7186045 : Nat := 4983230072969 + 3 ^ 40 * 7186045 * 2
def baseEnd_7186045 : Nat := 3689895089838442299589487

theorem tailTrace_7186045 : CollatzResearch.WordTrace tailWord_7186045 prefixEnd_7186045 3689895089838442299589487 := by
  unfold tailWord_7186045
  simp only [CollatzResearch.WordTrace]
  refine ⟨262096593251193718622455589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174731062167462479081637059 262096593251193718622455589)
  ·
    refine ⟨49143111234598822241710423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 262096593251193718622455589 49143111234598822241710423)
    ·
      refine ⟨73714666851898233362565635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 49143111234598822241710423 73714666851898233362565635)
      ·
        refine ⟨110572000277847350043848453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73714666851898233362565635 110572000277847350043848453)
        ·
          refine ⟨20732250052096378133221585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 110572000277847350043848453 20732250052096378133221585)
          ·
            refine ⟨15549187539072283599916189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 20732250052096378133221585 15549187539072283599916189)
            ·
              refine ⟨5830945327152106349968571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 15549187539072283599916189 5830945327152106349968571)
              ·
                refine ⟨8746417990728159524952857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5830945327152106349968571 8746417990728159524952857)
                ·
                  refine ⟨6559813493046119643714643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8746417990728159524952857 6559813493046119643714643)
                  ·
                    refine ⟨9839720239569179465571965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6559813493046119643714643 9839720239569179465571965)
                    ·
                      refine ⟨3689895089838442299589487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9839720239569179465571965 3689895089838442299589487)
                      ·
                        rfl

theorem cell23_7186045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 2, 3, 1, 2, 1, 3].length) (baseStart_7186045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186045 prefixEnd_7186045 := by exact prefixLift 7186045
  have htrace : WordTrace (prefixWord ++ tailWord_7186045) baseStart_7186045 baseEnd_7186045 := by
    simpa [prefixWord, tailWord_7186045, baseEnd_7186045] using wordTrace_append hprefix tailTrace_7186045
  have hstable : (prefixWord ++ tailWord_7186045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186045).length < 2 ^ (prefixWord ++ tailWord_7186045).sum := by decide
  have hdescent : baseEnd_7186045 < baseStart_7186045 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186067 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7]
def baseStart_7186067 : Nat := 118140960795 + 7186067 * 2 ^ 59
def prefixEnd_7186067 : Nat := 4983230072969 + 3 ^ 40 * 7186067 * 2
def baseEnd_7186067 : Nat := 3689906386412841213514385

theorem tailTrace_7186067 : CollatzResearch.WordTrace tailWord_7186067 prefixEnd_7186067 3689906386412841213514385 := by
  unfold tailWord_7186067
  simp only [CollatzResearch.WordTrace]
  refine ⟨262097395657114016379756455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174731597104742677586504303 262097395657114016379756455)
  ·
    refine ⟨393146093485671024569634683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262097395657114016379756455 393146093485671024569634683)
    ·
      refine ⟨589719140228506536854452025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393146093485671024569634683 589719140228506536854452025)
      ·
        refine ⟨442289355171379902640839019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 589719140228506536854452025 442289355171379902640839019)
        ·
          refine ⟨663434032757069853961258529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442289355171379902640839019 663434032757069853961258529)
          ·
            refine ⟨497575524567802390470943897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 663434032757069853961258529 497575524567802390470943897)
            ·
              refine ⟨373181643425851792853207923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 497575524567802390470943897 373181643425851792853207923)
              ·
                refine ⟨559772465138777689279811885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 373181643425851792853207923 559772465138777689279811885)
                ·
                  refine ⟨209914674427041633479929457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 559772465138777689279811885 209914674427041633479929457)
                  ·
                    refine ⟨157436005820281225109947093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 209914674427041633479929457 157436005820281225109947093)
                    ·
                      refine ⟨3689906386412841213514385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 157436005820281225109947093 3689906386412841213514385)
                      ·
                        rfl

theorem cell23_7186067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_7186067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186067 prefixEnd_7186067 := by exact prefixLift 7186067
  have htrace : WordTrace (prefixWord ++ tailWord_7186067) baseStart_7186067 baseEnd_7186067 := by
    simpa [prefixWord, tailWord_7186067, baseEnd_7186067] using wordTrace_append hprefix tailTrace_7186067
  have hstable : (prefixWord ++ tailWord_7186067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186067).length < 2 ^ (prefixWord ++ tailWord_7186067).sum := by decide
  have hdescent : baseEnd_7186067 < baseStart_7186067 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186158 : List Nat := [4, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2]
def baseStart_7186158 : Nat := 118140960795 + 7186158 * 2 ^ 59
def prefixEnd_7186158 : Nat := 4983230072969 + 3 ^ 40 * 7186158 * 2
def baseEnd_7186158 : Nat := 3689953113152400357476467

theorem tailTrace_7186158 : CollatzResearch.WordTrace tailWord_7186158 prefixEnd_7186158 3689953113152400357476467 := by
  unfold tailWord_7186158
  simp only [CollatzResearch.WordTrace]
  refine ⟨32762589337473042365164891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174733809799856225947546085 32762589337473042365164891)
  ·
    refine ⟨49143884006209563547747337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 32762589337473042365164891 49143884006209563547747337)
    ·
      refine ⟨36857913004657172660810503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49143884006209563547747337 36857913004657172660810503)
      ·
        refine ⟨55286869506985758991215755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36857913004657172660810503 55286869506985758991215755)
        ·
          refine ⟨82930304260478638486823633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55286869506985758991215755 82930304260478638486823633)
          ·
            refine ⟨62197728195358978865117725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 82930304260478638486823633 62197728195358978865117725)
            ·
              refine ⟨23324148073259617074419147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62197728195358978865117725 23324148073259617074419147)
              ·
                refine ⟨34986222109889425611628721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23324148073259617074419147 34986222109889425611628721)
                ·
                  refine ⟨26239666582417069208721541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 34986222109889425611628721 26239666582417069208721541)
                  ·
                    refine ⟨4919937484203200476635289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 26239666582417069208721541 4919937484203200476635289)
                    ·
                      refine ⟨3689953113152400357476467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4919937484203200476635289 3689953113152400357476467)
                      ·
                        rfl

theorem cell23_7186158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 1, 2, 4, 2].length) (baseStart_7186158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186158 prefixEnd_7186158 := by exact prefixLift 7186158
  have htrace : WordTrace (prefixWord ++ tailWord_7186158) baseStart_7186158 baseEnd_7186158 := by
    simpa [prefixWord, tailWord_7186158, baseEnd_7186158] using wordTrace_append hprefix tailTrace_7186158
  have hstable : (prefixWord ++ tailWord_7186158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186158).length < 2 ^ (prefixWord ++ tailWord_7186158).sum := by decide
  have hdescent : baseEnd_7186158 < baseStart_7186158 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186178 : List Nat := [3, 4, 1, 1, 1, 1, 3, 1, 1, 4, 3]
def baseStart_7186178 : Nat := 118140960795 + 7186178 * 2 ^ 59
def prefixEnd_7186178 : Nat := 4983230072969 + 3 ^ 40 * 7186178 * 2
def baseEnd_7186178 : Nat := 3689963382765490279226375

theorem tailTrace_7186178 : CollatzResearch.WordTrace tailWord_7186178 prefixEnd_7186178 3689963382765490279226375 := by
  unfold tailWord_7186178
  simp only [CollatzResearch.WordTrace]
  refine ⟨65525361039927970584261797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174734296106474588224698125 65525361039927970584261797)
  ·
    refine ⟨12286005194986494484549087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 65525361039927970584261797 12286005194986494484549087)
    ·
      refine ⟨18429007792479741726823631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 12286005194986494484549087 18429007792479741726823631)
      ·
        refine ⟨27643511688719612590235447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 18429007792479741726823631 27643511688719612590235447)
        ·
          refine ⟨41465267533079418885353171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 27643511688719612590235447 41465267533079418885353171)
          ·
            refine ⟨62197901299619128328029757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 41465267533079418885353171 62197901299619128328029757)
            ·
              refine ⟨23324212987357173123011159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 62197901299619128328029757 23324212987357173123011159)
              ·
                refine ⟨34986319481035759684516739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23324212987357173123011159 34986319481035759684516739)
                ·
                  refine ⟨52479479221553639526775109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34986319481035759684516739 52479479221553639526775109)
                  ·
                    refine ⟨9839902354041307411270333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 52479479221553639526775109 9839902354041307411270333)
                    ·
                      refine ⟨3689963382765490279226375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9839902354041307411270333 3689963382765490279226375)
                      ·
                        rfl

theorem cell23_7186178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 1, 1, 4, 3].length) (baseStart_7186178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186178 prefixEnd_7186178 := by exact prefixLift 7186178
  have htrace : WordTrace (prefixWord ++ tailWord_7186178) baseStart_7186178 baseEnd_7186178 := by
    simpa [prefixWord, tailWord_7186178, baseEnd_7186178] using wordTrace_append hprefix tailTrace_7186178
  have hstable : (prefixWord ++ tailWord_7186178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186178).length < 2 ^ (prefixWord ++ tailWord_7186178).sum := by decide
  have hdescent : baseEnd_7186178 < baseStart_7186178 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186248 : List Nat := [2, 1, 3, 1, 1, 4, 2, 3, 1, 1, 4]
def baseStart_7186248 : Nat := 118140960795 + 7186248 * 2 ^ 59
def prefixEnd_7186248 : Nat := 4983230072969 + 3 ^ 40 * 7186248 * 2
def baseEnd_7186248 : Nat := 3689999326411305005351053

theorem tailTrace_7186248 : CollatzResearch.WordTrace tailWord_7186248 prefixEnd_7186248 3689999326411305005351053 := by
  unfold tailWord_7186248
  simp only [CollatzResearch.WordTrace]
  refine ⟨131051998634729142146047699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 174735998179638856194730265 131051998634729142146047699)
  ·
    refine ⟨196577997952093713219071549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 131051998634729142146047699 196577997952093713219071549)
    ·
      refine ⟨73716749232035142457151831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 196577997952093713219071549 73716749232035142457151831)
      ·
        refine ⟨110575123848052713685727747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 73716749232035142457151831 110575123848052713685727747)
        ·
          refine ⟨165862685772079070528591621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110575123848052713685727747 165862685772079070528591621)
          ·
            refine ⟨31099253582264825724110929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 165862685772079070528591621 31099253582264825724110929)
            ·
              refine ⟨23324440186698619293083197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31099253582264825724110929 23324440186698619293083197)
              ·
                refine ⟨8746665070011982234906199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23324440186698619293083197 8746665070011982234906199)
                ·
                  refine ⟨13119997605017973352359299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8746665070011982234906199 13119997605017973352359299)
                  ·
                    refine ⟨19679996407526960028538949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 13119997605017973352359299 19679996407526960028538949)
                    ·
                      refine ⟨3689999326411305005351053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 19679996407526960028538949 3689999326411305005351053)
                      ·
                        rfl

theorem cell23_7186248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 1, 4].length) (baseStart_7186248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186248 prefixEnd_7186248 := by exact prefixLift 7186248
  have htrace : WordTrace (prefixWord ++ tailWord_7186248) baseStart_7186248 baseEnd_7186248 := by
    simpa [prefixWord, tailWord_7186248, baseEnd_7186248] using wordTrace_append hprefix tailTrace_7186248
  have hstable : (prefixWord ++ tailWord_7186248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186248).length < 2 ^ (prefixWord ++ tailWord_7186248).sum := by decide
  have hdescent : baseEnd_7186248 < baseStart_7186248 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186258 : List Nat := [3, 2, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_7186258 : Nat := 118140960795 + 7186258 * 2 ^ 59
def prefixEnd_7186258 : Nat := 4983230072969 + 3 ^ 40 * 7186258 * 2
def baseEnd_7186258 : Nat := 1230001487072616655408669

theorem tailTrace_7186258 : CollatzResearch.WordTrace tailWord_7186258 prefixEnd_7186258 1230001487072616655408669 := by
  unfold tailWord_7186258
  simp only [CollatzResearch.WordTrace]
  refine ⟨65526090499855513999989857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174736241332948037333306285 65526090499855513999989857)
  ·
    refine ⟨49144567874891635499992393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 65526090499855513999989857 49144567874891635499992393)
    ·
      refine ⟨36858425906168726624994295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 49144567874891635499992393 36858425906168726624994295)
      ·
        refine ⟨55287638859253089937491443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36858425906168726624994295 55287638859253089937491443)
        ·
          refine ⟨82931458288879634906237165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55287638859253089937491443 82931458288879634906237165)
          ·
            refine ⟨31099296858329863089838937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 82931458288879634906237165 31099296858329863089838937)
            ·
              refine ⟨23324472643747397317379203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 31099296858329863089838937 23324472643747397317379203)
              ·
                refine ⟨34986708965621095976068805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 23324472643747397317379203 34986708965621095976068805)
                ·
                  refine ⟨6560007931053955495512901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 34986708965621095976068805 6560007931053955495512901)
                  ·
                    refine ⟨1230001487072616655408669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6560007931053955495512901 1230001487072616655408669)
                    ·
                      rfl

theorem cell23_7186258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_7186258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186258 prefixEnd_7186258 := by exact prefixLift 7186258
  have htrace : WordTrace (prefixWord ++ tailWord_7186258) baseStart_7186258 baseEnd_7186258 := by
    simpa [prefixWord, tailWord_7186258, baseEnd_7186258] using wordTrace_append hprefix tailTrace_7186258
  have hstable : (prefixWord ++ tailWord_7186258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186258).length < 2 ^ (prefixWord ++ tailWord_7186258).sum := by decide
  have hdescent : baseEnd_7186258 < baseStart_7186258 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186261 : List Nat := [1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_7186261 : Nat := 118140960795 + 7186261 * 2 ^ 59
def prefixEnd_7186261 : Nat := 4983230072969 + 3 ^ 40 * 7186261 * 2
def baseEnd_7186261 : Nat := 3690006001659813454488493

theorem tailTrace_7186261 : CollatzResearch.WordTrace tailWord_7186261 prefixEnd_7186261 3690006001659813454488493 := by
  unfold tailWord_7186261
  simp only [CollatzResearch.WordTrace]
  refine ⟨262104471418411187512318637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174736314278940791674879091 262104471418411187512318637)
  ·
    refine ⟨98289176781904195317119489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 262104471418411187512318637 98289176781904195317119489)
    ·
      refine ⟨73716882586428146487839617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 98289176781904195317119489 73716882586428146487839617)
      ·
        refine ⟨55287661939821109865879713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 73716882586428146487839617 55287661939821109865879713)
        ·
          refine ⟨41465746454865832399409785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 55287661939821109865879713 41465746454865832399409785)
          ·
            refine ⟨31099309841149374299557339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 41465746454865832399409785 31099309841149374299557339)
            ·
              refine ⟨46648964761724061449336009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 31099309841149374299557339 46648964761724061449336009)
              ·
                refine ⟨34986723571293046087002007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 46648964761724061449336009 34986723571293046087002007)
                ·
                  refine ⟨52480085356939569130503011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 34986723571293046087002007 52480085356939569130503011)
                  ·
                    refine ⟨78720128035409353695754517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 52480085356939569130503011 78720128035409353695754517)
                    ·
                      refine ⟨3690006001659813454488493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 78720128035409353695754517 3690006001659813454488493)
                      ·
                        rfl

theorem cell23_7186261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_7186261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186261 prefixEnd_7186261 := by exact prefixLift 7186261
  have htrace : WordTrace (prefixWord ++ tailWord_7186261) baseStart_7186261 baseEnd_7186261 := by
    simpa [prefixWord, tailWord_7186261, baseEnd_7186261] using wordTrace_append hprefix tailTrace_7186261
  have hstable : (prefixWord ++ tailWord_7186261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186261).length < 2 ^ (prefixWord ++ tailWord_7186261).sum := by decide
  have hdescent : baseEnd_7186261 < baseStart_7186261 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186271 : List Nat := [1, 1, 2, 3, 1, 5, 2, 8]
def baseStart_7186271 : Nat := 118140960795 + 7186271 * 2 ^ 59
def prefixEnd_7186271 : Nat := 4983230072969 + 3 ^ 40 * 7186271 * 2
def baseEnd_7186271 : Nat := 136667079128383645013461

theorem tailTrace_7186271 : CollatzResearch.WordTrace tailWord_7186271 prefixEnd_7186271 136667079128383645013461 := by
  unfold tailWord_7186271
  simp only [CollatzResearch.WordTrace]
  refine ⟨262104836148374959220182667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174736557432249972813455111 262104836148374959220182667)
  ·
    refine ⟨393157254222562438830274001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262104836148374959220182667 393157254222562438830274001)
    ·
      refine ⟨294867940666921829122705501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 393157254222562438830274001 294867940666921829122705501)
      ·
        refine ⟨110575477750095685921014563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 294867940666921829122705501 110575477750095685921014563)
        ·
          refine ⟨165863216625143528881521845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 110575477750095685921014563 165863216625143528881521845)
          ·
            refine ⟨15549676558607205832642673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 165863216625143528881521845 15549676558607205832642673)
            ·
              refine ⟨11662257418955404374482005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 15549676558607205832642673 11662257418955404374482005)
              ·
                refine ⟨136667079128383645013461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11662257418955404374482005 136667079128383645013461)
                ·
                  rfl

theorem cell23_7186271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 5, 2, 8].length) (baseStart_7186271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186271 prefixEnd_7186271 := by exact prefixLift 7186271
  have htrace : WordTrace (prefixWord ++ tailWord_7186271) baseStart_7186271 baseEnd_7186271 := by
    simpa [prefixWord, tailWord_7186271, baseEnd_7186271] using wordTrace_append hprefix tailTrace_7186271
  have hstable : (prefixWord ++ tailWord_7186271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186271).length < 2 ^ (prefixWord ++ tailWord_7186271).sum := by decide
  have hdescent : baseEnd_7186271 < baseStart_7186271 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186275 : List Nat := [1, 1, 1, 5, 4, 1, 1, 3, 2, 4]
def baseStart_7186275 : Nat := 118140960795 + 7186275 * 2 ^ 59
def prefixEnd_7186275 : Nat := 4983230072969 + 3 ^ 40 * 7186275 * 2
def baseEnd_7186275 : Nat := 1230004396796325466571143

theorem tailTrace_7186275 : CollatzResearch.WordTrace tailWord_7186275 prefixEnd_7186275 1230004396796325466571143 := by
  unfold tailWord_7186275
  simp only [CollatzResearch.WordTrace]
  refine ⟨262104982040360467903328279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174736654693573645268885519 262104982040360467903328279)
  ·
    refine ⟨393157473060540701854992419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 262104982040360467903328279 393157473060540701854992419)
    ·
      refine ⟨589736209590811052782488629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 393157473060540701854992419 589736209590811052782488629)
      ·
        refine ⟨55287769649138536198358309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 589736209590811052782488629 55287769649138536198358309)
        ·
          refine ⟨10366456809213475537192183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 55287769649138536198358309 10366456809213475537192183)
          ·
            refine ⟨15549685213820213305788275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 10366456809213475537192183 15549685213820213305788275)
            ·
              refine ⟨23324527820730319958682413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 15549685213820213305788275 23324527820730319958682413)
              ·
                refine ⟨8746697932773869984505905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 23324527820730319958682413 8746697932773869984505905)
                ·
                  refine ⟨6560023449580402488379429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8746697932773869984505905 6560023449580402488379429)
                  ·
                    refine ⟨1230004396796325466571143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6560023449580402488379429 1230004396796325466571143)
                    ·
                      rfl

theorem cell23_7186275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 1, 3, 2, 4].length) (baseStart_7186275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186275 prefixEnd_7186275 := by exact prefixLift 7186275
  have htrace : WordTrace (prefixWord ++ tailWord_7186275) baseStart_7186275 baseEnd_7186275 := by
    simpa [prefixWord, tailWord_7186275, baseEnd_7186275] using wordTrace_append hprefix tailTrace_7186275
  have hstable : (prefixWord ++ tailWord_7186275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186275).length < 2 ^ (prefixWord ++ tailWord_7186275).sum := by decide
  have hdescent : baseEnd_7186275 < baseStart_7186275 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186281 : List Nat := [1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 3]
def baseStart_7186281 : Nat := 118140960795 + 7186281 * 2 ^ 59
def prefixEnd_7186281 : Nat := 4983230072969 + 3 ^ 40 * 7186281 * 2
def baseEnd_7186281 : Nat := 3690016271272903376238401

theorem tailTrace_7186281 : CollatzResearch.WordTrace tailWord_7186281 prefixEnd_7186281 3690016271272903376238401 := by
  unfold tailWord_7186281
  simp only [CollatzResearch.WordTrace]
  refine ⟨262105200878338730928046697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174736800585559153952031131 262105200878338730928046697)
  ·
    refine ⟨196578900658754048196035023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 262105200878338730928046697 196578900658754048196035023)
    ·
      refine ⟨294868350988131072294052535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 196578900658754048196035023 294868350988131072294052535)
      ·
        refine ⟨442302526482196608441078803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 294868350988131072294052535 442302526482196608441078803)
        ·
          refine ⟨663453789723294912661618205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 442302526482196608441078803 663453789723294912661618205)
          ·
            refine ⟨248795171146235592248106827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 663453789723294912661618205 248795171146235592248106827)
            ·
              refine ⟨373192756719353388372160241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 248795171146235592248106827 373192756719353388372160241)
              ·
                refine ⟨279894567539515041279120181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 373192756719353388372160241 279894567539515041279120181)
                ·
                  refine ⟨26240115706829535119917517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 279894567539515041279120181 26240115706829535119917517)
                  ·
                    refine ⟨9840043390061075669969069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 26240115706829535119917517 9840043390061075669969069)
                    ·
                      refine ⟨3690016271272903376238401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9840043390061075669969069 3690016271272903376238401)
                      ·
                        rfl

theorem cell23_7186281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 2, 5, 3, 3].length) (baseStart_7186281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186281 prefixEnd_7186281 := by exact prefixLift 7186281
  have htrace : WordTrace (prefixWord ++ tailWord_7186281) baseStart_7186281 baseEnd_7186281 := by
    simpa [prefixWord, tailWord_7186281, baseEnd_7186281] using wordTrace_append hprefix tailTrace_7186281
  have hstable : (prefixWord ++ tailWord_7186281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186281).length < 2 ^ (prefixWord ++ tailWord_7186281).sum := by decide
  have hdescent : baseEnd_7186281 < baseStart_7186281 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186285 : List Nat := [1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_7186285 : Nat := 118140960795 + 7186285 * 2 ^ 59
def prefixEnd_7186285 : Nat := 4983230072969 + 3 ^ 40 * 7186285 * 2
def baseEnd_7186285 : Nat := 3690018325195521360588383

theorem tailTrace_7186285 : CollatzResearch.WordTrace tailWord_7186285 prefixEnd_7186285 3690018325195521360588383 := by
  unfold tailWord_7186285
  simp only [CollatzResearch.WordTrace]
  refine ⟨262105346770324239611192309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 174736897846882826407461539 262105346770324239611192309)
  ·
    refine ⟨24572376259717897463549279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 262105346770324239611192309 24572376259717897463549279)
    ·
      refine ⟨36858564389576846195323919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 24572376259717897463549279 36858564389576846195323919)
      ·
        refine ⟨55287846584365269292985879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 36858564389576846195323919 55287846584365269292985879)
        ·
          refine ⟨82931769876547903939478819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 55287846584365269292985879 82931769876547903939478819)
          ·
            refine ⟨124397654814821855909218229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 82931769876547903939478819 124397654814821855909218229)
            ·
              refine ⟨11662280138889548991489209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 124397654814821855909218229 11662280138889548991489209)
              ·
                refine ⟨8746710104167161743616907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11662280138889548991489209 8746710104167161743616907)
                ·
                  refine ⟨13120065156250742615425361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8746710104167161743616907 13120065156250742615425361)
                  ·
                    refine ⟨9840048867188056961569021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 13120065156250742615425361 9840048867188056961569021)
                    ·
                      refine ⟨3690018325195521360588383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9840048867188056961569021 3690018325195521360588383)
                      ·
                        rfl

theorem cell23_7186285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_7186285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186285 prefixEnd_7186285 := by exact prefixLift 7186285
  have htrace : WordTrace (prefixWord ++ tailWord_7186285) baseStart_7186285 baseEnd_7186285 := by
    simpa [prefixWord, tailWord_7186285, baseEnd_7186285] using wordTrace_append hprefix tailTrace_7186285
  have hstable : (prefixWord ++ tailWord_7186285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186285).length < 2 ^ (prefixWord ++ tailWord_7186285).sum := by decide
  have hdescent : baseEnd_7186285 < baseStart_7186285 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186298 : List Nat := [3, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3]
def baseStart_7186298 : Nat := 118140960795 + 7186298 * 2 ^ 59
def prefixEnd_7186298 : Nat := 4983230072969 + 3 ^ 40 * 7186298 * 2
def baseEnd_7186298 : Nat := 3690025000444029809725823

theorem tailTrace_7186298 : CollatzResearch.WordTrace tailWord_7186298 prefixEnd_7186298 3690025000444029809725823 := by
  unfold tailWord_7186298
  simp only [CollatzResearch.WordTrace]
  refine ⟨65526455229819285707853887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 174737213946184761887610365 65526455229819285707853887)
  ·
    refine ⟨98289682844728928561780831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 65526455229819285707853887 98289682844728928561780831)
    ·
      refine ⟨147434524267093392842671247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 98289682844728928561780831 147434524267093392842671247)
      ·
        refine ⟨221151786400640089264006871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 147434524267093392842671247 221151786400640089264006871)
        ·
          refine ⟨331727679600960133896010307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 221151786400640089264006871 331727679600960133896010307)
          ·
            refine ⟨497591519401440200844015461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 331727679600960133896010307 497591519401440200844015461)
            ·
              refine ⟨93298409887770037658252899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 497591519401440200844015461 93298409887770037658252899)
              ·
                refine ⟨139947614831655056487379349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 93298409887770037658252899 139947614831655056487379349)
                ·
                  refine ⟨6560044445233830772845907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 139947614831655056487379349 6560044445233830772845907)
                  ·
                    refine ⟨9840066667850746159268861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6560044445233830772845907 9840066667850746159268861)
                    ·
                      refine ⟨3690025000444029809725823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9840066667850746159268861 3690025000444029809725823)
                      ·
                        rfl

theorem cell23_7186298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 1, 6, 1, 3].length) (baseStart_7186298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186298 prefixEnd_7186298 := by exact prefixLift 7186298
  have htrace : WordTrace (prefixWord ++ tailWord_7186298) baseStart_7186298 baseEnd_7186298 := by
    simpa [prefixWord, tailWord_7186298, baseEnd_7186298] using wordTrace_append hprefix tailTrace_7186298
  have hstable : (prefixWord ++ tailWord_7186298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186298).length < 2 ^ (prefixWord ++ tailWord_7186298).sum := by decide
  have hdescent : baseEnd_7186298 < baseStart_7186298 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_7186302 : List Nat := [4, 2, 3, 1, 1, 3, 1, 1, 1, 1, 5]
def baseStart_7186302 : Nat := 118140960795 + 7186302 * 2 ^ 59
def prefixEnd_7186302 : Nat := 4983230072969 + 3 ^ 40 * 7186302 * 2
def baseEnd_7186302 : Nat := 3690027054366647794075805

theorem tailTrace_7186302 : CollatzResearch.WordTrace tailWord_7186302 prefixEnd_7186302 3690027054366647794075805 := by
  unfold tailWord_7186302
  simp only [CollatzResearch.WordTrace]
  refine ⟨32763245851407831439320145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 174737311207508434343040773 32763245851407831439320145)
  ·
    refine ⟨24572434388555873579490109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 32763245851407831439320145 24572434388555873579490109)
    ·
      refine ⟨9214662895708452592308791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 24572434388555873579490109 9214662895708452592308791)
      ·
        refine ⟨13821994343562678888463187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 9214662895708452592308791 13821994343562678888463187)
        ·
          refine ⟨20732991515344018332694781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13821994343562678888463187 20732991515344018332694781)
          ·
            refine ⟨7774871818254006874760543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 20732991515344018332694781 7774871818254006874760543)
            ·
              refine ⟨11662307727381010312140815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7774871818254006874760543 11662307727381010312140815)
              ·
                refine ⟨17493461591071515468211223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11662307727381010312140815 17493461591071515468211223)
                ·
                  refine ⟨26240192386607273202316835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 17493461591071515468211223 26240192386607273202316835)
                  ·
                    refine ⟨39360288579910909803475253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 26240192386607273202316835 39360288579910909803475253)
                    ·
                      refine ⟨3690027054366647794075805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 39360288579910909803475253 3690027054366647794075805)
                      ·
                        rfl

theorem cell23_7186302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 1, 1, 1, 1, 5].length) (baseStart_7186302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_7186302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_7186302 prefixEnd_7186302 := by exact prefixLift 7186302
  have htrace : WordTrace (prefixWord ++ tailWord_7186302) baseStart_7186302 baseEnd_7186302 := by
    simpa [prefixWord, tailWord_7186302, baseEnd_7186302] using wordTrace_append hprefix tailTrace_7186302
  have hstable : (prefixWord ++ tailWord_7186302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_7186302).length < 2 ^ (prefixWord ++ tailWord_7186302).sum := by decide
  have hdescent : baseEnd_7186302 < baseStart_7186302 := by decide
  rcases family_descends (prefixWord ++ tailWord_7186302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
