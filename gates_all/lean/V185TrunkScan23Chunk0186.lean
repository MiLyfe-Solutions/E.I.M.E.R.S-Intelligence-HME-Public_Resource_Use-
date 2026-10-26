import V185TrunkScan23Chunk0185

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1100963 : List Nat := [1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6]
def baseStart_1100963 : Nat := 118140960795 + 1100963 * 2 ^ 59
def prefixEnd_1100963 : Nat := 4983230072969 + 3 ^ 40 * 1100963 * 2
def baseEnd_1100963 : Nat := 565323201816081210899269

theorem tailTrace_1100963 : CollatzResearch.WordTrace tailWord_1100963 prefixEnd_1100963 565323201816081210899269 := by
  unfold tailWord_1100963
  simp only [CollatzResearch.WordTrace]
  refine ⟨40155419510406555355715543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26770279673604370237143695 40155419510406555355715543)
  ·
    refine ⟨60233129265609833033573315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40155419510406555355715543 60233129265609833033573315)
    ·
      refine ⟨90349693898414749550359973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60233129265609833033573315 90349693898414749550359973)
      ·
        refine ⟨16940567605952765540692495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90349693898414749550359973 16940567605952765540692495)
        ·
          refine ⟨25410851408929148311038743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16940567605952765540692495 25410851408929148311038743)
          ·
            refine ⟨38116277113393722466558115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25410851408929148311038743 38116277113393722466558115)
            ·
              refine ⟨57174415670090583699837173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38116277113393722466558115 57174415670090583699837173)
              ·
                refine ⟨5360101469070992221859735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57174415670090583699837173 5360101469070992221859735)
                ·
                  refine ⟨8040152203606488332789603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360101469070992221859735 8040152203606488332789603)
                  ·
                    refine ⟨12060228305409732499184405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8040152203606488332789603 12060228305409732499184405)
                    ·
                      refine ⟨565323201816081210899269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12060228305409732499184405 565323201816081210899269)
                      ·
                        rfl

theorem cell23_1100963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 6].length) (baseStart_1100963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100963 prefixEnd_1100963 := by exact prefixLift 1100963
  have htrace : WordTrace (prefixWord ++ tailWord_1100963) baseStart_1100963 baseEnd_1100963 := by
    simpa [prefixWord, tailWord_1100963, baseEnd_1100963] using wordTrace_append hprefix tailTrace_1100963
  have hstable : (prefixWord ++ tailWord_1100963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100963).length < 2 ^ (prefixWord ++ tailWord_1100963).sum := by decide
  have hdescent : baseEnd_1100963 < baseStart_1100963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100967 : List Nat := [1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 4]
def baseStart_1100967 : Nat := 118140960795 + 1100967 * 2 ^ 59
def prefixEnd_1100967 : Nat := 4983230072969 + 3 ^ 40 * 1100967 * 2
def baseEnd_1100967 : Nat := 565325255738699195249251

theorem tailTrace_1100967 : CollatzResearch.WordTrace tailWord_1100967 prefixEnd_1100967 565325255738699195249251 := by
  unfold tailWord_1100967
  simp only [CollatzResearch.WordTrace]
  refine ⟨40155565402392064038861155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26770376934928042692574103 40155565402392064038861155)
  ·
    refine ⟨60233348103588096058291733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40155565402392064038861155 60233348103588096058291733)
    ·
      refine ⟨2823438192355692002732425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60233348103588096058291733 2823438192355692002732425)
      ·
        refine ⟨2117578644266769002049319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2823438192355692002732425 2117578644266769002049319)
        ·
          refine ⟨3176367966400153503073979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117578644266769002049319 3176367966400153503073979)
          ·
            refine ⟨4764551949600230254610969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176367966400153503073979 4764551949600230254610969)
            ·
              refine ⟨3573413962200172690958227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4764551949600230254610969 3573413962200172690958227)
              ·
                refine ⟨5360120943300259036437341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573413962200172690958227 5360120943300259036437341)
                ·
                  refine ⟨2010045353737597138664003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5360120943300259036437341 2010045353737597138664003)
                  ·
                    refine ⟨3015068030606395707996005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2010045353737597138664003 3015068030606395707996005)
                    ·
                      refine ⟨565325255738699195249251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3015068030606395707996005 565325255738699195249251)
                      ·
                        rfl

theorem cell23_1100967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_1100967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100967 prefixEnd_1100967 := by exact prefixLift 1100967
  have htrace : WordTrace (prefixWord ++ tailWord_1100967) baseStart_1100967 baseEnd_1100967 := by
    simpa [prefixWord, tailWord_1100967, baseEnd_1100967] using wordTrace_append hprefix tailTrace_1100967
  have hstable : (prefixWord ++ tailWord_1100967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100967).length < 2 ^ (prefixWord ++ tailWord_1100967).sum := by decide
  have hdescent : baseEnd_1100967 < baseStart_1100967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1100990 : List Nat := [4, 2, 1, 1, 3, 2, 10]
def baseStart_1100990 : Nat := 118140960795 + 1100990 * 2 ^ 59
def prefixEnd_1100990 : Nat := 4983230072969 + 3 ^ 40 * 1100990 * 2
def baseEnd_1100990 : Nat := 6979469948071019818045

theorem tailTrace_1100990 : CollatzResearch.WordTrace tailWord_1100990 prefixEnd_1100990 6979469948071019818045 := by
  unfold tailWord_1100990
  simp only [CollatzResearch.WordTrace]
  refine ⟨5019550535163592370868553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26770936187539159311298949 5019550535163592370868553)
  ·
    refine ⟨3764662901372694278151415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5019550535163592370868553 3764662901372694278151415)
    ·
      refine ⟨5646994352059041417227123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3764662901372694278151415 5646994352059041417227123)
      ·
        refine ⟨8470491528088562125840685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5646994352059041417227123 8470491528088562125840685)
        ·
          refine ⟨3176434323033210797190257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8470491528088562125840685 3176434323033210797190257)
          ·
            refine ⟨2382325742274908097892693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3176434323033210797190257 2382325742274908097892693)
            ·
              refine ⟨6979469948071019818045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2382325742274908097892693 6979469948071019818045)
              ·
                rfl

theorem cell23_1100990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 2, 10].length) (baseStart_1100990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1100990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1100990 prefixEnd_1100990 := by exact prefixLift 1100990
  have htrace : WordTrace (prefixWord ++ tailWord_1100990) baseStart_1100990 baseEnd_1100990 := by
    simpa [prefixWord, tailWord_1100990, baseEnd_1100990] using wordTrace_append hprefix tailTrace_1100990
  have hstable : (prefixWord ++ tailWord_1100990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1100990).length < 2 ^ (prefixWord ++ tailWord_1100990).sum := by decide
  have hdescent : baseEnd_1100990 < baseStart_1100990 := by decide
  rcases family_descends (prefixWord ++ tailWord_1100990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101000 : List Nat := [2, 1, 3, 1, 2, 1, 2, 2, 3, 3, 3]
def baseStart_1101000 : Nat := 118140960795 + 1101000 * 2 ^ 59
def prefixEnd_1101000 : Nat := 4983230072969 + 3 ^ 40 * 1101000 * 2
def baseEnd_1101000 : Nat := 565342200600297566136599

theorem tailTrace_1101000 : CollatzResearch.WordTrace tailWord_1101000 prefixEnd_1101000 565342200600297566136599 := by
  unfold tailWord_1101000
  simp only [CollatzResearch.WordTrace]
  refine ⟨20078384505636255337406227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26771179340848340449874969 20078384505636255337406227)
  ·
    refine ⟨30117576758454383006109341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20078384505636255337406227 30117576758454383006109341)
    ·
      refine ⟨11294091284420393627291003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30117576758454383006109341 11294091284420393627291003)
      ·
        refine ⟨16941136926630590440936505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11294091284420393627291003 16941136926630590440936505)
        ·
          refine ⟨12705852694972942830702379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16941136926630590440936505 12705852694972942830702379)
          ·
            refine ⟨19058779042459414246053569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12705852694972942830702379 19058779042459414246053569)
            ·
              refine ⟨14294084281844560684540177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19058779042459414246053569 14294084281844560684540177)
              ·
                refine ⟨10720563211383420513405133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14294084281844560684540177 10720563211383420513405133)
                ·
                  refine ⟨4020211204268782692526925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10720563211383420513405133 4020211204268782692526925)
                  ·
                    refine ⟨1507579201600793509697597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4020211204268782692526925 1507579201600793509697597)
                    ·
                      refine ⟨565342200600297566136599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507579201600793509697597 565342200600297566136599)
                      ·
                        rfl

theorem cell23_1101000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 2, 2, 3, 3, 3].length) (baseStart_1101000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101000 prefixEnd_1101000 := by exact prefixLift 1101000
  have htrace : WordTrace (prefixWord ++ tailWord_1101000) baseStart_1101000 baseEnd_1101000 := by
    simpa [prefixWord, tailWord_1101000, baseEnd_1101000] using wordTrace_append hprefix tailTrace_1101000
  have hstable : (prefixWord ++ tailWord_1101000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101000).length < 2 ^ (prefixWord ++ tailWord_1101000).sum := by decide
  have hdescent : baseEnd_1101000 < baseStart_1101000 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101003 : List Nat := [1, 1, 1, 1, 3, 2, 2, 3, 2, 7]
def baseStart_1101003 : Nat := 118140960795 + 1101003 * 2 ^ 59
def prefixEnd_1101003 : Nat := 4983230072969 + 3 ^ 40 * 1101003 * 2
def baseEnd_1101003 : Nat := 188447913680753684799695

theorem tailTrace_1101003 : CollatzResearch.WordTrace tailWord_1101003 prefixEnd_1101003 188447913680753684799695 := by
  unfold tailWord_1101003
  simp only [CollatzResearch.WordTrace]
  refine ⟨40156878430261642187171663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26771252286841094791447775 40156878430261642187171663)
  ·
    refine ⟨60235317645392463280757495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40156878430261642187171663 60235317645392463280757495)
    ·
      refine ⟨90352976468088694921136243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60235317645392463280757495 90352976468088694921136243)
      ·
        refine ⟨135529464702133042381704365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90352976468088694921136243 135529464702133042381704365)
        ·
          refine ⟨50823549263299890893139137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135529464702133042381704365 50823549263299890893139137)
          ·
            refine ⟨38117661947474918169854353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50823549263299890893139137 38117661947474918169854353)
            ·
              refine ⟨28588246460606188627390765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38117661947474918169854353 28588246460606188627390765)
              ·
                refine ⟨10720592422727320735271537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28588246460606188627390765 10720592422727320735271537)
                ·
                  refine ⟨8040444317045490551453653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10720592422727320735271537 8040444317045490551453653)
                  ·
                    refine ⟨188447913680753684799695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8040444317045490551453653 188447913680753684799695)
                    ·
                      rfl

theorem cell23_1101003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 3, 2, 7].length) (baseStart_1101003 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101003 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101003 prefixEnd_1101003 := by exact prefixLift 1101003
  have htrace : WordTrace (prefixWord ++ tailWord_1101003) baseStart_1101003 baseEnd_1101003 := by
    simpa [prefixWord, tailWord_1101003, baseEnd_1101003] using wordTrace_append hprefix tailTrace_1101003
  have hstable : (prefixWord ++ tailWord_1101003).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101003).length < 2 ^ (prefixWord ++ tailWord_1101003).sum := by decide
  have hdescent : baseEnd_1101003 < baseStart_1101003 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101014 : List Nat := [5, 2, 1, 2, 2, 1, 1, 1, 1, 1, 6]
def baseStart_1101014 : Nat := 118140960795 + 1101014 * 2 ^ 59
def prefixEnd_1101014 : Nat := 4983230072969 + 3 ^ 40 * 1101014 * 2
def baseEnd_1101014 : Nat := 565349389329460511361535

theorem tailTrace_1101014 : CollatzResearch.WordTrace tailWord_1101014 prefixEnd_1101014 565349389329460511361535 := by
  unfold tailWord_1101014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2509829977076361941613881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26771519755481194043881397 2509829977076361941613881)
  ·
    refine ⟨1882372482807271456210411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2509829977076361941613881 1882372482807271456210411)
    ·
      refine ⟨2823558724210907184315617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1882372482807271456210411 2823558724210907184315617)
      ·
        refine ⟨2117669043158180388236713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2823558724210907184315617 2117669043158180388236713)
        ·
          refine ⟨1588251782368635291177535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2117669043158180388236713 1588251782368635291177535)
          ·
            refine ⟨2382377673552952936766303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588251782368635291177535 2382377673552952936766303)
            ·
              refine ⟨3573566510329429405149455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2382377673552952936766303 3573566510329429405149455)
              ·
                refine ⟨5360349765494144107724183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3573566510329429405149455 5360349765494144107724183)
                ·
                  refine ⟨8040524648241216161586275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360349765494144107724183 8040524648241216161586275)
                  ·
                    refine ⟨12060786972361824242379413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8040524648241216161586275 12060786972361824242379413)
                    ·
                      refine ⟨565349389329460511361535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12060786972361824242379413 565349389329460511361535)
                      ·
                        rfl

theorem cell23_1101014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 1, 1, 1, 1, 6].length) (baseStart_1101014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101014 prefixEnd_1101014 := by exact prefixLift 1101014
  have htrace : WordTrace (prefixWord ++ tailWord_1101014) baseStart_1101014 baseEnd_1101014 := by
    simpa [prefixWord, tailWord_1101014, baseEnd_1101014] using wordTrace_append hprefix tailTrace_1101014
  have hstable : (prefixWord ++ tailWord_1101014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101014).length < 2 ^ (prefixWord ++ tailWord_1101014).sum := by decide
  have hdescent : baseEnd_1101014 < baseStart_1101014 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101021 : List Nat := [1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 3]
def baseStart_1101021 : Nat := 118140960795 + 1101021 * 2 ^ 59
def prefixEnd_1101021 : Nat := 4983230072969 + 3 ^ 40 * 1101021 * 2
def baseEnd_1101021 : Nat := 565352983694041983974003

theorem tailTrace_1101021 : CollatzResearch.WordTrace tailWord_1101021 prefixEnd_1101021 565352983694041983974003 := by
  unfold tailWord_1101021
  simp only [CollatzResearch.WordTrace]
  refine ⟨40157534944196431261326917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26771689962797620840884611 40157534944196431261326917)
  ·
    refine ⟨7529537802036830861498797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40157534944196431261326917 7529537802036830861498797)
    ·
      refine ⟨2823576675763811573062049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7529537802036830861498797 2823576675763811573062049)
      ·
        refine ⟨2117682506822858679796537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2823576675763811573062049 2117682506822858679796537)
        ·
          refine ⟨1588261880117144009847403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2117682506822858679796537 1588261880117144009847403)
          ·
            refine ⟨2382392820175716014771105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588261880117144009847403 2382392820175716014771105)
            ·
              refine ⟨1786794615131787011078329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2382392820175716014771105 1786794615131787011078329)
              ·
                refine ⟨1340095961348840258308747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786794615131787011078329 1340095961348840258308747)
                ·
                  refine ⟨2010143942023260387463121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340095961348840258308747 2010143942023260387463121)
                  ·
                    refine ⟨1507607956517445290597341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2010143942023260387463121 1507607956517445290597341)
                    ·
                      refine ⟨565352983694041983974003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507607956517445290597341 565352983694041983974003)
                      ·
                        rfl

theorem cell23_1101021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 2, 1, 2, 2, 1, 2, 3].length) (baseStart_1101021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101021 prefixEnd_1101021 := by exact prefixLift 1101021
  have htrace : WordTrace (prefixWord ++ tailWord_1101021) baseStart_1101021 baseEnd_1101021 := by
    simpa [prefixWord, tailWord_1101021, baseEnd_1101021] using wordTrace_append hprefix tailTrace_1101021
  have hstable : (prefixWord ++ tailWord_1101021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101021).length < 2 ^ (prefixWord ++ tailWord_1101021).sum := by decide
  have hdescent : baseEnd_1101021 < baseStart_1101021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101108 : List Nat := [2, 5, 1, 1, 1, 1, 4, 2, 2, 2, 2]
def baseStart_1101108 : Nat := 118140960795 + 1101108 * 2 ^ 59
def prefixEnd_1101108 : Nat := 4983230072969 + 3 ^ 40 * 1101108 * 2
def baseEnd_1101108 : Nat := 565397656510983143586103

theorem tailTrace_1101108 : CollatzResearch.WordTrace tailWord_1101108 prefixEnd_1101108 565397656510983143586103 := by
  unfold tailWord_1101108
  simp only [CollatzResearch.WordTrace]
  refine ⟨20080354047440622559871989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26773805396587496746495985 20080354047440622559871989)
  ·
    refine ⟨1882533191947558364987999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20080354047440622559871989 1882533191947558364987999)
    ·
      refine ⟨2823799787921337547481999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1882533191947558364987999 2823799787921337547481999)
      ·
        refine ⟨4235699681882006321222999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2823799787921337547481999 4235699681882006321222999)
        ·
          refine ⟨6353549522823009481834499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4235699681882006321222999 6353549522823009481834499)
          ·
            refine ⟨9530324284234514222751749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6353549522823009481834499 9530324284234514222751749)
            ·
              refine ⟨1786935803293971416765953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9530324284234514222751749 1786935803293971416765953)
              ·
                refine ⟨1340201852470478562574465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1786935803293971416765953 1340201852470478562574465)
                ·
                  refine ⟨1005151389352858921930849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340201852470478562574465 1005151389352858921930849)
                  ·
                    refine ⟨753863542014644191448137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1005151389352858921930849 753863542014644191448137)
                    ·
                      refine ⟨565397656510983143586103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753863542014644191448137 565397656510983143586103)
                      ·
                        rfl

theorem cell23_1101108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_1101108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101108 prefixEnd_1101108 := by exact prefixLift 1101108
  have htrace : WordTrace (prefixWord ++ tailWord_1101108) baseStart_1101108 baseEnd_1101108 := by
    simpa [prefixWord, tailWord_1101108, baseEnd_1101108] using wordTrace_append hprefix tailTrace_1101108
  have hstable : (prefixWord ++ tailWord_1101108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101108).length < 2 ^ (prefixWord ++ tailWord_1101108).sum := by decide
  have hdescent : baseEnd_1101108 < baseStart_1101108 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101120 : List Nat := [2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5]
def baseStart_1101120 : Nat := 118140960795 + 1101120 * 2 ^ 59
def prefixEnd_1101120 : Nat := 4983230072969 + 3 ^ 40 * 1101120 * 2
def baseEnd_1101120 : Nat := 565403818278837096636047

theorem tailTrace_1101120 : CollatzResearch.WordTrace tailWord_1101120 prefixEnd_1101120 565403818278837096636047 := by
  unfold tailWord_1101120
  simp only [CollatzResearch.WordTrace]
  refine ⟨20080572885418885584590407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26774097180558514112787209 20080572885418885584590407)
  ·
    refine ⟨30120859328128328376885611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20080572885418885584590407 30120859328128328376885611)
    ·
      refine ⟨45181288992192492565328417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30120859328128328376885611 45181288992192492565328417)
      ·
        refine ⟨33885966744144369423996313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45181288992192492565328417 33885966744144369423996313)
        ·
          refine ⟨25414475058108277067997235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33885966744144369423996313 25414475058108277067997235)
          ·
            refine ⟨38121712587162415601995853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25414475058108277067997235 38121712587162415601995853)
            ·
              refine ⟨14295642220185905850748445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38121712587162415601995853 14295642220185905850748445)
              ·
                refine ⟨5360865832569714694030667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14295642220185905850748445 5360865832569714694030667)
                ·
                  refine ⟨8041298748854572041046001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5360865832569714694030667 8041298748854572041046001)
                  ·
                    refine ⟨6030974061640929030784501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8041298748854572041046001 6030974061640929030784501)
                    ·
                      refine ⟨565403818278837096636047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6030974061640929030784501 565403818278837096636047)
                      ·
                        rfl

theorem cell23_1101120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 5].length) (baseStart_1101120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101120 prefixEnd_1101120 := by exact prefixLift 1101120
  have htrace : WordTrace (prefixWord ++ tailWord_1101120) baseStart_1101120 baseEnd_1101120 := by
    simpa [prefixWord, tailWord_1101120, baseEnd_1101120] using wordTrace_append hprefix tailTrace_1101120
  have hstable : (prefixWord ++ tailWord_1101120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101120).length < 2 ^ (prefixWord ++ tailWord_1101120).sum := by decide
  have hdescent : baseEnd_1101120 < baseStart_1101120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101124 : List Nat := [2, 3, 4, 1, 1, 1, 1, 1, 1, 5, 3]
def baseStart_1101124 : Nat := 118140960795 + 1101124 * 2 ^ 59
def prefixEnd_1101124 : Nat := 4983230072969 + 3 ^ 40 * 1101124 * 2
def baseEnd_1101124 : Nat := 565405872201455080986029

theorem tailTrace_1101124 : CollatzResearch.WordTrace tailWord_1101124 prefixEnd_1101124 565405872201455080986029 := by
  unfold tailWord_1101124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20080645831411639926163213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26774194441882186568217617 20080645831411639926163213)
  ·
    refine ⟨7530242186779364972311205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20080645831411639926163213 7530242186779364972311205)
    ·
      refine ⟨1411920410021130932308351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7530242186779364972311205 1411920410021130932308351)
      ·
        refine ⟨2117880615031696398462527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1411920410021130932308351 2117880615031696398462527)
        ·
          refine ⟨3176820922547544597693791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2117880615031696398462527 3176820922547544597693791)
          ·
            refine ⟨4765231383821316896540687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176820922547544597693791 4765231383821316896540687)
            ·
              refine ⟨7147847075731975344811031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765231383821316896540687 7147847075731975344811031)
              ·
                refine ⟨10721770613597963017216547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7147847075731975344811031 10721770613597963017216547)
                ·
                  refine ⟨16082655920396944525824821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10721770613597963017216547 16082655920396944525824821)
                  ·
                    refine ⟨1507748992537213549296077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16082655920396944525824821 1507748992537213549296077)
                    ·
                      refine ⟨565405872201455080986029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507748992537213549296077 565405872201455080986029)
                      ·
                        rfl

theorem cell23_1101124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 1, 1, 1, 1, 1, 5, 3].length) (baseStart_1101124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101124 prefixEnd_1101124 := by exact prefixLift 1101124
  have htrace : WordTrace (prefixWord ++ tailWord_1101124) baseStart_1101124 baseEnd_1101124 := by
    simpa [prefixWord, tailWord_1101124, baseEnd_1101124] using wordTrace_append hprefix tailTrace_1101124
  have hstable : (prefixWord ++ tailWord_1101124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101124).length < 2 ^ (prefixWord ++ tailWord_1101124).sum := by decide
  have hdescent : baseEnd_1101124 < baseStart_1101124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101157 : List Nat := [1, 3, 1, 3, 1, 2, 1, 2, 5, 4]
def baseStart_1101157 : Nat := 118140960795 + 1101157 * 2 ^ 59
def prefixEnd_1101157 : Nat := 4983230072969 + 3 ^ 40 * 1101157 * 2
def baseEnd_1101157 : Nat := 188474272354351150624459

theorem tailTrace_1101157 : CollatzResearch.WordTrace tailWord_1101157 prefixEnd_1101157 188474272354351150624459 := by
  unfold tailWord_1101157
  simp only [CollatzResearch.WordTrace]
  refine ⟨40162495271703726488277725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26774996847802484325518483 40162495271703726488277725)
  ·
    refine ⟨15060935726888897433104147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40162495271703726488277725 15060935726888897433104147)
    ·
      refine ⟨22591403590333346149656221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15060935726888897433104147 22591403590333346149656221)
      ·
        refine ⟨8471776346375004806121083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22591403590333346149656221 8471776346375004806121083)
        ·
          refine ⟨12707664519562507209181625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8471776346375004806121083 12707664519562507209181625)
          ·
            refine ⟨9530748389671880406886219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12707664519562507209181625 9530748389671880406886219)
            ·
              refine ⟨14296122584507820610329329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9530748389671880406886219 14296122584507820610329329)
              ·
                refine ⟨10722091938380865457746997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14296122584507820610329329 10722091938380865457746997)
                ·
                  refine ⟨1005196119223206136663781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10722091938380865457746997 1005196119223206136663781)
                  ·
                    refine ⟨188474272354351150624459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005196119223206136663781 188474272354351150624459)
                    ·
                      rfl

theorem cell23_1101157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 2, 5, 4].length) (baseStart_1101157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101157 prefixEnd_1101157 := by exact prefixLift 1101157
  have htrace : WordTrace (prefixWord ++ tailWord_1101157) baseStart_1101157 baseEnd_1101157 := by
    simpa [prefixWord, tailWord_1101157, baseEnd_1101157] using wordTrace_append hprefix tailTrace_1101157
  have hstable : (prefixWord ++ tailWord_1101157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101157).length < 2 ^ (prefixWord ++ tailWord_1101157).sum := by decide
  have hdescent : baseEnd_1101157 < baseStart_1101157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101164 : List Nat := [2, 2, 1, 1, 5, 1, 1, 2, 2, 4, 2]
def baseStart_1101164 : Nat := 118140960795 + 1101164 * 2 ^ 59
def prefixEnd_1101164 : Nat := 4983230072969 + 3 ^ 40 * 1101164 * 2
def baseEnd_1101164 : Nat := 565426411427634924485845

theorem tailTrace_1101164 : CollatzResearch.WordTrace tailWord_1101164 prefixEnd_1101164 565426411427634924485845 := by
  unfold tailWord_1101164
  simp only [CollatzResearch.WordTrace]
  refine ⟨20081375291339183341891273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26775167055118911122521697 20081375291339183341891273)
  ·
    refine ⟨15061031468504387506418455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20081375291339183341891273 15061031468504387506418455)
    ·
      refine ⟨22591547202756581259627683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15061031468504387506418455 22591547202756581259627683)
      ·
        refine ⟨33887320804134871889441525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22591547202756581259627683 33887320804134871889441525)
        ·
          refine ⟨3176936325387644239635143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33887320804134871889441525 3176936325387644239635143)
          ·
            refine ⟨4765404488081466359452715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3176936325387644239635143 4765404488081466359452715)
            ·
              refine ⟨7148106732122199539179073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765404488081466359452715 7148106732122199539179073)
              ·
                refine ⟨5361080049091649654384305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7148106732122199539179073 5361080049091649654384305)
                ·
                  refine ⟨4020810036818737240788229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5361080049091649654384305 4020810036818737240788229)
                  ·
                    refine ⟨753901881903513232647793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4020810036818737240788229 753901881903513232647793)
                    ·
                      refine ⟨565426411427634924485845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 753901881903513232647793 565426411427634924485845)
                      ·
                        rfl

theorem cell23_1101164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 4, 2].length) (baseStart_1101164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101164 prefixEnd_1101164 := by exact prefixLift 1101164
  have htrace : WordTrace (prefixWord ++ tailWord_1101164) baseStart_1101164 baseEnd_1101164 := by
    simpa [prefixWord, tailWord_1101164, baseEnd_1101164] using wordTrace_append hprefix tailTrace_1101164
  have hstable : (prefixWord ++ tailWord_1101164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101164).length < 2 ^ (prefixWord ++ tailWord_1101164).sum := by decide
  have hdescent : baseEnd_1101164 < baseStart_1101164 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101167 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 3]
def baseStart_1101167 : Nat := 118140960795 + 1101167 * 2 ^ 59
def prefixEnd_1101167 : Nat := 4983230072969 + 3 ^ 40 * 1101167 * 2
def baseEnd_1101167 : Nat := 565427951869598412748331

theorem tailTrace_1101167 : CollatzResearch.WordTrace tailWord_1101167 prefixEnd_1101167 565427951869598412748331 := by
  unfold tailWord_1101167
  simp only [CollatzResearch.WordTrace]
  refine ⟨40162860001667498196141755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26775240001111665464094503 40162860001667498196141755)
  ·
    refine ⟨60244290002501247294212633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40162860001667498196141755 60244290002501247294212633)
    ·
      refine ⟨45183217501875935470659475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60244290002501247294212633 45183217501875935470659475)
      ·
        refine ⟨67774826252813903205989213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45183217501875935470659475 67774826252813903205989213)
        ·
          refine ⟨25415559844805213702245955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67774826252813903205989213 25415559844805213702245955)
          ·
            refine ⟨38123339767207820553368933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25415559844805213702245955 38123339767207820553368933)
            ·
              refine ⟨7148126206351466353756675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38123339767207820553368933 7148126206351466353756675)
              ·
                refine ⟨10722189309527199530635013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7148126206351466353756675 10722189309527199530635013)
                ·
                  refine ⟨2010410495536349911994065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10722189309527199530635013 2010410495536349911994065)
                  ·
                    refine ⟨1507807871652262433995549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2010410495536349911994065 1507807871652262433995549)
                    ·
                      refine ⟨565427951869598412748331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507807871652262433995549 565427951869598412748331)
                      ·
                        rfl

theorem cell23_1101167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 4, 2, 3].length) (baseStart_1101167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101167 prefixEnd_1101167 := by exact prefixLift 1101167
  have htrace : WordTrace (prefixWord ++ tailWord_1101167) baseStart_1101167 baseEnd_1101167 := by
    simpa [prefixWord, tailWord_1101167, baseEnd_1101167] using wordTrace_append hprefix tailTrace_1101167
  have hstable : (prefixWord ++ tailWord_1101167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101167).length < 2 ^ (prefixWord ++ tailWord_1101167).sum := by decide
  have hdescent : baseEnd_1101167 < baseStart_1101167 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101231 : List Nat := [1, 1, 2, 1, 2, 2, 1, 8, 1, 1, 3]
def baseStart_1101231 : Nat := 118140960795 + 1101231 * 2 ^ 59
def prefixEnd_1101231 : Nat := 4983230072969 + 3 ^ 40 * 1101231 * 2
def baseEnd_1101231 : Nat := 565460814631486162348037

theorem tailTrace_1101231 : CollatzResearch.WordTrace tailWord_1101231 prefixEnd_1101231 565460814631486162348037 := by
  unfold tailWord_1101231
  simp only [CollatzResearch.WordTrace]
  refine ⟨40165194273435637126471547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26776796182290424750981031 40165194273435637126471547)
  ·
    refine ⟨60247791410153455689707321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40165194273435637126471547 60247791410153455689707321)
    ·
      refine ⟨45185843557615091767280491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60247791410153455689707321 45185843557615091767280491)
      ·
        refine ⟨67778765336422637650920737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45185843557615091767280491 67778765336422637650920737)
        ·
          refine ⟨50834074002316978238190553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67778765336422637650920737 50834074002316978238190553)
          ·
            refine ⟨38125555501737733678642915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50834074002316978238190553 38125555501737733678642915)
            ·
              refine ⟨57188333252606600517964373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38125555501737733678642915 57188333252606600517964373)
              ·
                refine ⟨670175780303983599819895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 57188333252606600517964373 670175780303983599819895)
                ·
                  refine ⟨1005263670455975399729843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670175780303983599819895 1005263670455975399729843)
                  ·
                    refine ⟨1507895505683963099594765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1005263670455975399729843 1507895505683963099594765)
                    ·
                      refine ⟨565460814631486162348037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507895505683963099594765 565460814631486162348037)
                      ·
                        rfl

theorem cell23_1101231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 8, 1, 1, 3].length) (baseStart_1101231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101231 prefixEnd_1101231 := by exact prefixLift 1101231
  have htrace : WordTrace (prefixWord ++ tailWord_1101231) baseStart_1101231 baseEnd_1101231 := by
    simpa [prefixWord, tailWord_1101231, baseEnd_1101231] using wordTrace_append hprefix tailTrace_1101231
  have hstable : (prefixWord ++ tailWord_1101231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101231).length < 2 ^ (prefixWord ++ tailWord_1101231).sum := by decide
  have hdescent : baseEnd_1101231 < baseStart_1101231 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101268 : List Nat := [2, 4, 1, 2, 3, 1, 3, 1, 1, 5]
def baseStart_1101268 : Nat := 118140960795 + 1101268 * 2 ^ 59
def prefixEnd_1101268 : Nat := 4983230072969 + 3 ^ 40 * 1101268 * 2
def baseEnd_1101268 : Nat := 188493271138567505861789

theorem tailTrace_1101268 : CollatzResearch.WordTrace tailWord_1101268 prefixEnd_1101268 188493271138567505861789 := by
  unfold tailWord_1101268
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083271887150796222784229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26777695849534394963712305 20083271887150796222784229)
  ·
    refine ⟨3765613478840774291772043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20083271887150796222784229 3765613478840774291772043)
    ·
      refine ⟨5648420218261161437658065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3765613478840774291772043 5648420218261161437658065)
      ·
        refine ⟨4236315163695871078243549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5648420218261161437658065 4236315163695871078243549)
        ·
          refine ⟨1588618186385951654341331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4236315163695871078243549 1588618186385951654341331)
          ·
            refine ⟨2382927279578927481511997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1588618186385951654341331 2382927279578927481511997)
            ·
              refine ⟨893597729842097805566999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2382927279578927481511997 893597729842097805566999)
              ·
                refine ⟨1340396594763146708350499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893597729842097805566999 1340396594763146708350499)
                ·
                  refine ⟨2010594892144720062525749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1340396594763146708350499 2010594892144720062525749)
                  ·
                    refine ⟨188493271138567505861789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2010594892144720062525749 188493271138567505861789)
                    ·
                      rfl

theorem cell23_1101268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 3, 1, 1, 5].length) (baseStart_1101268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101268 prefixEnd_1101268 := by exact prefixLift 1101268
  have htrace : WordTrace (prefixWord ++ tailWord_1101268) baseStart_1101268 baseEnd_1101268 := by
    simpa [prefixWord, tailWord_1101268, baseEnd_1101268] using wordTrace_append hprefix tailTrace_1101268
  have hstable : (prefixWord ++ tailWord_1101268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101268).length < 2 ^ (prefixWord ++ tailWord_1101268).sum := by decide
  have hdescent : baseEnd_1101268 < baseStart_1101268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101274 : List Nat := [3, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5]
def baseStart_1101274 : Nat := 118140960795 + 1101274 * 2 ^ 59
def prefixEnd_1101274 : Nat := 4983230072969 + 3 ^ 40 * 1101274 * 2
def baseEnd_1101274 : Nat := 565482894299629494110339

theorem tailTrace_1101274 : CollatzResearch.WordTrace tailWord_1101274 prefixEnd_1101274 565482894299629494110339 := by
  unfold tailWord_1101274
  simp only [CollatzResearch.WordTrace]
  refine ⟨10041690653069963867571719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26777841741519903646857917 10041690653069963867571719)
  ·
    refine ⟨15062535979604945801357579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10041690653069963867571719 15062535979604945801357579)
    ·
      refine ⟨22593803969407418702036369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15062535979604945801357579 22593803969407418702036369)
      ·
        refine ⟨16945352977055564026527277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22593803969407418702036369 16945352977055564026527277)
        ·
          refine ⟨6354507366395836509947729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16945352977055564026527277 6354507366395836509947729)
          ·
            refine ⟨4765880524796877382460797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6354507366395836509947729 4765880524796877382460797)
            ·
              refine ⟨1787205196798829018422799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4765880524796877382460797 1787205196798829018422799)
              ·
                refine ⟨2680807795198243527634199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1787205196798829018422799 2680807795198243527634199)
                ·
                  refine ⟨4021211692797365291451299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680807795198243527634199 4021211692797365291451299)
                  ·
                    refine ⟨6031817539196047937176949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4021211692797365291451299 6031817539196047937176949)
                    ·
                      refine ⟨565482894299629494110339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6031817539196047937176949 565482894299629494110339)
                      ·
                        rfl

theorem cell23_1101274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5].length) (baseStart_1101274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101274 prefixEnd_1101274 := by exact prefixLift 1101274
  have htrace : WordTrace (prefixWord ++ tailWord_1101274) baseStart_1101274 baseEnd_1101274 := by
    simpa [prefixWord, tailWord_1101274, baseEnd_1101274] using wordTrace_append hprefix tailTrace_1101274
  have hstable : (prefixWord ++ tailWord_1101274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101274).length < 2 ^ (prefixWord ++ tailWord_1101274).sum := by decide
  have hdescent : baseEnd_1101274 < baseStart_1101274 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101277 : List Nat := [1, 4, 3, 1, 1, 13]
def baseStart_1101277 : Nat := 118140960795 + 1101277 * 2 ^ 59
def prefixEnd_1101277 : Nat := 4983230072969 + 3 ^ 40 * 1101277 * 2
def baseEnd_1101277 : Nat := 2327096439265814742275

theorem tailTrace_1101277 : CollatzResearch.WordTrace tailWord_1101277 prefixEnd_1101277 2327096439265814742275 := by
  unfold tailWord_1101277
  simp only [CollatzResearch.WordTrace]
  refine ⟨40166872031268986982646085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26777914687512657988430723 40166872031268986982646085)
  ·
    refine ⟨7531288505862935059246141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40166872031268986982646085 7531288505862935059246141)
    ·
      refine ⟨2824233189698600647217303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7531288505862935059246141 2824233189698600647217303)
      ·
        refine ⟨4236349784547900970825955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824233189698600647217303 4236349784547900970825955)
        ·
          refine ⟨6354524676821851456238933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236349784547900970825955 6354524676821851456238933)
          ·
            refine ⟨2327096439265814742275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 6354524676821851456238933 2327096439265814742275)
            ·
              rfl

theorem cell23_1101277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 13].length) (baseStart_1101277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101277 prefixEnd_1101277 := by exact prefixLift 1101277
  have htrace : WordTrace (prefixWord ++ tailWord_1101277) baseStart_1101277 baseEnd_1101277 := by
    simpa [prefixWord, tailWord_1101277, baseEnd_1101277] using wordTrace_append hprefix tailTrace_1101277
  have hstable : (prefixWord ++ tailWord_1101277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101277).length < 2 ^ (prefixWord ++ tailWord_1101277).sum := by decide
  have hdescent : baseEnd_1101277 < baseStart_1101277 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101281 : List Nat := [1, 2, 3, 1, 2, 4, 2, 2, 2, 4]
def baseStart_1101281 : Nat := 118140960795 + 1101281 * 2 ^ 59
def prefixEnd_1101281 : Nat := 4983230072969 + 3 ^ 40 * 1101281 * 2
def baseEnd_1101281 : Nat := 188495496221403655574269

theorem tailTrace_1101281 : CollatzResearch.WordTrace tailWord_1101281 prefixEnd_1101281 188495496221403655574269 := by
  unfold tailWord_1101281
  simp only [CollatzResearch.WordTrace]
  refine ⟨40167017923254495665791697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26778011948836330443861131 40167017923254495665791697)
  ·
    refine ⟨30125263442440871749343773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40167017923254495665791697 30125263442440871749343773)
    ·
      refine ⟨11296973790915326906003915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30125263442440871749343773 11296973790915326906003915)
      ·
        refine ⟨16945460686372990359005873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11296973790915326906003915 16945460686372990359005873)
        ·
          refine ⟨12709095514779742769254405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16945460686372990359005873 12709095514779742769254405)
          ·
            refine ⟨2382955409021201769235201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12709095514779742769254405 2382955409021201769235201)
            ·
              refine ⟨1787216556765901326926401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2382955409021201769235201 1787216556765901326926401)
              ·
                refine ⟨1340412417574425995194801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787216556765901326926401 1340412417574425995194801)
                ·
                  refine ⟨1005309313180819496396101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340412417574425995194801 1005309313180819496396101)
                  ·
                    refine ⟨188495496221403655574269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005309313180819496396101 188495496221403655574269)
                    ·
                      rfl

theorem cell23_1101281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 2, 2, 2, 4].length) (baseStart_1101281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101281 prefixEnd_1101281 := by exact prefixLift 1101281
  have htrace : WordTrace (prefixWord ++ tailWord_1101281) baseStart_1101281 baseEnd_1101281 := by
    simpa [prefixWord, tailWord_1101281, baseEnd_1101281] using wordTrace_append hprefix tailTrace_1101281
  have hstable : (prefixWord ++ tailWord_1101281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101281).length < 2 ^ (prefixWord ++ tailWord_1101281).sum := by decide
  have hdescent : baseEnd_1101281 < baseStart_1101281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101301 : List Nat := [1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1101301 : Nat := 118140960795 + 1101301 * 2 ^ 59
def prefixEnd_1101301 : Nat := 4983230072969 + 3 ^ 40 * 1101301 * 2
def baseEnd_1101301 : Nat := 565496758277300888472715

theorem tailTrace_1101301 : CollatzResearch.WordTrace tailWord_1101301 prefixEnd_1101301 565496758277300888472715 := by
  unfold tailWord_1101301
  simp only [CollatzResearch.WordTrace]
  refine ⟨40167747383182039081519757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26778498255454692721013171 40167747383182039081519757)
  ·
    refine ⟨15062905268693264655569909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40167747383182039081519757 15062905268693264655569909)
    ·
      refine ⟨1412147368939993561459679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15062905268693264655569909 1412147368939993561459679)
      ·
        refine ⟨2118221053409990342189519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412147368939993561459679 2118221053409990342189519)
        ·
          refine ⟨3177331580114985513284279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2118221053409990342189519 3177331580114985513284279)
          ·
            refine ⟨4765997370172478269926419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3177331580114985513284279 4765997370172478269926419)
            ·
              refine ⟨7148996055258717404889629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4765997370172478269926419 7148996055258717404889629)
              ·
                refine ⟨2680873520722019026833611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7148996055258717404889629 2680873520722019026833611)
                ·
                  refine ⟨4021310281083028540250417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680873520722019026833611 4021310281083028540250417)
                  ·
                    refine ⟨3015982710812271405187813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4021310281083028540250417 3015982710812271405187813)
                    ·
                      refine ⟨565496758277300888472715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3015982710812271405187813 565496758277300888472715)
                      ·
                        rfl

theorem cell23_1101301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1101301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101301 prefixEnd_1101301 := by exact prefixLift 1101301
  have htrace : WordTrace (prefixWord ++ tailWord_1101301) baseStart_1101301 baseEnd_1101301 := by
    simpa [prefixWord, tailWord_1101301, baseEnd_1101301] using wordTrace_append hprefix tailTrace_1101301
  have hstable : (prefixWord ++ tailWord_1101301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101301).length < 2 ^ (prefixWord ++ tailWord_1101301).sum := by decide
  have hdescent : baseEnd_1101301 < baseStart_1101301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101304 : List Nat := [2, 1, 2, 1, 1, 5, 1, 3, 1, 3, 3]
def baseStart_1101304 : Nat := 118140960795 + 1101304 * 2 ^ 59
def prefixEnd_1101304 : Nat := 4983230072969 + 3 ^ 40 * 1101304 * 2
def baseEnd_1101304 : Nat := 565498298719264376735201

theorem tailTrace_1101304 : CollatzResearch.WordTrace tailWord_1101304 prefixEnd_1101304 565498298719264376735201 := by
  unfold tailWord_1101304
  simp only [CollatzResearch.WordTrace]
  refine ⟨20083928401085585296939483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26778571201447447062585977 20083928401085585296939483)
  ·
    refine ⟨30125892601628377945409225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20083928401085585296939483 30125892601628377945409225)
    ·
      refine ⟨22594419451221283459056919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30125892601628377945409225 22594419451221283459056919)
      ·
        refine ⟨33891629176831925188585379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22594419451221283459056919 33891629176831925188585379)
        ·
          refine ⟨50837443765247887782878069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33891629176831925188585379 50837443765247887782878069)
          ·
            refine ⟨4766010352991989479644819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50837443765247887782878069 4766010352991989479644819)
            ·
              refine ⟨7149015529487984219467229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4766010352991989479644819 7149015529487984219467229)
              ·
                refine ⟨2680880823557994082300211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7149015529487984219467229 2680880823557994082300211)
                ·
                  refine ⟨4021321235336991123450317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2680880823557994082300211 4021321235336991123450317)
                  ·
                    refine ⟨1507995463251371671293869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4021321235336991123450317 1507995463251371671293869)
                    ·
                      refine ⟨565498298719264376735201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1507995463251371671293869 565498298719264376735201)
                      ·
                        rfl

theorem cell23_1101304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 3, 1, 3, 3].length) (baseStart_1101304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101304 prefixEnd_1101304 := by exact prefixLift 1101304
  have htrace : WordTrace (prefixWord ++ tailWord_1101304) baseStart_1101304 baseEnd_1101304 := by
    simpa [prefixWord, tailWord_1101304, baseEnd_1101304] using wordTrace_append hprefix tailTrace_1101304
  have hstable : (prefixWord ++ tailWord_1101304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101304).length < 2 ^ (prefixWord ++ tailWord_1101304).sum := by decide
  have hdescent : baseEnd_1101304 < baseStart_1101304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101317 : List Nat := [1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 5]
def baseStart_1101317 : Nat := 118140960795 + 1101317 * 2 ^ 59
def prefixEnd_1101317 : Nat := 4983230072969 + 3 ^ 40 * 1101317 * 2
def baseEnd_1101317 : Nat := 565504973967772825872641

theorem tailTrace_1101317 : CollatzResearch.WordTrace tailWord_1101317 prefixEnd_1101317 565504973967772825872641 := by
  unfold tailWord_1101317
  simp only [CollatzResearch.WordTrace]
  refine ⟨40168330951124073814102205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26778887300749382542734803 40168330951124073814102205)
  ·
    refine ⟨15063124106671527680288327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40168330951124073814102205 15063124106671527680288327)
    ·
      refine ⟨22594686160007291520432491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15063124106671527680288327 22594686160007291520432491)
      ·
        refine ⟨33892029240010937280648737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22594686160007291520432491 33892029240010937280648737)
        ·
          refine ⟨25419021930008202960486553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33892029240010937280648737 25419021930008202960486553)
          ·
            refine ⟨19064266447506152220364915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25419021930008202960486553 19064266447506152220364915)
            ·
              refine ⟨28596399671259228330547373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19064266447506152220364915 28596399671259228330547373)
              ·
                refine ⟨10723649876722210623955265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28596399671259228330547373 10723649876722210623955265)
                ·
                  refine ⟨8042737407541657967966449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10723649876722210623955265 8042737407541657967966449)
                  ·
                    refine ⟨6032053055656243475974837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8042737407541657967966449 6032053055656243475974837)
                    ·
                      refine ⟨565504973967772825872641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6032053055656243475974837 565504973967772825872641)
                      ·
                        rfl

theorem cell23_1101317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 3, 2, 2, 5].length) (baseStart_1101317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101317 prefixEnd_1101317 := by exact prefixLift 1101317
  have htrace : WordTrace (prefixWord ++ tailWord_1101317) baseStart_1101317 baseEnd_1101317 := by
    simpa [prefixWord, tailWord_1101317, baseEnd_1101317] using wordTrace_append hprefix tailTrace_1101317
  have hstable : (prefixWord ++ tailWord_1101317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101317).length < 2 ^ (prefixWord ++ tailWord_1101317).sum := by decide
  have hdescent : baseEnd_1101317 < baseStart_1101317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101332 : List Nat := [2, 4, 3, 1, 3, 1, 1, 2, 2, 4]
def baseStart_1101332 : Nat := 118140960795 + 1101332 * 2 ^ 59
def prefixEnd_1101332 : Nat := 4983230072969 + 3 ^ 40 * 1101332 * 2
def baseEnd_1101332 : Nat := 188504225392530089061691

theorem tailTrace_1101332 : CollatzResearch.WordTrace tailWord_1101332 prefixEnd_1101332 188504225392530089061691 := by
  unfold tailWord_1101332
  simp only [CollatzResearch.WordTrace]
  refine ⟨20084439023034865687949125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26779252030713154250598833 20084439023034865687949125)
  ·
    refine ⟨3765832316819037316490461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20084439023034865687949125 3765832316819037316490461)
    ·
      refine ⟨1412187118807138993683923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3765832316819037316490461 1412187118807138993683923)
      ·
        refine ⟨2118280678210708490525885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1412187118807138993683923 2118280678210708490525885)
        ·
          refine ⟨794355254329015683947207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2118280678210708490525885 794355254329015683947207)
          ·
            refine ⟨1191532881493523525920811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794355254329015683947207 1191532881493523525920811)
            ·
              refine ⟨1787299322240285288881217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191532881493523525920811 1787299322240285288881217)
              ·
                refine ⟨1340474491680213966660913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1787299322240285288881217 1340474491680213966660913)
                ·
                  refine ⟨1005355868760160474995685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340474491680213966660913 1005355868760160474995685)
                  ·
                    refine ⟨188504225392530089061691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005355868760160474995685 188504225392530089061691)
                    ·
                      rfl

theorem cell23_1101332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 1, 2, 2, 4].length) (baseStart_1101332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101332 prefixEnd_1101332 := by exact prefixLift 1101332
  have htrace : WordTrace (prefixWord ++ tailWord_1101332) baseStart_1101332 baseEnd_1101332 := by
    simpa [prefixWord, tailWord_1101332, baseEnd_1101332] using wordTrace_append hprefix tailTrace_1101332
  have hstable : (prefixWord ++ tailWord_1101332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101332).length < 2 ^ (prefixWord ++ tailWord_1101332).sum := by decide
  have hdescent : baseEnd_1101332 < baseStart_1101332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101354 : List Nat := [3, 1, 4, 1, 1, 1, 1, 3, 2, 6]
def baseStart_1101354 : Nat := 118140960795 + 1101354 * 2 ^ 59
def prefixEnd_1101354 : Nat := 4983230072969 + 3 ^ 40 * 1101354 * 2
def baseEnd_1101354 : Nat := 188507990917329727036657

theorem tailTrace_1101354 : CollatzResearch.WordTrace tailWord_1101354 prefixEnd_1101354 188507990917329727036657 := by
  unfold tailWord_1101354
  simp only [CollatzResearch.WordTrace]
  refine ⟨10042420112997507283299779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26779786967993352755466077 10042420112997507283299779)
  ·
    refine ⟨15063630169496260924949669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10042420112997507283299779 15063630169496260924949669)
    ·
      refine ⟨2824430656780548923428063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15063630169496260924949669 2824430656780548923428063)
      ·
        refine ⟨4236645985170823385142095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2824430656780548923428063 4236645985170823385142095)
        ·
          refine ⟨6354968977756235077713143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4236645985170823385142095 6354968977756235077713143)
          ·
            refine ⟨9532453466634352616569715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6354968977756235077713143 9532453466634352616569715)
            ·
              refine ⟨14298680199951528924854573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9532453466634352616569715 14298680199951528924854573)
              ·
                refine ⟨5362005074981823346820465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14298680199951528924854573 5362005074981823346820465)
                ·
                  refine ⟨4021503806236367510115349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5362005074981823346820465 4021503806236367510115349)
                  ·
                    refine ⟨188507990917329727036657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4021503806236367510115349 188507990917329727036657)
                    ·
                      rfl

theorem cell23_1101354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 1, 3, 2, 6].length) (baseStart_1101354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101354 prefixEnd_1101354 := by exact prefixLift 1101354
  have htrace : WordTrace (prefixWord ++ tailWord_1101354) baseStart_1101354 baseEnd_1101354 := by
    simpa [prefixWord, tailWord_1101354, baseEnd_1101354] using wordTrace_append hprefix tailTrace_1101354
  have hstable : (prefixWord ++ tailWord_1101354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101354).length < 2 ^ (prefixWord ++ tailWord_1101354).sum := by decide
  have hdescent : baseEnd_1101354 < baseStart_1101354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101412 : List Nat := [2, 3, 1, 1, 2, 5, 2, 1, 2, 2, 2]
def baseStart_1101412 : Nat := 118140960795 + 1101412 * 2 ^ 59
def prefixEnd_1101412 : Nat := 4983230072969 + 3 ^ 40 * 1101412 * 2
def baseEnd_1101412 : Nat := 565553754629949954184705

theorem tailTrace_1101412 : CollatzResearch.WordTrace tailWord_1101412 prefixEnd_1101412 565553754629949954184705 := by
  unfold tailWord_1101412
  simp only [CollatzResearch.WordTrace]
  refine ⟨20085897942889952519405245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26781197257186603359206993 20085897942889952519405245)
  ·
    refine ⟨7532211728583732194776967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20085897942889952519405245 7532211728583732194776967)
    ·
      refine ⟨11298317592875598292165451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7532211728583732194776967 11298317592875598292165451)
      ·
        refine ⟨16947476389313397438248177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11298317592875598292165451 16947476389313397438248177)
        ·
          refine ⟨12710607291985048078686133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16947476389313397438248177 12710607291985048078686133)
          ·
            refine ⟨1191619433623598257376825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12710607291985048078686133 1191619433623598257376825)
            ·
              refine ⟨893714575217698693032619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191619433623598257376825 893714575217698693032619)
              ·
                refine ⟨1340571862826548039548929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893714575217698693032619 1340571862826548039548929)
                ·
                  refine ⟨1005428897119911029661697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340571862826548039548929 1005428897119911029661697)
                  ·
                    refine ⟨754071672839933272246273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1005428897119911029661697 754071672839933272246273)
                    ·
                      refine ⟨565553754629949954184705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754071672839933272246273 565553754629949954184705)
                      ·
                        rfl

theorem cell23_1101412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 2, 1, 2, 2, 2].length) (baseStart_1101412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101412 prefixEnd_1101412 := by exact prefixLift 1101412
  have htrace : WordTrace (prefixWord ++ tailWord_1101412) baseStart_1101412 baseEnd_1101412 := by
    simpa [prefixWord, tailWord_1101412, baseEnd_1101412] using wordTrace_append hprefix tailTrace_1101412
  have hstable : (prefixWord ++ tailWord_1101412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101412).length < 2 ^ (prefixWord ++ tailWord_1101412).sum := by decide
  have hdescent : baseEnd_1101412 < baseStart_1101412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101451 : List Nat := [1, 1, 1, 1, 4, 1, 4, 2, 2, 4, 2]
def baseStart_1101451 : Nat := 118140960795 + 1101451 * 2 ^ 59
def prefixEnd_1101451 : Nat := 4983230072969 + 3 ^ 40 * 1101451 * 2
def baseEnd_1101451 : Nat := 565573780375475301597025

theorem tailTrace_1101451 : CollatzResearch.WordTrace tailWord_1101451 prefixEnd_1101451 565573780375475301597025 := by
  unfold tailWord_1101451
  simp only [CollatzResearch.WordTrace]
  refine ⟨40173218332638614699480207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26782145555092409799653471 40173218332638614699480207)
  ·
    refine ⟨60259827498957922049220311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40173218332638614699480207 60259827498957922049220311)
    ·
      refine ⟨90389741248436883073830467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60259827498957922049220311 90389741248436883073830467)
      ·
        refine ⟨135584611872655324610745701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90389741248436883073830467 135584611872655324610745701)
        ·
          refine ⟨25422114726122873364514819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135584611872655324610745701 25422114726122873364514819)
          ·
            refine ⟨38133172089184310046772229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25422114726122873364514819 38133172089184310046772229)
            ·
              refine ⟨7149969766722058133769793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38133172089184310046772229 7149969766722058133769793)
              ·
                refine ⟨5362477325041543600327345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7149969766722058133769793 5362477325041543600327345)
                ·
                  refine ⟨4021857993781157700245509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5362477325041543600327345 4021857993781157700245509)
                  ·
                    refine ⟨754098373833967068796033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4021857993781157700245509 754098373833967068796033)
                    ·
                      refine ⟨565573780375475301597025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754098373833967068796033 565573780375475301597025)
                      ·
                        rfl

theorem cell23_1101451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4, 2].length) (baseStart_1101451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101451 prefixEnd_1101451 := by exact prefixLift 1101451
  have htrace : WordTrace (prefixWord ++ tailWord_1101451) baseStart_1101451 baseEnd_1101451 := by
    simpa [prefixWord, tailWord_1101451, baseEnd_1101451] using wordTrace_append hprefix tailTrace_1101451
  have hstable : (prefixWord ++ tailWord_1101451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101451).length < 2 ^ (prefixWord ++ tailWord_1101451).sum := by decide
  have hdescent : baseEnd_1101451 < baseStart_1101451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101495 : List Nat := [1, 1, 3, 1, 5, 2, 2, 3, 1, 4]
def baseStart_1101495 : Nat := 118140960795 + 1101495 * 2 ^ 59
def prefixEnd_1101495 : Nat := 4983230072969 + 3 ^ 40 * 1101495 * 2
def baseEnd_1101495 : Nat := 188532124508091043148941

theorem tailTrace_1101495 : CollatzResearch.WordTrace tailWord_1101495 prefixEnd_1101495 188532124508091043148941 := by
  unfold tailWord_1101495
  simp only [CollatzResearch.WordTrace]
  refine ⟨40174823144479210214081939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26783215429652806809387959 40174823144479210214081939)
  ·
    refine ⟨60262234716718815321122909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40174823144479210214081939 60262234716718815321122909)
    ·
      refine ⟨22598338018769555745421091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60262234716718815321122909 22598338018769555745421091)
      ·
        refine ⟨33897507028154333618131637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22598338018769555745421091 33897507028154333618131637)
        ·
          refine ⟨3177891283889468776699841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33897507028154333618131637 3177891283889468776699841)
          ·
            refine ⟨2383418462917101582524881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3177891283889468776699841 2383418462917101582524881)
            ·
              refine ⟨1787563847187826186893661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2383418462917101582524881 1787563847187826186893661)
              ·
                refine ⟨670336442695434820085123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1787563847187826186893661 670336442695434820085123)
                ·
                  refine ⟨1005504664043152230127685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670336442695434820085123 1005504664043152230127685)
                  ·
                    refine ⟨188532124508091043148941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005504664043152230127685 188532124508091043148941)
                    ·
                      rfl

theorem cell23_1101495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 3, 1, 4].length) (baseStart_1101495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101495 prefixEnd_1101495 := by exact prefixLift 1101495
  have htrace : WordTrace (prefixWord ++ tailWord_1101495) baseStart_1101495 baseEnd_1101495 := by
    simpa [prefixWord, tailWord_1101495, baseEnd_1101495] using wordTrace_append hprefix tailTrace_1101495
  have hstable : (prefixWord ++ tailWord_1101495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101495).length < 2 ^ (prefixWord ++ tailWord_1101495).sum := by decide
  have hdescent : baseEnd_1101495 < baseStart_1101495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101551 : List Nat := [1, 1, 2, 1, 5, 1, 1, 1, 6, 4]
def baseStart_1101551 : Nat := 118140960795 + 1101551 * 2 ^ 59
def prefixEnd_1101551 : Nat := 4983230072969 + 3 ^ 40 * 1101551 * 2
def baseEnd_1101551 : Nat := 188541709480308303448855

theorem tailTrace_1101551 : CollatzResearch.WordTrace tailWord_1101551 prefixEnd_1101551 188541709480308303448855 := by
  unfold tailWord_1101551
  simp only [CollatzResearch.WordTrace]
  refine ⟨40176865632276331778120507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26784577088184221185413671 40176865632276331778120507)
  ·
    refine ⟨60265298448414497667180761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40176865632276331778120507 60265298448414497667180761)
    ·
      refine ⟨45198973836310873250385571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60265298448414497667180761 45198973836310873250385571)
      ·
        refine ⟨67798460754466309875578357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45198973836310873250385571 67798460754466309875578357)
        ·
          refine ⟨6356105695731216550835471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67798460754466309875578357 6356105695731216550835471)
          ·
            refine ⟨9534158543596824826253207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6356105695731216550835471 9534158543596824826253207)
            ·
              refine ⟨14301237815395237239379811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9534158543596824826253207 14301237815395237239379811)
              ·
                refine ⟨21451856723092855859069717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14301237815395237239379811 21451856723092855859069717)
                ·
                  refine ⟨1005555783894977618393893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21451856723092855859069717 1005555783894977618393893)
                  ·
                    refine ⟨188541709480308303448855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005555783894977618393893 188541709480308303448855)
                    ·
                      rfl

theorem cell23_1101551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 1, 6, 4].length) (baseStart_1101551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101551 prefixEnd_1101551 := by exact prefixLift 1101551
  have htrace : WordTrace (prefixWord ++ tailWord_1101551) baseStart_1101551 baseEnd_1101551 := by
    simpa [prefixWord, tailWord_1101551, baseEnd_1101551] using wordTrace_append hprefix tailTrace_1101551
  have hstable : (prefixWord ++ tailWord_1101551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101551).length < 2 ^ (prefixWord ++ tailWord_1101551).sum := by decide
  have hdescent : baseEnd_1101551 < baseStart_1101551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101561 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 3]
def baseStart_1101561 : Nat := 118140960795 + 1101561 * 2 ^ 59
def prefixEnd_1101561 : Nat := 4983230072969 + 3 ^ 40 * 1101561 * 2
def baseEnd_1101561 : Nat := 565630263247469871221519

theorem tailTrace_1101561 : CollatzResearch.WordTrace tailWord_1101561 prefixEnd_1101561 565630263247469871221519 := by
  unfold tailWord_1101561
  simp only [CollatzResearch.WordTrace]
  refine ⟨40177230362240103485984537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26784820241493402323989691 40177230362240103485984537)
  ·
    refine ⟨30132922771680077614488403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40177230362240103485984537 30132922771680077614488403)
    ·
      refine ⟨45199384157520116421732605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30132922771680077614488403 45199384157520116421732605)
      ·
        refine ⟨16949769059070043658149727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45199384157520116421732605 16949769059070043658149727)
        ·
          refine ⟨25424653588605065487224591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16949769059070043658149727 25424653588605065487224591)
          ·
            refine ⟨38136980382907598230836887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25424653588605065487224591 38136980382907598230836887)
            ·
              refine ⟨57205470574361397346255331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38136980382907598230836887 57205470574361397346255331)
              ·
                refine ⟨85808205861542096019382997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57205470574361397346255331 85808205861542096019382997)
                ·
                  refine ⟨2011129824879892875454289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 85808205861542096019382997 2011129824879892875454289)
                  ·
                    refine ⟨1508347368659919656590717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011129824879892875454289 1508347368659919656590717)
                    ·
                      refine ⟨565630263247469871221519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1508347368659919656590717 565630263247469871221519)
                      ·
                        rfl

theorem cell23_1101561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 7, 2, 3].length) (baseStart_1101561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101561 prefixEnd_1101561 := by exact prefixLift 1101561
  have htrace : WordTrace (prefixWord ++ tailWord_1101561) baseStart_1101561 baseEnd_1101561 := by
    simpa [prefixWord, tailWord_1101561, baseEnd_1101561] using wordTrace_append hprefix tailTrace_1101561
  have hstable : (prefixWord ++ tailWord_1101561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101561).length < 2 ^ (prefixWord ++ tailWord_1101561).sum := by decide
  have hdescent : baseEnd_1101561 < baseStart_1101561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101608 : List Nat := [2, 1, 5, 1, 1, 2, 1, 1, 3, 3, 3]
def baseStart_1101608 : Nat := 118140960795 + 1101608 * 2 ^ 59
def prefixEnd_1101608 : Nat := 4983230072969 + 3 ^ 40 * 1101608 * 2
def baseEnd_1101608 : Nat := 565654396838231187333803

theorem tailTrace_1101608 : CollatzResearch.WordTrace tailWord_1101608 prefixEnd_1101608 565654396838231187333803 := by
  unfold tailWord_1101608
  simp only [CollatzResearch.WordTrace]
  refine ⟨20089472296534915256472739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26785963062046553675296985 20089472296534915256472739)
  ·
    refine ⟨30134208444802372884709109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20089472296534915256472739 30134208444802372884709109)
    ·
      refine ⟨2825082041700222457941479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30134208444802372884709109 2825082041700222457941479)
      ·
        refine ⟨4237623062550333686912219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2825082041700222457941479 4237623062550333686912219)
        ·
          refine ⟨6356434593825500530368329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4237623062550333686912219 6356434593825500530368329)
          ·
            refine ⟨4767325945369125397776247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6356434593825500530368329 4767325945369125397776247)
            ·
              refine ⟨7150988918053688096664371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4767325945369125397776247 7150988918053688096664371)
              ·
                refine ⟨10726483377080532144996557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7150988918053688096664371 10726483377080532144996557)
                ·
                  refine ⟨4022431266405199554373709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10726483377080532144996557 4022431266405199554373709)
                  ·
                    refine ⟨1508411724901949832890141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4022431266405199554373709 1508411724901949832890141)
                    ·
                      refine ⟨565654396838231187333803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1508411724901949832890141 565654396838231187333803)
                      ·
                        rfl

theorem cell23_1101608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_1101608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101608 prefixEnd_1101608 := by exact prefixLift 1101608
  have htrace : WordTrace (prefixWord ++ tailWord_1101608) baseStart_1101608 baseEnd_1101608 := by
    simpa [prefixWord, tailWord_1101608, baseEnd_1101608] using wordTrace_append hprefix tailTrace_1101608
  have hstable : (prefixWord ++ tailWord_1101608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101608).length < 2 ^ (prefixWord ++ tailWord_1101608).sum := by decide
  have hdescent : baseEnd_1101608 < baseStart_1101608 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101626 : List Nat := [3, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2]
def baseStart_1101626 : Nat := 118140960795 + 1101626 * 2 ^ 59
def prefixEnd_1101626 : Nat := 4983230072969 + 3 ^ 40 * 1101626 * 2
def baseEnd_1101626 : Nat := 565663639490012116908721

theorem tailTrace_1101626 : CollatzResearch.WordTrace tailWord_1101626 prefixEnd_1101626 565663639490012116908721 := by
  unfold tailWord_1101626
  simp only [CollatzResearch.WordTrace]
  refine ⟨10044900276751154896775183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26786400738003079724733821 10044900276751154896775183)
  ·
    refine ⟨15067350415126732345162775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10044900276751154896775183 15067350415126732345162775)
    ·
      refine ⟨22601025622690098517744163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15067350415126732345162775 22601025622690098517744163)
      ·
        refine ⟨33901538434035147776616245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22601025622690098517744163 33901538434035147776616245)
        ·
          refine ⟨3178269228190795104057773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 33901538434035147776616245 3178269228190795104057773)
          ·
            refine ⟨1191850960571548164021665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3178269228190795104057773 1191850960571548164021665)
            ·
              refine ⟨893888220428661123016249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1191850960571548164021665 893888220428661123016249)
              ·
                refine ⟨670416165321495842262187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 893888220428661123016249 670416165321495842262187)
                ·
                  refine ⟨1005624247982243763393281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670416165321495842262187 1005624247982243763393281)
                  ·
                    refine ⟨754218185986682822544961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1005624247982243763393281 754218185986682822544961)
                    ·
                      refine ⟨565663639490012116908721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754218185986682822544961 565663639490012116908721)
                      ·
                        rfl

theorem cell23_1101626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 3, 2, 2, 1, 2, 2].length) (baseStart_1101626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101626 prefixEnd_1101626 := by exact prefixLift 1101626
  have htrace : WordTrace (prefixWord ++ tailWord_1101626) baseStart_1101626 baseEnd_1101626 := by
    simpa [prefixWord, tailWord_1101626, baseEnd_1101626] using wordTrace_append hprefix tailTrace_1101626
  have hstable : (prefixWord ++ tailWord_1101626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101626).length < 2 ^ (prefixWord ++ tailWord_1101626).sum := by decide
  have hdescent : baseEnd_1101626 < baseStart_1101626 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101641 : List Nat := [1, 2, 1, 1, 2, 4, 3, 1, 2, 6]
def baseStart_1101641 : Nat := 118140960795 + 1101641 * 2 ^ 59
def prefixEnd_1101641 : Nat := 4983230072969 + 3 ^ 40 * 1101641 * 2
def baseEnd_1101641 : Nat := 188557113899943186073717

theorem tailTrace_1101641 : CollatzResearch.WordTrace tailWord_1101641 prefixEnd_1101641 188557113899943186073717 := by
  unfold tailWord_1101641
  simp only [CollatzResearch.WordTrace]
  refine ⟨40180148201950277148896777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26786765467966851432597851 40180148201950277148896777)
  ·
    refine ⟨30135111151462707861672583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40180148201950277148896777 30135111151462707861672583)
    ·
      refine ⟨45202666727194061792508875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30135111151462707861672583 45202666727194061792508875)
      ·
        refine ⟨67804000090791092688763313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45202666727194061792508875 67804000090791092688763313)
        ·
          refine ⟨50853000068093319516572485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67804000090791092688763313 50853000068093319516572485)
          ·
            refine ⟨9534937512767497409357341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50853000068093319516572485 9534937512767497409357341)
            ·
              refine ⟨3575601567287811528509003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9534937512767497409357341 3575601567287811528509003)
              ·
                refine ⟨5363402350931717292763505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3575601567287811528509003 5363402350931717292763505)
                ·
                  refine ⟨4022551763198787969572629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5363402350931717292763505 4022551763198787969572629)
                  ·
                    refine ⟨188557113899943186073717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4022551763198787969572629 188557113899943186073717)
                    ·
                      rfl

theorem cell23_1101641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 3, 1, 2, 6].length) (baseStart_1101641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101641 prefixEnd_1101641 := by exact prefixLift 1101641
  have htrace : WordTrace (prefixWord ++ tailWord_1101641) baseStart_1101641 baseEnd_1101641 := by
    simpa [prefixWord, tailWord_1101641, baseEnd_1101641] using wordTrace_append hprefix tailTrace_1101641
  have hstable : (prefixWord ++ tailWord_1101641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101641).length < 2 ^ (prefixWord ++ tailWord_1101641).sum := by decide
  have hdescent : baseEnd_1101641 < baseStart_1101641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101665 : List Nat := [1, 2, 3, 1, 1, 1, 4, 2, 4, 2, 2]
def baseStart_1101665 : Nat := 118140960795 + 1101665 * 2 ^ 59
def prefixEnd_1101665 : Nat := 4983230072969 + 3 ^ 40 * 1101665 * 2
def baseEnd_1101665 : Nat := 565683665235537464321041

theorem tailTrace_1101665 : CollatzResearch.WordTrace tailWord_1101665 prefixEnd_1101665 565683665235537464321041 := by
  unfold tailWord_1101665
  simp only [CollatzResearch.WordTrace]
  refine ⟨40181023553863329247770449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26787349035908886165180299 40181023553863329247770449)
  ·
    refine ⟨30135767665397496935827837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40181023553863329247770449 30135767665397496935827837)
    ·
      refine ⟨11300912874524061350935439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30135767665397496935827837 11300912874524061350935439)
      ·
        refine ⟨16951369311786092026403159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11300912874524061350935439 16951369311786092026403159)
        ·
          refine ⟨25427053967679138039604739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16951369311786092026403159 25427053967679138039604739)
          ·
            refine ⟨38140580951518707059407109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25427053967679138039604739 38140580951518707059407109)
            ·
              refine ⟨7151358928409757573638833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38140580951518707059407109 7151358928409757573638833)
              ·
                refine ⟨5363519196307318180229125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7151358928409757573638833 5363519196307318180229125)
                ·
                  refine ⟨1005659849307622158792961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5363519196307318180229125 1005659849307622158792961)
                  ·
                    refine ⟨754244886980716619094721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1005659849307622158792961 754244886980716619094721)
                    ·
                      refine ⟨565683665235537464321041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754244886980716619094721 565683665235537464321041)
                      ·
                        rfl

theorem cell23_1101665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 2, 4, 2, 2].length) (baseStart_1101665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101665 prefixEnd_1101665 := by exact prefixLift 1101665
  have htrace : WordTrace (prefixWord ++ tailWord_1101665) baseStart_1101665 baseEnd_1101665 := by
    simpa [prefixWord, tailWord_1101665, baseEnd_1101665] using wordTrace_append hprefix tailTrace_1101665
  have hstable : (prefixWord ++ tailWord_1101665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101665).length < 2 ^ (prefixWord ++ tailWord_1101665).sum := by decide
  have hdescent : baseEnd_1101665 < baseStart_1101665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101671 : List Nat := [1, 1, 5, 1, 2, 1, 1, 2, 9]
def baseStart_1101671 : Nat := 118140960795 + 1101671 * 2 ^ 59
def prefixEnd_1101671 : Nat := 4983230072969 + 3 ^ 40 * 1101671 * 2
def baseEnd_1101671 : Nat := 62854082902162715649557

theorem tailTrace_1101671 : CollatzResearch.WordTrace tailWord_1101671 prefixEnd_1101671 62854082902162715649557 := by
  unfold tailWord_1101671
  simp only [CollatzResearch.WordTrace]
  refine ⟨40181242391841592272488867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26787494927894394848325911 40181242391841592272488867)
  ·
    refine ⟨60271863587762388408733301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40181242391841592272488867 60271863587762388408733301)
    ·
      refine ⟨5650487211352723913318747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60271863587762388408733301 5650487211352723913318747)
      ·
        refine ⟨8475730817029085869978121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5650487211352723913318747 8475730817029085869978121)
        ·
          refine ⟨6356798112771814402483591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8475730817029085869978121 6356798112771814402483591)
          ·
            refine ⟨9535197169157721603725387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6356798112771814402483591 9535197169157721603725387)
            ·
              refine ⟨14302795753736582405588081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9535197169157721603725387 14302795753736582405588081)
              ·
                refine ⟨10727096815302436804191061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14302795753736582405588081 10727096815302436804191061)
                ·
                  refine ⟨62854082902162715649557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 10727096815302436804191061 62854082902162715649557)
                  ·
                    rfl

theorem cell23_1101671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 1, 2, 9].length) (baseStart_1101671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101671 prefixEnd_1101671 := by exact prefixLift 1101671
  have htrace : WordTrace (prefixWord ++ tailWord_1101671) baseStart_1101671 baseEnd_1101671 := by
    simpa [prefixWord, tailWord_1101671, baseEnd_1101671] using wordTrace_append hprefix tailTrace_1101671
  have hstable : (prefixWord ++ tailWord_1101671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101671).length < 2 ^ (prefixWord ++ tailWord_1101671).sum := by decide
  have hdescent : baseEnd_1101671 < baseStart_1101671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101699 : List Nat := [1, 1, 1, 3, 4, 3, 3, 1, 2, 2, 2]
def baseStart_1101699 : Nat := 118140960795 + 1101699 * 2 ^ 59
def prefixEnd_1101699 : Nat := 4983230072969 + 3 ^ 40 * 1101699 * 2
def baseEnd_1101699 : Nat := 565701123577790331295885

theorem tailTrace_1101699 : CollatzResearch.WordTrace tailWord_1101699 prefixEnd_1101699 565701123577790331295885 := by
  unfold tailWord_1101699
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182263635740153054508151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26788175757160102036338767 40182263635740153054508151)
  ·
    refine ⟨60273395453610229581762227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40182263635740153054508151 60273395453610229581762227)
    ·
      refine ⟨90410093180415344372643341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60273395453610229581762227 90410093180415344372643341)
      ·
        refine ⟨33903784942655754139741253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90410093180415344372643341 33903784942655754139741253)
        ·
          refine ⟨6356959676747953901201485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33903784942655754139741253 6356959676747953901201485)
          ·
            refine ⟨2383859878780482712950557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6356959676747953901201485 2383859878780482712950557)
            ·
              refine ⟨893947454542681017356459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2383859878780482712950557 893947454542681017356459)
              ·
                refine ⟨1340921181814021526034689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 893947454542681017356459 1340921181814021526034689)
                ·
                  refine ⟨1005690886360516144526017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1340921181814021526034689 1005690886360516144526017)
                  ·
                    refine ⟨754268164770387108394513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1005690886360516144526017 754268164770387108394513)
                    ·
                      refine ⟨565701123577790331295885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754268164770387108394513 565701123577790331295885)
                      ·
                        rfl

theorem cell23_1101699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 3, 1, 2, 2, 2].length) (baseStart_1101699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101699 prefixEnd_1101699 := by exact prefixLift 1101699
  have htrace : WordTrace (prefixWord ++ tailWord_1101699) baseStart_1101699 baseEnd_1101699 := by
    simpa [prefixWord, tailWord_1101699, baseEnd_1101699] using wordTrace_append hprefix tailTrace_1101699
  have hstable : (prefixWord ++ tailWord_1101699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101699).length < 2 ^ (prefixWord ++ tailWord_1101699).sum := by decide
  have hdescent : baseEnd_1101699 < baseStart_1101699 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101701 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 3, 7]
def baseStart_1101701 : Nat := 118140960795 + 1101701 * 2 ^ 59
def prefixEnd_1101701 : Nat := 4983230072969 + 3 ^ 40 * 1101701 * 2
def baseEnd_1101701 : Nat := 188567383513033107823625

theorem tailTrace_1101701 : CollatzResearch.WordTrace tailWord_1101701 prefixEnd_1101701 188567383513033107823625 := by
  unfold tailWord_1101701
  simp only [CollatzResearch.WordTrace]
  refine ⟨40182336581732907396080957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26788224387821938264053971 40182336581732907396080957)
  ·
    refine ⟨15068376218149840273530359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40182336581732907396080957 15068376218149840273530359)
    ·
      refine ⟨22602564327224760410295539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15068376218149840273530359 22602564327224760410295539)
      ·
        refine ⟨33903846490837140615443309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22602564327224760410295539 33903846490837140615443309)
        ·
          refine ⟨12713942434063927730791241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33903846490837140615443309 12713942434063927730791241)
          ·
            refine ⟨9535456825547945798093431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12713942434063927730791241 9535456825547945798093431)
            ·
              refine ⟨14303185238321918697140147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9535456825547945798093431 14303185238321918697140147)
              ·
                refine ⟨21454777857482878045710221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14303185238321918697140147 21454777857482878045710221)
                ·
                  refine ⟨8045541696556079267141333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21454777857482878045710221 8045541696556079267141333)
                  ·
                    refine ⟨188567383513033107823625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8045541696556079267141333 188567383513033107823625)
                    ·
                      rfl

theorem cell23_1101701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 7].length) (baseStart_1101701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101701 prefixEnd_1101701 := by exact prefixLift 1101701
  have htrace : WordTrace (prefixWord ++ tailWord_1101701) baseStart_1101701 baseEnd_1101701 := by
    simpa [prefixWord, tailWord_1101701, baseEnd_1101701] using wordTrace_append hprefix tailTrace_1101701
  have hstable : (prefixWord ++ tailWord_1101701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101701).length < 2 ^ (prefixWord ++ tailWord_1101701).sum := by decide
  have hdescent : baseEnd_1101701 < baseStart_1101701 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101722 : List Nat := [3, 1, 1, 4, 2, 3, 1, 3, 5]
def baseStart_1101722 : Nat := 118140960795 + 1101722 * 2 ^ 59
def prefixEnd_1101722 : Nat := 4983230072969 + 3 ^ 40 * 1101722 * 2
def baseEnd_1101722 : Nat := 62856992625871526812031

theorem tailTrace_1101722 : CollatzResearch.WordTrace tailWord_1101722 prefixEnd_1101722 62856992625871526812031 := by
  unfold tailWord_1101722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10045775628664206995648855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26788735009771218655063613 10045775628664206995648855)
  ·
    refine ⟨15068663442996310493473283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10045775628664206995648855 15068663442996310493473283)
    ·
      refine ⟨22602995164494465740209925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15068663442996310493473283 22602995164494465740209925)
      ·
        refine ⟨4238061593342712326289361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22602995164494465740209925 4238061593342712326289361)
        ·
          refine ⟨3178546195007034244717021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4238061593342712326289361 3178546195007034244717021)
          ·
            refine ⟨1191954823127637841768883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3178546195007034244717021 1191954823127637841768883)
            ·
              refine ⟨1787932234691456762653325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1191954823127637841768883 1787932234691456762653325)
              ·
                refine ⟨670474588009296285994997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1787932234691456762653325 670474588009296285994997)
                ·
                  refine ⟨62856992625871526812031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 670474588009296285994997 62856992625871526812031)
                  ·
                    rfl

theorem cell23_1101722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 3, 1, 3, 5].length) (baseStart_1101722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101722 prefixEnd_1101722 := by exact prefixLift 1101722
  have htrace : WordTrace (prefixWord ++ tailWord_1101722) baseStart_1101722 baseEnd_1101722 := by
    simpa [prefixWord, tailWord_1101722, baseEnd_1101722] using wordTrace_append hprefix tailTrace_1101722
  have hstable : (prefixWord ++ tailWord_1101722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101722).length < 2 ^ (prefixWord ++ tailWord_1101722).sum := by decide
  have hdescent : baseEnd_1101722 < baseStart_1101722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101735 : List Nat := [1, 1, 6, 1, 2, 2, 1, 2, 2, 5]
def baseStart_1101735 : Nat := 118140960795 + 1101735 * 2 ^ 59
def prefixEnd_1101735 : Nat := 4983230072969 + 3 ^ 40 * 1101735 * 2
def baseEnd_1101735 : Nat := 188573202960450730148573

theorem tailTrace_1101735 : CollatzResearch.WordTrace tailWord_1101735 prefixEnd_1101735 188573202960450730148573 := by
  unfold tailWord_1101735
  simp only [CollatzResearch.WordTrace]
  refine ⟨40183576663609731202818659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26789051109073154135212439 40183576663609731202818659)
  ·
    refine ⟨60275364995414596804227989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40183576663609731202818659 60275364995414596804227989)
    ·
      refine ⟨2825407734160059225198187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60275364995414596804227989 2825407734160059225198187)
      ·
        refine ⟨4238111601240088837797281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2825407734160059225198187 4238111601240088837797281)
        ·
          refine ⟨3178583700930066628347961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4238111601240088837797281 3178583700930066628347961)
          ·
            refine ⟨2383937775697549971260971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3178583700930066628347961 2383937775697549971260971)
            ·
              refine ⟨3575906663546324956891457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2383937775697549971260971 3575906663546324956891457)
              ·
                refine ⟨2681929997659743717668593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3575906663546324956891457 2681929997659743717668593)
                ·
                  refine ⟨2011447498244807788251445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2681929997659743717668593 2011447498244807788251445)
                  ·
                    refine ⟨188573202960450730148573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2011447498244807788251445 188573202960450730148573)
                    ·
                      rfl

theorem cell23_1101735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 2, 2, 5].length) (baseStart_1101735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101735 prefixEnd_1101735 := by exact prefixLift 1101735
  have htrace : WordTrace (prefixWord ++ tailWord_1101735) baseStart_1101735 baseEnd_1101735 := by
    simpa [prefixWord, tailWord_1101735, baseEnd_1101735] using wordTrace_append hprefix tailTrace_1101735
  have hstable : (prefixWord ++ tailWord_1101735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101735).length < 2 ^ (prefixWord ++ tailWord_1101735).sum := by decide
  have hdescent : baseEnd_1101735 < baseStart_1101735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101775 : List Nat := [1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 3]
def baseStart_1101775 : Nat := 118140960795 + 1101775 * 2 ^ 59
def prefixEnd_1101775 : Nat := 4983230072969 + 3 ^ 40 * 1101775 * 2
def baseEnd_1101775 : Nat := 565740148107532033945535

theorem tailTrace_1101775 : CollatzResearch.WordTrace tailWord_1101775 prefixEnd_1101775 565740148107532033945535 := by
  unfold tailWord_1101775
  simp only [CollatzResearch.WordTrace]
  refine ⟨40185035583464818034274779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26790023722309878689516519 40185035583464818034274779)
  ·
    refine ⟨60277553375197227051412169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40185035583464818034274779 60277553375197227051412169)
    ·
      refine ⟨45208165031397920288559127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60277553375197227051412169 45208165031397920288559127)
      ·
        refine ⟨67812247547096880432838691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45208165031397920288559127 67812247547096880432838691)
        ·
          refine ⟨101718371320645320649258037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67812247547096880432838691 101718371320645320649258037)
          ·
            refine ⟨9536097311310498810867941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101718371320645320649258037 9536097311310498810867941)
            ·
              refine ⟨1788018245870718527037739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9536097311310498810867941 1788018245870718527037739)
              ·
                refine ⟨2682027368806077790556609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788018245870718527037739 2682027368806077790556609)
                ·
                  refine ⟨2011520526604558342917457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2682027368806077790556609 2011520526604558342917457)
                  ·
                    refine ⟨1508640394953418757188093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2011520526604558342917457 1508640394953418757188093)
                    ·
                      refine ⟨565740148107532033945535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1508640394953418757188093 565740148107532033945535)
                      ·
                        rfl

theorem cell23_1101775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 1, 2, 2, 3].length) (baseStart_1101775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101775 prefixEnd_1101775 := by exact prefixLift 1101775
  have htrace : WordTrace (prefixWord ++ tailWord_1101775) baseStart_1101775 baseEnd_1101775 := by
    simpa [prefixWord, tailWord_1101775, baseEnd_1101775] using wordTrace_append hprefix tailTrace_1101775
  have hstable : (prefixWord ++ tailWord_1101775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101775).length < 2 ^ (prefixWord ++ tailWord_1101775).sum := by decide
  have hdescent : baseEnd_1101775 < baseStart_1101775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101795 : List Nat := [1, 1, 1, 6, 1, 3, 2, 2, 6]
def baseStart_1101795 : Nat := 118140960795 + 1101795 * 2 ^ 59
def prefixEnd_1101795 : Nat := 4983230072969 + 3 ^ 40 * 1101795 * 2
def baseEnd_1101795 : Nat := 62861157524513550632827

theorem tailTrace_1101795 : CollatzResearch.WordTrace tailWord_1101795 prefixEnd_1101795 62861157524513550632827 := by
  unfold tailWord_1101795
  simp only [CollatzResearch.WordTrace]
  refine ⟨40185765043392361450002839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26790510028928240966668559 40185765043392361450002839)
  ·
    refine ⟨60278647565088542175004259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40185765043392361450002839 60278647565088542175004259)
    ·
      refine ⟨90417971347632813262506389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60278647565088542175004259 90417971347632813262506389)
      ·
        refine ⟨4238342406920288121679987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 90417971347632813262506389 4238342406920288121679987)
        ·
          refine ⟨6357513610380432182519981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4238342406920288121679987 6357513610380432182519981)
          ·
            refine ⟨2384067603892662068444993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6357513610380432182519981 2384067603892662068444993)
            ·
              refine ⟨1788050702919496551333745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384067603892662068444993 1788050702919496551333745)
              ·
                refine ⟨1341038027189622413500309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1788050702919496551333745 1341038027189622413500309)
                ·
                  refine ⟨62861157524513550632827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1341038027189622413500309 62861157524513550632827)
                  ·
                    rfl

theorem cell23_1101795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 2, 2, 6].length) (baseStart_1101795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101795 prefixEnd_1101795 := by exact prefixLift 1101795
  have htrace : WordTrace (prefixWord ++ tailWord_1101795) baseStart_1101795 baseEnd_1101795 := by
    simpa [prefixWord, tailWord_1101795, baseEnd_1101795] using wordTrace_append hprefix tailTrace_1101795
  have hstable : (prefixWord ++ tailWord_1101795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101795).length < 2 ^ (prefixWord ++ tailWord_1101795).sum := by decide
  have hdescent : baseEnd_1101795 < baseStart_1101795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101799 : List Nat := [1, 1, 5, 2, 3, 1, 1, 4, 1, 4]
def baseStart_1101799 : Nat := 118140960795 + 1101799 * 2 ^ 59
def prefixEnd_1101799 : Nat := 4983230072969 + 3 ^ 40 * 1101799 * 2
def baseEnd_1101799 : Nat := 188584157214413313348475

theorem tailTrace_1101799 : CollatzResearch.WordTrace tailWord_1101799 prefixEnd_1101799 188584157214413313348475 := by
  unfold tailWord_1101799
  simp only [CollatzResearch.WordTrace]
  refine ⟨40185910935377870133148451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26790607290251913422098967 40185910935377870133148451)
  ·
    refine ⟨60278866403066805199722677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40185910935377870133148451 60278866403066805199722677)
    ·
      refine ⟨5651143725287512987474001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60278866403066805199722677 5651143725287512987474001)
      ·
        refine ⟨4238357793965634740605501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5651143725287512987474001 4238357793965634740605501)
        ·
          refine ⟨1589384172737113027727063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4238357793965634740605501 1589384172737113027727063)
          ·
            refine ⟨2384076259105669541590595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1589384172737113027727063 2384076259105669541590595)
            ·
              refine ⟨3576114388658504312385893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2384076259105669541590595 3576114388658504312385893)
              ·
                refine ⟨670521447873469558572355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3576114388658504312385893 670521447873469558572355)
                ·
                  refine ⟨1005782171810204337858533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670521447873469558572355 1005782171810204337858533)
                  ·
                    refine ⟨188584157214413313348475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005782171810204337858533 188584157214413313348475)
                    ·
                      rfl

theorem cell23_1101799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 4, 1, 4].length) (baseStart_1101799 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101799 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101799 prefixEnd_1101799 := by exact prefixLift 1101799
  have htrace : WordTrace (prefixWord ++ tailWord_1101799) baseStart_1101799 baseEnd_1101799 := by
    simpa [prefixWord, tailWord_1101799, baseEnd_1101799] using wordTrace_append hprefix tailTrace_1101799
  have hstable : (prefixWord ++ tailWord_1101799).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101799).length < 2 ^ (prefixWord ++ tailWord_1101799).sum := by decide
  have hdescent : baseEnd_1101799 < baseStart_1101799 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101808 : List Nat := [2, 1, 1, 1, 3, 2, 3, 2, 3, 5]
def baseStart_1101808 : Nat := 118140960795 + 1101808 * 2 ^ 59
def prefixEnd_1101808 : Nat := 4983230072969 + 3 ^ 40 * 1101808 * 2
def baseEnd_1101808 : Nat := 188585697656376801610961

theorem tailTrace_1101808 : CollatzResearch.WordTrace tailWord_1101808 prefixEnd_1101808 188585697656376801610961 := by
  unfold tailWord_1101808
  simp only [CollatzResearch.WordTrace]
  refine ⟨20093119596172632335113039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26790826128230176446817385 20093119596172632335113039)
  ·
    refine ⟨30139679394258948502669559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20093119596172632335113039 30139679394258948502669559)
    ·
      refine ⟨45209519091388422754004339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30139679394258948502669559 45209519091388422754004339)
      ·
        refine ⟨67814278637082634131006509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45209519091388422754004339 67814278637082634131006509)
        ·
          refine ⟨25430354488905987799127441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67814278637082634131006509 25430354488905987799127441)
          ·
            refine ⟨19072765866679490849345581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25430354488905987799127441 19072765866679490849345581)
            ·
              refine ⟨7152287200004809068504593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19072765866679490849345581 7152287200004809068504593)
              ·
                refine ⟨5364215400003606801378445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7152287200004809068504593 5364215400003606801378445)
                ·
                  refine ⟨2011580775001352550516917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5364215400003606801378445 2011580775001352550516917)
                  ·
                    refine ⟨188585697656376801610961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2011580775001352550516917 188585697656376801610961)
                    ·
                      rfl

theorem cell23_1101808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 3, 2, 3, 5].length) (baseStart_1101808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101808 prefixEnd_1101808 := by exact prefixLift 1101808
  have htrace : WordTrace (prefixWord ++ tailWord_1101808) baseStart_1101808 baseEnd_1101808 := by
    simpa [prefixWord, tailWord_1101808, baseEnd_1101808] using wordTrace_append hprefix tailTrace_1101808
  have hstable : (prefixWord ++ tailWord_1101808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101808).length < 2 ^ (prefixWord ++ tailWord_1101808).sum := by decide
  have hdescent : baseEnd_1101808 < baseStart_1101808 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101825 : List Nat := [1, 2, 4, 1, 2, 1, 2, 4, 1, 5]
def baseStart_1101825 : Nat := 118140960795 + 1101825 * 2 ^ 59
def prefixEnd_1101825 : Nat := 4983230072969 + 3 ^ 40 * 1101825 * 2
def baseEnd_1101825 : Nat := 188588607380085612773435

theorem tailTrace_1101825 : CollatzResearch.WordTrace tailWord_1101825 prefixEnd_1101825 188588607380085612773435 := by
  unfold tailWord_1101825
  simp only [CollatzResearch.WordTrace]
  refine ⟨40186859233283676573594929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26791239488855784382396619 40186859233283676573594929)
  ·
    refine ⟨30140144424962757430196197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40186859233283676573594929 30140144424962757430196197)
    ·
      refine ⟨5651277079680517018161787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30140144424962757430196197 5651277079680517018161787)
      ·
        refine ⟨8476915619520775527242681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5651277079680517018161787 8476915619520775527242681)
        ·
          refine ⟨6357686714640581645432011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8476915619520775527242681 6357686714640581645432011)
          ·
            refine ⟨9536530071960872468148017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6357686714640581645432011 9536530071960872468148017)
            ·
              refine ⟨7152397553970654351111013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9536530071960872468148017 7152397553970654351111013)
              ·
                refine ⟨1341074541369497690833315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7152397553970654351111013 1341074541369497690833315)
                ·
                  refine ⟨2011611812054246536249973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341074541369497690833315 2011611812054246536249973)
                  ·
                    refine ⟨188588607380085612773435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2011611812054246536249973 188588607380085612773435)
                    ·
                      rfl

theorem cell23_1101825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_1101825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101825 prefixEnd_1101825 := by exact prefixLift 1101825
  have htrace : WordTrace (prefixWord ++ tailWord_1101825) baseStart_1101825 baseEnd_1101825 := by
    simpa [prefixWord, tailWord_1101825, baseEnd_1101825] using wordTrace_append hprefix tailTrace_1101825
  have hstable : (prefixWord ++ tailWord_1101825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101825).length < 2 ^ (prefixWord ++ tailWord_1101825).sum := by decide
  have hdescent : baseEnd_1101825 < baseStart_1101825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101855 : List Nat := [1, 1, 2, 4, 1, 2, 3, 1, 4, 4]
def baseStart_1101855 : Nat := 118140960795 + 1101855 * 2 ^ 59
def prefixEnd_1101855 : Nat := 4983230072969 + 3 ^ 40 * 1101855 * 2
def baseEnd_1101855 : Nat := 188593742186630573648389

theorem tailTrace_1101855 : CollatzResearch.WordTrace tailWord_1101855 prefixEnd_1101855 188593742186630573648389 := by
  unfold tailWord_1101855
  simp only [CollatzResearch.WordTrace]
  refine ⟨40187953423174991697187019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26791968948783327798124679 40187953423174991697187019)
  ·
    refine ⟨60281930134762487545780529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40187953423174991697187019 60281930134762487545780529)
    ·
      refine ⟨45211447601071865659335397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60281930134762487545780529 45211447601071865659335397)
      ·
        refine ⟨8477146425200974811125387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45211447601071865659335397 8477146425200974811125387)
        ·
          refine ⟨12715719637801462216688081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8477146425200974811125387 12715719637801462216688081)
          ·
            refine ⟨9536789728351096662516061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12715719637801462216688081 9536789728351096662516061)
            ·
              refine ⟨3576296148131661248443523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9536789728351096662516061 3576296148131661248443523)
              ·
                refine ⟨5364444222197491872665285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576296148131661248443523 5364444222197491872665285)
                ·
                  refine ⟨1005833291662029726124741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5364444222197491872665285 1005833291662029726124741)
                  ·
                    refine ⟨188593742186630573648389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1005833291662029726124741 188593742186630573648389)
                    ·
                      rfl

theorem cell23_1101855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 2, 3, 1, 4, 4].length) (baseStart_1101855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101855 prefixEnd_1101855 := by exact prefixLift 1101855
  have htrace : WordTrace (prefixWord ++ tailWord_1101855) baseStart_1101855 baseEnd_1101855 := by
    simpa [prefixWord, tailWord_1101855, baseEnd_1101855] using wordTrace_append hprefix tailTrace_1101855
  have hstable : (prefixWord ++ tailWord_1101855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101855).length < 2 ^ (prefixWord ++ tailWord_1101855).sum := by decide
  have hdescent : baseEnd_1101855 < baseStart_1101855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101875 : List Nat := [1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 4]
def baseStart_1101875 : Nat := 118140960795 + 1101875 * 2 ^ 59
def prefixEnd_1101875 : Nat := 4983230072969 + 3 ^ 40 * 1101875 * 2
def baseEnd_1101875 : Nat := 565791496172981642695075

theorem tailTrace_1101875 : CollatzResearch.WordTrace tailWord_1101875 prefixEnd_1101875 565791496172981642695075 := by
  unfold tailWord_1101875
  simp only [CollatzResearch.WordTrace]
  refine ⟨40188682883102535112915079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26792455255401690075276719 40188682883102535112915079)
  ·
    refine ⟨60283024324653802669372619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40188682883102535112915079 60283024324653802669372619)
    ·
      refine ⟨90424536486980704004058929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60283024324653802669372619 90424536486980704004058929)
      ·
        refine ⟨67818402365235528003044197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90424536486980704004058929 67818402365235528003044197)
        ·
          refine ⟨12715950443481661500570787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67818402365235528003044197 12715950443481661500570787)
          ·
            refine ⟨19073925665222492250856181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12715950443481661500570787 19073925665222492250856181)
            ·
              refine ⟨1788180531114608648517767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19073925665222492250856181 1788180531114608648517767)
              ·
                refine ⟨2682270796671912972776651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788180531114608648517767 2682270796671912972776651)
                ·
                  refine ⟨4023406195007869459164977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682270796671912972776651 4023406195007869459164977)
                  ·
                    refine ⟨3017554646255902094373733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4023406195007869459164977 3017554646255902094373733)
                    ·
                      refine ⟨565791496172981642695075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3017554646255902094373733 565791496172981642695075)
                      ·
                        rfl

theorem cell23_1101875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 1, 1, 2, 4].length) (baseStart_1101875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101875 prefixEnd_1101875 := by exact prefixLift 1101875
  have htrace : WordTrace (prefixWord ++ tailWord_1101875) baseStart_1101875 baseEnd_1101875 := by
    simpa [prefixWord, tailWord_1101875, baseEnd_1101875] using wordTrace_append hprefix tailTrace_1101875
  have hstable : (prefixWord ++ tailWord_1101875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101875).length < 2 ^ (prefixWord ++ tailWord_1101875).sum := by decide
  have hdescent : baseEnd_1101875 < baseStart_1101875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101895 : List Nat := [1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 3]
def baseStart_1101895 : Nat := 118140960795 + 1101895 * 2 ^ 59
def prefixEnd_1101895 : Nat := 4983230072969 + 3 ^ 40 * 1101895 * 2
def baseEnd_1101895 : Nat := 565801765786071564444983

theorem tailTrace_1101895 : CollatzResearch.WordTrace tailWord_1101895 prefixEnd_1101895 565801765786071564444983 := by
  unfold tailWord_1101895
  simp only [CollatzResearch.WordTrace]
  refine ⟨40189412343030078528643139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26792941562020052352428759 40189412343030078528643139)
  ·
    refine ⟨60284118514545117792964709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40189412343030078528643139 60284118514545117792964709)
    ·
      refine ⟨11303272221477209586180883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60284118514545117792964709 11303272221477209586180883)
      ·
        refine ⟨16954908332215814379271325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11303272221477209586180883 16954908332215814379271325)
        ·
          refine ⟨6358090624580930392226747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16954908332215814379271325 6358090624580930392226747)
          ·
            refine ⟨9537135936871395588340121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358090624580930392226747 9537135936871395588340121)
            ·
              refine ⟨7152851952653546691255091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9537135936871395588340121 7152851952653546691255091)
              ·
                refine ⟨10729277928980320036882637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7152851952653546691255091 10729277928980320036882637)
                ·
                  refine ⟨4023479223367620013830989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10729277928980320036882637 4023479223367620013830989)
                  ·
                    refine ⟨1508804708762857505186621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4023479223367620013830989 1508804708762857505186621)
                    ·
                      refine ⟨565801765786071564444983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1508804708762857505186621 565801765786071564444983)
                      ·
                        rfl

theorem cell23_1101895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 2, 1, 3, 3, 3].length) (baseStart_1101895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101895 prefixEnd_1101895 := by exact prefixLift 1101895
  have htrace : WordTrace (prefixWord ++ tailWord_1101895) baseStart_1101895 baseEnd_1101895 := by
    simpa [prefixWord, tailWord_1101895, baseEnd_1101895] using wordTrace_append hprefix tailTrace_1101895
  have hstable : (prefixWord ++ tailWord_1101895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101895).length < 2 ^ (prefixWord ++ tailWord_1101895).sum := by decide
  have hdescent : baseEnd_1101895 < baseStart_1101895 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101898 : List Nat := [3, 1, 2, 1, 1, 2, 1, 2, 1, 9]
def baseStart_1101898 : Nat := 118140960795 + 1101898 * 2 ^ 59
def prefixEnd_1101898 : Nat := 4983230072969 + 3 ^ 40 * 1101898 * 2
def baseEnd_1101898 : Nat := 188601102076011684235823

theorem tailTrace_1101898 : CollatzResearch.WordTrace tailWord_1101898 prefixEnd_1101898 188601102076011684235823 := by
  unfold tailWord_1101898
  simp only [CollatzResearch.WordTrace]
  refine ⟨10047380440504802510250587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26793014508012806694001565 10047380440504802510250587)
  ·
    refine ⟨15071070660757203765375881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10047380440504802510250587 15071070660757203765375881)
    ·
      refine ⟨11303302995567902824031911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15071070660757203765375881 11303302995567902824031911)
      ·
        refine ⟨16954954493351854236047867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11303302995567902824031911 16954954493351854236047867)
        ·
          refine ⟨25432431740027781354071801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16954954493351854236047867 25432431740027781354071801)
          ·
            refine ⟨19074323805020836015553851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25432431740027781354071801 19074323805020836015553851)
            ·
              refine ⟨28611485707531254023330777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19074323805020836015553851 28611485707531254023330777)
              ·
                refine ⟨21458614280648440517498083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28611485707531254023330777 21458614280648440517498083)
                ·
                  refine ⟨32187921420972660776247125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21458614280648440517498083 32187921420972660776247125)
                  ·
                    refine ⟨188601102076011684235823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32187921420972660776247125 188601102076011684235823)
                    ·
                      rfl

theorem cell23_1101898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 2, 1, 9].length) (baseStart_1101898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101898 prefixEnd_1101898 := by exact prefixLift 1101898
  have htrace : WordTrace (prefixWord ++ tailWord_1101898) baseStart_1101898 baseEnd_1101898 := by
    simpa [prefixWord, tailWord_1101898, baseEnd_1101898] using wordTrace_append hprefix tailTrace_1101898
  have hstable : (prefixWord ++ tailWord_1101898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101898).length < 2 ^ (prefixWord ++ tailWord_1101898).sum := by decide
  have hdescent : baseEnd_1101898 < baseStart_1101898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101912 : List Nat := [2, 1, 2, 2, 1, 4, 2, 1, 4, 1, 3]
def baseStart_1101912 : Nat := 118140960795 + 1101912 * 2 ^ 59
def prefixEnd_1101912 : Nat := 4983230072969 + 3 ^ 40 * 1101912 * 2
def baseEnd_1101912 : Nat := 565810494957197997932405

theorem tailTrace_1101912 : CollatzResearch.WordTrace tailWord_1101912 prefixEnd_1101912 565810494957197997932405 := by
  unfold tailWord_1101912
  simp only [CollatzResearch.WordTrace]
  refine ⟨20095016191984245216005995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26793354922645660288007993 20095016191984245216005995)
  ·
    refine ⟨30142524287976367824008993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20095016191984245216005995 30142524287976367824008993)
    ·
      refine ⟨22606893215982275868006745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30142524287976367824008993 22606893215982275868006745)
      ·
        refine ⟨16955169911986706901005059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22606893215982275868006745 16955169911986706901005059)
        ·
          refine ⟨25432754867980060351507589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16955169911986706901005059 25432754867980060351507589)
          ·
            refine ⟨4768641537746261315907673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25432754867980060351507589 4768641537746261315907673)
            ·
              refine ⟨3576481153309695986930755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4768641537746261315907673 3576481153309695986930755)
              ·
                refine ⟨5364721729964543980396133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576481153309695986930755 5364721729964543980396133)
                ·
                  refine ⟨1005885324368351996324275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5364721729964543980396133 1005885324368351996324275)
                  ·
                    refine ⟨1508827986552527994486413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1005885324368351996324275 1508827986552527994486413)
                    ·
                      refine ⟨565810494957197997932405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1508827986552527994486413 565810494957197997932405)
                      ·
                        rfl

theorem cell23_1101912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 1, 4, 1, 3].length) (baseStart_1101912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101912 prefixEnd_1101912 := by exact prefixLift 1101912
  have htrace : WordTrace (prefixWord ++ tailWord_1101912) baseStart_1101912 baseEnd_1101912 := by
    simpa [prefixWord, tailWord_1101912, baseEnd_1101912] using wordTrace_append hprefix tailTrace_1101912
  have hstable : (prefixWord ++ tailWord_1101912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101912).length < 2 ^ (prefixWord ++ tailWord_1101912).sum := by decide
  have hdescent : baseEnd_1101912 < baseStart_1101912 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101955 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5]
def baseStart_1101955 : Nat := 118140960795 + 1101955 * 2 ^ 59
def prefixEnd_1101955 : Nat := 4983230072969 + 3 ^ 40 * 1101955 * 2
def baseEnd_1101955 : Nat := 565832574625341329694707

theorem tailTrace_1101955 : CollatzResearch.WordTrace tailWord_1101955 prefixEnd_1101955 565832574625341329694707 := by
  unfold tailWord_1101955
  simp only [CollatzResearch.WordTrace]
  refine ⟨40191600722812708775827319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26794400481875139183884879 40191600722812708775827319)
  ·
    refine ⟨60287401084219063163740979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40191600722812708775827319 60287401084219063163740979)
    ·
      refine ⟨90431101626328594745611469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60287401084219063163740979 90431101626328594745611469)
      ·
        refine ⟨33911663109873223029604301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90431101626328594745611469 33911663109873223029604301)
        ·
          refine ⟨12716873666202458636101613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33911663109873223029604301 12716873666202458636101613)
          ·
            refine ⟨4768827624825921988538105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12716873666202458636101613 4768827624825921988538105)
            ·
              refine ⟨3576620718619441491403579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4768827624825921988538105 3576620718619441491403579)
              ·
                refine ⟨5364931077929162237105369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3576620718619441491403579 5364931077929162237105369)
                ·
                  refine ⟨4023698308446871677829027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5364931077929162237105369 4023698308446871677829027)
                  ·
                    refine ⟨6035547462670307516743541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4023698308446871677829027 6035547462670307516743541)
                    ·
                      refine ⟨565832574625341329694707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6035547462670307516743541 565832574625341329694707)
                      ·
                        rfl

theorem cell23_1101955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 2, 1, 5].length) (baseStart_1101955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101955 prefixEnd_1101955 := by exact prefixLift 1101955
  have htrace : WordTrace (prefixWord ++ tailWord_1101955) baseStart_1101955 baseEnd_1101955 := by
    simpa [prefixWord, tailWord_1101955, baseEnd_1101955] using wordTrace_append hprefix tailTrace_1101955
  have hstable : (prefixWord ++ tailWord_1101955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101955).length < 2 ^ (prefixWord ++ tailWord_1101955).sum := by decide
  have hdescent : baseEnd_1101955 < baseStart_1101955 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101956 : List Nat := [2, 3, 2, 1, 2, 1, 5, 1, 1, 3, 2]
def baseStart_1101956 : Nat := 118140960795 + 1101956 * 2 ^ 59
def prefixEnd_1101956 : Nat := 4983230072969 + 3 ^ 40 * 1101956 * 2
def baseEnd_1101956 : Nat := 565833088105995825782203

theorem tailTrace_1101956 : CollatzResearch.WordTrace tailWord_1101956 prefixEnd_1101956 565833088105995825782203 := by
  unfold tailWord_1101956
  simp only [CollatzResearch.WordTrace]
  refine ⟨20095818597904542973306861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26794424797206057297742481 20095818597904542973306861)
  ·
    refine ⟨7535931974214203614990073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20095818597904542973306861 7535931974214203614990073)
    ·
      refine ⟨5651948980660652711242555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7535931974214203614990073 5651948980660652711242555)
      ·
        refine ⟨8477923470990979066863833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5651948980660652711242555 8477923470990979066863833)
        ·
          refine ⟨6358442603243234300147875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8477923470990979066863833 6358442603243234300147875)
          ·
            refine ⟨9537663904864851450221813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6358442603243234300147875 9537663904864851450221813)
            ·
              refine ⟨894155991081079823458295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9537663904864851450221813 894155991081079823458295)
              ·
                refine ⟨1341233986621619735187443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894155991081079823458295 1341233986621619735187443)
                ·
                  refine ⟨2011850979932429602781165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341233986621619735187443 2011850979932429602781165)
                  ·
                    refine ⟨754444117474661101042937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2011850979932429602781165 754444117474661101042937)
                    ·
                      refine ⟨565833088105995825782203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754444117474661101042937 565833088105995825782203)
                      ·
                        rfl

theorem cell23_1101956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 5, 1, 1, 3, 2].length) (baseStart_1101956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101956 prefixEnd_1101956 := by exact prefixLift 1101956
  have htrace : WordTrace (prefixWord ++ tailWord_1101956) baseStart_1101956 baseEnd_1101956 := by
    simpa [prefixWord, tailWord_1101956, baseEnd_1101956] using wordTrace_append hprefix tailTrace_1101956
  have hstable : (prefixWord ++ tailWord_1101956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101956).length < 2 ^ (prefixWord ++ tailWord_1101956).sum := by decide
  have hdescent : baseEnd_1101956 < baseStart_1101956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1101986 : List Nat := [3, 3, 1, 3, 1, 2, 2, 1, 1, 4, 2]
def baseStart_1101986 : Nat := 118140960795 + 1101986 * 2 ^ 59
def prefixEnd_1101986 : Nat := 4983230072969 + 3 ^ 40 * 1101986 * 2
def baseEnd_1101986 : Nat := 565848492525630708407065

theorem tailTrace_1101986 : CollatzResearch.WordTrace tailWord_1101986 prefixEnd_1101986 565848492525630708407065 := by
  unfold tailWord_1101986
  simp only [CollatzResearch.WordTrace]
  refine ⟨10048182846425100267551453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26795154257133600713470541 10048182846425100267551453)
  ·
    refine ⟨3768068567409412600331795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10048182846425100267551453 3768068567409412600331795)
    ·
      refine ⟨5652102851114118900497693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3768068567409412600331795 5652102851114118900497693)
      ·
        refine ⟨2119538569167794587686635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5652102851114118900497693 2119538569167794587686635)
        ·
          refine ⟨3179307853751691881529953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2119538569167794587686635 3179307853751691881529953)
          ·
            refine ⟨2384480890313768911147465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3179307853751691881529953 2384480890313768911147465)
            ·
              refine ⟨1788360667735326683360599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2384480890313768911147465 1788360667735326683360599)
              ·
                refine ⟨2682541001602990025040899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788360667735326683360599 2682541001602990025040899)
                ·
                  refine ⟨4023811502404485037561349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682541001602990025040899 4023811502404485037561349)
                  ·
                    refine ⟨754464656700840944542753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4023811502404485037561349 754464656700840944542753)
                    ·
                      refine ⟨565848492525630708407065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754464656700840944542753 565848492525630708407065)
                      ·
                        rfl

theorem cell23_1101986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_1101986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1101986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1101986 prefixEnd_1101986 := by exact prefixLift 1101986
  have htrace : WordTrace (prefixWord ++ tailWord_1101986) baseStart_1101986 baseEnd_1101986 := by
    simpa [prefixWord, tailWord_1101986, baseEnd_1101986] using wordTrace_append hprefix tailTrace_1101986
  have hstable : (prefixWord ++ tailWord_1101986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1101986).length < 2 ^ (prefixWord ++ tailWord_1101986).sum := by decide
  have hdescent : baseEnd_1101986 < baseStart_1101986 := by decide
  rcases family_descends (prefixWord ++ tailWord_1101986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102065 : List Nat := [1, 2, 2, 2, 2, 1, 3, 2, 8]
def baseStart_1102065 : Nat := 118140960795 + 1102065 * 2 ^ 59
def prefixEnd_1102065 : Nat := 4983230072969 + 3 ^ 40 * 1102065 * 2
def baseEnd_1102065 : Nat := 62876561944148433257689

theorem tailTrace_1102065 : CollatzResearch.WordTrace tailWord_1102065 prefixEnd_1102065 62876561944148433257689 := by
  unfold tailWord_1102065
  simp only [CollatzResearch.WordTrace]
  refine ⟨40195612752414197562331649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26797075168276131708221099 40195612752414197562331649)
  ·
    refine ⟨30146709564310648171748737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40195612752414197562331649 30146709564310648171748737)
    ·
      refine ⟨22610032173232986128811553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30146709564310648171748737 22610032173232986128811553)
      ·
        refine ⟨16957524129924739596608665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22610032173232986128811553 16957524129924739596608665)
        ·
          refine ⟨12718143097443554697456499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16957524129924739596608665 12718143097443554697456499)
          ·
            refine ⟨19077214646165332046184749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12718143097443554697456499 19077214646165332046184749)
            ·
              refine ⟨7153955492311999517319281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19077214646165332046184749 7153955492311999517319281)
              ·
                refine ⟨5365466619233999637989461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7153955492311999517319281 5365466619233999637989461)
                ·
                  refine ⟨62876561944148433257689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5365466619233999637989461 62876561944148433257689)
                  ·
                    rfl

theorem cell23_1102065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 3, 2, 8].length) (baseStart_1102065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102065 prefixEnd_1102065 := by exact prefixLift 1102065
  have htrace : WordTrace (prefixWord ++ tailWord_1102065) baseStart_1102065 baseEnd_1102065 := by
    simpa [prefixWord, tailWord_1102065, baseEnd_1102065] using wordTrace_append hprefix tailTrace_1102065
  have hstable : (prefixWord ++ tailWord_1102065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102065).length < 2 ^ (prefixWord ++ tailWord_1102065).sum := by decide
  have hdescent : baseEnd_1102065 < baseStart_1102065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102085 : List Nat := [1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 6]
def baseStart_1102085 : Nat := 118140960795 + 1102085 * 2 ^ 59
def prefixEnd_1102085 : Nat := 4983230072969 + 3 ^ 40 * 1102085 * 2
def baseEnd_1102085 : Nat := 565899327110425821069109

theorem tailTrace_1102085 : CollatzResearch.WordTrace tailWord_1102085 prefixEnd_1102085 565899327110425821069109 := by
  unfold tailWord_1102085
  simp only [CollatzResearch.WordTrace]
  refine ⟨40196342212341740978059709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26797561474894493985373139 40196342212341740978059709)
  ·
    refine ⟨15073628329628152866772391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40196342212341740978059709 15073628329628152866772391)
    ·
      refine ⟨22610442494442229300158587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15073628329628152866772391 22610442494442229300158587)
      ·
        refine ⟨33915663741663343950237881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22610442494442229300158587 33915663741663343950237881)
        ·
          refine ⟨25436747806247507962678411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33915663741663343950237881 25436747806247507962678411)
          ·
            refine ⟨38155121709371261944017617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25436747806247507962678411 38155121709371261944017617)
            ·
              refine ⟨28616341282028446458013213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38155121709371261944017617 28616341282028446458013213)
              ·
                refine ⟨10731127980760667421754955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28616341282028446458013213 10731127980760667421754955)
                ·
                  refine ⟨16096691971141001132632433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10731127980760667421754955 16096691971141001132632433)
                  ·
                    refine ⟨12072518978355750849474325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16096691971141001132632433 12072518978355750849474325)
                    ·
                      refine ⟨565899327110425821069109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12072518978355750849474325 565899327110425821069109)
                      ·
                        rfl

theorem cell23_1102085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 3, 1, 2, 6].length) (baseStart_1102085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102085 prefixEnd_1102085 := by exact prefixLift 1102085
  have htrace : WordTrace (prefixWord ++ tailWord_1102085) baseStart_1102085 baseEnd_1102085 := by
    simpa [prefixWord, tailWord_1102085, baseEnd_1102085] using wordTrace_append hprefix tailTrace_1102085
  have hstable : (prefixWord ++ tailWord_1102085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102085).length < 2 ^ (prefixWord ++ tailWord_1102085).sum := by decide
  have hdescent : baseEnd_1102085 < baseStart_1102085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102152 : List Nat := [2, 1, 3, 1, 1, 2, 2, 4, 1, 1, 5]
def baseStart_1102152 : Nat := 118140960795 + 1102152 * 2 ^ 59
def prefixEnd_1102152 : Nat := 4983230072969 + 3 ^ 40 * 1102152 * 2
def baseEnd_1102152 : Nat := 565933730314277058931301

theorem tailTrace_1102152 : CollatzResearch.WordTrace tailWord_1102152 prefixEnd_1102152 565933730314277058931301 := by
  unfold tailWord_1102152
  simp only [CollatzResearch.WordTrace]
  refine ⟨20099392951549505710374355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26799190602066007613832473 20099392951549505710374355)
  ·
    refine ⟨30149089427324258565561533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20099392951549505710374355 30149089427324258565561533)
    ·
      refine ⟨11305908535246596962085575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30149089427324258565561533 11305908535246596962085575)
      ·
        refine ⟨16958862802869895443128363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11305908535246596962085575 16958862802869895443128363)
        ·
          refine ⟨25438294204304843164692545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16958862802869895443128363 25438294204304843164692545)
          ·
            refine ⟨19078720653228632373519409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25438294204304843164692545 19078720653228632373519409)
            ·
              refine ⟨14309040489921474280139557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19078720653228632373519409 14309040489921474280139557)
              ·
                refine ⟨2682945091860276427526167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14309040489921474280139557 2682945091860276427526167)
                ·
                  refine ⟨4024417637790414641289251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2682945091860276427526167 4024417637790414641289251)
                  ·
                    refine ⟨6036626456685621961933877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4024417637790414641289251 6036626456685621961933877)
                    ·
                      refine ⟨565933730314277058931301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6036626456685621961933877 565933730314277058931301)
                      ·
                        rfl

theorem cell23_1102152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 2, 4, 1, 1, 5].length) (baseStart_1102152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102152 prefixEnd_1102152 := by exact prefixLift 1102152
  have htrace : WordTrace (prefixWord ++ tailWord_1102152) baseStart_1102152 baseEnd_1102152 := by
    simpa [prefixWord, tailWord_1102152, baseEnd_1102152] using wordTrace_append hprefix tailTrace_1102152
  have hstable : (prefixWord ++ tailWord_1102152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102152).length < 2 ^ (prefixWord ++ tailWord_1102152).sum := by decide
  have hdescent : baseEnd_1102152 < baseStart_1102152 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102155 : List Nat := [1, 1, 1, 1, 3, 1, 1, 14]
def baseStart_1102155 : Nat := 118140960795 + 1102155 * 2 ^ 59
def prefixEnd_1102155 : Nat := 4983230072969 + 3 ^ 40 * 1102155 * 2
def baseEnd_1102155 : Nat := 20960565583564464710881

theorem tailTrace_1102155 : CollatzResearch.WordTrace tailWord_1102155 prefixEnd_1102155 20960565583564464710881 := by
  unfold tailWord_1102155
  simp only [CollatzResearch.WordTrace]
  refine ⟨40198895322088142933107919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26799263548058761955405279 40198895322088142933107919)
  ·
    refine ⟨60298342983132214399661879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40198895322088142933107919 60298342983132214399661879)
    ·
      refine ⟨90447514474698321599492819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60298342983132214399661879 90447514474698321599492819)
      ·
        refine ⟨135671271712047482399239229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90447514474698321599492819 135671271712047482399239229)
        ·
          refine ⟨50876726892017805899714711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135671271712047482399239229 50876726892017805899714711)
          ·
            refine ⟨76315090338026708849572067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50876726892017805899714711 76315090338026708849572067)
            ·
              refine ⟨114472635507040063274358101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76315090338026708849572067 114472635507040063274358101)
              ·
                refine ⟨20960565583564464710881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 114472635507040063274358101 20960565583564464710881)
                ·
                  rfl

theorem cell23_1102155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 14].length) (baseStart_1102155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102155 prefixEnd_1102155 := by exact prefixLift 1102155
  have htrace : WordTrace (prefixWord ++ tailWord_1102155) baseStart_1102155 baseEnd_1102155 := by
    simpa [prefixWord, tailWord_1102155, baseEnd_1102155] using wordTrace_append hprefix tailTrace_1102155
  have hstable : (prefixWord ++ tailWord_1102155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102155).length < 2 ^ (prefixWord ++ tailWord_1102155).sum := by decide
  have hdescent : baseEnd_1102155 < baseStart_1102155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102162 : List Nat := [3, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6]
def baseStart_1102162 : Nat := 118140960795 + 1102162 * 2 ^ 59
def prefixEnd_1102162 : Nat := 4983230072969 + 3 ^ 40 * 1102162 * 2
def baseEnd_1102162 : Nat := 565938865120822019806255

theorem tailTrace_1102162 : CollatzResearch.WordTrace tailWord_1102162 prefixEnd_1102162 565938865120822019806255 := by
  unfold tailWord_1102162
  simp only [CollatzResearch.WordTrace]
  refine ⟨10049787658265695782153185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26799433755375188752408493 10049787658265695782153185)
  ·
    refine ⟨7537340743699271836614889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10049787658265695782153185 7537340743699271836614889)
    ·
      refine ⟨5653005557774453877461167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7537340743699271836614889 5653005557774453877461167)
      ·
        refine ⟨8479508336661680816191751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5653005557774453877461167 8479508336661680816191751)
        ·
          refine ⟨12719262504992521224287627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8479508336661680816191751 12719262504992521224287627)
          ·
            refine ⟨19078893757488781836431441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12719262504992521224287627 19078893757488781836431441)
            ·
              refine ⟨14309170318116586377323581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19078893757488781836431441 14309170318116586377323581)
              ·
                refine ⟨5365938869293719891496343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14309170318116586377323581 5365938869293719891496343)
                ·
                  refine ⟨8048908303940579837244515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5365938869293719891496343 8048908303940579837244515)
                  ·
                    refine ⟨12073362455910869755866773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8048908303940579837244515 12073362455910869755866773)
                    ·
                      refine ⟨565938865120822019806255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12073362455910869755866773 565938865120822019806255)
                      ·
                        rfl

theorem cell23_1102162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 2, 3, 1, 1, 6].length) (baseStart_1102162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102162 prefixEnd_1102162 := by exact prefixLift 1102162
  have htrace : WordTrace (prefixWord ++ tailWord_1102162) baseStart_1102162 baseEnd_1102162 := by
    simpa [prefixWord, tailWord_1102162, baseEnd_1102162] using wordTrace_append hprefix tailTrace_1102162
  have hstable : (prefixWord ++ tailWord_1102162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102162).length < 2 ^ (prefixWord ++ tailWord_1102162).sum := by decide
  have hdescent : baseEnd_1102162 < baseStart_1102162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102169 : List Nat := [1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 3]
def baseStart_1102169 : Nat := 118140960795 + 1102169 * 2 ^ 59
def prefixEnd_1102169 : Nat := 4983230072969 + 3 ^ 40 * 1102169 * 2
def baseEnd_1102169 : Nat := 565942459485403492418723

theorem tailTrace_1102169 : CollatzResearch.WordTrace tailWord_1102169 prefixEnd_1102169 565942459485403492418723 := by
  unfold tailWord_1102169
  simp only [CollatzResearch.WordTrace]
  refine ⟨40199405944037423324117561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26799603962691615549411707 40199405944037423324117561)
  ·
    refine ⟨30149554458028067493088171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40199405944037423324117561 30149554458028067493088171)
    ·
      refine ⟨45224331687042101239632257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30149554458028067493088171 45224331687042101239632257)
      ·
        refine ⟨33918248765281575929724193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45224331687042101239632257 33918248765281575929724193)
        ·
          refine ⟨25438686573961181947293145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33918248765281575929724193 25438686573961181947293145)
          ·
            refine ⟨19079014930470886460469859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25438686573961181947293145 19079014930470886460469859)
            ·
              refine ⟨28618522395706329690704789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19079014930470886460469859 28618522395706329690704789)
              ·
                refine ⟨1341493237298734204251787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28618522395706329690704789 1341493237298734204251787)
                ·
                  refine ⟨2012239855948101306377681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341493237298734204251787 2012239855948101306377681)
                  ·
                    refine ⟨1509179891961075979783261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2012239855948101306377681 1509179891961075979783261)
                    ·
                      refine ⟨565942459485403492418723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1509179891961075979783261 565942459485403492418723)
                      ·
                        rfl

theorem cell23_1102169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 6, 1, 2, 3].length) (baseStart_1102169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102169 prefixEnd_1102169 := by exact prefixLift 1102169
  have htrace : WordTrace (prefixWord ++ tailWord_1102169) baseStart_1102169 baseEnd_1102169 := by
    simpa [prefixWord, tailWord_1102169, baseEnd_1102169] using wordTrace_append hprefix tailTrace_1102169
  have hstable : (prefixWord ++ tailWord_1102169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102169).length < 2 ^ (prefixWord ++ tailWord_1102169).sum := by decide
  have hdescent : baseEnd_1102169 < baseStart_1102169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102183 : List Nat := [1, 1, 5, 1, 3, 3, 2, 1, 1, 1, 4]
def baseStart_1102183 : Nat := 118140960795 + 1102183 * 2 ^ 59
def prefixEnd_1102183 : Nat := 4983230072969 + 3 ^ 40 * 1102183 * 2
def baseEnd_1102183 : Nat := 565949648214566437643659

theorem tailTrace_1102183 : CollatzResearch.WordTrace tailWord_1102183 prefixEnd_1102183 565949648214566437643659 := by
  unfold tailWord_1102183
  simp only [CollatzResearch.WordTrace]
  refine ⟨40199916565986703715127203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26799944377324469143418135 40199916565986703715127203)
  ·
    refine ⟨60299874848980055572690805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40199916565986703715127203 60299874848980055572690805)
    ·
      refine ⟨5653113267091880209939763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 60299874848980055572690805 5653113267091880209939763)
      ·
        refine ⟨8479669900637820314909645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5653113267091880209939763 8479669900637820314909645)
        ·
          refine ⟨3179876212739182618091117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8479669900637820314909645 3179876212739182618091117)
          ·
            refine ⟨1192453579777193481784169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3179876212739182618091117 1192453579777193481784169)
            ·
              refine ⟨894340184832895111338127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1192453579777193481784169 894340184832895111338127)
              ·
                refine ⟨1341510277249342667007191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894340184832895111338127 1341510277249342667007191)
                ·
                  refine ⟨2012265415874014000510787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341510277249342667007191 2012265415874014000510787)
                  ·
                    refine ⟨3018398123811021000766181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2012265415874014000510787 3018398123811021000766181)
                    ·
                      refine ⟨565949648214566437643659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3018398123811021000766181 565949648214566437643659)
                      ·
                        rfl

theorem cell23_1102183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 2, 1, 1, 1, 4].length) (baseStart_1102183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102183 prefixEnd_1102183 := by exact prefixLift 1102183
  have htrace : WordTrace (prefixWord ++ tailWord_1102183) baseStart_1102183 baseEnd_1102183 := by
    simpa [prefixWord, tailWord_1102183, baseEnd_1102183] using wordTrace_append hprefix tailTrace_1102183
  have hstable : (prefixWord ++ tailWord_1102183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102183).length < 2 ^ (prefixWord ++ tailWord_1102183).sum := by decide
  have hdescent : baseEnd_1102183 < baseStart_1102183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102210 : List Nat := [3, 4, 2, 1, 3, 1, 1, 1, 1, 6]
def baseStart_1102210 : Nat := 118140960795 + 1102210 * 2 ^ 59
def prefixEnd_1102210 : Nat := 4983230072969 + 3 ^ 40 * 1102210 * 2
def baseEnd_1102210 : Nat := 188654504064079277335345

theorem tailTrace_1102210 : CollatzResearch.WordTrace tailWord_1102210 prefixEnd_1102210 188654504064079277335345 := by
  unfold tailWord_1102210
  simp only [CollatzResearch.WordTrace]
  refine ⟨10050225334222221831590021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26800600891259258217573389 10050225334222221831590021)
  ·
    refine ⟨1884417250166666593423129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10050225334222221831590021 1884417250166666593423129)
    ·
      refine ⟨1413312937624999945067347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1884417250166666593423129 1413312937624999945067347)
      ·
        refine ⟨2119969406437499917601021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413312937624999945067347 2119969406437499917601021)
        ·
          refine ⟨794988527414062469100383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2119969406437499917601021 794988527414062469100383)
          ·
            refine ⟨1192482791121093703650575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 794988527414062469100383 1192482791121093703650575)
            ·
              refine ⟨1788724186681640555475863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192482791121093703650575 1788724186681640555475863)
              ·
                refine ⟨2683086280022460833213795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788724186681640555475863 2683086280022460833213795)
                ·
                  refine ⟨4024629420033691249820693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683086280022460833213795 4024629420033691249820693)
                  ·
                    refine ⟨188654504064079277335345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4024629420033691249820693 188654504064079277335345)
                    ·
                      rfl

theorem cell23_1102210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_1102210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102210 prefixEnd_1102210 := by exact prefixLift 1102210
  have htrace : WordTrace (prefixWord ++ tailWord_1102210) baseStart_1102210 baseEnd_1102210 := by
    simpa [prefixWord, tailWord_1102210, baseEnd_1102210] using wordTrace_append hprefix tailTrace_1102210
  have hstable : (prefixWord ++ tailWord_1102210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102210).length < 2 ^ (prefixWord ++ tailWord_1102210).sum := by decide
  have hdescent : baseEnd_1102210 < baseStart_1102210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102290 : List Nat := [3, 2, 2, 4, 1, 1, 1, 2, 1, 4, 2]
def baseStart_1102290 : Nat := 118140960795 + 1102290 * 2 ^ 59
def prefixEnd_1102290 : Nat := 4983230072969 + 3 ^ 40 * 1102290 * 2
def baseEnd_1102290 : Nat := 566004590644597519005667

theorem tailTrace_1102290 : CollatzResearch.WordTrace tailWord_1102290 prefixEnd_1102290 566004590644597519005667 := by
  unfold tailWord_1102290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10050954794149765247318081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26802546117732707326181549 10050954794149765247318081)
  ·
    refine ⟨7538216095612323935488561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10050954794149765247318081 7538216095612323935488561)
    ·
      refine ⟨5653662071709242951616421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7538216095612323935488561 5653662071709242951616421)
      ·
        refine ⟨1060061638445483053428079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5653662071709242951616421 1060061638445483053428079)
        ·
          refine ⟨1590092457668224580142119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060061638445483053428079 1590092457668224580142119)
          ·
            refine ⟨2385138686502336870213179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1590092457668224580142119 2385138686502336870213179)
            ·
              refine ⟨3577708029753505305319769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2385138686502336870213179 3577708029753505305319769)
              ·
                refine ⟨2683281022315128978989827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3577708029753505305319769 2683281022315128978989827)
                ·
                  refine ⟨4024921533472693468484741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2683281022315128978989827 4024921533472693468484741)
                  ·
                    refine ⟨754672787526130025340889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4024921533472693468484741 754672787526130025340889)
                    ·
                      refine ⟨566004590644597519005667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754672787526130025340889 566004590644597519005667)
                      ·
                        rfl

theorem cell23_1102290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 2, 1, 4, 2].length) (baseStart_1102290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102290 prefixEnd_1102290 := by exact prefixLift 1102290
  have htrace : WordTrace (prefixWord ++ tailWord_1102290) baseStart_1102290 baseEnd_1102290 := by
    simpa [prefixWord, tailWord_1102290, baseEnd_1102290] using wordTrace_append hprefix tailTrace_1102290
  have hstable : (prefixWord ++ tailWord_1102290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102290).length < 2 ^ (prefixWord ++ tailWord_1102290).sum := by decide
  have hdescent : baseEnd_1102290 < baseStart_1102290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102329 : List Nat := [1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 4]
def baseStart_1102329 : Nat := 118140960795 + 1102329 * 2 ^ 59
def prefixEnd_1102329 : Nat := 4983230072969 + 3 ^ 40 * 1102329 * 2
def baseEnd_1102329 : Nat := 566024616390122866417987

theorem tailTrace_1102329 : CollatzResearch.WordTrace tailWord_1102329 prefixEnd_1102329 566024616390122866417987 := by
  unfold tailWord_1102329
  simp only [CollatzResearch.WordTrace]
  refine ⟨40205241623457770649942041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26803494415638513766628027 40205241623457770649942041)
  ·
    refine ⟨30153931217593327987456531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40205241623457770649942041 30153931217593327987456531)
    ·
      refine ⟨45230896826389991981184797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30153931217593327987456531 45230896826389991981184797)
      ·
        refine ⟨16961586309896246992944299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45230896826389991981184797 16961586309896246992944299)
        ·
          refine ⟨25442379464844370489416449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16961586309896246992944299 25442379464844370489416449)
          ·
            refine ⟨19081784598633277867062337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25442379464844370489416449 19081784598633277867062337)
            ·
              refine ⟨14311338448974958400296753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19081784598633277867062337 14311338448974958400296753)
              ·
                refine ⟨10733503836731218800222565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14311338448974958400296753 10733503836731218800222565)
                ·
                  refine ⟨2012531969387103525041731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10733503836731218800222565 2012531969387103525041731)
                  ·
                    refine ⟨3018797954080655287562597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2012531969387103525041731 3018797954080655287562597)
                    ·
                      refine ⟨566024616390122866417987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3018797954080655287562597 566024616390122866417987)
                      ·
                        rfl

theorem cell23_1102329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_1102329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102329 prefixEnd_1102329 := by exact prefixLift 1102329
  have htrace : WordTrace (prefixWord ++ tailWord_1102329) baseStart_1102329 baseEnd_1102329 := by
    simpa [prefixWord, tailWord_1102329, baseEnd_1102329] using wordTrace_append hprefix tailTrace_1102329
  have hstable : (prefixWord ++ tailWord_1102329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102329).length < 2 ^ (prefixWord ++ tailWord_1102329).sum := by decide
  have hdescent : baseEnd_1102329 < baseStart_1102329 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102343 : List Nat := [1, 1, 4, 3, 3, 2, 1, 1, 2, 5]
def baseStart_1102343 : Nat := 118140960795 + 1102343 * 2 ^ 59
def prefixEnd_1102343 : Nat := 4983230072969 + 3 ^ 40 * 1102343 * 2
def baseEnd_1102343 : Nat := 188677268373095270547641

theorem tailTrace_1102343 : CollatzResearch.WordTrace tailWord_1102343 prefixEnd_1102343 188677268373095270547641 := by
  unfold tailWord_1102343
  simp only [CollatzResearch.WordTrace]
  refine ⟨40205752245407051040951683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26803834830271367360634455 40205752245407051040951683)
  ·
    refine ⟨60308628368110576561427525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40205752245407051040951683 60308628368110576561427525)
    ·
      refine ⟨11307867819020733105267661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60308628368110576561427525 11307867819020733105267661)
      ·
        refine ⟨4240450432132774914475373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11307867819020733105267661 4240450432132774914475373)
        ·
          refine ⟨1590168912049790592928265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4240450432132774914475373 1590168912049790592928265)
          ·
            refine ⟨1192626684037342944696199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590168912049790592928265 1192626684037342944696199)
            ·
              refine ⟨1788940026056014417044299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192626684037342944696199 1788940026056014417044299)
              ·
                refine ⟨2683410039084021625566449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1788940026056014417044299 2683410039084021625566449)
                ·
                  refine ⟨2012557529313016219174837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2683410039084021625566449 2012557529313016219174837)
                  ·
                    refine ⟨188677268373095270547641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2012557529313016219174837 188677268373095270547641)
                    ·
                      rfl

theorem cell23_1102343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 1, 2, 5].length) (baseStart_1102343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102343 prefixEnd_1102343 := by exact prefixLift 1102343
  have htrace : WordTrace (prefixWord ++ tailWord_1102343) baseStart_1102343 baseEnd_1102343 := by
    simpa [prefixWord, tailWord_1102343, baseEnd_1102343] using wordTrace_append hprefix tailTrace_1102343
  have hstable : (prefixWord ++ tailWord_1102343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102343).length < 2 ^ (prefixWord ++ tailWord_1102343).sum := by decide
  have hdescent : baseEnd_1102343 < baseStart_1102343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102346 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2]
def baseStart_1102346 : Nat := 118140960795 + 1102346 * 2 ^ 59
def prefixEnd_1102346 : Nat := 4983230072969 + 3 ^ 40 * 1102346 * 2
def baseEnd_1102346 : Nat := 566033345561249299905409

theorem tailTrace_1102346 : CollatzResearch.WordTrace tailWord_1102346 prefixEnd_1102346 566033345561249299905409 := by
  unfold tailWord_1102346
  simp only [CollatzResearch.WordTrace]
  refine ⟨10051465416099045638327723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26803907776264121702207261 10051465416099045638327723)
  ·
    refine ⟨15077198124148568457491585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10051465416099045638327723 15077198124148568457491585)
    ·
      refine ⟨11307898593111426343118689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15077198124148568457491585 11307898593111426343118689)
      ·
        refine ⟨8480923944833569757339017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11307898593111426343118689 8480923944833569757339017)
        ·
          refine ⟨6360692958625177318004263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8480923944833569757339017 6360692958625177318004263)
          ·
            refine ⟨9541039437937765977006395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6360692958625177318004263 9541039437937765977006395)
            ·
              refine ⟨14311559156906648965509593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9541039437937765977006395 14311559156906648965509593)
              ·
                refine ⟨10733669367679986724132195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14311559156906648965509593 10733669367679986724132195)
                ·
                  refine ⟨16100504051519980086198293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10733669367679986724132195 16100504051519980086198293)
                  ·
                    refine ⟨754711127414999066540545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16100504051519980086198293 754711127414999066540545)
                    ·
                      refine ⟨566033345561249299905409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754711127414999066540545 566033345561249299905409)
                      ·
                        rfl

theorem cell23_1102346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 1, 6, 2].length) (baseStart_1102346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102346 prefixEnd_1102346 := by exact prefixLift 1102346
  have htrace : WordTrace (prefixWord ++ tailWord_1102346) baseStart_1102346 baseEnd_1102346 := by
    simpa [prefixWord, tailWord_1102346, baseEnd_1102346] using wordTrace_append hprefix tailTrace_1102346
  have hstable : (prefixWord ++ tailWord_1102346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102346).length < 2 ^ (prefixWord ++ tailWord_1102346).sum := by decide
  have hdescent : baseEnd_1102346 < baseStart_1102346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102369 : List Nat := [1, 2, 3, 2, 2, 1, 3, 1, 8]
def baseStart_1102369 : Nat := 118140960795 + 1102369 * 2 ^ 59
def prefixEnd_1102369 : Nat := 4983230072969 + 3 ^ 40 * 1102369 * 2
def baseEnd_1102369 : Nat := 62893906179589189990867

theorem tailTrace_1102369 : CollatzResearch.WordTrace tailWord_1102369 prefixEnd_1102369 62893906179589189990867 := by
  unfold tailWord_1102369
  simp only [CollatzResearch.WordTrace]
  refine ⟨40206700543312857481398161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26804467028875238320932107 40206700543312857481398161)
  ·
    refine ⟨30155025407484643111048621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40206700543312857481398161 30155025407484643111048621)
    ·
      refine ⟨11308134527806741166643233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30155025407484643111048621 11308134527806741166643233)
      ·
        refine ⟨8481100895855055874982425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11308134527806741166643233 8481100895855055874982425)
        ·
          refine ⟨6360825671891291906236819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8481100895855055874982425 6360825671891291906236819)
          ·
            refine ⟨9541238507836937859355229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6360825671891291906236819 9541238507836937859355229)
            ·
              refine ⟨3577964440438851697258211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9541238507836937859355229 3577964440438851697258211)
              ·
                refine ⟨5366946660658277545887317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3577964440438851697258211 5366946660658277545887317)
                ·
                  refine ⟨62893906179589189990867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5366946660658277545887317 62893906179589189990867)
                  ·
                    rfl

theorem cell23_1102369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 8].length) (baseStart_1102369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102369 prefixEnd_1102369 := by exact prefixLift 1102369
  have htrace : WordTrace (prefixWord ++ tailWord_1102369) baseStart_1102369 baseEnd_1102369 := by
    simpa [prefixWord, tailWord_1102369, baseEnd_1102369] using wordTrace_append hprefix tailTrace_1102369
  have hstable : (prefixWord ++ tailWord_1102369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102369).length < 2 ^ (prefixWord ++ tailWord_1102369).sum := by decide
  have hdescent : baseEnd_1102369 < baseStart_1102369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102373 : List Nat := [1, 3, 1, 2, 2, 1, 4, 4, 1, 4]
def baseStart_1102373 : Nat := 118140960795 + 1102373 * 2 ^ 59
def prefixEnd_1102373 : Nat := 4983230072969 + 3 ^ 40 * 1102373 * 2
def baseEnd_1102373 : Nat := 188682403179640231422595

theorem tailTrace_1102373 : CollatzResearch.WordTrace tailWord_1102373 prefixEnd_1102373 188682403179640231422595 := by
  unfold tailWord_1102373
  simp only [CollatzResearch.WordTrace]
  refine ⟨40206846435298366164543773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26804564290198910776362515 40206846435298366164543773)
  ·
    refine ⟨15077567413236887311703915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40206846435298366164543773 15077567413236887311703915)
    ·
      refine ⟨22616351119855330967555873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15077567413236887311703915 22616351119855330967555873)
      ·
        refine ⟨16962263339891498225666905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22616351119855330967555873 16962263339891498225666905)
        ·
          refine ⟨12721697504918623669250179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16962263339891498225666905 12721697504918623669250179)
          ·
            refine ⟨19082546257377935503875269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12721697504918623669250179 19082546257377935503875269)
            ·
              refine ⟨3577977423258362906976613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19082546257377935503875269 3577977423258362906976613)
              ·
                refine ⟨670870766860943045058115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3577977423258362906976613 670870766860943045058115)
                ·
                  refine ⟨1006306150291414567587173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670870766860943045058115 1006306150291414567587173)
                  ·
                    refine ⟨188682403179640231422595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1006306150291414567587173 188682403179640231422595)
                    ·
                      rfl

theorem cell23_1102373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 4, 1, 4].length) (baseStart_1102373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102373 prefixEnd_1102373 := by exact prefixLift 1102373
  have htrace : WordTrace (prefixWord ++ tailWord_1102373) baseStart_1102373 baseEnd_1102373 := by
    simpa [prefixWord, tailWord_1102373, baseEnd_1102373] using wordTrace_append hprefix tailTrace_1102373
  have hstable : (prefixWord ++ tailWord_1102373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102373).length < 2 ^ (prefixWord ++ tailWord_1102373).sum := by decide
  have hdescent : baseEnd_1102373 < baseStart_1102373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102389 : List Nat := [1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 6]
def baseStart_1102389 : Nat := 118140960795 + 1102389 * 2 ^ 59
def prefixEnd_1102389 : Nat := 4983230072969 + 3 ^ 40 * 1102389 * 2
def baseEnd_1102389 : Nat := 566055425229392631667711

theorem tailTrace_1102389 : CollatzResearch.WordTrace tailWord_1102389 prefixEnd_1102389 566055425229392631667711 := by
  unfold tailWord_1102389
  simp only [CollatzResearch.WordTrace]
  refine ⟨40207430003240400897126221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26804953335493600598084147 40207430003240400897126221)
  ·
    refine ⟨15077786251215150336422333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40207430003240400897126221 15077786251215150336422333)
    ·
      refine ⟨5654169844205681376158375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15077786251215150336422333 5654169844205681376158375)
      ·
        refine ⟨8481254766308522064237563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5654169844205681376158375 8481254766308522064237563)
        ·
          refine ⟨12721882149462783096356345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8481254766308522064237563 12721882149462783096356345)
          ·
            refine ⟨9541411612097087322267259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12721882149462783096356345 9541411612097087322267259)
            ·
              refine ⟨14312117418145630983400889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9541411612097087322267259 14312117418145630983400889)
              ·
                refine ⟨10734088063609223237550667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14312117418145630983400889 10734088063609223237550667)
                ·
                  refine ⟨16101132095413834856326001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10734088063609223237550667 16101132095413834856326001)
                  ·
                    refine ⟨12075849071560376142244501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16101132095413834856326001 12075849071560376142244501)
                    ·
                      refine ⟨566055425229392631667711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12075849071560376142244501 566055425229392631667711)
                      ·
                        rfl

theorem cell23_1102389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 2, 6].length) (baseStart_1102389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102389 prefixEnd_1102389 := by exact prefixLift 1102389
  have htrace : WordTrace (prefixWord ++ tailWord_1102389) baseStart_1102389 baseEnd_1102389 := by
    simpa [prefixWord, tailWord_1102389, baseEnd_1102389] using wordTrace_append hprefix tailTrace_1102389
  have hstable : (prefixWord ++ tailWord_1102389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102389).length < 2 ^ (prefixWord ++ tailWord_1102389).sum := by decide
  have hdescent : baseEnd_1102389 < baseStart_1102389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102423 : List Nat := [1, 1, 3, 2, 2, 2, 3, 2, 2, 3, 2]
def baseStart_1102423 : Nat := 118140960795 + 1102423 * 2 ^ 59
def prefixEnd_1102423 : Nat := 4983230072969 + 3 ^ 40 * 1102423 * 2
def baseEnd_1102423 : Nat := 566072883571645498642555

theorem tailTrace_1102423 : CollatzResearch.WordTrace tailWord_1102423 prefixEnd_1102423 566072883571645498642555 := by
  unfold tailWord_1102423
  simp only [CollatzResearch.WordTrace]
  refine ⟨40208670085117224703863923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26805780056744816469242615 40208670085117224703863923)
  ·
    refine ⟨60313005127675837055795885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40208670085117224703863923 60313005127675837055795885)
    ·
      refine ⟨22617376922878438895923457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60313005127675837055795885 22617376922878438895923457)
      ·
        refine ⟨16963032692158829171942593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22617376922878438895923457 16963032692158829171942593)
        ·
          refine ⟨12722274519119121878956945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16963032692158829171942593 12722274519119121878956945)
          ·
            refine ⟨9541705889339341409217709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12722274519119121878956945 9541705889339341409217709)
            ·
              refine ⟨3578139708502253028456641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9541705889339341409217709 3578139708502253028456641)
              ·
                refine ⟨2683604781376689771342481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3578139708502253028456641 2683604781376689771342481)
                ·
                  refine ⟨2012703586032517328506861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2683604781376689771342481 2012703586032517328506861)
                  ·
                    refine ⟨754763844762193998190073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2012703586032517328506861 754763844762193998190073)
                    ·
                      refine ⟨566072883571645498642555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754763844762193998190073 566072883571645498642555)
                      ·
                        rfl

theorem cell23_1102423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3, 2].length) (baseStart_1102423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102423 prefixEnd_1102423 := by exact prefixLift 1102423
  have htrace : WordTrace (prefixWord ++ tailWord_1102423) baseStart_1102423 baseEnd_1102423 := by
    simpa [prefixWord, tailWord_1102423, baseEnd_1102423] using wordTrace_append hprefix tailTrace_1102423
  have hstable : (prefixWord ++ tailWord_1102423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102423).length < 2 ^ (prefixWord ++ tailWord_1102423).sum := by decide
  have hdescent : baseEnd_1102423 < baseStart_1102423 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102436 : List Nat := [2, 3, 1, 1, 2, 2, 2, 2, 3, 1, 4]
def baseStart_1102436 : Nat := 118140960795 + 1102436 * 2 ^ 59
def prefixEnd_1102436 : Nat := 4983230072969 + 3 ^ 40 * 1102436 * 2
def baseEnd_1102436 : Nat := 566079558820153947779995

theorem tailTrace_1102436 : CollatzResearch.WordTrace tailWord_1102436 prefixEnd_1102436 566079558820153947779995 := by
  unfold tailWord_1102436
  simp only [CollatzResearch.WordTrace]
  refine ⟨20104572117035063962043581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26806096156046751949391441 20104572117035063962043581)
  ·
    refine ⟨7539214543888148985766343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20104572117035063962043581 7539214543888148985766343)
    ·
      refine ⟨11308821815832223478649515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7539214543888148985766343 11308821815832223478649515)
      ·
        refine ⟨16963232723748335217974273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11308821815832223478649515 16963232723748335217974273)
        ·
          refine ⟨12722424542811251413480705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16963232723748335217974273 12722424542811251413480705)
          ·
            refine ⟨9541818407108438560110529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12722424542811251413480705 9541818407108438560110529)
            ·
              refine ⟨7156363805331328920082897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9541818407108438560110529 7156363805331328920082897)
              ·
                refine ⟨5367272853998496690062173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7156363805331328920082897 5367272853998496690062173)
                ·
                  refine ⟨2012727320249436258773315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5367272853998496690062173 2012727320249436258773315)
                  ·
                    refine ⟨3019090980374154388159973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2012727320249436258773315 3019090980374154388159973)
                    ·
                      refine ⟨566079558820153947779995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3019090980374154388159973 566079558820153947779995)
                      ·
                        rfl

theorem cell23_1102436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 2, 2, 3, 1, 4].length) (baseStart_1102436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102436 prefixEnd_1102436 := by exact prefixLift 1102436
  have htrace : WordTrace (prefixWord ++ tailWord_1102436) baseStart_1102436 baseEnd_1102436 := by
    simpa [prefixWord, tailWord_1102436, baseEnd_1102436] using wordTrace_append hprefix tailTrace_1102436
  have hstable : (prefixWord ++ tailWord_1102436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102436).length < 2 ^ (prefixWord ++ tailWord_1102436).sum := by decide
  have hdescent : baseEnd_1102436 < baseStart_1102436 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102450 : List Nat := [3, 2, 1, 2, 4, 2, 1, 2, 1, 5]
def baseStart_1102450 : Nat := 118140960795 + 1102450 * 2 ^ 59
def prefixEnd_1102450 : Nat := 4983230072969 + 3 ^ 40 * 1102450 * 2
def baseEnd_1102450 : Nat := 188695582516438964334977

theorem tailTrace_1102450 : CollatzResearch.WordTrace tailWord_1102450 prefixEnd_1102450 188695582516438964334977 := by
  unfold tailWord_1102450
  simp only [CollatzResearch.WordTrace]
  refine ⟨10052413714004852078774201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26806436570679605543397869 10052413714004852078774201)
  ·
    refine ⟨7539310285503639059080651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10052413714004852078774201 7539310285503639059080651)
    ·
      refine ⟨11308965428255458588620977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7539310285503639059080651 11308965428255458588620977)
      ·
        refine ⟨8481724071191593941465733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11308965428255458588620977 8481724071191593941465733)
        ·
          refine ⟨1590323263348423864024825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8481724071191593941465733 1590323263348423864024825)
          ·
            refine ⟨1192742447511317898018619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1590323263348423864024825 1192742447511317898018619)
            ·
              refine ⟨1789113671266976847027929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1192742447511317898018619 1789113671266976847027929)
              ·
                refine ⟨1341835253450232635270947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789113671266976847027929 1341835253450232635270947)
                ·
                  refine ⟨2012752880175348952906421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1341835253450232635270947 2012752880175348952906421)
                  ·
                    refine ⟨188695582516438964334977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2012752880175348952906421 188695582516438964334977)
                    ·
                      rfl

theorem cell23_1102450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 2, 1, 2, 1, 5].length) (baseStart_1102450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102450 prefixEnd_1102450 := by exact prefixLift 1102450
  have htrace : WordTrace (prefixWord ++ tailWord_1102450) baseStart_1102450 baseEnd_1102450 := by
    simpa [prefixWord, tailWord_1102450, baseEnd_1102450] using wordTrace_append hprefix tailTrace_1102450
  have hstable : (prefixWord ++ tailWord_1102450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102450).length < 2 ^ (prefixWord ++ tailWord_1102450).sum := by decide
  have hdescent : baseEnd_1102450 < baseStart_1102450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102456 : List Nat := [2, 1, 2, 1, 1, 1, 2, 5, 3, 2, 3]
def baseStart_1102456 : Nat := 118140960795 + 1102456 * 2 ^ 59
def prefixEnd_1102456 : Nat := 4983230072969 + 3 ^ 40 * 1102456 * 2
def baseEnd_1102456 : Nat := 566089828433243869529903

theorem tailTrace_1102456 : CollatzResearch.WordTrace tailWord_1102456 prefixEnd_1102456 566089828433243869529903 := by
  unfold tailWord_1102456
  simp only [CollatzResearch.WordTrace]
  refine ⟨20104936846998835669907611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26806582462665114226543481 20104936846998835669907611)
  ·
    refine ⟨30157405270498253504861417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20104936846998835669907611 30157405270498253504861417)
    ·
      refine ⟨22618053952873690128646063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30157405270498253504861417 22618053952873690128646063)
      ·
        refine ⟨33927080929310535192969095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22618053952873690128646063 33927080929310535192969095)
        ·
          refine ⟨50890621393965802789453643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33927080929310535192969095 50890621393965802789453643)
          ·
            refine ⟨76335932090948704184180465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50890621393965802789453643 76335932090948704184180465)
            ·
              refine ⟨57251949068211528138135349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76335932090948704184180465 57251949068211528138135349)
              ·
                refine ⟨5367370225144830762950189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57251949068211528138135349 5367370225144830762950189)
                ·
                  refine ⟨2012763834429311536106321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5367370225144830762950189 2012763834429311536106321)
                  ·
                    refine ⟨1509572875821983652079741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2012763834429311536106321 1509572875821983652079741)
                    ·
                      refine ⟨566089828433243869529903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1509572875821983652079741 566089828433243869529903)
                      ·
                        rfl

theorem cell23_1102456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 5, 3, 2, 3].length) (baseStart_1102456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102456 prefixEnd_1102456 := by exact prefixLift 1102456
  have htrace : WordTrace (prefixWord ++ tailWord_1102456) baseStart_1102456 baseEnd_1102456 := by
    simpa [prefixWord, tailWord_1102456, baseEnd_1102456] using wordTrace_append hprefix tailTrace_1102456
  have hstable : (prefixWord ++ tailWord_1102456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102456).length < 2 ^ (prefixWord ++ tailWord_1102456).sum := by decide
  have hdescent : baseEnd_1102456 < baseStart_1102456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102487 : List Nat := [1, 1, 3, 3, 2, 1, 3, 4, 1, 2, 2]
def baseStart_1102487 : Nat := 118140960795 + 1102487 * 2 ^ 59
def prefixEnd_1102487 : Nat := 4983230072969 + 3 ^ 40 * 1102487 * 2
def baseEnd_1102487 : Nat := 566105746333533248242261

theorem tailTrace_1102487 : CollatzResearch.WordTrace tailWord_1102487 prefixEnd_1102487 566105746333533248242261 := by
  unfold tailWord_1102487
  simp only [CollatzResearch.WordTrace]
  refine ⟨40211004356885363634193715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26807336237923575756129143 40211004356885363634193715)
  ·
    refine ⟨60316506535328045451290573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40211004356885363634193715 60316506535328045451290573)
    ·
      refine ⟨22618689950748017044233965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60316506535328045451290573 22618689950748017044233965)
      ·
        refine ⟨8482008731530506391587737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22618689950748017044233965 8482008731530506391587737)
        ·
          refine ⟨6361506548647879793690803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8482008731530506391587737 6361506548647879793690803)
          ·
            refine ⟨9542259822971819690536205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6361506548647879793690803 9542259822971819690536205)
            ·
              refine ⟨3578347433614432383951077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9542259822971819690536205 3578347433614432383951077)
              ·
                refine ⟨670940143802706071990827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3578347433614432383951077 670940143802706071990827)
                ·
                  refine ⟨1006410215704059107986241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 670940143802706071990827 1006410215704059107986241)
                  ·
                    refine ⟨754807661778044330989681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1006410215704059107986241 754807661778044330989681)
                    ·
                      refine ⟨566105746333533248242261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754807661778044330989681 566105746333533248242261)
                      ·
                        rfl

theorem cell23_1102487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 3, 4, 1, 2, 2].length) (baseStart_1102487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102487 prefixEnd_1102487 := by exact prefixLift 1102487
  have htrace : WordTrace (prefixWord ++ tailWord_1102487) baseStart_1102487 baseEnd_1102487 := by
    simpa [prefixWord, tailWord_1102487, baseEnd_1102487] using wordTrace_append hprefix tailTrace_1102487
  have hstable : (prefixWord ++ tailWord_1102487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102487).length < 2 ^ (prefixWord ++ tailWord_1102487).sum := by decide
  have hdescent : baseEnd_1102487 < baseStart_1102487 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102489 : List Nat := [1, 2, 1, 2, 1, 2, 3, 1, 1, 9]
def baseStart_1102489 : Nat := 118140960795 + 1102489 * 2 ^ 59
def prefixEnd_1102489 : Nat := 4983230072969 + 3 ^ 40 * 1102489 * 2
def baseEnd_1102489 : Nat := 188702257764947413472417

theorem tailTrace_1102489 : CollatzResearch.WordTrace tailWord_1102489 prefixEnd_1102489 188702257764947413472417 := by
  unfold tailWord_1102489
  simp only [CollatzResearch.WordTrace]
  refine ⟨40211077302878117975766521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26807384868585411983844347 40211077302878117975766521)
  ·
    refine ⟨30158307977158588481824891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40211077302878117975766521 30158307977158588481824891)
    ·
      refine ⟨45237461965737882722737337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30158307977158588481824891 45237461965737882722737337)
      ·
        refine ⟨33928096474303412042053003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45237461965737882722737337 33928096474303412042053003)
        ·
          refine ⟨50892144711455118063079505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33928096474303412042053003 50892144711455118063079505)
          ·
            refine ⟨38169108533591338547309629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50892144711455118063079505 38169108533591338547309629)
            ·
              refine ⟨14313415700096751955241111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38169108533591338547309629 14313415700096751955241111)
              ·
                refine ⟨21470123550145127932861667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14313415700096751955241111 21470123550145127932861667)
                ·
                  refine ⟨32205185325217691899292501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21470123550145127932861667 32205185325217691899292501)
                  ·
                    refine ⟨188702257764947413472417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32205185325217691899292501 188702257764947413472417)
                    ·
                      rfl

theorem cell23_1102489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 9].length) (baseStart_1102489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102489 prefixEnd_1102489 := by exact prefixLift 1102489
  have htrace : WordTrace (prefixWord ++ tailWord_1102489) baseStart_1102489 baseEnd_1102489 := by
    simpa [prefixWord, tailWord_1102489, baseEnd_1102489] using wordTrace_append hprefix tailTrace_1102489
  have hstable : (prefixWord ++ tailWord_1102489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102489).length < 2 ^ (prefixWord ++ tailWord_1102489).sum := by decide
  have hdescent : baseEnd_1102489 < baseStart_1102489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102510 : List Nat := [4, 1, 4, 1, 1, 2, 3, 7]
def baseStart_1102510 : Nat := 118140960795 + 1102510 * 2 ^ 59
def prefixEnd_1102510 : Nat := 4983230072969 + 3 ^ 40 * 1102510 * 2
def baseEnd_1102510 : Nat := 20967316903280987342765

theorem tailTrace_1102510 : CollatzResearch.WordTrace tailWord_1102510 prefixEnd_1102510 20967316903280987342765 := by
  unfold tailWord_1102510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5026480404475254820285123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26807895490534692374853989 5026480404475254820285123)
  ·
    refine ⟨7539720606712882230427685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5026480404475254820285123 7539720606712882230427685)
    ·
      refine ⟨1413697613758665418205191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7539720606712882230427685 1413697613758665418205191)
      ·
        refine ⟨2120546420637998127307787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1413697613758665418205191 2120546420637998127307787)
        ·
          refine ⟨3180819630956997190961681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2120546420637998127307787 3180819630956997190961681)
          ·
            refine ⟨2385614723217747893221261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3180819630956997190961681 2385614723217747893221261)
            ·
              refine ⟨894605521206655459957973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2385614723217747893221261 894605521206655459957973)
              ·
                refine ⟨20967316903280987342765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 894605521206655459957973 20967316903280987342765)
                ·
                  rfl

theorem cell23_1102510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 2, 3, 7].length) (baseStart_1102510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102510 prefixEnd_1102510 := by exact prefixLift 1102510
  have htrace : WordTrace (prefixWord ++ tailWord_1102510) baseStart_1102510 baseEnd_1102510 := by
    simpa [prefixWord, tailWord_1102510, baseEnd_1102510] using wordTrace_append hprefix tailTrace_1102510
  have hstable : (prefixWord ++ tailWord_1102510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102510).length < 2 ^ (prefixWord ++ tailWord_1102510).sum := by decide
  have hdescent : baseEnd_1102510 < baseStart_1102510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102536 : List Nat := [2, 1, 3, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1102536 : Nat := 118140960795 + 1102536 * 2 ^ 59
def prefixEnd_1102536 : Nat := 4983230072969 + 3 ^ 40 * 1102536 * 2
def baseEnd_1102536 : Nat := 188710302295201185509845

theorem tailTrace_1102536 : CollatzResearch.WordTrace tailWord_1102536 prefixEnd_1102536 188710302295201185509845 := by
  unfold tailWord_1102536
  simp only [CollatzResearch.WordTrace]
  refine ⟨20106395766853922501363731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26808527689138563335151641 20106395766853922501363731)
  ·
    refine ⟨30159593650280883752045597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20106395766853922501363731 30159593650280883752045597)
    ·
      refine ⟨11309847618855331407017099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30159593650280883752045597 11309847618855331407017099)
      ·
        refine ⟨16964771428282997110525649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11309847618855331407017099 16964771428282997110525649)
        ·
          refine ⟨12723578571212247832894237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16964771428282997110525649 12723578571212247832894237)
          ·
            refine ⟨4771341964204592937335339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12723578571212247832894237 4771341964204592937335339)
            ·
              refine ⟨7157012946306889406003009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4771341964204592937335339 7157012946306889406003009)
              ·
                refine ⟨5367759709730167054502257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7157012946306889406003009 5367759709730167054502257)
                ·
                  refine ⟨4025819782297625290876693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5367759709730167054502257 4025819782297625290876693)
                  ·
                    refine ⟨188710302295201185509845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4025819782297625290876693 188710302295201185509845)
                    ·
                      rfl

theorem cell23_1102536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1102536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102536 prefixEnd_1102536 := by exact prefixLift 1102536
  have htrace : WordTrace (prefixWord ++ tailWord_1102536) baseStart_1102536 baseEnd_1102536 := by
    simpa [prefixWord, tailWord_1102536, baseEnd_1102536] using wordTrace_append hprefix tailTrace_1102536
  have hstable : (prefixWord ++ tailWord_1102536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102536).length < 2 ^ (prefixWord ++ tailWord_1102536).sum := by decide
  have hdescent : baseEnd_1102536 < baseStart_1102536 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102603 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 2, 5, 2]
def baseStart_1102603 : Nat := 118140960795 + 1102603 * 2 ^ 59
def prefixEnd_1102603 : Nat := 4983230072969 + 3 ^ 40 * 1102603 * 2
def baseEnd_1102603 : Nat := 566165310089454794391727

theorem tailTrace_1102603 : CollatzResearch.WordTrace tailWord_1102603 prefixEnd_1102603 566165310089454794391727 := by
  unfold tailWord_1102603
  simp only [CollatzResearch.WordTrace]
  refine ⟨40215235224465115445416463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26810156816310076963610975 40215235224465115445416463)
  ·
    refine ⟨60322852836697673168124695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40215235224465115445416463 60322852836697673168124695)
    ·
      refine ⟨90484279255046509752187043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60322852836697673168124695 90484279255046509752187043)
      ·
        refine ⟨135726418882569764628280565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90484279255046509752187043 135726418882569764628280565)
        ·
          refine ⟨12724351770240915433901303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135726418882569764628280565 12724351770240915433901303)
          ·
            refine ⟨19086527655361373150851955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12724351770240915433901303 19086527655361373150851955)
            ·
              refine ⟨28629791483042059726277933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19086527655361373150851955 28629791483042059726277933)
              ·
                refine ⟨10736171806140772397354225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28629791483042059726277933 10736171806140772397354225)
                ·
                  refine ⟨8052128854605579298015669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10736171806140772397354225 8052128854605579298015669)
                  ·
                    refine ⟨754887080119273059188969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8052128854605579298015669 754887080119273059188969)
                    ·
                      refine ⟨566165310089454794391727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754887080119273059188969 566165310089454794391727)
                      ·
                        rfl

theorem cell23_1102603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5, 2].length) (baseStart_1102603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102603 prefixEnd_1102603 := by exact prefixLift 1102603
  have htrace : WordTrace (prefixWord ++ tailWord_1102603) baseStart_1102603 baseEnd_1102603 := by
    simpa [prefixWord, tailWord_1102603, baseEnd_1102603] using wordTrace_append hprefix tailTrace_1102603
  have hstable : (prefixWord ++ tailWord_1102603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102603).length < 2 ^ (prefixWord ++ tailWord_1102603).sum := by decide
  have hdescent : baseEnd_1102603 < baseStart_1102603 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102633 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 1, 6, 2]
def baseStart_1102633 : Nat := 118140960795 + 1102633 * 2 ^ 59
def prefixEnd_1102633 : Nat := 4983230072969 + 3 ^ 40 * 1102633 * 2
def baseEnd_1102633 : Nat := 566180714509089677016589

theorem tailTrace_1102633 : CollatzResearch.WordTrace tailWord_1102633 prefixEnd_1102633 566180714509089677016589 := by
  unfold tailWord_1102633
  simp only [CollatzResearch.WordTrace]
  refine ⟨40216329414356430569008553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26810886276237620379339035 40216329414356430569008553)
  ·
    refine ⟨30162247060767322926756415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40216329414356430569008553 30162247060767322926756415)
    ·
      refine ⟨45243370591150984390134623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30162247060767322926756415 45243370591150984390134623)
      ·
        refine ⟨67865055886726476585201935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45243370591150984390134623 67865055886726476585201935)
        ·
          refine ⟨101797583830089714877802903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67865055886726476585201935 101797583830089714877802903)
          ·
            refine ⟨152696375745134572316704355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101797583830089714877802903 152696375745134572316704355)
            ·
              refine ⟨229044563617701858475056533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152696375745134572316704355 229044563617701858475056533)
              ·
                refine ⟨10736463919579774616018275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229044563617701858475056533 10736463919579774616018275)
                ·
                  refine ⟨16104695879369661924027413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10736463919579774616018275 16104695879369661924027413)
                  ·
                    refine ⟨754907619345452902688785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16104695879369661924027413 754907619345452902688785)
                    ·
                      refine ⟨566180714509089677016589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 754907619345452902688785 566180714509089677016589)
                      ·
                        rfl

theorem cell23_1102633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 1, 6, 2].length) (baseStart_1102633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102633 prefixEnd_1102633 := by exact prefixLift 1102633
  have htrace : WordTrace (prefixWord ++ tailWord_1102633) baseStart_1102633 baseEnd_1102633 := by
    simpa [prefixWord, tailWord_1102633, baseEnd_1102633] using wordTrace_append hprefix tailTrace_1102633
  have hstable : (prefixWord ++ tailWord_1102633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102633).length < 2 ^ (prefixWord ++ tailWord_1102633).sum := by decide
  have hdescent : baseEnd_1102633 < baseStart_1102633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102656 : List Nat := [2, 1, 1, 2, 2, 1, 1, 5, 8]
def baseStart_1102656 : Nat := 118140960795 + 1102656 * 2 ^ 59
def prefixEnd_1102656 : Nat := 4983230072969 + 3 ^ 40 * 1102656 * 2
def baseEnd_1102656 : Nat := 62910280507127009669887

theorem tailTrace_1102656 : CollatzResearch.WordTrace tailWord_1102656 prefixEnd_1102656 62910280507127009669887 := by
  unfold tailWord_1102656
  simp only [CollatzResearch.WordTrace]
  refine ⟨20108584146636552748547911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26811445528848736998063881 20108584146636552748547911)
  ·
    refine ⟨30162876219954829122821867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20108584146636552748547911 30162876219954829122821867)
    ·
      refine ⟨45244314329932243684232801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30162876219954829122821867 45244314329932243684232801)
      ·
        refine ⟨33933235747449182763174601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45244314329932243684232801 33933235747449182763174601)
        ·
          refine ⟨25449926810586887072380951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33933235747449182763174601 25449926810586887072380951)
          ·
            refine ⟨38174890215880330608571427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25449926810586887072380951 38174890215880330608571427)
            ·
              refine ⟨57262335323820495912857141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38174890215880330608571427 57262335323820495912857141)
              ·
                refine ⟨5368343936608171491830357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57262335323820495912857141 5368343936608171491830357)
                ·
                  refine ⟨62910280507127009669887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5368343936608171491830357 62910280507127009669887)
                  ·
                    rfl

theorem cell23_1102656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 5, 8].length) (baseStart_1102656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102656 prefixEnd_1102656 := by exact prefixLift 1102656
  have htrace : WordTrace (prefixWord ++ tailWord_1102656) baseStart_1102656 baseEnd_1102656 := by
    simpa [prefixWord, tailWord_1102656, baseEnd_1102656] using wordTrace_append hprefix tailTrace_1102656
  have hstable : (prefixWord ++ tailWord_1102656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102656).length < 2 ^ (prefixWord ++ tailWord_1102656).sum := by decide
  have hdescent : baseEnd_1102656 < baseStart_1102656 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102700 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 3]
def baseStart_1102700 : Nat := 118140960795 + 1102700 * 2 ^ 59
def prefixEnd_1102700 : Nat := 4983230072969 + 3 ^ 40 * 1102700 * 2
def baseEnd_1102700 : Nat := 566215117712940914878781

theorem tailTrace_1102700 : CollatzResearch.WordTrace tailWord_1102700 prefixEnd_1102700 566215117712940914878781 := by
  unfold tailWord_1102700
  simp only [CollatzResearch.WordTrace]
  refine ⟨20109386552556850505848777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26812515403409134007798369 20109386552556850505848777)
  ·
    refine ⟨15082039914417637879386583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20109386552556850505848777 15082039914417637879386583)
    ·
      refine ⟨22623059871626456819079875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15082039914417637879386583 22623059871626456819079875)
      ·
        refine ⟨33934589807439685228619813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22623059871626456819079875 33934589807439685228619813)
        ·
          refine ⟨6362735588894940980366215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33934589807439685228619813 6362735588894940980366215)
          ·
            refine ⟨9544103383342411470549323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6362735588894940980366215 9544103383342411470549323)
            ·
              refine ⟨14316155075013617205823985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9544103383342411470549323 14316155075013617205823985)
              ·
                refine ⟨10737116306260212904367989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14316155075013617205823985 10737116306260212904367989)
                ·
                  refine ⟨1006604653711894959784499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10737116306260212904367989 1006604653711894959784499)
                  ·
                    refine ⟨1509906980567842439676749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1006604653711894959784499 1509906980567842439676749)
                    ·
                      refine ⟨566215117712940914878781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1509906980567842439676749 566215117712940914878781)
                      ·
                        rfl

theorem cell23_1102700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 5, 1, 3].length) (baseStart_1102700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102700 prefixEnd_1102700 := by exact prefixLift 1102700
  have htrace : WordTrace (prefixWord ++ tailWord_1102700) baseStart_1102700 baseEnd_1102700 := by
    simpa [prefixWord, tailWord_1102700, baseEnd_1102700] using wordTrace_append hprefix tailTrace_1102700
  have hstable : (prefixWord ++ tailWord_1102700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102700).length < 2 ^ (prefixWord ++ tailWord_1102700).sum := by decide
  have hdescent : baseEnd_1102700 < baseStart_1102700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102710 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6]
def baseStart_1102710 : Nat := 118140960795 + 1102710 * 2 ^ 59
def prefixEnd_1102710 : Nat := 4983230072969 + 3 ^ 40 * 1102710 * 2
def baseEnd_1102710 : Nat := 566220252519485875753735

theorem tailTrace_1102710 : CollatzResearch.WordTrace tailWord_1102710 prefixEnd_1102710 566220252519485875753735 := by
  unfold tailWord_1102710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2513696114692342044972599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26812758556718315146374389 2513696114692342044972599)
  ·
    refine ⟨3770544172038513067458899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2513696114692342044972599 3770544172038513067458899)
    ·
      refine ⟨5655816258057769601188349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3770544172038513067458899 5655816258057769601188349)
      ·
        refine ⟨2120931096771663600445631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5655816258057769601188349 2120931096771663600445631)
        ·
          refine ⟨3181396645157495400668447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2120931096771663600445631 3181396645157495400668447)
          ·
            refine ⟨4772094967736243101002671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181396645157495400668447 4772094967736243101002671)
            ·
              refine ⟨7158142451604364651504007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4772094967736243101002671 7158142451604364651504007)
              ·
                refine ⟨10737213677406546977256011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7158142451604364651504007 10737213677406546977256011)
                ·
                  refine ⟨16105820516109820465884017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10737213677406546977256011 16105820516109820465884017)
                  ·
                    refine ⟨12079365387082365349413013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16105820516109820465884017 12079365387082365349413013)
                    ·
                      refine ⟨566220252519485875753735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12079365387082365349413013 566220252519485875753735)
                      ·
                        rfl

theorem cell23_1102710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6].length) (baseStart_1102710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102710 prefixEnd_1102710 := by exact prefixLift 1102710
  have htrace : WordTrace (prefixWord ++ tailWord_1102710) baseStart_1102710 baseEnd_1102710 := by
    simpa [prefixWord, tailWord_1102710, baseEnd_1102710] using wordTrace_append hprefix tailTrace_1102710
  have hstable : (prefixWord ++ tailWord_1102710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102710).length < 2 ^ (prefixWord ++ tailWord_1102710).sum := by decide
  have hdescent : baseEnd_1102710 < baseStart_1102710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102743 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1102743 : Nat := 118140960795 + 1102743 * 2 ^ 59
def prefixEnd_1102743 : Nat := 4983230072969 + 3 ^ 40 * 1102743 * 2
def baseEnd_1102743 : Nat := 566237197381084246641083

theorem tailTrace_1102743 : CollatzResearch.WordTrace tailWord_1102743 prefixEnd_1102743 566237197381084246641083 := by
  unfold tailWord_1102743
  simp only [CollatzResearch.WordTrace]
  refine ⟨40220341443957919355512883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26813560962638612903675255 40220341443957919355512883)
  ·
    refine ⟨60330512165936879033269325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40220341443957919355512883 60330512165936879033269325)
    ·
      refine ⟨22623942062226329637475997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60330512165936879033269325 22623942062226329637475997)
      ·
        refine ⟨8483978273334873614053499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22623942062226329637475997 8483978273334873614053499)
        ·
          refine ⟨12725967410002310421080249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8483978273334873614053499 12725967410002310421080249)
          ·
            refine ⟨9544475557501732815810187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12725967410002310421080249 9544475557501732815810187)
            ·
              refine ⟨14316713336252599223715281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9544475557501732815810187 14316713336252599223715281)
              ·
                refine ⟨10737535002189449417786461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14316713336252599223715281 10737535002189449417786461)
                ·
                  refine ⟨4026575625821043531669923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10737535002189449417786461 4026575625821043531669923)
                  ·
                    refine ⟨6039863438731565297504885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026575625821043531669923 6039863438731565297504885)
                    ·
                      refine ⟨566237197381084246641083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6039863438731565297504885 566237197381084246641083)
                      ·
                        rfl

theorem cell23_1102743_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1102743 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102743 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102743 prefixEnd_1102743 := by exact prefixLift 1102743
  have htrace : WordTrace (prefixWord ++ tailWord_1102743) baseStart_1102743 baseEnd_1102743 := by
    simpa [prefixWord, tailWord_1102743, baseEnd_1102743] using wordTrace_append hprefix tailTrace_1102743
  have hstable : (prefixWord ++ tailWord_1102743).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102743).length < 2 ^ (prefixWord ++ tailWord_1102743).sum := by decide
  have hdescent : baseEnd_1102743 < baseStart_1102743 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102743) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102751 : List Nat := [1, 1, 2, 5, 2, 3, 1, 3, 1, 1, 3]
def baseStart_1102751 : Nat := 118140960795 + 1102751 * 2 ^ 59
def prefixEnd_1102751 : Nat := 4983230072969 + 3 ^ 40 * 1102751 * 2
def baseEnd_1102751 : Nat := 566241305226320215341047

theorem tailTrace_1102751 : CollatzResearch.WordTrace tailWord_1102751 prefixEnd_1102751 566241305226320215341047 := by
  unfold tailWord_1102751
  simp only [CollatzResearch.WordTrace]
  refine ⟨40220633227928936721804107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26813755485285957814536071 40220633227928936721804107)
  ·
    refine ⟨60330949841893405082706161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40220633227928936721804107 60330949841893405082706161)
    ·
      refine ⟨45248212381420053812029621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60330949841893405082706161 45248212381420053812029621)
      ·
        refine ⟨4242019910758130044877777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45248212381420053812029621 4242019910758130044877777)
        ·
          refine ⟨3181514933068597533658333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4242019910758130044877777 3181514933068597533658333)
          ·
            refine ⟨1193068099900724075121875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3181514933068597533658333 1193068099900724075121875)
            ·
              refine ⟨1789602149851086112682813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1193068099900724075121875 1789602149851086112682813)
              ·
                refine ⟨671100806194157292256055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1789602149851086112682813 671100806194157292256055)
                ·
                  refine ⟨1006651209291235938384083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671100806194157292256055 1006651209291235938384083)
                  ·
                    refine ⟨1509976813936853907576125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1006651209291235938384083 1509976813936853907576125)
                    ·
                      refine ⟨566241305226320215341047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1509976813936853907576125 566241305226320215341047)
                      ·
                        rfl

theorem cell23_1102751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_1102751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102751 prefixEnd_1102751 := by exact prefixLift 1102751
  have htrace : WordTrace (prefixWord ++ tailWord_1102751) baseStart_1102751 baseEnd_1102751 := by
    simpa [prefixWord, tailWord_1102751, baseEnd_1102751] using wordTrace_append hprefix tailTrace_1102751
  have hstable : (prefixWord ++ tailWord_1102751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102751).length < 2 ^ (prefixWord ++ tailWord_1102751).sum := by decide
  have hdescent : baseEnd_1102751 < baseStart_1102751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102784 : List Nat := [2, 1, 1, 2, 3, 5, 2, 1, 2, 4]
def baseStart_1102784 : Nat := 118140960795 + 1102784 * 2 ^ 59
def prefixEnd_1102784 : Nat := 4983230072969 + 3 ^ 40 * 1102784 * 2
def baseEnd_1102784 : Nat := 188752750029306195409465

theorem tailTrace_1102784 : CollatzResearch.WordTrace tailWord_1102784 prefixEnd_1102784 188752750029306195409465 := by
  unfold tailWord_1102784
  simp only [CollatzResearch.WordTrace]
  refine ⟨20110918418404691678877703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26814557891206255571836937 20110918418404691678877703)
  ·
    refine ⟨30166377627607037518316555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20110918418404691678877703 30166377627607037518316555)
    ·
      refine ⟨45249566441410556277474833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30166377627607037518316555 45249566441410556277474833)
      ·
        refine ⟨33937174831057917208106125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45249566441410556277474833 33937174831057917208106125)
        ·
          refine ⟨12726440561646718953039797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33937174831057917208106125 12726440561646718953039797)
          ·
            refine ⟨1193103802654379901847481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12726440561646718953039797 1193103802654379901847481)
            ·
              refine ⟨894827851990784926385611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193103802654379901847481 894827851990784926385611)
              ·
                refine ⟨1342241777986177389578417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 894827851990784926385611 1342241777986177389578417)
                ·
                  refine ⟨1006681333489633042183813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342241777986177389578417 1006681333489633042183813)
                  ·
                    refine ⟨188752750029306195409465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1006681333489633042183813 188752750029306195409465)
                    ·
                      rfl

theorem cell23_1102784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 2, 1, 2, 4].length) (baseStart_1102784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102784 prefixEnd_1102784 := by exact prefixLift 1102784
  have htrace : WordTrace (prefixWord ++ tailWord_1102784) baseStart_1102784 baseEnd_1102784 := by
    simpa [prefixWord, tailWord_1102784, baseEnd_1102784] using wordTrace_append hprefix tailTrace_1102784
  have hstable : (prefixWord ++ tailWord_1102784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102784).length < 2 ^ (prefixWord ++ tailWord_1102784).sum := by decide
  have hdescent : baseEnd_1102784 < baseStart_1102784 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102847 : List Nat := [1, 1, 2, 2, 1, 2, 1, 1, 8, 2, 2]
def baseStart_1102847 : Nat := 118140960795 + 1102847 * 2 ^ 59
def prefixEnd_1102847 : Nat := 4983230072969 + 3 ^ 40 * 1102847 * 2
def baseEnd_1102847 : Nat := 566290599369151839740605

theorem tailTrace_1102847 : CollatzResearch.WordTrace tailWord_1102847 prefixEnd_1102847 566290599369151839740605 := by
  unfold tailWord_1102847
  simp only [CollatzResearch.WordTrace]
  refine ⟨40224134635581145117298795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26816089757054096744865863 40224134635581145117298795)
  ·
    refine ⟨60336201953371717675948193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40224134635581145117298795 60336201953371717675948193)
    ·
      refine ⟨45252151465028788256961145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60336201953371717675948193 45252151465028788256961145)
      ·
        refine ⟨33939113598771591192720859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45252151465028788256961145 33939113598771591192720859)
        ·
          refine ⟨50908670398157386789081289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33939113598771591192720859 50908670398157386789081289)
          ·
            refine ⟨38181502798618040091810967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50908670398157386789081289 38181502798618040091810967)
            ·
              refine ⟨57272254197927060137716451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38181502798618040091810967 57272254197927060137716451)
              ·
                refine ⟨85908381296890590206574677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57272254197927060137716451 85908381296890590206574677)
                ·
                  refine ⟨1006738843322936603983297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 85908381296890590206574677 1006738843322936603983297)
                  ·
                    refine ⟨755054132492202452987473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1006738843322936603983297 755054132492202452987473)
                    ·
                      refine ⟨566290599369151839740605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755054132492202452987473 566290599369151839740605)
                      ·
                        rfl

theorem cell23_1102847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_1102847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102847 prefixEnd_1102847 := by exact prefixLift 1102847
  have htrace : WordTrace (prefixWord ++ tailWord_1102847) baseStart_1102847 baseEnd_1102847 := by
    simpa [prefixWord, tailWord_1102847, baseEnd_1102847] using wordTrace_append hprefix tailTrace_1102847
  have hstable : (prefixWord ++ tailWord_1102847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102847).length < 2 ^ (prefixWord ++ tailWord_1102847).sum := by decide
  have hdescent : baseEnd_1102847 < baseStart_1102847 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102881 : List Nat := [1, 2, 3, 2, 3, 1, 3, 2, 2, 2, 2]
def baseStart_1102881 : Nat := 118140960795 + 1102881 * 2 ^ 59
def prefixEnd_1102881 : Nat := 4983230072969 + 3 ^ 40 * 1102881 * 2
def baseEnd_1102881 : Nat := 566308057711404706715449

theorem tailTrace_1102881 : CollatzResearch.WordTrace tailWord_1102881 prefixEnd_1102881 566308057711404706715449 := by
  unfold tailWord_1102881
  simp only [CollatzResearch.WordTrace]
  refine ⟨40225374717457968924036497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26816916478305312616024331 40225374717457968924036497)
  ·
    refine ⟨30169031038093476693027373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40225374717457968924036497 30169031038093476693027373)
    ·
      refine ⟨11313386639285053759885265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30169031038093476693027373 11313386639285053759885265)
      ·
        refine ⟨8485039979463790319913949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11313386639285053759885265 8485039979463790319913949)
        ·
          refine ⟨3181889992298921369967731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8485039979463790319913949 3181889992298921369967731)
          ·
            refine ⟨4772834988448382054951597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181889992298921369967731 4772834988448382054951597)
            ·
              refine ⟨1789813120668143270606849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4772834988448382054951597 1789813120668143270606849)
              ·
                refine ⟨1342359840501107452955137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789813120668143270606849 1342359840501107452955137)
                ·
                  refine ⟨1006769880375830589716353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342359840501107452955137 1006769880375830589716353)
                  ·
                    refine ⟨755077410281872942287265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1006769880375830589716353 755077410281872942287265)
                    ·
                      refine ⟨566308057711404706715449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755077410281872942287265 566308057711404706715449)
                      ·
                        rfl

theorem cell23_1102881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_1102881 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102881 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102881 prefixEnd_1102881 := by exact prefixLift 1102881
  have htrace : WordTrace (prefixWord ++ tailWord_1102881) baseStart_1102881 baseEnd_1102881 := by
    simpa [prefixWord, tailWord_1102881, baseEnd_1102881] using wordTrace_append hprefix tailTrace_1102881
  have hstable : (prefixWord ++ tailWord_1102881).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102881).length < 2 ^ (prefixWord ++ tailWord_1102881).sum := by decide
  have hdescent : baseEnd_1102881 < baseStart_1102881 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102887 : List Nat := [1, 1, 7, 1, 1, 1, 1, 3, 7]
def baseStart_1102887 : Nat := 118140960795 + 1102887 * 2 ^ 59
def prefixEnd_1102887 : Nat := 4983230072969 + 3 ^ 40 * 1102887 * 2
def baseEnd_1102887 : Nat := 62923459843925742582269

theorem tailTrace_1102887 : CollatzResearch.WordTrace tailWord_1102887 prefixEnd_1102887 62923459843925742582269 := by
  unfold tailWord_1102887
  simp only [CollatzResearch.WordTrace]
  refine ⟨40225593555436231948754915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26817062370290821299169943 40225593555436231948754915)
  ·
    refine ⟨60338390333154347923132373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40225593555436231948754915 60338390333154347923132373)
    ·
      refine ⟨1414181023433305029448415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 60338390333154347923132373 1414181023433305029448415)
      ·
        refine ⟨2121271535149957544172623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414181023433305029448415 2121271535149957544172623)
        ·
          refine ⟨3181907302724936316258935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121271535149957544172623 3181907302724936316258935)
          ·
            refine ⟨4772860954087404474388403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181907302724936316258935 4772860954087404474388403)
            ·
              refine ⟨7159291431131106711582605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4772860954087404474388403 7159291431131106711582605)
              ·
                refine ⟨2684734286674165016843477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7159291431131106711582605 2684734286674165016843477)
                ·
                  refine ⟨62923459843925742582269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2684734286674165016843477 62923459843925742582269)
                  ·
                    rfl

theorem cell23_1102887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 3, 7].length) (baseStart_1102887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102887 prefixEnd_1102887 := by exact prefixLift 1102887
  have htrace : WordTrace (prefixWord ++ tailWord_1102887) baseStart_1102887 baseEnd_1102887 := by
    simpa [prefixWord, tailWord_1102887, baseEnd_1102887] using wordTrace_append hprefix tailTrace_1102887
  have hstable : (prefixWord ++ tailWord_1102887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102887).length < 2 ^ (prefixWord ++ tailWord_1102887).sum := by decide
  have hdescent : baseEnd_1102887 < baseStart_1102887 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102920 : List Nat := [2, 1, 3, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1102920 : Nat := 118140960795 + 1102920 * 2 ^ 59
def prefixEnd_1102920 : Nat := 4983230072969 + 3 ^ 40 * 1102920 * 2
def baseEnd_1102920 : Nat := 566328083456930054127769

theorem tailTrace_1102920 : CollatzResearch.WordTrace tailWord_1102920 prefixEnd_1102920 566328083456930054127769 := by
  unfold tailWord_1102920
  simp only [CollatzResearch.WordTrace]
  refine ⟨20113398582158339292353107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26817864776211119056470809 20113398582158339292353107)
  ·
    refine ⟨30170097873237508938529661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20113398582158339292353107 30170097873237508938529661)
    ·
      refine ⟨11313786702464065851948623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30170097873237508938529661 11313786702464065851948623)
      ·
        refine ⟨16970680053696098777922935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11313786702464065851948623 16970680053696098777922935)
        ·
          refine ⟨25456020080544148166884403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16970680053696098777922935 25456020080544148166884403)
          ·
            refine ⟨38184030120816222250326605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25456020080544148166884403 38184030120816222250326605)
            ·
              refine ⟨14319011295306083343872477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38184030120816222250326605 14319011295306083343872477)
              ·
                refine ⟨5369629235739781253952179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14319011295306083343872477 5369629235739781253952179)
                ·
                  refine ⟨8054443853609671880928269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5369629235739781253952179 8054443853609671880928269)
                  ·
                    refine ⟨3020416445103626955348101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8054443853609671880928269 3020416445103626955348101)
                    ·
                      refine ⟨566328083456930054127769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3020416445103626955348101 566328083456930054127769)
                      ·
                        rfl

theorem cell23_1102920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1102920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102920 prefixEnd_1102920 := by exact prefixLift 1102920
  have htrace : WordTrace (prefixWord ++ tailWord_1102920) baseStart_1102920 baseEnd_1102920 := by
    simpa [prefixWord, tailWord_1102920, baseEnd_1102920] using wordTrace_append hprefix tailTrace_1102920
  have hstable : (prefixWord ++ tailWord_1102920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102920).length < 2 ^ (prefixWord ++ tailWord_1102920).sum := by decide
  have hdescent : baseEnd_1102920 < baseStart_1102920 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102937 : List Nat := [1, 2, 1, 2, 2, 1, 2, 4, 2, 4, 2]
def baseStart_1102937 : Nat := 118140960795 + 1102937 * 2 ^ 59
def prefixEnd_1102937 : Nat := 4983230072969 + 3 ^ 40 * 1102937 * 2
def baseEnd_1102937 : Nat := 566336812628056487615191

theorem tailTrace_1102937 : CollatzResearch.WordTrace tailWord_1102937 prefixEnd_1102937 566336812628056487615191 := by
  unfold tailWord_1102937
  simp only [CollatzResearch.WordTrace]
  refine ⟨40227417205255090488075065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26818278136836726992050043 40227417205255090488075065)
  ·
    refine ⟨30170562903941317866056299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40227417205255090488075065 30170562903941317866056299)
    ·
      refine ⟨45255844355911976799084449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30170562903941317866056299 45255844355911976799084449)
      ·
        refine ⟨33941883266933982599313337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45255844355911976799084449 33941883266933982599313337)
        ·
          refine ⟨25456412450200486949485003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33941883266933982599313337 25456412450200486949485003)
          ·
            refine ⟨38184618675300730424227505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25456412450200486949485003 38184618675300730424227505)
            ·
              refine ⟨28638464006475547818170629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38184618675300730424227505 28638464006475547818170629)
              ·
                refine ⟨5369712001214165215906993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28638464006475547818170629 5369712001214165215906993)
                ·
                  refine ⟨4027284000910623911930245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5369712001214165215906993 4027284000910623911930245)
                  ·
                    refine ⟨755115750170741983486921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027284000910623911930245 755115750170741983486921)
                    ·
                      refine ⟨566336812628056487615191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755115750170741983486921 566336812628056487615191)
                      ·
                        rfl

theorem cell23_1102937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 4, 2].length) (baseStart_1102937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102937 prefixEnd_1102937 := by exact prefixLift 1102937
  have htrace : WordTrace (prefixWord ++ tailWord_1102937) baseStart_1102937 baseEnd_1102937 := by
    simpa [prefixWord, tailWord_1102937, baseEnd_1102937] using wordTrace_append hprefix tailTrace_1102937
  have hstable : (prefixWord ++ tailWord_1102937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102937).length < 2 ^ (prefixWord ++ tailWord_1102937).sum := by decide
  have hdescent : baseEnd_1102937 < baseStart_1102937 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1102994 : List Nat := [3, 2, 3, 1, 1, 3, 2, 2, 6]
def baseStart_1102994 : Nat := 118140960795 + 1102994 * 2 ^ 59
def prefixEnd_1102994 : Nat := 4983230072969 + 3 ^ 40 * 1102994 * 2
def baseEnd_1102994 : Nat := 62929564558373640511381

theorem tailTrace_1102994 : CollatzResearch.WordTrace tailWord_1102994 prefixEnd_1102994 62929564558373640511381 := by
  unfold tailWord_1102994
  simp only [CollatzResearch.WordTrace]
  refine ⟨10057374041512147305725009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26819664110699059481933357 10057374041512147305725009)
  ·
    refine ⟨7543030531134110479293757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10057374041512147305725009 7543030531134110479293757)
    ·
      refine ⟨2828636449175291429735159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7543030531134110479293757 2828636449175291429735159)
      ·
        refine ⟨4242954673762937144602739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828636449175291429735159 4242954673762937144602739)
        ·
          refine ⟨6364432010644405716904109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4242954673762937144602739 6364432010644405716904109)
          ·
            refine ⟨2386662003991652143839041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6364432010644405716904109 2386662003991652143839041)
            ·
              refine ⟨1789996502993739107879281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2386662003991652143839041 1789996502993739107879281)
              ·
                refine ⟨1342497377245304330909461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1789996502993739107879281 1342497377245304330909461)
                ·
                  refine ⟨62929564558373640511381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1342497377245304330909461 62929564558373640511381)
                  ·
                    rfl

theorem cell23_1102994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 2, 2, 6].length) (baseStart_1102994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1102994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1102994 prefixEnd_1102994 := by exact prefixLift 1102994
  have htrace : WordTrace (prefixWord ++ tailWord_1102994) baseStart_1102994 baseEnd_1102994 := by
    simpa [prefixWord, tailWord_1102994, baseEnd_1102994] using wordTrace_append hprefix tailTrace_1102994
  have hstable : (prefixWord ++ tailWord_1102994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1102994).length < 2 ^ (prefixWord ++ tailWord_1102994).sum := by decide
  have hdescent : baseEnd_1102994 < baseStart_1102994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1102994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103027 : List Nat := [1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 4]
def baseStart_1103027 : Nat := 118140960795 + 1103027 * 2 ^ 59
def prefixEnd_1103027 : Nat := 4983230072969 + 3 ^ 40 * 1103027 * 2
def baseEnd_1103027 : Nat := 566383025886961135489777

theorem tailTrace_1103027 : CollatzResearch.WordTrace tailWord_1103027 prefixEnd_1103027 566383025886961135489777 := by
  unfold tailWord_1103027
  simp only [CollatzResearch.WordTrace]
  refine ⟨40230699774929035858851335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26820466516619357239234223 40230699774929035858851335)
  ·
    refine ⟨60346049662393553788277003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40230699774929035858851335 60346049662393553788277003)
    ·
      refine ⟨90519074493590330682415505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60346049662393553788277003 90519074493590330682415505)
      ·
        refine ⟨67889305870192748011811629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90519074493590330682415505 67889305870192748011811629)
        ·
          refine ⟨25458489701322280504429361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67889305870192748011811629 25458489701322280504429361)
          ·
            refine ⟨19093867275991710378322021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25458489701322280504429361 19093867275991710378322021)
            ·
              refine ⟨3580100114248445695935379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19093867275991710378322021 3580100114248445695935379)
              ·
                refine ⟨5370150171372668543903069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580100114248445695935379 5370150171372668543903069)
                ·
                  refine ⟨2013806314264750703963651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5370150171372668543903069 2013806314264750703963651)
                  ·
                    refine ⟨3020709471397126055945477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2013806314264750703963651 3020709471397126055945477)
                    ·
                      refine ⟨566383025886961135489777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3020709471397126055945477 566383025886961135489777)
                      ·
                        rfl

theorem cell23_1103027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 1, 3, 1, 4].length) (baseStart_1103027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103027 prefixEnd_1103027 := by exact prefixLift 1103027
  have htrace : WordTrace (prefixWord ++ tailWord_1103027) baseStart_1103027 baseEnd_1103027 := by
    simpa [prefixWord, tailWord_1103027, baseEnd_1103027] using wordTrace_append hprefix tailTrace_1103027
  have hstable : (prefixWord ++ tailWord_1103027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103027).length < 2 ^ (prefixWord ++ tailWord_1103027).sum := by decide
  have hdescent : baseEnd_1103027 < baseStart_1103027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103037 : List Nat := [1, 4, 1, 2, 1, 1, 4, 2, 1, 6]
def baseStart_1103037 : Nat := 118140960795 + 1103037 * 2 ^ 59
def prefixEnd_1103037 : Nat := 4983230072969 + 3 ^ 40 * 1103037 * 2
def baseEnd_1103037 : Nat := 188796053564502032121577

theorem tailTrace_1103037 : CollatzResearch.WordTrace tailWord_1103037 prefixEnd_1103037 188796053564502032121577 := by
  unfold tailWord_1103037
  simp only [CollatzResearch.WordTrace]
  refine ⟨40231064504892807566715365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26820709669928538377810243 40231064504892807566715365)
  ·
    refine ⟨7543324594667401418759131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40231064504892807566715365 7543324594667401418759131)
    ·
      refine ⟨11314986892001102128138697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7543324594667401418759131 11314986892001102128138697)
      ·
        refine ⟨8486240169000826596104023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11314986892001102128138697 8486240169000826596104023)
        ·
          refine ⟨12729360253501239894156035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486240169000826596104023 12729360253501239894156035)
          ·
            refine ⟨19094040380251859841234053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12729360253501239894156035 19094040380251859841234053)
            ·
              refine ⟨3580132571297223720231385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19094040380251859841234053 3580132571297223720231385)
              ·
                refine ⟨2685099428472917790173539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580132571297223720231385 2685099428472917790173539)
                ·
                  refine ⟨4027649142709376685260309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685099428472917790173539 4027649142709376685260309)
                  ·
                    refine ⟨188796053564502032121577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4027649142709376685260309 188796053564502032121577)
                    ·
                      rfl

theorem cell23_1103037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 4, 2, 1, 6].length) (baseStart_1103037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103037 prefixEnd_1103037 := by exact prefixLift 1103037
  have htrace : WordTrace (prefixWord ++ tailWord_1103037) baseStart_1103037 baseEnd_1103037 := by
    simpa [prefixWord, tailWord_1103037, baseEnd_1103037] using wordTrace_append hprefix tailTrace_1103037
  have hstable : (prefixWord ++ tailWord_1103037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103037).length < 2 ^ (prefixWord ++ tailWord_1103037).sum := by decide
  have hdescent : baseEnd_1103037 < baseStart_1103037 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103038 : List Nat := [4, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3]
def baseStart_1103038 : Nat := 118140960795 + 1103038 * 2 ^ 59
def prefixEnd_1103038 : Nat := 4983230072969 + 3 ^ 40 * 1103038 * 2
def baseEnd_1103038 : Nat := 566388674174160592452227

theorem tailTrace_1103038 : CollatzResearch.WordTrace tailWord_1103038 prefixEnd_1103038 566388674174160592452227 := by
  unfold tailWord_1103038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5028887622236148092187721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26820733985259456491667845 5028887622236148092187721)
  ·
    refine ⟨3771665716677111069140791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5028887622236148092187721 3771665716677111069140791)
    ·
      refine ⟨5657498575015666603711187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771665716677111069140791 5657498575015666603711187)
      ·
        refine ⟨8486247862523499905566781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657498575015666603711187 8486247862523499905566781)
        ·
          refine ⟨3182342948446312464587543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8486247862523499905566781 3182342948446312464587543)
          ·
            refine ⟨4773514422669468696881315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182342948446312464587543 4773514422669468696881315)
            ·
              refine ⟨7160271634004203045321973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773514422669468696881315 7160271634004203045321973)
              ·
                refine ⟨671275465687894035498935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7160271634004203045321973 671275465687894035498935)
                ·
                  refine ⟨1006913198531841053248403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671275465687894035498935 1006913198531841053248403)
                  ·
                    refine ⟨1510369797797761579872605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1006913198531841053248403 1510369797797761579872605)
                    ·
                      refine ⟨566388674174160592452227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1510369797797761579872605 566388674174160592452227)
                      ·
                        rfl

theorem cell23_1103038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_1103038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103038 prefixEnd_1103038 := by exact prefixLift 1103038
  have htrace : WordTrace (prefixWord ++ tailWord_1103038) baseStart_1103038 baseEnd_1103038 := by
    simpa [prefixWord, tailWord_1103038, baseEnd_1103038] using wordTrace_append hprefix tailTrace_1103038
  have hstable : (prefixWord ++ tailWord_1103038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103038).length < 2 ^ (prefixWord ++ tailWord_1103038).sum := by decide
  have hdescent : baseEnd_1103038 < baseStart_1103038 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103041 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 1, 5]
def baseStart_1103041 : Nat := 118140960795 + 1103041 * 2 ^ 59
def prefixEnd_1103041 : Nat := 4983230072969 + 3 ^ 40 * 1103041 * 2
def baseEnd_1103041 : Nat := 188796738205374693571571

theorem tailTrace_1103041 : CollatzResearch.WordTrace tailWord_1103041 prefixEnd_1103041 188796738205374693571571 := by
  unfold tailWord_1103041
  simp only [CollatzResearch.WordTrace]
  refine ⟨40231210396878316249860977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26820806931252210833240651 40231210396878316249860977)
  ·
    refine ⟨30173407797658737187395733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40231210396878316249860977 30173407797658737187395733)
    ·
      refine ⟨1414378490515253305659175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 30173407797658737187395733 1414378490515253305659175)
      ·
        refine ⟨2121567735772879958488763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1414378490515253305659175 2121567735772879958488763)
        ·
          refine ⟨3182351603659319937733145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2121567735772879958488763 3182351603659319937733145)
          ·
            refine ⟨2386763702744489953299859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3182351603659319937733145 2386763702744489953299859)
            ·
              refine ⟨3580145554116734929949789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386763702744489953299859 3580145554116734929949789)
              ·
                refine ⟨1342554582793775598731171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3580145554116734929949789 1342554582793775598731171)
                ·
                  refine ⟨2013831874190663398096757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342554582793775598731171 2013831874190663398096757)
                  ·
                    refine ⟨188796738205374693571571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2013831874190663398096757 188796738205374693571571)
                    ·
                      rfl

theorem cell23_1103041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_1103041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103041 prefixEnd_1103041 := by exact prefixLift 1103041
  have htrace : WordTrace (prefixWord ++ tailWord_1103041) baseStart_1103041 baseEnd_1103041 := by
    simpa [prefixWord, tailWord_1103041, baseEnd_1103041] using wordTrace_append hprefix tailTrace_1103041
  have hstable : (prefixWord ++ tailWord_1103041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103041).length < 2 ^ (prefixWord ++ tailWord_1103041).sum := by decide
  have hdescent : baseEnd_1103041 < baseStart_1103041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103064 : List Nat := [2, 1, 2, 2, 5, 1, 1, 2, 1, 1, 5]
def baseStart_1103064 : Nat := 118140960795 + 1103064 * 2 ^ 59
def prefixEnd_1103064 : Nat := 4983230072969 + 3 ^ 40 * 1103064 * 2
def baseEnd_1103064 : Nat := 566402024671177490727107

theorem tailTrace_1103064 : CollatzResearch.WordTrace tailWord_1103064 prefixEnd_1103064 566402024671177490727107 := by
  unfold tailWord_1103064
  simp only [CollatzResearch.WordTrace]
  refine ⟨20116024637897495588974123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26821366183863327451965497 20116024637897495588974123)
  ·
    refine ⟨30174036956846243383461185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20116024637897495588974123 30174036956846243383461185)
    ·
      refine ⟨22630527717634682537595889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30174036956846243383461185 22630527717634682537595889)
      ·
        refine ⟨16972895788226011903196917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22630527717634682537595889 16972895788226011903196917)
        ·
          refine ⟨1591208980146188615924711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16972895788226011903196917 1591208980146188615924711)
          ·
            refine ⟨2386813470219282923887067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591208980146188615924711 2386813470219282923887067)
            ·
              refine ⟨3580220205328924385830601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386813470219282923887067 3580220205328924385830601)
              ·
                refine ⟨2685165153996693289372951, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580220205328924385830601 2685165153996693289372951)
                ·
                  refine ⟨4027747730995039934059427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685165153996693289372951 4027747730995039934059427)
                  ·
                    refine ⟨6041621596492559901089141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4027747730995039934059427 6041621596492559901089141)
                    ·
                      refine ⟨566402024671177490727107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6041621596492559901089141 566402024671177490727107)
                      ·
                        rfl

theorem cell23_1103064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 2, 1, 1, 5].length) (baseStart_1103064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103064 prefixEnd_1103064 := by exact prefixLift 1103064
  have htrace : WordTrace (prefixWord ++ tailWord_1103064) baseStart_1103064 baseEnd_1103064 := by
    simpa [prefixWord, tailWord_1103064, baseEnd_1103064] using wordTrace_append hprefix tailTrace_1103064
  have hstable : (prefixWord ++ tailWord_1103064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103064).length < 2 ^ (prefixWord ++ tailWord_1103064).sum := by decide
  have hdescent : baseEnd_1103064 < baseStart_1103064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103084 : List Nat := [2, 2, 1, 1, 2, 6, 2, 7]
def baseStart_1103084 : Nat := 118140960795 + 1103084 * 2 ^ 59
def prefixEnd_1103084 : Nat := 4983230072969 + 3 ^ 40 * 1103084 * 2
def baseEnd_1103084 : Nat := 20978233121639533795445

theorem tailTrace_1103084 : CollatzResearch.WordTrace tailWord_1103084 prefixEnd_1103084 20978233121639533795445 := by
  unfold tailWord_1103084
  simp only [CollatzResearch.WordTrace]
  refine ⟨20116389367861267296838153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26821852490481689729117537 20116389367861267296838153)
  ·
    refine ⟨15087292025895950472628615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20116389367861267296838153 15087292025895950472628615)
    ·
      refine ⟨22630938038843925708942923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15087292025895950472628615 22630938038843925708942923)
      ·
        refine ⟨33946407058265888563414385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22630938038843925708942923 33946407058265888563414385)
        ·
          refine ⟨25459805293699416422560789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33946407058265888563414385 25459805293699416422560789)
          ·
            refine ⟨1193428373142160144807537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25459805293699416422560789 1193428373142160144807537)
            ·
              refine ⟨895071279856620108605653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193428373142160144807537 895071279856620108605653)
              ·
                refine ⟨20978233121639533795445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 895071279856620108605653 20978233121639533795445)
                ·
                  rfl

theorem cell23_1103084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 2, 7].length) (baseStart_1103084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103084 prefixEnd_1103084 := by exact prefixLift 1103084
  have htrace : WordTrace (prefixWord ++ tailWord_1103084) baseStart_1103084 baseEnd_1103084 := by
    simpa [prefixWord, tailWord_1103084, baseEnd_1103084] using wordTrace_append hprefix tailTrace_1103084
  have hstable : (prefixWord ++ tailWord_1103084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103084).length < 2 ^ (prefixWord ++ tailWord_1103084).sum := by decide
  have hdescent : baseEnd_1103084 < baseStart_1103084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103094 : List Nat := [5, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3]
def baseStart_1103094 : Nat := 118140960795 + 1103094 * 2 ^ 59
def prefixEnd_1103094 : Nat := 4983230072969 + 3 ^ 40 * 1103094 * 2
def baseEnd_1103094 : Nat := 566417429090812373351969

theorem tailTrace_1103094 : CollatzResearch.WordTrace tailWord_1103094 prefixEnd_1103094 566417429090812373351969 := by
  unfold tailWord_1103094
  simp only [CollatzResearch.WordTrace]
  refine ⟨2514571466605394143846271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26822095643790870867693557 2514571466605394143846271)
  ·
    refine ⟨3771857199908091215769407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2514571466605394143846271 3771857199908091215769407)
    ·
      refine ⟨5657785799862136823654111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771857199908091215769407 5657785799862136823654111)
      ·
        refine ⟨8486678699793205235481167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657785799862136823654111 8486678699793205235481167)
        ·
          refine ⟨12730018049689807853221751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486678699793205235481167 12730018049689807853221751)
          ·
            refine ⟨19095027074534711779832627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12730018049689807853221751 19095027074534711779832627)
            ·
              refine ⟨28642540611802067669748941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19095027074534711779832627 28642540611802067669748941)
              ·
                refine ⟨10740952729425775376155853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28642540611802067669748941 10740952729425775376155853)
                ·
                  refine ⟨4027857273534665766058445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10740952729425775376155853 4027857273534665766058445)
                  ·
                    refine ⟨1510446477575499662271917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4027857273534665766058445 1510446477575499662271917)
                    ·
                      refine ⟨566417429090812373351969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1510446477575499662271917 566417429090812373351969)
                      ·
                        rfl

theorem cell23_1103094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3].length) (baseStart_1103094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103094 prefixEnd_1103094 := by exact prefixLift 1103094
  have htrace : WordTrace (prefixWord ++ tailWord_1103094) baseStart_1103094 baseEnd_1103094 := by
    simpa [prefixWord, tailWord_1103094, baseEnd_1103094] using wordTrace_append hprefix tailTrace_1103094
  have hstable : (prefixWord ++ tailWord_1103094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103094).length < 2 ^ (prefixWord ++ tailWord_1103094).sum := by decide
  have hdescent : baseEnd_1103094 < baseStart_1103094 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103104 : List Nat := [2, 1, 1, 2, 1, 1, 3, 2, 5, 3, 2]
def baseStart_1103104 : Nat := 118140960795 + 1103104 * 2 ^ 59
def prefixEnd_1103104 : Nat := 4983230072969 + 3 ^ 40 * 1103104 * 2
def baseEnd_1103104 : Nat := 566422563897357334226923

theorem tailTrace_1103104 : CollatzResearch.WordTrace tailWord_1103104 prefixEnd_1103104 566422563897357334226923 := by
  unfold tailWord_1103104
  simp only [CollatzResearch.WordTrace]
  refine ⟨20116754097825039004702183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26822338797100052006269577 20116754097825039004702183)
  ·
    refine ⟨30175131146737558507053275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20116754097825039004702183 30175131146737558507053275)
    ·
      refine ⟨45262696720106337760579913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30175131146737558507053275 45262696720106337760579913)
      ·
        refine ⟨33947022540079753320434935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45262696720106337760579913 33947022540079753320434935)
        ·
          refine ⟨50920533810119629980652403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33947022540079753320434935 50920533810119629980652403)
          ·
            refine ⟨76380800715179444970978605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50920533810119629980652403 76380800715179444970978605)
            ·
              refine ⟨28642800268192291864116977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76380800715179444970978605 28642800268192291864116977)
              ·
                refine ⟨21482100201144218898087733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28642800268192291864116977 21482100201144218898087733)
                ·
                  refine ⟨2013946893857270521695725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21482100201144218898087733 2013946893857270521695725)
                  ·
                    refine ⟨755230085196476445635897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2013946893857270521695725 755230085196476445635897)
                    ·
                      refine ⟨566422563897357334226923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755230085196476445635897 566422563897357334226923)
                      ·
                        rfl

theorem cell23_1103104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 3, 2, 5, 3, 2].length) (baseStart_1103104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103104 prefixEnd_1103104 := by exact prefixLift 1103104
  have htrace : WordTrace (prefixWord ++ tailWord_1103104) baseStart_1103104 baseEnd_1103104 := by
    simpa [prefixWord, tailWord_1103104, baseEnd_1103104] using wordTrace_append hprefix tailTrace_1103104
  have hstable : (prefixWord ++ tailWord_1103104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103104).length < 2 ^ (prefixWord ++ tailWord_1103104).sum := by decide
  have hdescent : baseEnd_1103104 < baseStart_1103104 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103112 : List Nat := [2, 1, 3, 2, 4, 1, 3, 2, 1, 2, 2]
def baseStart_1103112 : Nat := 118140960795 + 1103112 * 2 ^ 59
def prefixEnd_1103112 : Nat := 4983230072969 + 3 ^ 40 * 1103112 * 2
def baseEnd_1103112 : Nat := 566426671742593302926887

theorem tailTrace_1103112 : CollatzResearch.WordTrace tailWord_1103112 prefixEnd_1103112 566426671742593302926887 := by
  unfold tailWord_1103112
  simp only [CollatzResearch.WordTrace]
  refine ⟨20116899989810547687847795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26822533319747396917130393 20116899989810547687847795)
  ·
    refine ⟨30175349984715821531771693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20116899989810547687847795 30175349984715821531771693)
    ·
      refine ⟨11315756244268433074414385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30175349984715821531771693 11315756244268433074414385)
      ·
        refine ⟨8486817183201324805810789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11315756244268433074414385 8486817183201324805810789)
        ·
          refine ⟨1591278221850248401089523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8486817183201324805810789 1591278221850248401089523)
          ·
            refine ⟨2386917332775372601634285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591278221850248401089523 2386917332775372601634285)
            ·
              refine ⟨895093999790764725612857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2386917332775372601634285 895093999790764725612857)
              ·
                refine ⟨671320499843073544209643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895093999790764725612857 671320499843073544209643)
                ·
                  refine ⟨1006980749764610316314465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671320499843073544209643 1006980749764610316314465)
                  ·
                    refine ⟨755235562323457737235849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1006980749764610316314465 755235562323457737235849)
                    ·
                      refine ⟨566426671742593302926887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755235562323457737235849 566426671742593302926887)
                      ·
                        rfl

theorem cell23_1103112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 3, 2, 1, 2, 2].length) (baseStart_1103112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103112 prefixEnd_1103112 := by exact prefixLift 1103112
  have htrace : WordTrace (prefixWord ++ tailWord_1103112) baseStart_1103112 baseEnd_1103112 := by
    simpa [prefixWord, tailWord_1103112, baseEnd_1103112] using wordTrace_append hprefix tailTrace_1103112
  have hstable : (prefixWord ++ tailWord_1103112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103112).length < 2 ^ (prefixWord ++ tailWord_1103112).sum := by decide
  have hdescent : baseEnd_1103112 < baseStart_1103112 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103122 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 2, 4]
def baseStart_1103122 : Nat := 118140960795 + 1103122 * 2 ^ 59
def prefixEnd_1103122 : Nat := 4983230072969 + 3 ^ 40 * 1103122 * 2
def baseEnd_1103122 : Nat := 188810602183046087933947

theorem tailTrace_1103122 : CollatzResearch.WordTrace tailWord_1103122 prefixEnd_1103122 188810602183046087933947 := by
  unfold tailWord_1103122
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058541177396216770889905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26822776473056578055706413 10058541177396216770889905)
  ·
    refine ⟨7543905883047162578167429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10058541177396216770889905 7543905883047162578167429)
    ·
      refine ⟨1414482353071342983406393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7543905883047162578167429 1414482353071342983406393)
      ·
        refine ⟨1060861764803507237554795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1414482353071342983406393 1060861764803507237554795)
        ·
          refine ⟨1591292647205260856332193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1060861764803507237554795 1591292647205260856332193)
          ·
            refine ⟨1193469485403945642249145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1591292647205260856332193 1193469485403945642249145)
            ·
              refine ⟨895102114052959231686859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193469485403945642249145 895102114052959231686859)
              ·
                refine ⟨1342653171079438847530289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895102114052959231686859 1342653171079438847530289)
                ·
                  refine ⟨1006989878309579135647717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342653171079438847530289 1006989878309579135647717)
                  ·
                    refine ⟨188810602183046087933947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1006989878309579135647717 188810602183046087933947)
                    ·
                      rfl

theorem cell23_1103122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 2, 4].length) (baseStart_1103122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103122 prefixEnd_1103122 := by exact prefixLift 1103122
  have htrace : WordTrace (prefixWord ++ tailWord_1103122) baseStart_1103122 baseEnd_1103122 := by
    simpa [prefixWord, tailWord_1103122, baseEnd_1103122] using wordTrace_append hprefix tailTrace_1103122
  have hstable : (prefixWord ++ tailWord_1103122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103122).length < 2 ^ (prefixWord ++ tailWord_1103122).sum := by decide
  have hdescent : baseEnd_1103122 < baseStart_1103122 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103127 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 1, 8]
def baseStart_1103127 : Nat := 118140960795 + 1103127 * 2 ^ 59
def prefixEnd_1103127 : Nat := 4983230072969 + 3 ^ 40 * 1103127 * 2
def baseEnd_1103127 : Nat := 188811457984136914746439

theorem tailTrace_1103127 : CollatzResearch.WordTrace tailWord_1103127 prefixEnd_1103127 188811457984136914746439 := by
  unfold tailWord_1103127
  simp only [CollatzResearch.WordTrace]
  refine ⟨40234347074566752937491635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26822898049711168624994423 40234347074566752937491635)
  ·
    refine ⟨60351520611850129406237453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40234347074566752937491635 60351520611850129406237453)
    ·
      refine ⟨22631820229443798527339045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60351520611850129406237453 22631820229443798527339045)
      ·
        refine ⟨4243466293020712223876071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22631820229443798527339045 4243466293020712223876071)
        ·
          refine ⟨6365199439531068335814107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243466293020712223876071 6365199439531068335814107)
          ·
            refine ⟨9547799159296602503721161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6365199439531068335814107 9547799159296602503721161)
            ·
              refine ⟨7160849369472451877790871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9547799159296602503721161 7160849369472451877790871)
              ·
                refine ⟨10741274054208677816686307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7160849369472451877790871 10741274054208677816686307)
                ·
                  refine ⟨16111911081313016725029461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10741274054208677816686307 16111911081313016725029461)
                  ·
                    refine ⟨188811457984136914746439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 16111911081313016725029461 188811457984136914746439)
                    ·
                      rfl

theorem cell23_1103127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 1, 8].length) (baseStart_1103127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103127 prefixEnd_1103127 := by exact prefixLift 1103127
  have htrace : WordTrace (prefixWord ++ tailWord_1103127) baseStart_1103127 baseEnd_1103127 := by
    simpa [prefixWord, tailWord_1103127, baseEnd_1103127] using wordTrace_append hprefix tailTrace_1103127
  have hstable : (prefixWord ++ tailWord_1103127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103127).length < 2 ^ (prefixWord ++ tailWord_1103127).sum := by decide
  have hdescent : baseEnd_1103127 < baseStart_1103127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103128 : List Nat := [2, 1, 2, 3, 1, 3, 4, 1, 2, 1, 3]
def baseStart_1103128 : Nat := 118140960795 + 1103128 * 2 ^ 59
def prefixEnd_1103128 : Nat := 4983230072969 + 3 ^ 40 * 1103128 * 2
def baseEnd_1103128 : Nat := 566434887433065240326813

theorem tailTrace_1103128 : CollatzResearch.WordTrace tailWord_1103128 prefixEnd_1103128 566434887433065240326813 := by
  unfold tailWord_1103128
  simp only [CollatzResearch.WordTrace]
  refine ⟨20117191773781565054139019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26822922365042086738852025 20117191773781565054139019)
  ·
    refine ⟨30175787660672347581208529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20117191773781565054139019 30175787660672347581208529)
    ·
      refine ⟨22631840745504260685906397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30175787660672347581208529 22631840745504260685906397)
      ·
        refine ⟨8486940279564097757214899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22631840745504260685906397 8486940279564097757214899)
        ·
          refine ⟨12730410419346146635822349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486940279564097757214899 12730410419346146635822349)
          ·
            refine ⟨4773903907254804988433381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12730410419346146635822349 4773903907254804988433381)
            ·
              refine ⟨895106982610275935331259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4773903907254804988433381 895106982610275935331259)
              ·
                refine ⟨1342660473915413902996889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895106982610275935331259 1342660473915413902996889)
                ·
                  refine ⟨1006995355436560427247667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342660473915413902996889 1006995355436560427247667)
                  ·
                    refine ⟨1510493033154840640871501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1006995355436560427247667 1510493033154840640871501)
                    ·
                      refine ⟨566434887433065240326813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1510493033154840640871501 566434887433065240326813)
                      ·
                        rfl

theorem cell23_1103128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 4, 1, 2, 1, 3].length) (baseStart_1103128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103128 prefixEnd_1103128 := by exact prefixLift 1103128
  have htrace : WordTrace (prefixWord ++ tailWord_1103128) baseStart_1103128 baseEnd_1103128 := by
    simpa [prefixWord, tailWord_1103128, baseEnd_1103128] using wordTrace_append hprefix tailTrace_1103128
  have hstable : (prefixWord ++ tailWord_1103128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103128).length < 2 ^ (prefixWord ++ tailWord_1103128).sum := by decide
  have hdescent : baseEnd_1103128 < baseStart_1103128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103138 : List Nat := [3, 3, 1, 1, 4, 1, 1, 1, 3, 3, 2]
def baseStart_1103138 : Nat := 118140960795 + 1103138 * 2 ^ 59
def prefixEnd_1103138 : Nat := 4983230072969 + 3 ^ 40 * 1103138 * 2
def baseEnd_1103138 : Nat := 566440022239610201201767

theorem tailTrace_1103138 : CollatzResearch.WordTrace tailWord_1103138 prefixEnd_1103138 566440022239610201201767 := by
  unfold tailWord_1103138
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058687069381725454035517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26823165518351267877428045 10058687069381725454035517)
  ·
    refine ⟨3772007651018147045263319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10058687069381725454035517 3772007651018147045263319)
    ·
      refine ⟨5658011476527220567894979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3772007651018147045263319 5658011476527220567894979)
      ·
        refine ⟨8487017214790830851842469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5658011476527220567894979 8487017214790830851842469)
        ·
          refine ⟨1591315727773280784720463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8487017214790830851842469 1591315727773280784720463)
          ·
            refine ⟨2386973591659921177080695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591315727773280784720463 2386973591659921177080695)
            ·
              refine ⟨3580460387489881765621043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2386973591659921177080695 3580460387489881765621043)
              ·
                refine ⟨5370690581234822648431565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580460387489881765621043 5370690581234822648431565)
                ·
                  refine ⟨2014008967963058493161837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5370690581234822648431565 2014008967963058493161837)
                  ·
                    refine ⟨755253362986146934935689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2014008967963058493161837 755253362986146934935689)
                    ·
                      refine ⟨566440022239610201201767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755253362986146934935689 566440022239610201201767)
                      ·
                        rfl

theorem cell23_1103138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_1103138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103138 prefixEnd_1103138 := by exact prefixLift 1103138
  have htrace : WordTrace (prefixWord ++ tailWord_1103138) baseStart_1103138 baseEnd_1103138 := by
    simpa [prefixWord, tailWord_1103138, baseEnd_1103138] using wordTrace_append hprefix tailTrace_1103138
  have hstable : (prefixWord ++ tailWord_1103138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103138).length < 2 ^ (prefixWord ++ tailWord_1103138).sum := by decide
  have hdescent : baseEnd_1103138 < baseStart_1103138 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103154 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5]
def baseStart_1103154 : Nat := 118140960795 + 1103154 * 2 ^ 59
def prefixEnd_1103154 : Nat := 4983230072969 + 3 ^ 40 * 1103154 * 2
def baseEnd_1103154 : Nat := 566448237930082138601693

theorem tailTrace_1103154 : CollatzResearch.WordTrace tailWord_1103154 prefixEnd_1103154 566448237930082138601693 := by
  unfold tailWord_1103154
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058832961367234137181129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26823554563645957699149677 10058832961367234137181129)
  ·
    refine ⟨7544124721025425602885847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10058832961367234137181129 7544124721025425602885847)
    ·
      refine ⟨11316187081538138404328771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7544124721025425602885847 11316187081538138404328771)
      ·
        refine ⟨16974280622307207606493157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11316187081538138404328771 16974280622307207606493157)
        ·
          refine ⟨3182677616682601426217467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16974280622307207606493157 3182677616682601426217467)
          ·
            refine ⟨4774016425023902139326201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182677616682601426217467 4774016425023902139326201)
            ·
              refine ⟨3580512318767926604494651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4774016425023902139326201 3580512318767926604494651)
              ·
                refine ⟨5370768478151889906741977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580512318767926604494651 5370768478151889906741977)
                ·
                  refine ⟨4028076358613917430056483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5370768478151889906741977 4028076358613917430056483)
                  ·
                    refine ⟨6042114537920876145084725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4028076358613917430056483 6042114537920876145084725)
                    ·
                      refine ⟨566448237930082138601693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6042114537920876145084725 566448237930082138601693)
                      ·
                        rfl

theorem cell23_1103154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 2, 1, 5].length) (baseStart_1103154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103154 prefixEnd_1103154 := by exact prefixLift 1103154
  have htrace : WordTrace (prefixWord ++ tailWord_1103154) baseStart_1103154 baseEnd_1103154 := by
    simpa [prefixWord, tailWord_1103154, baseEnd_1103154] using wordTrace_append hprefix tailTrace_1103154
  have hstable : (prefixWord ++ tailWord_1103154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103154).length < 2 ^ (prefixWord ++ tailWord_1103154).sum := by decide
  have hdescent : baseEnd_1103154 < baseStart_1103154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103168 : List Nat := [2, 1, 1, 2, 2, 1, 6, 2, 2, 2, 2]
def baseStart_1103168 : Nat := 118140960795 + 1103168 * 2 ^ 59
def prefixEnd_1103168 : Nat := 4983230072969 + 3 ^ 40 * 1103168 * 2
def baseEnd_1103168 : Nat := 566455426659245083826629

theorem tailTrace_1103168 : CollatzResearch.WordTrace tailWord_1103168 prefixEnd_1103168 566455426659245083826629 := by
  unfold tailWord_1103168
  simp only [CollatzResearch.WordTrace]
  refine ⟨20117921233709108469867079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26823894978278811293156105 20117921233709108469867079)
  ·
    refine ⟨30176881850563662704800619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20117921233709108469867079 30176881850563662704800619)
    ·
      refine ⟨45265322775845494057200929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30176881850563662704800619 45265322775845494057200929)
      ·
        refine ⟨33948992081884120542900697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45265322775845494057200929 33948992081884120542900697)
        ·
          refine ⟨25461744061413090407175523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33948992081884120542900697 25461744061413090407175523)
          ·
            refine ⟨38192616092119635610763285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25461744061413090407175523 38192616092119635610763285)
            ·
              refine ⟨1790278879318107919254529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 38192616092119635610763285 1790278879318107919254529)
              ·
                refine ⟨1342709159488580939440897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790278879318107919254529 1342709159488580939440897)
                ·
                  refine ⟨1007031869616435704580673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1342709159488580939440897 1007031869616435704580673)
                  ·
                    refine ⟨755273902212326778435505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1007031869616435704580673 755273902212326778435505)
                    ·
                      refine ⟨566455426659245083826629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755273902212326778435505 566455426659245083826629)
                      ·
                        rfl

theorem cell23_1103168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 6, 2, 2, 2, 2].length) (baseStart_1103168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103168 prefixEnd_1103168 := by exact prefixLift 1103168
  have htrace : WordTrace (prefixWord ++ tailWord_1103168) baseStart_1103168 baseEnd_1103168 := by
    simpa [prefixWord, tailWord_1103168, baseEnd_1103168] using wordTrace_append hprefix tailTrace_1103168
  have hstable : (prefixWord ++ tailWord_1103168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103168).length < 2 ^ (prefixWord ++ tailWord_1103168).sum := by decide
  have hdescent : baseEnd_1103168 < baseStart_1103168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103184 : List Nat := [2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3]
def baseStart_1103184 : Nat := 118140960795 + 1103184 * 2 ^ 59
def prefixEnd_1103184 : Nat := 4983230072969 + 3 ^ 40 * 1103184 * 2
def baseEnd_1103184 : Nat := 566463642349717021226555

theorem tailTrace_1103184 : CollatzResearch.WordTrace tailWord_1103184 prefixEnd_1103184 566463642349717021226555 := by
  unfold tailWord_1103184
  simp only [CollatzResearch.WordTrace]
  refine ⟨20118213017680125836158303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26824284023573501114877737 20118213017680125836158303)
  ·
    refine ⟨30177319526520188754237455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20118213017680125836158303 30177319526520188754237455)
    ·
      refine ⟨45265979289780283131356183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30177319526520188754237455 45265979289780283131356183)
      ·
        refine ⟨67898968934670424697034275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45265979289780283131356183 67898968934670424697034275)
        ·
          refine ⟨101848453402005637045551413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67898968934670424697034275 101848453402005637045551413)
          ·
            refine ⟨9548292506438028473020445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101848453402005637045551413 9548292506438028473020445)
            ·
              refine ⟨3580609689914260677382667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9548292506438028473020445 3580609689914260677382667)
              ·
                refine ⟨5370914534871391016074001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580609689914260677382667 5370914534871391016074001)
                ·
                  refine ⟨4028185901153543262055501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5370914534871391016074001 4028185901153543262055501)
                  ·
                    refine ⟨1510569712932578723270813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4028185901153543262055501 1510569712932578723270813)
                    ·
                      refine ⟨566463642349717021226555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1510569712932578723270813 566463642349717021226555)
                      ·
                        rfl

theorem cell23_1103184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 1, 2, 3, 3].length) (baseStart_1103184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103184 prefixEnd_1103184 := by exact prefixLift 1103184
  have htrace : WordTrace (prefixWord ++ tailWord_1103184) baseStart_1103184 baseEnd_1103184 := by
    simpa [prefixWord, tailWord_1103184, baseEnd_1103184] using wordTrace_append hprefix tailTrace_1103184
  have hstable : (prefixWord ++ tailWord_1103184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103184).length < 2 ^ (prefixWord ++ tailWord_1103184).sum := by decide
  have hdescent : baseEnd_1103184 < baseStart_1103184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103187 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 1, 7]
def baseStart_1103187 : Nat := 118140960795 + 1103187 * 2 ^ 59
def prefixEnd_1103187 : Nat := 4983230072969 + 3 ^ 40 * 1103187 * 2
def baseEnd_1103187 : Nat := 188821727597226836496347

theorem tailTrace_1103187 : CollatzResearch.WordTrace tailWord_1103187 prefixEnd_1103187 188821727597226836496347 := by
  unfold tailWord_1103187
  simp only [CollatzResearch.WordTrace]
  refine ⟨40236535454349383184675815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26824356969566255456450543 40236535454349383184675815)
  ·
    refine ⟨60354803181524074777013723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40236535454349383184675815 60354803181524074777013723)
    ·
      refine ⟨90532204772286112165520585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60354803181524074777013723 90532204772286112165520585)
      ·
        refine ⟨67899153579214584124140439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90532204772286112165520585 67899153579214584124140439)
        ·
          refine ⟨101848730368821876186210659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67899153579214584124140439 101848730368821876186210659)
          ·
            refine ⟨152773095553232814279315989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101848730368821876186210659 152773095553232814279315989)
            ·
              refine ⟨7161238854057788169342937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 152773095553232814279315989 7161238854057788169342937)
              ·
                refine ⟨5370929140543341127007203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7161238854057788169342937 5370929140543341127007203)
                ·
                  refine ⟨8056393710815011690510805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5370929140543341127007203 8056393710815011690510805)
                  ·
                    refine ⟨188821727597226836496347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8056393710815011690510805 188821727597226836496347)
                    ·
                      rfl

theorem cell23_1103187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 1, 7].length) (baseStart_1103187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103187 prefixEnd_1103187 := by exact prefixLift 1103187
  have htrace : WordTrace (prefixWord ++ tailWord_1103187) baseStart_1103187 baseEnd_1103187 := by
    simpa [prefixWord, tailWord_1103187, baseEnd_1103187] using wordTrace_append hprefix tailTrace_1103187
  have hstable : (prefixWord ++ tailWord_1103187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103187).length < 2 ^ (prefixWord ++ tailWord_1103187).sum := by decide
  have hdescent : baseEnd_1103187 < baseStart_1103187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103204 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 1, 7]
def baseStart_1103204 : Nat := 118140960795 + 1103204 * 2 ^ 59
def prefixEnd_1103204 : Nat := 4983230072969 + 3 ^ 40 * 1103204 * 2
def baseEnd_1103204 : Nat := 188824637320935647658821

theorem tailTrace_1103204 : CollatzResearch.WordTrace tailWord_1103204 prefixEnd_1103204 188824637320935647658821 := by
  unfold tailWord_1103204
  simp only [CollatzResearch.WordTrace]
  refine ⟨20118577747643897544022333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26824770330191863392029777 20118577747643897544022333)
  ·
    refine ⟨7544466655366461579008375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20118577747643897544022333 7544466655366461579008375)
    ·
      refine ⟨11316699983049692368512563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7544466655366461579008375 11316699983049692368512563)
      ·
        refine ⟨16975049974574538552768845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11316699983049692368512563 16975049974574538552768845)
        ·
          refine ⟨6365643740465451957288317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16975049974574538552768845 6365643740465451957288317)
          ·
            refine ⟨2387116402674544483983119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6365643740465451957288317 2387116402674544483983119)
            ·
              refine ⟨3580674604011816725974679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387116402674544483983119 3580674604011816725974679)
              ·
                refine ⟨5371011906017725088962019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580674604011816725974679 5371011906017725088962019)
                ·
                  refine ⟨8056517859026587633443029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5371011906017725088962019 8056517859026587633443029)
                  ·
                    refine ⟨188824637320935647658821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8056517859026587633443029 188824637320935647658821)
                    ·
                      rfl

theorem cell23_1103204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_1103204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103204 prefixEnd_1103204 := by exact prefixLift 1103204
  have htrace : WordTrace (prefixWord ++ tailWord_1103204) baseStart_1103204 baseEnd_1103204 := by
    simpa [prefixWord, tailWord_1103204, baseEnd_1103204] using wordTrace_append hprefix tailTrace_1103204
  have hstable : (prefixWord ++ tailWord_1103204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103204).length < 2 ^ (prefixWord ++ tailWord_1103204).sum := by decide
  have hdescent : baseEnd_1103204 < baseStart_1103204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103208 : List Nat := [2, 1, 4, 2, 3, 1, 2, 3, 5]
def baseStart_1103208 : Nat := 118140960795 + 1103208 * 2 ^ 59
def prefixEnd_1103208 : Nat := 4983230072969 + 3 ^ 40 * 1103208 * 2
def baseEnd_1103208 : Nat := 62941773987269436369605

theorem tailTrace_1103208 : CollatzResearch.WordTrace tailWord_1103208 prefixEnd_1103208 62941773987269436369605 := by
  unfold tailWord_1103208
  simp only [CollatzResearch.WordTrace]
  refine ⟨20118650693636651885595139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26824867591515535847460185 20118650693636651885595139)
  ·
    refine ⟨30177976040454977828392709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20118650693636651885595139 30177976040454977828392709)
    ·
      refine ⟨5658370507585308342823633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30177976040454977828392709 5658370507585308342823633)
      ·
        refine ⟨4243777880688981257117725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5658370507585308342823633 4243777880688981257117725)
        ·
          refine ⟨1591416705258367971419147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4243777880688981257117725 1591416705258367971419147)
          ·
            refine ⟨2387125057887551957128721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591416705258367971419147 2387125057887551957128721)
            ·
              refine ⟨1790343793415663967846541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387125057887551957128721 1790343793415663967846541)
              ·
                refine ⟨671378922530873987942453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1790343793415663967846541 671378922530873987942453)
                ·
                  refine ⟨62941773987269436369605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 671378922530873987942453 62941773987269436369605)
                  ·
                    rfl

theorem cell23_1103208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 2, 3, 5].length) (baseStart_1103208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103208 prefixEnd_1103208 := by exact prefixLift 1103208
  have htrace : WordTrace (prefixWord ++ tailWord_1103208) baseStart_1103208 baseEnd_1103208 := by
    simpa [prefixWord, tailWord_1103208, baseEnd_1103208] using wordTrace_append hprefix tailTrace_1103208
  have hstable : (prefixWord ++ tailWord_1103208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103208).length < 2 ^ (prefixWord ++ tailWord_1103208).sum := by decide
  have hdescent : baseEnd_1103208 < baseStart_1103208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103244 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 3, 4, 3]
def baseStart_1103244 : Nat := 118140960795 + 1103244 * 2 ^ 59
def prefixEnd_1103244 : Nat := 4983230072969 + 3 ^ 40 * 1103244 * 2
def baseEnd_1103244 : Nat := 566494451188986786476279

theorem tailTrace_1103244 : CollatzResearch.WordTrace tailWord_1103244 prefixEnd_1103244 566494451188986786476279 := by
  unfold tailWord_1103244
  simp only [CollatzResearch.WordTrace]
  refine ⟨20119307207571440959750393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26825742943428587946333857 20119307207571440959750393)
  ·
    refine ⟨15089480405678580719812795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20119307207571440959750393 15089480405678580719812795)
    ·
      refine ⟨22634220608517871079719193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15089480405678580719812795 22634220608517871079719193)
      ·
        refine ⟨16975665456388403309789395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22634220608517871079719193 16975665456388403309789395)
        ·
          refine ⟨25463498184582604964684093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16975665456388403309789395 25463498184582604964684093)
          ·
            refine ⟨9548811819218476861756535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25463498184582604964684093 9548811819218476861756535)
            ·
              refine ⟨14323217728827715292634803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9548811819218476861756535 14323217728827715292634803)
              ·
                refine ⟨21484826593241572938952205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14323217728827715292634803 21484826593241572938952205)
                ·
                  refine ⟨8056809972465589852107077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21484826593241572938952205 8056809972465589852107077)
                  ·
                    refine ⟨1510651869837298097270077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8056809972465589852107077 1510651869837298097270077)
                    ·
                      refine ⟨566494451188986786476279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1510651869837298097270077 566494451188986786476279)
                      ·
                        rfl

theorem cell23_1103244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 3, 4, 3].length) (baseStart_1103244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103244 prefixEnd_1103244 := by exact prefixLift 1103244
  have htrace : WordTrace (prefixWord ++ tailWord_1103244) baseStart_1103244 baseEnd_1103244 := by
    simpa [prefixWord, tailWord_1103244, baseEnd_1103244] using wordTrace_append hprefix tailTrace_1103244
  have hstable : (prefixWord ++ tailWord_1103244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103244).length < 2 ^ (prefixWord ++ tailWord_1103244).sum := by decide
  have hdescent : baseEnd_1103244 < baseStart_1103244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103261 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 3]
def baseStart_1103261 : Nat := 118140960795 + 1103261 * 2 ^ 59
def prefixEnd_1103261 : Nat := 4983230072969 + 3 ^ 40 * 1103261 * 2
def baseEnd_1103261 : Nat := 566503180360113219963701

theorem tailTrace_1103261 : CollatzResearch.WordTrace tailWord_1103261 prefixEnd_1103261 566503180360113219963701 := by
  unfold tailWord_1103261
  simp only [CollatzResearch.WordTrace]
  refine ⟨40239234456081293822869637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26826156304054195881913091 40239234456081293822869637)
  ·
    refine ⟨7544856460515242591788057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40239234456081293822869637 7544856460515242591788057)
    ·
      refine ⟨5658642345386431943841043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7544856460515242591788057 5658642345386431943841043)
      ·
        refine ⟨8487963518079647915761565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5658642345386431943841043 8487963518079647915761565)
        ·
          refine ⟨3182986319279867968410587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8487963518079647915761565 3182986319279867968410587)
          ·
            refine ⟨4774479478919801952615881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182986319279867968410587 4774479478919801952615881)
            ·
              refine ⟨3580859609189851464461911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4774479478919801952615881 3580859609189851464461911)
              ·
                refine ⟨5371289413784777196692867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580859609189851464461911 5371289413784777196692867)
                ·
                  refine ⟨8056934120677165795039301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5371289413784777196692867 8056934120677165795039301)
                  ·
                    refine ⟨1510675147626968586569869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8056934120677165795039301 1510675147626968586569869)
                    ·
                      refine ⟨566503180360113219963701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1510675147626968586569869 566503180360113219963701)
                      ·
                        rfl

theorem cell23_1103261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 1, 4, 3].length) (baseStart_1103261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103261 prefixEnd_1103261 := by exact prefixLift 1103261
  have htrace : WordTrace (prefixWord ++ tailWord_1103261) baseStart_1103261 baseEnd_1103261 := by
    simpa [prefixWord, tailWord_1103261, baseEnd_1103261] using wordTrace_append hprefix tailTrace_1103261
  have hstable : (prefixWord ++ tailWord_1103261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103261).length < 2 ^ (prefixWord ++ tailWord_1103261).sum := by decide
  have hdescent : baseEnd_1103261 < baseStart_1103261 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103294 : List Nat := [4, 2, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_1103294 : Nat := 118140960795 + 1103294 * 2 ^ 59
def prefixEnd_1103294 : Nat := 4983230072969 + 3 ^ 40 * 1103294 * 2
def baseEnd_1103294 : Nat := 188840041740570530283683

theorem tailTrace_1103294 : CollatzResearch.WordTrace tailWord_1103294 prefixEnd_1103294 188840041740570530283683 := by
  unfold tailWord_1103294
  simp only [CollatzResearch.WordTrace]
  refine ⟨5030054758120217557352617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26826958709974493639213957 5030054758120217557352617)
  ·
    refine ⟨3772541068590163168014463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5030054758120217557352617 3772541068590163168014463)
    ·
      refine ⟨5658811602885244752021695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3772541068590163168014463 5658811602885244752021695)
      ·
        refine ⟨8488217404327867128032543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5658811602885244752021695 8488217404327867128032543)
        ·
          refine ⟨12732326106491800692048815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8488217404327867128032543 12732326106491800692048815)
          ·
            refine ⟨19098489159737701038073223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12732326106491800692048815 19098489159737701038073223)
            ·
              refine ⟨28647733739606551557109835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19098489159737701038073223 28647733739606551557109835)
              ·
                refine ⟨42971600609409827335664753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28647733739606551557109835 42971600609409827335664753)
                ·
                  refine ⟨32228700457057370501748565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42971600609409827335664753 32228700457057370501748565)
                  ·
                    refine ⟨188840041740570530283683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 32228700457057370501748565 188840041740570530283683)
                    ·
                      rfl

theorem cell23_1103294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_1103294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103294 prefixEnd_1103294 := by exact prefixLift 1103294
  have htrace : WordTrace (prefixWord ++ tailWord_1103294) baseStart_1103294 baseEnd_1103294 := by
    simpa [prefixWord, tailWord_1103294, baseEnd_1103294] using wordTrace_append hprefix tailTrace_1103294
  have hstable : (prefixWord ++ tailWord_1103294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103294).length < 2 ^ (prefixWord ++ tailWord_1103294).sum := by decide
  have hdescent : baseEnd_1103294 < baseStart_1103294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103311 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 1, 5]
def baseStart_1103311 : Nat := 118140960795 + 1103311 * 2 ^ 59
def prefixEnd_1103311 : Nat := 4983230072969 + 3 ^ 40 * 1103311 * 2
def baseEnd_1103311 : Nat := 188842951464279341446157

theorem tailTrace_1103311 : CollatzResearch.WordTrace tailWord_1103311 prefixEnd_1103311 188842951464279341446157 := by
  unfold tailWord_1103311
  simp only [CollatzResearch.WordTrace]
  refine ⟨40241058105900152362189787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26827372070600101574793191 40241058105900152362189787)
  ·
    refine ⟨60361587158850228543284681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40241058105900152362189787 60361587158850228543284681)
    ·
      refine ⟨45271190369137671407463511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60361587158850228543284681 45271190369137671407463511)
      ·
        refine ⟨67906785553706507111195267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45271190369137671407463511 67906785553706507111195267)
        ·
          refine ⟨101860178330559760666792901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67906785553706507111195267 101860178330559760666792901)
          ·
            refine ⟨19098783436979955125023669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101860178330559760666792901 19098783436979955125023669)
            ·
              refine ⟨1790510947216870792970969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19098783436979955125023669 1790510947216870792970969)
              ·
                refine ⟨1342883210412653094728227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1790510947216870792970969 1342883210412653094728227)
                ·
                  refine ⟨2014324815618979642092341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1342883210412653094728227 2014324815618979642092341)
                  ·
                    refine ⟨188842951464279341446157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2014324815618979642092341 188842951464279341446157)
                    ·
                      rfl

theorem cell23_1103311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 1, 5].length) (baseStart_1103311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103311 prefixEnd_1103311 := by exact prefixLift 1103311
  have htrace : WordTrace (prefixWord ++ tailWord_1103311) baseStart_1103311 baseEnd_1103311 := by
    simpa [prefixWord, tailWord_1103311, baseEnd_1103311] using wordTrace_append hprefix tailTrace_1103311
  have hstable : (prefixWord ++ tailWord_1103311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103311).length < 2 ^ (prefixWord ++ tailWord_1103311).sum := by decide
  have hdescent : baseEnd_1103311 < baseStart_1103311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103438 : List Nat := [4, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2]
def baseStart_1103438 : Nat := 118140960795 + 1103438 * 2 ^ 59
def prefixEnd_1103438 : Nat := 4983230072969 + 3 ^ 40 * 1103438 * 2
def baseEnd_1103438 : Nat := 566594066435959027450387

theorem tailTrace_1103438 : CollatzResearch.WordTrace tailWord_1103438 prefixEnd_1103438 566594066435959027450387 := by
  unfold tailWord_1103438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5030711272055006631507871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26830460117626702034708645 5030711272055006631507871)
  ·
    refine ⟨7546066908082509947261807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5030711272055006631507871 7546066908082509947261807)
    ·
      refine ⟨11319100362123764920892711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7546066908082509947261807 11319100362123764920892711)
      ·
        refine ⟨16978650543185647381339067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11319100362123764920892711 16978650543185647381339067)
        ·
          refine ⟨25467975814778471072008601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16978650543185647381339067 25467975814778471072008601)
          ·
            refine ⟨19100981861083853304006451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25467975814778471072008601 19100981861083853304006451)
            ·
              refine ⟨28651472791625779956009677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19100981861083853304006451 28651472791625779956009677)
              ·
                refine ⟨10744302296859667483503629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28651472791625779956009677 10744302296859667483503629)
                ·
                  refine ⟨4029113361322375306313861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10744302296859667483503629 4029113361322375306313861)
                  ·
                    refine ⟨755458755247945369933849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029113361322375306313861 755458755247945369933849)
                    ·
                      refine ⟨566594066435959027450387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755458755247945369933849 566594066435959027450387)
                      ·
                        rfl

theorem cell23_1103438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 1, 3, 3, 4, 2].length) (baseStart_1103438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103438 prefixEnd_1103438 := by exact prefixLift 1103438
  have htrace : WordTrace (prefixWord ++ tailWord_1103438) baseStart_1103438 baseEnd_1103438 := by
    simpa [prefixWord, tailWord_1103438, baseEnd_1103438] using wordTrace_append hprefix tailTrace_1103438
  have hstable : (prefixWord ++ tailWord_1103438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103438).length < 2 ^ (prefixWord ++ tailWord_1103438).sum := by decide
  have hdescent : baseEnd_1103438 < baseStart_1103438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103441 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 5]
def baseStart_1103441 : Nat := 118140960795 + 1103441 * 2 ^ 59
def prefixEnd_1103441 : Nat := 4983230072969 + 3 ^ 40 * 1103441 * 2
def baseEnd_1103441 : Nat := 566595606877922515712873

theorem tailTrace_1103441 : CollatzResearch.WordTrace tailWord_1103441 prefixEnd_1103441 566595606877922515712873 := by
  unfold tailWord_1103441
  simp only [CollatzResearch.WordTrace]
  refine ⟨40245799595429184564422177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26830533063619456376281451 40245799595429184564422177)
  ·
    refine ⟨30184349696571888423316633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40245799595429184564422177 30184349696571888423316633)
    ·
      refine ⟨22638262272428916317487475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30184349696571888423316633 22638262272428916317487475)
      ·
        refine ⟨33957393408643374476231213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22638262272428916317487475 33957393408643374476231213)
        ·
          refine ⟨12734022528241265428586705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33957393408643374476231213 12734022528241265428586705)
          ·
            refine ⟨9550516896180949071440029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12734022528241265428586705 9550516896180949071440029)
            ·
              refine ⟨3581443836067855901790011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9550516896180949071440029 3581443836067855901790011)
              ·
                refine ⟨5372165754101783852685017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581443836067855901790011 5372165754101783852685017)
                ·
                  refine ⟨4029124315576337889513763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5372165754101783852685017 4029124315576337889513763)
                  ·
                    refine ⟨6043686473364506834270645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4029124315576337889513763 6043686473364506834270645)
                    ·
                      refine ⟨566595606877922515712873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6043686473364506834270645 566595606877922515712873)
                      ·
                        rfl

theorem cell23_1103441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 2, 1, 5].length) (baseStart_1103441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103441 prefixEnd_1103441 := by exact prefixLift 1103441
  have htrace : WordTrace (prefixWord ++ tailWord_1103441) baseStart_1103441 baseEnd_1103441 := by
    simpa [prefixWord, tailWord_1103441, baseEnd_1103441] using wordTrace_append hprefix tailTrace_1103441
  have hstable : (prefixWord ++ tailWord_1103441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103441).length < 2 ^ (prefixWord ++ tailWord_1103441).sum := by decide
  have hdescent : baseEnd_1103441 < baseStart_1103441 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103471 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 3]
def baseStart_1103471 : Nat := 118140960795 + 1103471 * 2 ^ 59
def prefixEnd_1103471 : Nat := 4983230072969 + 3 ^ 40 * 1103471 * 2
def baseEnd_1103471 : Nat := 566611011297557398337735

theorem tailTrace_1103471 : CollatzResearch.WordTrace tailWord_1103471 prefixEnd_1103471 566611011297557398337735 := by
  unfold tailWord_1103471
  simp only [CollatzResearch.WordTrace]
  refine ⟨40246893785320499688014267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26831262523546999792009511 40246893785320499688014267)
  ·
    refine ⟨60370340677980749532021401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40246893785320499688014267 60370340677980749532021401)
    ·
      refine ⟨45277755508485562149016051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60370340677980749532021401 45277755508485562149016051)
      ·
        refine ⟨67916633262728343223524077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45277755508485562149016051 67916633262728343223524077)
        ·
          refine ⟨25468737473523128708821529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67916633262728343223524077 25468737473523128708821529)
          ·
            refine ⟨19101553105142346531616147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25468737473523128708821529 19101553105142346531616147)
            ·
              refine ⟨28652329657713519797424221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19101553105142346531616147 28652329657713519797424221)
              ·
                refine ⟨10744623621642569924034083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28652329657713519797424221 10744623621642569924034083)
                ·
                  refine ⟨16116935432463854886051125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10744623621642569924034083 16116935432463854886051125)
                  ·
                    refine ⟨1510962696793486395567293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16116935432463854886051125 1510962696793486395567293)
                    ·
                      refine ⟨566611011297557398337735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1510962696793486395567293 566611011297557398337735)
                      ·
                        rfl

theorem cell23_1103471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 1, 5, 3].length) (baseStart_1103471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103471 prefixEnd_1103471 := by exact prefixLift 1103471
  have htrace : WordTrace (prefixWord ++ tailWord_1103471) baseStart_1103471 baseEnd_1103471 := by
    simpa [prefixWord, tailWord_1103471, baseEnd_1103471] using wordTrace_append hprefix tailTrace_1103471
  have hstable : (prefixWord ++ tailWord_1103471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103471).length < 2 ^ (prefixWord ++ tailWord_1103471).sum := by decide
  have hdescent : baseEnd_1103471 < baseStart_1103471 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103472 : List Nat := [2, 1, 1, 1, 6, 2, 1, 3, 2, 2, 2]
def baseStart_1103472 : Nat := 118140960795 + 1103472 * 2 ^ 59
def prefixEnd_1103472 : Nat := 4983230072969 + 3 ^ 40 * 1103472 * 2
def baseEnd_1103472 : Nat := 566611524778211894425231

theorem tailTrace_1103472 : CollatzResearch.WordTrace tailWord_1103472 prefixEnd_1103472 566611524778211894425231 := by
  unfold tailWord_1103472
  simp only [CollatzResearch.WordTrace]
  refine ⟨20123465129158438429400335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26831286838877917905867113 20123465129158438429400335)
  ·
    refine ⟨30185197693737657644100503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20123465129158438429400335 30185197693737657644100503)
    ·
      refine ⟨45277796540606486466150755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30185197693737657644100503 45277796540606486466150755)
      ·
        refine ⟨67916694810909729699226133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45277796540606486466150755 67916694810909729699226133)
        ·
          refine ⟨3183595069261393579651225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 67916694810909729699226133 3183595069261393579651225)
          ·
            refine ⟨2387696301946045184738419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3183595069261393579651225 2387696301946045184738419)
            ·
              refine ⟨3581544452919067777107629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387696301946045184738419 3581544452919067777107629)
              ·
                refine ⟨1343079169844650416415361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3581544452919067777107629 1343079169844650416415361)
                ·
                  refine ⟨1007309377383487812311521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1343079169844650416415361 1007309377383487812311521)
                  ·
                    refine ⟨755482033037615859233641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1007309377383487812311521 755482033037615859233641)
                    ·
                      refine ⟨566611524778211894425231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755482033037615859233641 566611524778211894425231)
                      ·
                        rfl

theorem cell23_1103472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 3, 2, 2, 2].length) (baseStart_1103472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103472 prefixEnd_1103472 := by exact prefixLift 1103472
  have htrace : WordTrace (prefixWord ++ tailWord_1103472) baseStart_1103472 baseEnd_1103472 := by
    simpa [prefixWord, tailWord_1103472, baseEnd_1103472] using wordTrace_append hprefix tailTrace_1103472
  have hstable : (prefixWord ++ tailWord_1103472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103472).length < 2 ^ (prefixWord ++ tailWord_1103472).sum := by decide
  have hdescent : baseEnd_1103472 < baseStart_1103472 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103512 : List Nat := [2, 1, 2, 4, 1, 4, 2, 2, 5]
def baseStart_1103512 : Nat := 118140960795 + 1103512 * 2 ^ 59
def prefixEnd_1103512 : Nat := 4983230072969 + 3 ^ 40 * 1103512 * 2
def baseEnd_1103512 : Nat := 62959118222710193102783

theorem tailTrace_1103512 : CollatzResearch.WordTrace tailWord_1103512 prefixEnd_1103512 62959118222710193102783 := by
  unfold tailWord_1103512
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124194589085981845128395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26832259452114642460171193 20124194589085981845128395)
  ·
    refine ⟨30186291883628972767692593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20124194589085981845128395 30186291883628972767692593)
    ·
      refine ⟨22639718912721729575769445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30186291883628972767692593 22639718912721729575769445)
      ·
        refine ⟨4244947296135324295456771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22639718912721729575769445 4244947296135324295456771)
        ·
          refine ⟨6367420944202986443185157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244947296135324295456771 6367420944202986443185157)
          ·
            refine ⟨1193891427038059958097217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6367420944202986443185157 1193891427038059958097217)
            ·
              refine ⟨895418570278544968572913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1193891427038059958097217 895418570278544968572913)
              ·
                refine ⟨671563927708908726429685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895418570278544968572913 671563927708908726429685)
                ·
                  refine ⟨62959118222710193102783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 671563927708908726429685 62959118222710193102783)
                  ·
                    rfl

theorem cell23_1103512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 5].length) (baseStart_1103512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103512 prefixEnd_1103512 := by exact prefixLift 1103512
  have htrace : WordTrace (prefixWord ++ tailWord_1103512) baseStart_1103512 baseEnd_1103512 := by
    simpa [prefixWord, tailWord_1103512, baseEnd_1103512] using wordTrace_append hprefix tailTrace_1103512
  have hstable : (prefixWord ++ tailWord_1103512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103512).length < 2 ^ (prefixWord ++ tailWord_1103512).sum := by decide
  have hdescent : baseEnd_1103512 < baseStart_1103512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103522 : List Nat := [3, 3, 1, 4, 1, 1, 1, 1, 2, 3, 3]
def baseStart_1103522 : Nat := 118140960795 + 1103522 * 2 ^ 59
def prefixEnd_1103522 : Nat := 4983230072969 + 3 ^ 40 * 1103522 * 2
def baseEnd_1103522 : Nat := 566637198810936698800001

theorem tailTrace_1103522 : CollatzResearch.WordTrace tailWord_1103522 prefixEnd_1103522 566637198810936698800001 := by
  unfold tailWord_1103522
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062188477033933849530205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26832502605423823598747213 10062188477033933849530205)
  ·
    refine ⟨3773320678887725193573827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10062188477033933849530205 3773320678887725193573827)
    ·
      refine ⟨5659981018331587790360741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3773320678887725193573827 5659981018331587790360741)
      ·
        refine ⟨1061246440937172710692639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5659981018331587790360741 1061246440937172710692639)
        ·
          refine ⟨1591869661405759066038959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061246440937172710692639 1591869661405759066038959)
          ·
            refine ⟨2387804492108638599058439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1591869661405759066038959 2387804492108638599058439)
            ·
              refine ⟨3581706738162957898587659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2387804492108638599058439 3581706738162957898587659)
              ·
                refine ⟨5372560107244436847881489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581706738162957898587659 5372560107244436847881489)
                ·
                  refine ⟨4029420080433327635911117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5372560107244436847881489 4029420080433327635911117)
                  ·
                    refine ⟨1511032530162497863466669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4029420080433327635911117 1511032530162497863466669)
                    ·
                      refine ⟨566637198810936698800001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1511032530162497863466669 566637198810936698800001)
                      ·
                        rfl

theorem cell23_1103522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_1103522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103522 prefixEnd_1103522 := by exact prefixLift 1103522
  have htrace : WordTrace (prefixWord ++ tailWord_1103522) baseStart_1103522 baseEnd_1103522 := by
    simpa [prefixWord, tailWord_1103522, baseEnd_1103522] using wordTrace_append hprefix tailTrace_1103522
  have hstable : (prefixWord ++ tailWord_1103522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103522).length < 2 ^ (prefixWord ++ tailWord_1103522).sum := by decide
  have hdescent : baseEnd_1103522 < baseStart_1103522 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103538 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 5, 4]
def baseStart_1103538 : Nat := 118140960795 + 1103538 * 2 ^ 59
def prefixEnd_1103538 : Nat := 4983230072969 + 3 ^ 40 * 1103538 * 2
def baseEnd_1103538 : Nat := 188881804833802878733309

theorem tailTrace_1103538 : CollatzResearch.WordTrace tailWord_1103538 prefixEnd_1103538 188881804833802878733309 := by
  unfold tailWord_1103538
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062334369019442532675817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26832891650718513420468845 10062334369019442532675817)
  ·
    refine ⟨7546750776764581899506863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10062334369019442532675817 7546750776764581899506863)
    ·
      refine ⟨11320126165146872849260295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7546750776764581899506863 11320126165146872849260295)
      ·
        refine ⟨16980189247720309273890443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11320126165146872849260295 16980189247720309273890443)
        ·
          refine ⟨25470283871580463910835665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16980189247720309273890443 25470283871580463910835665)
          ·
            refine ⟨19102712903685347933126749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25470283871580463910835665 19102712903685347933126749)
            ·
              refine ⟨7163517338882005474922531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19102712903685347933126749 7163517338882005474922531)
              ·
                refine ⟨10745276008323008212383797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7163517338882005474922531 10745276008323008212383797)
                ·
                  refine ⟨1007369625780282019910981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10745276008323008212383797 1007369625780282019910981)
                  ·
                    refine ⟨188881804833802878733309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1007369625780282019910981 188881804833802878733309)
                    ·
                      rfl

theorem cell23_1103538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 5, 4].length) (baseStart_1103538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103538 prefixEnd_1103538 := by exact prefixLift 1103538
  have htrace : WordTrace (prefixWord ++ tailWord_1103538) baseStart_1103538 baseEnd_1103538 := by
    simpa [prefixWord, tailWord_1103538, baseEnd_1103538] using wordTrace_append hprefix tailTrace_1103538
  have hstable : (prefixWord ++ tailWord_1103538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103538).length < 2 ^ (prefixWord ++ tailWord_1103538).sum := by decide
  have hdescent : baseEnd_1103538 < baseStart_1103538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103542 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 2, 5]
def baseStart_1103542 : Nat := 118140960795 + 1103542 * 2 ^ 59
def prefixEnd_1103542 : Nat := 4983230072969 + 3 ^ 40 * 1103542 * 2
def baseEnd_1103542 : Nat := 188882489474675540183303

theorem tailTrace_1103542 : CollatzResearch.WordTrace tailWord_1103542 prefixEnd_1103542 188882489474675540183303 := by
  unfold tailWord_1103542
  simp only [CollatzResearch.WordTrace]
  refine ⟨2515592710503954925865555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26832988912042185875899253 2515592710503954925865555)
  ·
    refine ⟨3773389065755932388798333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2515592710503954925865555 3773389065755932388798333)
    ·
      refine ⟨1415020899658474645799375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3773389065755932388798333 1415020899658474645799375)
      ·
        refine ⟨2122531349487711968699063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1415020899658474645799375 2122531349487711968699063)
        ·
          refine ⟨3183797024231567953048595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122531349487711968699063 3183797024231567953048595)
          ·
            refine ⟨4775695536347351929572893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3183797024231567953048595 4775695536347351929572893)
            ·
              refine ⟨1790885826130256973589835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4775695536347351929572893 1790885826130256973589835)
              ·
                refine ⟨2686328739195385460384753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790885826130256973589835 2686328739195385460384753)
                ·
                  refine ⟨2014746554396539095288565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2686328739195385460384753 2014746554396539095288565)
                  ·
                    refine ⟨188882489474675540183303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2014746554396539095288565 188882489474675540183303)
                    ·
                      rfl

theorem cell23_1103542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_1103542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103542 prefixEnd_1103542 := by exact prefixLift 1103542
  have htrace : WordTrace (prefixWord ++ tailWord_1103542) baseStart_1103542 baseEnd_1103542 := by
    simpa [prefixWord, tailWord_1103542, baseEnd_1103542] using wordTrace_append hprefix tailTrace_1103542
  have hstable : (prefixWord ++ tailWord_1103542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103542).length < 2 ^ (prefixWord ++ tailWord_1103542).sum := by decide
  have hdescent : baseEnd_1103542 < baseStart_1103542 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103551 : List Nat := [1, 1, 2, 2, 2, 3, 2, 2, 8]
def baseStart_1103551 : Nat := 118140960795 + 1103551 * 2 ^ 59
def prefixEnd_1103551 : Nat := 4983230072969 + 3 ^ 40 * 1103551 * 2
def baseEnd_1103551 : Nat := 62961343305546342815263

theorem tailTrace_1103551 : CollatzResearch.WordTrace tailWord_1103551 prefixEnd_1103551 62961343305546342815263 := by
  unfold tailWord_1103551
  simp only [CollatzResearch.WordTrace]
  refine ⟨40249811625030673350926507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26833207750020448900617671 40249811625030673350926507)
  ·
    refine ⟨60374717437546010026389761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40249811625030673350926507 60374717437546010026389761)
    ·
      refine ⟨45281038078159507519792321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60374717437546010026389761 45281038078159507519792321)
      ·
        refine ⟨33960778558619630639844241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45281038078159507519792321 33960778558619630639844241)
        ·
          refine ⟨25470583918964722979883181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33960778558619630639844241 25470583918964722979883181)
          ·
            refine ⟨9551468969611771117456193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25470583918964722979883181 9551468969611771117456193)
            ·
              refine ⟨7163601727208828338092145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9551468969611771117456193 7163601727208828338092145)
              ·
                refine ⟨5372701295406621253569109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163601727208828338092145 5372701295406621253569109)
                ·
                  refine ⟨62961343305546342815263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5372701295406621253569109 62961343305546342815263)
                  ·
                    rfl

theorem cell23_1103551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 2, 2, 8].length) (baseStart_1103551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103551 prefixEnd_1103551 := by exact prefixLift 1103551
  have htrace : WordTrace (prefixWord ++ tailWord_1103551) baseStart_1103551 baseEnd_1103551 := by
    simpa [prefixWord, tailWord_1103551, baseEnd_1103551] using wordTrace_append hprefix tailTrace_1103551
  have hstable : (prefixWord ++ tailWord_1103551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103551).length < 2 ^ (prefixWord ++ tailWord_1103551).sum := by decide
  have hdescent : baseEnd_1103551 < baseStart_1103551 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103572 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 3, 4]
def baseStart_1103572 : Nat := 118140960795 + 1103572 * 2 ^ 59
def prefixEnd_1103572 : Nat := 4983230072969 + 3 ^ 40 * 1103572 * 2
def baseEnd_1103572 : Nat := 188887624281220501058257

theorem tailTrace_1103572 : CollatzResearch.WordTrace tailWord_1103572 prefixEnd_1103572 188887624281220501058257 := by
  unfold tailWord_1103572
  simp only [CollatzResearch.WordTrace]
  refine ⟨20125288778977296968720485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26833718371969729291627313 20125288778977296968720485)
  ·
    refine ⟨3773491646058243181635091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20125288778977296968720485 3773491646058243181635091)
    ·
      refine ⟨5660237469087364772452637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3773491646058243181635091 5660237469087364772452637)
      ·
        refine ⟨2122589050907761789669739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5660237469087364772452637 2122589050907761789669739)
        ·
          refine ⟨3183883576361642684504609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2122589050907761789669739 3183883576361642684504609)
          ·
            refine ⟨2387912682271232013378457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3183883576361642684504609 2387912682271232013378457)
            ·
              refine ⟨1790934511703424010033843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2387912682271232013378457 1790934511703424010033843)
              ·
                refine ⟨2686401767555136015050765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1790934511703424010033843 2686401767555136015050765)
                ·
                  refine ⟨1007400662833176005644037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2686401767555136015050765 1007400662833176005644037)
                  ·
                    refine ⟨188887624281220501058257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1007400662833176005644037 188887624281220501058257)
                    ·
                      rfl

theorem cell23_1103572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 3, 4].length) (baseStart_1103572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103572 prefixEnd_1103572 := by exact prefixLift 1103572
  have htrace : WordTrace (prefixWord ++ tailWord_1103572) baseStart_1103572 baseEnd_1103572 := by
    simpa [prefixWord, tailWord_1103572, baseEnd_1103572] using wordTrace_append hprefix tailTrace_1103572
  have hstable : (prefixWord ++ tailWord_1103572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103572).length < 2 ^ (prefixWord ++ tailWord_1103572).sum := by decide
  have hdescent : baseEnd_1103572 < baseStart_1103572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103595 : List Nat := [1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 3]
def baseStart_1103595 : Nat := 118140960795 + 1103595 * 2 ^ 59
def prefixEnd_1103595 : Nat := 4983230072969 + 3 ^ 40 * 1103595 * 2
def baseEnd_1103595 : Nat := 566674682898714913187165

theorem tailTrace_1103595 : CollatzResearch.WordTrace tailWord_1103595 prefixEnd_1103595 566674682898714913187165 := by
  unfold tailWord_1103595
  simp only [CollatzResearch.WordTrace]
  refine ⟨40251416436871268865528239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26834277624580845910352159 40251416436871268865528239)
  ·
    refine ⟨60377124655306903298292359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40251416436871268865528239 60377124655306903298292359)
    ·
      refine ⟨90565686982960354947438539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60377124655306903298292359 90565686982960354947438539)
      ·
        refine ⟨135848530474440532421157809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90565686982960354947438539 135848530474440532421157809)
        ·
          refine ⟨101886397855830399315868357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135848530474440532421157809 101886397855830399315868357)
          ·
            refine ⟨19103699597968199871725317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101886397855830399315868357 19103699597968199871725317)
            ·
              refine ⟨3581943674619037475948497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19103699597968199871725317 3581943674619037475948497)
              ·
                refine ⟨2686457755964278106961373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3581943674619037475948497 2686457755964278106961373)
                ·
                  refine ⟨1007421658486604290110515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2686457755964278106961373 1007421658486604290110515)
                  ·
                    refine ⟨1511132487729906435165773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1007421658486604290110515 1511132487729906435165773)
                    ·
                      refine ⟨566674682898714913187165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1511132487729906435165773 566674682898714913187165)
                      ·
                        rfl

theorem cell23_1103595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 2, 3, 1, 3].length) (baseStart_1103595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103595 prefixEnd_1103595 := by exact prefixLift 1103595
  have htrace : WordTrace (prefixWord ++ tailWord_1103595) baseStart_1103595 baseEnd_1103595 := by
    simpa [prefixWord, tailWord_1103595, baseEnd_1103595] using wordTrace_append hprefix tailTrace_1103595
  have hstable : (prefixWord ++ tailWord_1103595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103595).length < 2 ^ (prefixWord ++ tailWord_1103595).sum := by decide
  have hdescent : baseEnd_1103595 < baseStart_1103595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103648 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1103648 : Nat := 118140960795 + 1103648 * 2 ^ 59
def prefixEnd_1103648 : Nat := 4983230072969 + 3 ^ 40 * 1103648 * 2
def baseEnd_1103648 : Nat := 566701897373403205824421

theorem tailTrace_1103648 : CollatzResearch.WordTrace tailWord_1103648 prefixEnd_1103648 566701897373403205824421 := by
  unfold tailWord_1103648
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126674752839629458603799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26835566337119505944805065 20126674752839629458603799)
  ·
    refine ⟨30190012129259444187905699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20126674752839629458603799 30190012129259444187905699)
    ·
      refine ⟨45285018193889166281858549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30190012129259444187905699 45285018193889166281858549)
      ·
        refine ⟨4245470455677109338924239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45285018193889166281858549 4245470455677109338924239)
        ·
          refine ⟨6368205683515664008386359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245470455677109338924239 6368205683515664008386359)
          ·
            refine ⟨9552308525273496012579539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6368205683515664008386359 9552308525273496012579539)
            ·
              refine ⟨14328462787910244018869309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9552308525273496012579539 14328462787910244018869309)
              ·
                refine ⟨5373173545466341507075991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14328462787910244018869309 5373173545466341507075991)
                ·
                  refine ⟨8059760318199512260613987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5373173545466341507075991 8059760318199512260613987)
                  ·
                    refine ⟨12089640477299268390920981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8059760318199512260613987 12089640477299268390920981)
                    ·
                      refine ⟨566701897373403205824421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12089640477299268390920981 566701897373403205824421)
                      ·
                        rfl

theorem cell23_1103648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1103648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103648 prefixEnd_1103648 := by exact prefixLift 1103648
  have htrace : WordTrace (prefixWord ++ tailWord_1103648) baseStart_1103648 baseEnd_1103648 := by
    simpa [prefixWord, tailWord_1103648, baseEnd_1103648] using wordTrace_append hprefix tailTrace_1103648
  have hstable : (prefixWord ++ tailWord_1103648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103648).length < 2 ^ (prefixWord ++ tailWord_1103648).sum := by decide
  have hdescent : baseEnd_1103648 < baseStart_1103648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103652 : List Nat := [2, 3, 1, 3, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1103652 : Nat := 118140960795 + 1103652 * 2 ^ 59
def prefixEnd_1103652 : Nat := 4983230072969 + 3 ^ 40 * 1103652 * 2
def baseEnd_1103652 : Nat := 566703951296021190174403

theorem tailTrace_1103652 : CollatzResearch.WordTrace tailWord_1103652 prefixEnd_1103652 566703951296021190174403 := by
  unfold tailWord_1103652
  simp only [CollatzResearch.WordTrace]
  refine ⟨20126747698832383800176605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26835663598443178400235473 20126747698832383800176605)
  ·
    refine ⟨7547530387062143925066227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20126747698832383800176605 7547530387062143925066227)
    ·
      refine ⟨11321295580593215887599341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7547530387062143925066227 11321295580593215887599341)
      ·
        refine ⟨4245485842722455957849753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11321295580593215887599341 4245485842722455957849753)
        ·
          refine ⟨3184114382041841968387315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4245485842722455957849753 3184114382041841968387315)
          ·
            refine ⟨4776171573062762952580973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184114382041841968387315 4776171573062762952580973)
            ·
              refine ⟨1791064339898536107217865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4776171573062762952580973 1791064339898536107217865)
              ·
                refine ⟨1343298254923902080413399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791064339898536107217865 1343298254923902080413399)
                ·
                  refine ⟨2014947382385853120620099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343298254923902080413399 2014947382385853120620099)
                  ·
                    refine ⟨3022421073578779680930149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014947382385853120620099 3022421073578779680930149)
                    ·
                      refine ⟨566703951296021190174403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3022421073578779680930149 566703951296021190174403)
                      ·
                        rfl

theorem cell23_1103652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1103652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103652 prefixEnd_1103652 := by exact prefixLift 1103652
  have htrace : WordTrace (prefixWord ++ tailWord_1103652) baseStart_1103652 baseEnd_1103652 := by
    simpa [prefixWord, tailWord_1103652, baseEnd_1103652] using wordTrace_append hprefix tailTrace_1103652
  have hstable : (prefixWord ++ tailWord_1103652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103652).length < 2 ^ (prefixWord ++ tailWord_1103652).sum := by decide
  have hdescent : baseEnd_1103652 < baseStart_1103652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103662 : List Nat := [4, 1, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_1103662 : Nat := 118140960795 + 1103662 * 2 ^ 59
def prefixEnd_1103662 : Nat := 4983230072969 + 3 ^ 40 * 1103662 * 2
def baseEnd_1103662 : Nat := 188903028700855383683119

theorem tailTrace_1103662 : CollatzResearch.WordTrace tailWord_1103662 prefixEnd_1103662 188903028700855383683119 := by
  unfold tailWord_1103662
  simp only [CollatzResearch.WordTrace]
  refine ⟨5031732515953567413527155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26835906751752359538811493 5031732515953567413527155)
  ·
    refine ⟨7547598773930351120290733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5031732515953567413527155 7547598773930351120290733)
    ·
      refine ⟨2830349540223881670109025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7547598773930351120290733 2830349540223881670109025)
      ·
        refine ⟨2122762155167911252581769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2830349540223881670109025 2122762155167911252581769)
        ·
          refine ⟨1592071616375933439436327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2122762155167911252581769 1592071616375933439436327)
          ·
            refine ⟨2388107424563900159154491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592071616375933439436327 2388107424563900159154491)
            ·
              refine ⟨3582161136845850238731737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388107424563900159154491 3582161136845850238731737)
              ·
                refine ⟨2686620852634387679048803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582161136845850238731737 2686620852634387679048803)
                ·
                  refine ⟨4029931278951581518573205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686620852634387679048803 4029931278951581518573205)
                  ·
                    refine ⟨188903028700855383683119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4029931278951581518573205 188903028700855383683119)
                    ·
                      rfl

theorem cell23_1103662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_1103662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103662 prefixEnd_1103662 := by exact prefixLift 1103662
  have htrace : WordTrace (prefixWord ++ tailWord_1103662) baseStart_1103662 baseEnd_1103662 := by
    simpa [prefixWord, tailWord_1103662, baseEnd_1103662] using wordTrace_append hprefix tailTrace_1103662
  have hstable : (prefixWord ++ tailWord_1103662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103662).length < 2 ^ (prefixWord ++ tailWord_1103662).sum := by decide
  have hdescent : baseEnd_1103662 < baseStart_1103662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103665 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 4]
def baseStart_1103665 : Nat := 118140960795 + 1103665 * 2 ^ 59
def prefixEnd_1103665 : Nat := 4983230072969 + 3 ^ 40 * 1103665 * 2
def baseEnd_1103665 : Nat := 566710626544529639311843

theorem tailTrace_1103665 : CollatzResearch.WordTrace tailWord_1103665 prefixEnd_1103665 566710626544529639311843 := by
  unfold tailWord_1103665
  simp only [CollatzResearch.WordTrace]
  refine ⟨40253969546617670820576449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26835979697745113880384299 40253969546617670820576449)
  ·
    refine ⟨30190477159963253115432337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40253969546617670820576449 30190477159963253115432337)
    ·
      refine ⟨22642857869972439836574253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30190477159963253115432337 22642857869972439836574253)
      ·
        refine ⟨8491071701239664938715345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22642857869972439836574253 8491071701239664938715345)
        ·
          refine ⟨6368303775929748704036509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8491071701239664938715345 6368303775929748704036509)
          ·
            refine ⟨2388113915973655764013691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6368303775929748704036509 2388113915973655764013691)
            ·
              refine ⟨3582170873960483646020537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388113915973655764013691 3582170873960483646020537)
              ·
                refine ⟨2686628155470362734515403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582170873960483646020537 2686628155470362734515403)
                ·
                  refine ⟨4029942233205544101773105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686628155470362734515403 4029942233205544101773105)
                  ·
                    refine ⟨3022456674904158076329829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4029942233205544101773105 3022456674904158076329829)
                    ·
                      refine ⟨566710626544529639311843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3022456674904158076329829 566710626544529639311843)
                      ·
                        rfl

theorem cell23_1103665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_1103665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103665 prefixEnd_1103665 := by exact prefixLift 1103665
  have htrace : WordTrace (prefixWord ++ tailWord_1103665) baseStart_1103665 baseEnd_1103665 := by
    simpa [prefixWord, tailWord_1103665, baseEnd_1103665] using wordTrace_append hprefix tailTrace_1103665
  have hstable : (prefixWord ++ tailWord_1103665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103665).length < 2 ^ (prefixWord ++ tailWord_1103665).sum := by decide
  have hdescent : baseEnd_1103665 < baseStart_1103665 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103669 : List Nat := [1, 3, 3, 1, 4, 1, 3, 1, 1, 1, 4]
def baseStart_1103669 : Nat := 118140960795 + 1103669 * 2 ^ 59
def prefixEnd_1103669 : Nat := 4983230072969 + 3 ^ 40 * 1103669 * 2
def baseEnd_1103669 : Nat := 566712680467147623661825

theorem tailTrace_1103669 : CollatzResearch.WordTrace tailWord_1103669 prefixEnd_1103669 566712680467147623661825 := by
  unfold tailWord_1103669
  simp only [CollatzResearch.WordTrace]
  refine ⟨40254115438603179503722061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26836076959068786335814707 40254115438603179503722061)
  ·
    refine ⟨15095293289476192313895773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40254115438603179503722061 15095293289476192313895773)
    ·
      refine ⟨5660734983553572117710915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15095293289476192313895773 5660734983553572117710915)
      ·
        refine ⟨8491102475330358176566373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5660734983553572117710915 8491102475330358176566373)
        ·
          refine ⟨1592081714124442158106195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8491102475330358176566373 1592081714124442158106195)
          ·
            refine ⟨2388122571186663237159293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592081714124442158106195 2388122571186663237159293)
            ·
              refine ⟨895545964194998713934735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2388122571186663237159293 895545964194998713934735)
              ·
                refine ⟨1343318946292498070902103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 895545964194998713934735 1343318946292498070902103)
                ·
                  refine ⟨2014978419438747106353155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343318946292498070902103 2014978419438747106353155)
                  ·
                    refine ⟨3022467629158120659529733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2014978419438747106353155 3022467629158120659529733)
                    ·
                      refine ⟨566712680467147623661825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3022467629158120659529733 566712680467147623661825)
                      ·
                        rfl

theorem cell23_1103669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 1, 1, 1, 4].length) (baseStart_1103669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103669 prefixEnd_1103669 := by exact prefixLift 1103669
  have htrace : WordTrace (prefixWord ++ tailWord_1103669) baseStart_1103669 baseEnd_1103669 := by
    simpa [prefixWord, tailWord_1103669, baseEnd_1103669] using wordTrace_append hprefix tailTrace_1103669
  have hstable : (prefixWord ++ tailWord_1103669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103669).length < 2 ^ (prefixWord ++ tailWord_1103669).sum := by decide
  have hdescent : baseEnd_1103669 < baseStart_1103669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103688 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1103688 : Nat := 118140960795 + 1103688 * 2 ^ 59
def prefixEnd_1103688 : Nat := 4983230072969 + 3 ^ 40 * 1103688 * 2
def baseEnd_1103688 : Nat := 188907478866527683108079

theorem tailTrace_1103688 : CollatzResearch.WordTrace tailWord_1103688 prefixEnd_1103688 188907478866527683108079 := by
  unfold tailWord_1103688
  simp only [CollatzResearch.WordTrace]
  refine ⟨20127404212767172874331859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26836538950356230499109145 20127404212767172874331859)
  ·
    refine ⟨30191106319150759311497789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20127404212767172874331859 30191106319150759311497789)
    ·
      refine ⟨11321664869681534741811671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30191106319150759311497789 11321664869681534741811671)
      ·
        refine ⟨16982497304522302112717507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11321664869681534741811671 16982497304522302112717507)
        ·
          refine ⟨25473745956783453169076261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16982497304522302112717507 25473745956783453169076261)
          ·
            refine ⟨4776327366896897469201799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25473745956783453169076261 4776327366896897469201799)
            ·
              refine ⟨7164491050345346203802699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776327366896897469201799 7164491050345346203802699)
              ·
                refine ⟨10746736575518019305704049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7164491050345346203802699 10746736575518019305704049)
                ·
                  refine ⟨8060052431638514479278037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10746736575518019305704049 8060052431638514479278037)
                  ·
                    refine ⟨188907478866527683108079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8060052431638514479278037 188907478866527683108079)
                    ·
                      rfl

theorem cell23_1103688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1103688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103688 prefixEnd_1103688 := by exact prefixLift 1103688
  have htrace : WordTrace (prefixWord ++ tailWord_1103688) baseStart_1103688 baseEnd_1103688 := by
    simpa [prefixWord, tailWord_1103688, baseEnd_1103688] using wordTrace_append hprefix tailTrace_1103688
  have hstable : (prefixWord ++ tailWord_1103688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103688).length < 2 ^ (prefixWord ++ tailWord_1103688).sum := by decide
  have hdescent : baseEnd_1103688 < baseStart_1103688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103692 : List Nat := [2, 2, 1, 3, 5, 1, 1, 8]
def baseStart_1103692 : Nat := 118140960795 + 1103692 * 2 ^ 59
def prefixEnd_1103692 : Nat := 4983230072969 + 3 ^ 40 * 1103692 * 2
def baseEnd_1103692 : Nat := 20989795945266704950897

theorem tailTrace_1103692 : CollatzResearch.WordTrace tailWord_1103692 prefixEnd_1103692 20989795945266704950897 := by
  unfold tailWord_1103692
  simp only [CollatzResearch.WordTrace]
  refine ⟨20127477158759927215904665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26836636211679902954539553 20127477158759927215904665)
  ·
    refine ⟨15095607869069945411928499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20127477158759927215904665 15095607869069945411928499)
    ·
      refine ⟨22643411803604918117892749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15095607869069945411928499 22643411803604918117892749)
      ·
        refine ⟨8491279426351844294209781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22643411803604918117892749 8491279426351844294209781)
        ·
          refine ⟨796057446220485402582167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 8491279426351844294209781 796057446220485402582167)
          ·
            refine ⟨1194086169330728103873251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796057446220485402582167 1194086169330728103873251)
            ·
              refine ⟨1791129253996092155809877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194086169330728103873251 1791129253996092155809877)
              ·
                refine ⟨20989795945266704950897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1791129253996092155809877 20989795945266704950897)
                ·
                  rfl

theorem cell23_1103692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 5, 1, 1, 8].length) (baseStart_1103692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103692 prefixEnd_1103692 := by exact prefixLift 1103692
  have htrace : WordTrace (prefixWord ++ tailWord_1103692) baseStart_1103692 baseEnd_1103692 := by
    simpa [prefixWord, tailWord_1103692, baseEnd_1103692] using wordTrace_append hprefix tailTrace_1103692
  have hstable : (prefixWord ++ tailWord_1103692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103692).length < 2 ^ (prefixWord ++ tailWord_1103692).sum := by decide
  have hdescent : baseEnd_1103692 < baseStart_1103692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103712 : List Nat := [2, 1, 1, 3, 3, 2, 2, 1, 3, 3, 2]
def baseStart_1103712 : Nat := 118140960795 + 1103712 * 2 ^ 59
def prefixEnd_1103712 : Nat := 4983230072969 + 3 ^ 40 * 1103712 * 2
def baseEnd_1103712 : Nat := 566734760135290955424127

theorem tailTrace_1103712 : CollatzResearch.WordTrace tailWord_1103712 prefixEnd_1103712 566734760135290955424127 := by
  unfold tailWord_1103712
  simp only [CollatzResearch.WordTrace]
  refine ⟨20127841888723698923768695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26837122518298265231691593 20127841888723698923768695)
  ·
    refine ⟨30191762833085548385653043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20127841888723698923768695 30191762833085548385653043)
    ·
      refine ⟨45287644249628322578479565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30191762833085548385653043 45287644249628322578479565)
      ·
        refine ⟨16982866593610620966929837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45287644249628322578479565 16982866593610620966929837)
        ·
          refine ⟨6368574972603982862598689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16982866593610620966929837 6368574972603982862598689)
          ·
            refine ⟨4776431229452987146949017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6368574972603982862598689 4776431229452987146949017)
            ·
              refine ⟨3582323422089740360211763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4776431229452987146949017 3582323422089740360211763)
              ·
                refine ⟨5373485133134610540317645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582323422089740360211763 5373485133134610540317645)
                ·
                  refine ⟨2015056924925478952619117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5373485133134610540317645 2015056924925478952619117)
                  ·
                    refine ⟨755646346847054607232169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2015056924925478952619117 755646346847054607232169)
                    ·
                      refine ⟨566734760135290955424127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755646346847054607232169 566734760135290955424127)
                      ·
                        rfl

theorem cell23_1103712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 1, 3, 3, 2].length) (baseStart_1103712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103712 prefixEnd_1103712 := by exact prefixLift 1103712
  have htrace : WordTrace (prefixWord ++ tailWord_1103712) baseStart_1103712 baseEnd_1103712 := by
    simpa [prefixWord, tailWord_1103712, baseEnd_1103712] using wordTrace_append hprefix tailTrace_1103712
  have hstable : (prefixWord ++ tailWord_1103712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103712).length < 2 ^ (prefixWord ++ tailWord_1103712).sum := by decide
  have hdescent : baseEnd_1103712 < baseStart_1103712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103728 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_1103728 : Nat := 118140960795 + 1103728 * 2 ^ 59
def prefixEnd_1103728 : Nat := 4983230072969 + 3 ^ 40 * 1103728 * 2
def baseEnd_1103728 : Nat := 566742975825762892824053

theorem tailTrace_1103728 : CollatzResearch.WordTrace tailWord_1103728 prefixEnd_1103728 566742975825762892824053 := by
  unfold tailWord_1103728
  simp only [CollatzResearch.WordTrace]
  refine ⟨20128133672694716290059919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26837511563592955053413225 20128133672694716290059919)
  ·
    refine ⟨30192200509042074435089879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20128133672694716290059919 30192200509042074435089879)
    ·
      refine ⟨45288300763563111652634819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30192200509042074435089879 45288300763563111652634819)
      ·
        refine ⟨67932451145344667478952229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45288300763563111652634819 67932451145344667478952229)
        ·
          refine ⟨12737334589752125152303543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67932451145344667478952229 12737334589752125152303543)
          ·
            refine ⟨19106001884628187728455315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12737334589752125152303543 19106001884628187728455315)
            ·
              refine ⟨28659002826942281592682973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19106001884628187728455315 28659002826942281592682973)
              ·
                refine ⟨10747126060103355597256115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28659002826942281592682973 10747126060103355597256115)
                ·
                  refine ⟨16120689090155033395884173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10747126060103355597256115 16120689090155033395884173)
                  ·
                    refine ⟨6045258408808137523456565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16120689090155033395884173 6045258408808137523456565)
                    ·
                      refine ⟨566742975825762892824053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6045258408808137523456565 566742975825762892824053)
                      ·
                        rfl

theorem cell23_1103728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_1103728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103728 prefixEnd_1103728 := by exact prefixLift 1103728
  have htrace : WordTrace (prefixWord ++ tailWord_1103728) baseStart_1103728 baseEnd_1103728 := by
    simpa [prefixWord, tailWord_1103728, baseEnd_1103728] using wordTrace_append hprefix tailTrace_1103728
  have hstable : (prefixWord ++ tailWord_1103728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103728).length < 2 ^ (prefixWord ++ tailWord_1103728).sum := by decide
  have hdescent : baseEnd_1103728 < baseStart_1103728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103795 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 2, 5]
def baseStart_1103795 : Nat := 118140960795 + 1103795 * 2 ^ 59
def prefixEnd_1103795 : Nat := 4983230072969 + 3 ^ 40 * 1103795 * 2
def baseEnd_1103795 : Nat := 188925793009871376895415

theorem tailTrace_1103795 : CollatzResearch.WordTrace tailWord_1103795 prefixEnd_1103795 188925793009871376895415 := by
  unfold tailWord_1103795
  simp only [CollatzResearch.WordTrace]
  refine ⟨40258711036146703022808839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26839140690764468681872559 40258711036146703022808839)
  ·
    refine ⟨60388066554220054534213259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40258711036146703022808839 60388066554220054534213259)
    ·
      refine ⟨90582099831330081801319889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60388066554220054534213259 90582099831330081801319889)
      ·
        refine ⟨67936574873497561350989917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90582099831330081801319889 67936574873497561350989917)
        ·
          refine ⟨25476215577561585506621219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67936574873497561350989917 25476215577561585506621219)
          ·
            refine ⟨38214323366342378259931829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25476215577561585506621219 38214323366342378259931829)
            ·
              refine ⟨3582592815594597961868609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38214323366342378259931829 3582592815594597961868609)
              ·
                refine ⟨2686944611695948471401457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582592815594597961868609 2686944611695948471401457)
                ·
                  refine ⟨2015208458771961353551093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2686944611695948471401457 2015208458771961353551093)
                  ·
                    refine ⟨188925793009871376895415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2015208458771961353551093 188925793009871376895415)
                    ·
                      rfl

theorem cell23_1103795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 2, 5].length) (baseStart_1103795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103795 prefixEnd_1103795 := by exact prefixLift 1103795
  have htrace : WordTrace (prefixWord ++ tailWord_1103795) baseStart_1103795 baseEnd_1103795 := by
    simpa [prefixWord, tailWord_1103795, baseEnd_1103795] using wordTrace_append hprefix tailTrace_1103795
  have hstable : (prefixWord ++ tailWord_1103795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103795).length < 2 ^ (prefixWord ++ tailWord_1103795).sum := by decide
  have hdescent : baseEnd_1103795 < baseStart_1103795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103805 : List Nat := [1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 7]
def baseStart_1103805 : Nat := 118140960795 + 1103805 * 2 ^ 59
def prefixEnd_1103805 : Nat := 4983230072969 + 3 ^ 40 * 1103805 * 2
def baseEnd_1103805 : Nat := 566782513836159091561199

theorem tailTrace_1103805 : CollatzResearch.WordTrace tailWord_1103805 prefixEnd_1103805 566782513836159091561199 := by
  unfold tailWord_1103805
  simp only [CollatzResearch.WordTrace]
  refine ⟨40259075766110474730672869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26839383844073649820448579 40259075766110474730672869)
  ·
    refine ⟨7548576706145714012001163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40259075766110474730672869 7548576706145714012001163)
    ·
      refine ⟨11322865059218571018001745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7548576706145714012001163 11322865059218571018001745)
      ·
        refine ⟨8492148794413928263501309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11322865059218571018001745 8492148794413928263501309)
        ·
          refine ⟨3184555797905223098812991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8492148794413928263501309 3184555797905223098812991)
          ·
            refine ⟨4776833696857834648219487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184555797905223098812991 4776833696857834648219487)
            ·
              refine ⟨7165250545286751972329231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776833696857834648219487 7165250545286751972329231)
              ·
                refine ⟨10747875817930127958493847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7165250545286751972329231 10747875817930127958493847)
                ·
                  refine ⟨16121813726895191937740771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10747875817930127958493847 16121813726895191937740771)
                  ·
                    refine ⟨24182720590342787906611157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16121813726895191937740771 24182720590342787906611157)
                    ·
                      refine ⟨566782513836159091561199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24182720590342787906611157 566782513836159091561199)
                      ·
                        rfl

theorem cell23_1103805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_1103805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103805 prefixEnd_1103805 := by exact prefixLift 1103805
  have htrace : WordTrace (prefixWord ++ tailWord_1103805) baseStart_1103805 baseEnd_1103805 := by
    simpa [prefixWord, tailWord_1103805, baseEnd_1103805] using wordTrace_append hprefix tailTrace_1103805
  have hstable : (prefixWord ++ tailWord_1103805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103805).length < 2 ^ (prefixWord ++ tailWord_1103805).sum := by decide
  have hdescent : baseEnd_1103805 < baseStart_1103805 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103815 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 4]
def baseStart_1103815 : Nat := 118140960795 + 1103815 * 2 ^ 59
def prefixEnd_1103815 : Nat := 4983230072969 + 3 ^ 40 * 1103815 * 2
def baseEnd_1103815 : Nat := 566787648642704052436153

theorem tailTrace_1103815 : CollatzResearch.WordTrace tailWord_1103815 prefixEnd_1103815 566787648642704052436153 := by
  unfold tailWord_1103815
  simp only [CollatzResearch.WordTrace]
  refine ⟨40259440496074246438536899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26839626997382830959024599 40259440496074246438536899)
  ·
    refine ⟨60389160744111369657805349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40259440496074246438536899 60389160744111369657805349)
    ·
      refine ⟨11322967639520881810838503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60389160744111369657805349 11322967639520881810838503)
      ·
        refine ⟨16984451459281322716257755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11322967639520881810838503 16984451459281322716257755)
        ·
          refine ⟨25476677188921984074386633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16984451459281322716257755 25476677188921984074386633)
          ·
            refine ⟨19107507891691488055789975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25476677188921984074386633 19107507891691488055789975)
            ·
              refine ⟨28661261837537232083684963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19107507891691488055789975 28661261837537232083684963)
              ·
                refine ⟨42991892756305848125527445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28661261837537232083684963 42991892756305848125527445)
                ·
                  refine ⟨2015244972951836630884099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 42991892756305848125527445 2015244972951836630884099)
                  ·
                    refine ⟨3022867459427754946326149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2015244972951836630884099 3022867459427754946326149)
                    ·
                      refine ⟨566787648642704052436153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3022867459427754946326149 566787648642704052436153)
                      ·
                        rfl

theorem cell23_1103815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 6, 1, 4].length) (baseStart_1103815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103815 prefixEnd_1103815 := by exact prefixLift 1103815
  have htrace : WordTrace (prefixWord ++ tailWord_1103815) baseStart_1103815 baseEnd_1103815 := by
    simpa [prefixWord, tailWord_1103815, baseEnd_1103815] using wordTrace_append hprefix tailTrace_1103815
  have hstable : (prefixWord ++ tailWord_1103815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103815).length < 2 ^ (prefixWord ++ tailWord_1103815).sum := by decide
  have hdescent : baseEnd_1103815 < baseStart_1103815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103832 : List Nat := [2, 1, 2, 2, 2, 2, 4, 1, 2, 1, 4]
def baseStart_1103832 : Nat := 118140960795 + 1103832 * 2 ^ 59
def prefixEnd_1103832 : Nat := 4983230072969 + 3 ^ 40 * 1103832 * 2
def baseEnd_1103832 : Nat := 566796377813830485923575

theorem tailTrace_1103832 : CollatzResearch.WordTrace tailWord_1103832 prefixEnd_1103832 566796377813830485923575 := by
  unfold tailWord_1103832
  simp only [CollatzResearch.WordTrace]
  refine ⟨20130030268506329170952875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26840040358008438894603833 20130030268506329170952875)
  ·
    refine ⟨30195045402759493756429313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20130030268506329170952875 30195045402759493756429313)
    ·
      refine ⟨22646284052069620317321985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30195045402759493756429313 22646284052069620317321985)
      ·
        refine ⟨16984713039052215237991489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22646284052069620317321985 16984713039052215237991489)
        ·
          refine ⟨12738534779289161428493617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16984713039052215237991489 12738534779289161428493617)
          ·
            refine ⟨9553901084466871071370213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12738534779289161428493617 9553901084466871071370213)
            ·
              refine ⟨1791356453337538325881915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9553901084466871071370213 1791356453337538325881915)
              ·
                refine ⟨2687034680006307488822873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791356453337538325881915 2687034680006307488822873)
                ·
                  refine ⟨2015276010004730616617155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687034680006307488822873 2015276010004730616617155)
                  ·
                    refine ⟨3022914015007095924925733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2015276010004730616617155 3022914015007095924925733)
                    ·
                      refine ⟨566796377813830485923575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3022914015007095924925733 566796377813830485923575)
                      ·
                        rfl

theorem cell23_1103832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 4, 1, 2, 1, 4].length) (baseStart_1103832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103832 prefixEnd_1103832 := by exact prefixLift 1103832
  have htrace : WordTrace (prefixWord ++ tailWord_1103832) baseStart_1103832 baseEnd_1103832 := by
    simpa [prefixWord, tailWord_1103832, baseEnd_1103832] using wordTrace_append hprefix tailTrace_1103832
  have hstable : (prefixWord ++ tailWord_1103832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103832).length < 2 ^ (prefixWord ++ tailWord_1103832).sum := by decide
  have hdescent : baseEnd_1103832 < baseStart_1103832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103876 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 3, 4]
def baseStart_1103876 : Nat := 118140960795 + 1103876 * 2 ^ 59
def prefixEnd_1103876 : Nat := 4983230072969 + 3 ^ 40 * 1103876 * 2
def baseEnd_1103876 : Nat := 188939656987542771257791

theorem tailTrace_1103876 : CollatzResearch.WordTrace tailWord_1103876 prefixEnd_1103876 188939656987542771257791 := by
  unfold tailWord_1103876
  simp only [CollatzResearch.WordTrace]
  refine ⟨20130832674426626928253741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26841110232568835904338321 20130832674426626928253741)
  ·
    refine ⟨7549062252909985098095153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20130832674426626928253741 7549062252909985098095153)
    ·
      refine ⟨5661796689682488823571365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7549062252909985098095153 5661796689682488823571365)
      ·
        refine ⟨1061586879315466654419631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5661796689682488823571365 1061586879315466654419631)
        ·
          refine ⟨1592380318973199981629447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1061586879315466654419631 1592380318973199981629447)
          ·
            refine ⟨2388570478459799972444171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592380318973199981629447 2388570478459799972444171)
            ·
              refine ⟨3582855717689699958666257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2388570478459799972444171 3582855717689699958666257)
              ·
                refine ⟨2687141788267274968999693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582855717689699958666257 2687141788267274968999693)
                ·
                  refine ⟨1007678170600228113374885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2687141788267274968999693 1007678170600228113374885)
                  ·
                    refine ⟨188939656987542771257791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1007678170600228113374885 188939656987542771257791)
                    ·
                      rfl

theorem cell23_1103876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_1103876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103876 prefixEnd_1103876 := by exact prefixLift 1103876
  have htrace : WordTrace (prefixWord ++ tailWord_1103876) baseStart_1103876 baseEnd_1103876 := by
    simpa [prefixWord, tailWord_1103876, baseEnd_1103876] using wordTrace_append hprefix tailTrace_1103876
  have hstable : (prefixWord ++ tailWord_1103876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103876).length < 2 ^ (prefixWord ++ tailWord_1103876).sum := by decide
  have hdescent : baseEnd_1103876 < baseStart_1103876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103939 : List Nat := [1, 1, 1, 3, 1, 2, 2, 3, 5, 2, 2]
def baseStart_1103939 : Nat := 118140960795 + 1103939 * 2 ^ 59
def prefixEnd_1103939 : Nat := 4983230072969 + 3 ^ 40 * 1103939 * 2
def baseEnd_1103939 : Nat := 566851320243861567285583

theorem tailTrace_1103939 : CollatzResearch.WordTrace tailWord_1103939 prefixEnd_1103939 566851320243861567285583 := by
  unfold tailWord_1103939
  simp only [CollatzResearch.WordTrace]
  refine ⟨40263963147625015616050871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26842642098416677077367247 40263963147625015616050871)
  ·
    refine ⟨60395944721437523424076307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40263963147625015616050871 60395944721437523424076307)
    ·
      refine ⟨90593917082156285136114461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60395944721437523424076307 90593917082156285136114461)
      ·
        refine ⟨33972718905808606926042923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90593917082156285136114461 33972718905808606926042923)
        ·
          refine ⟨50959078358712910389064385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33972718905808606926042923 50959078358712910389064385)
          ·
            refine ⟨38219308769034682791798289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50959078358712910389064385 38219308769034682791798289)
            ·
              refine ⟨28664481576776012093848717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38219308769034682791798289 28664481576776012093848717)
              ·
                refine ⟨10749180591291004535193269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28664481576776012093848717 10749180591291004535193269)
                ·
                  refine ⟨1007735680433531675174369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10749180591291004535193269 1007735680433531675174369)
                  ·
                    refine ⟨755801760325148756380777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1007735680433531675174369 755801760325148756380777)
                    ·
                      refine ⟨566851320243861567285583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755801760325148756380777 566851320243861567285583)
                      ·
                        rfl

theorem cell23_1103939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 3, 5, 2, 2].length) (baseStart_1103939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103939 prefixEnd_1103939 := by exact prefixLift 1103939
  have htrace : WordTrace (prefixWord ++ tailWord_1103939) baseStart_1103939 baseEnd_1103939 := by
    simpa [prefixWord, tailWord_1103939, baseEnd_1103939] using wordTrace_append hprefix tailTrace_1103939
  have hstable : (prefixWord ++ tailWord_1103939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103939).length < 2 ^ (prefixWord ++ tailWord_1103939).sum := by decide
  have hdescent : baseEnd_1103939 < baseStart_1103939 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103945 : List Nat := [1, 2, 1, 1, 2, 2, 5, 9]
def baseStart_1103945 : Nat := 118140960795 + 1103945 * 2 ^ 59
def prefixEnd_1103945 : Nat := 4983230072969 + 3 ^ 40 * 1103945 * 2
def baseEnd_1103945 : Nat := 20994607449177353474465

theorem tailTrace_1103945 : CollatzResearch.WordTrace tailWord_1103945 prefixEnd_1103945 20994607449177353474465 := by
  unfold tailWord_1103945
  simp only [CollatzResearch.WordTrace]
  refine ⟨40264181985603278640769289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26842787990402185760512859 40264181985603278640769289)
  ·
    refine ⟨30198136489202458980576967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40264181985603278640769289 30198136489202458980576967)
    ·
      refine ⟨45297204733803688470865451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30198136489202458980576967 45297204733803688470865451)
      ·
        refine ⟨67945807100705532706298177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45297204733803688470865451 67945807100705532706298177)
        ·
          refine ⟨50959355325529149529723633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67945807100705532706298177 50959355325529149529723633)
          ·
            refine ⟨38219516494146862147292725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50959355325529149529723633 38219516494146862147292725)
            ·
              refine ⟨3583079671326268326308693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38219516494146862147292725 3583079671326268326308693)
              ·
                refine ⟨20994607449177353474465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3583079671326268326308693 20994607449177353474465)
                ·
                  rfl

theorem cell23_1103945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 5, 9].length) (baseStart_1103945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103945 prefixEnd_1103945 := by exact prefixLift 1103945
  have htrace : WordTrace (prefixWord ++ tailWord_1103945) baseStart_1103945 baseEnd_1103945 := by
    simpa [prefixWord, tailWord_1103945, baseEnd_1103945] using wordTrace_append hprefix tailTrace_1103945
  have hstable : (prefixWord ++ tailWord_1103945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103945).length < 2 ^ (prefixWord ++ tailWord_1103945).sum := by decide
  have hdescent : baseEnd_1103945 < baseStart_1103945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103949 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 6, 4]
def baseStart_1103949 : Nat := 118140960795 + 1103949 * 2 ^ 59
def prefixEnd_1103949 : Nat := 4983230072969 + 3 ^ 40 * 1103949 * 2
def baseEnd_1103949 : Nat := 188952151683468842720179

theorem tailTrace_1103949 : CollatzResearch.WordTrace tailWord_1103949 prefixEnd_1103949 188952151683468842720179 := by
  unfold tailWord_1103949
  simp only [CollatzResearch.WordTrace]
  refine ⟨40264327877588787323914901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26842885251725858215943267 40264327877588787323914901)
  ·
    refine ⟨1887390369261974405808511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 40264327877588787323914901 1887390369261974405808511)
    ·
      refine ⟨2831085553892961608712767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887390369261974405808511 2831085553892961608712767)
      ·
        refine ⟨4246628330839442413069151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2831085553892961608712767 4246628330839442413069151)
        ·
          refine ⟨6369942496259163619603727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246628330839442413069151 6369942496259163619603727)
          ·
            refine ⟨9554913744388745429405591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369942496259163619603727 9554913744388745429405591)
            ·
              refine ⟨14332370616583118144108387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9554913744388745429405591 14332370616583118144108387)
              ·
                refine ⟨21498555924874677216162581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14332370616583118144108387 21498555924874677216162581)
                ·
                  refine ⟨1007744808978500494507621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21498555924874677216162581 1007744808978500494507621)
                  ·
                    refine ⟨188952151683468842720179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1007744808978500494507621 188952151683468842720179)
                    ·
                      rfl

theorem cell23_1103949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 6, 4].length) (baseStart_1103949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103949 prefixEnd_1103949 := by exact prefixLift 1103949
  have htrace : WordTrace (prefixWord ++ tailWord_1103949) baseStart_1103949 baseEnd_1103949 := by
    simpa [prefixWord, tailWord_1103949, baseEnd_1103949] using wordTrace_append hprefix tailTrace_1103949
  have hstable : (prefixWord ++ tailWord_1103949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103949).length < 2 ^ (prefixWord ++ tailWord_1103949).sum := by decide
  have hdescent : baseEnd_1103949 < baseStart_1103949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103959 : List Nat := [1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 3]
def baseStart_1103959 : Nat := 118140960795 + 1103959 * 2 ^ 59
def prefixEnd_1103959 : Nat := 4983230072969 + 3 ^ 40 * 1103959 * 2
def baseEnd_1103959 : Nat := 566861589856951489035491

theorem tailTrace_1103959 : CollatzResearch.WordTrace tailWord_1103959 prefixEnd_1103959 566861589856951489035491 := by
  unfold tailWord_1103959
  simp only [CollatzResearch.WordTrace]
  refine ⟨40264692607552559031778931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26843128405035039354519287 40264692607552559031778931)
  ·
    refine ⟨60397038911328838547668397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40264692607552559031778931 60397038911328838547668397)
    ·
      refine ⟨22648889591748314455375649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60397038911328838547668397 22648889591748314455375649)
      ·
        refine ⟨16986667193811235841531737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22648889591748314455375649 16986667193811235841531737)
        ·
          refine ⟨12740000395358426881148803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16986667193811235841531737 12740000395358426881148803)
          ·
            refine ⟨19110000593037640321723205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12740000395358426881148803 19110000593037640321723205)
            ·
              refine ⟨3583125111194557560323101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19110000593037640321723205 3583125111194557560323101)
              ·
                refine ⟨1343671916697959085121163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3583125111194557560323101 1343671916697959085121163)
                ·
                  refine ⟨2015507875046938627681745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1343671916697959085121163 2015507875046938627681745)
                  ·
                    refine ⟨1511630906285203970761309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2015507875046938627681745 1511630906285203970761309)
                    ·
                      refine ⟨566861589856951489035491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1511630906285203970761309 566861589856951489035491)
                      ·
                        rfl

theorem cell23_1103959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 3, 1, 2, 3].length) (baseStart_1103959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103959 prefixEnd_1103959 := by exact prefixLift 1103959
  have htrace : WordTrace (prefixWord ++ tailWord_1103959) baseStart_1103959 baseEnd_1103959 := by
    simpa [prefixWord, tailWord_1103959, baseEnd_1103959] using wordTrace_append hprefix tailTrace_1103959
  have hstable : (prefixWord ++ tailWord_1103959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103959).length < 2 ^ (prefixWord ++ tailWord_1103959).sum := by decide
  have hdescent : baseEnd_1103959 < baseStart_1103959 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103973 : List Nat := [1, 3, 1, 3, 2, 4, 1, 1, 3, 2, 2]
def baseStart_1103973 : Nat := 118140960795 + 1103973 * 2 ^ 59
def prefixEnd_1103973 : Nat := 4983230072969 + 3 ^ 40 * 1103973 * 2
def baseEnd_1103973 : Nat := 566868778586114434260427

theorem tailTrace_1103973 : CollatzResearch.WordTrace tailWord_1103973 prefixEnd_1103973 566868778586114434260427 := by
  unfold tailWord_1103973
  simp only [CollatzResearch.WordTrace]
  refine ⟨40265203229501839422788573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26843468819667892948525715 40265203229501839422788573)
  ·
    refine ⟨15099451211063189783545715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40265203229501839422788573 15099451211063189783545715)
    ·
      refine ⟨22649176816594784675318573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15099451211063189783545715 22649176816594784675318573)
      ·
        refine ⟨8493441306223044253244465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22649176816594784675318573 8493441306223044253244465)
        ·
          refine ⟨6370080979667283189933349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8493441306223044253244465 6370080979667283189933349)
          ·
            refine ⟨1194390183687615598112503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6370080979667283189933349 1194390183687615598112503)
            ·
              refine ⟨1791585275531423397168755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1194390183687615598112503 1791585275531423397168755)
              ·
                refine ⟨2687377913297135095753133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1791585275531423397168755 2687377913297135095753133)
                ·
                  refine ⟨1007766717486425660907425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2687377913297135095753133 1007766717486425660907425)
                  ·
                    refine ⟨755825038114819245680569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1007766717486425660907425 755825038114819245680569)
                    ·
                      refine ⟨566868778586114434260427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755825038114819245680569 566868778586114434260427)
                      ·
                        rfl

theorem cell23_1103973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 4, 1, 1, 3, 2, 2].length) (baseStart_1103973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103973 prefixEnd_1103973 := by exact prefixLift 1103973
  have htrace : WordTrace (prefixWord ++ tailWord_1103973) baseStart_1103973 baseEnd_1103973 := by
    simpa [prefixWord, tailWord_1103973, baseEnd_1103973] using wordTrace_append hprefix tailTrace_1103973
  have hstable : (prefixWord ++ tailWord_1103973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103973).length < 2 ^ (prefixWord ++ tailWord_1103973).sum := by decide
  have hdescent : baseEnd_1103973 < baseStart_1103973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103982 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1103982 : Nat := 118140960795 + 1103982 * 2 ^ 59
def prefixEnd_1103982 : Nat := 4983230072969 + 3 ^ 40 * 1103982 * 2
def baseEnd_1103982 : Nat := 566873399912004899047885

theorem tailTrace_1103982 : CollatzResearch.WordTrace tailWord_1103982 prefixEnd_1103982 566873399912004899047885 := by
  unfold tailWord_1103982
  simp only [CollatzResearch.WordTrace]
  refine ⟨5033191435808654244983275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26843687657646155973244133 5033191435808654244983275)
  ·
    refine ⟨7549787153712981367474913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5033191435808654244983275 7549787153712981367474913)
    ·
      refine ⟨5662340365284736025606185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7549787153712981367474913 5662340365284736025606185)
      ·
        refine ⟨4246755273963552019204639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5662340365284736025606185 4246755273963552019204639)
        ·
          refine ⟨6370132910945328028806959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246755273963552019204639 6370132910945328028806959)
          ·
            refine ⟨9555199366417992043210439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6370132910945328028806959 9555199366417992043210439)
            ·
              refine ⟨14332799049626988064815659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9555199366417992043210439 14332799049626988064815659)
              ·
                refine ⟨21499198574440482097223489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14332799049626988064815659 21499198574440482097223489)
                ·
                  refine ⟨16124398930830361572917617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21499198574440482097223489 16124398930830361572917617)
                  ·
                    refine ⟨12093299198122771179688213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16124398930830361572917617 12093299198122771179688213)
                    ·
                      refine ⟨566873399912004899047885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12093299198122771179688213 566873399912004899047885)
                      ·
                        rfl

theorem cell23_1103982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1103982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103982 prefixEnd_1103982 := by exact prefixLift 1103982
  have htrace : WordTrace (prefixWord ++ tailWord_1103982) baseStart_1103982 baseEnd_1103982 := by
    simpa [prefixWord, tailWord_1103982, baseEnd_1103982] using wordTrace_append hprefix tailTrace_1103982
  have hstable : (prefixWord ++ tailWord_1103982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103982).length < 2 ^ (prefixWord ++ tailWord_1103982).sum := by decide
  have hdescent : baseEnd_1103982 < baseStart_1103982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1103995 : List Nat := [1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10]
def baseStart_1103995 : Nat := 118140960795 + 1103995 * 2 ^ 59
def prefixEnd_1103995 : Nat := 4983230072969 + 3 ^ 40 * 1103995 * 2
def baseEnd_1103995 : Nat := 566880075160513348185325

theorem tailTrace_1103995 : CollatzResearch.WordTrace tailWord_1103995 prefixEnd_1103995 566880075160513348185325 := by
  unfold tailWord_1103995
  simp only [CollatzResearch.WordTrace]
  refine ⟨40266005635422137180089439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26844003756948091453392959 40266005635422137180089439)
  ·
    refine ⟨60399008453133205770134159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40266005635422137180089439 60399008453133205770134159)
    ·
      refine ⟨90598512679699808655201239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60399008453133205770134159 90598512679699808655201239)
      ·
        refine ⟨135897769019549712982801859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90598512679699808655201239 135897769019549712982801859)
        ·
          refine ⟨203846653529324569474202789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135897769019549712982801859 203846653529324569474202789)
          ·
            refine ⟨38221247536748356776413023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203846653529324569474202789 38221247536748356776413023)
            ·
              refine ⟨57331871305122535164619535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38221247536748356776413023 57331871305122535164619535)
              ·
                refine ⟨85997806957683802746929303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57331871305122535164619535 85997806957683802746929303)
                ·
                  refine ⟨128996710436525704120393955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85997806957683802746929303 128996710436525704120393955)
                  ·
                    refine ⟨193495065654788556180590933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128996710436525704120393955 193495065654788556180590933)
                    ·
                      refine ⟨566880075160513348185325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 10 193495065654788556180590933 566880075160513348185325)
                      ·
                        rfl

theorem cell23_1103995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 10].length) (baseStart_1103995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1103995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1103995 prefixEnd_1103995 := by exact prefixLift 1103995
  have htrace : WordTrace (prefixWord ++ tailWord_1103995) baseStart_1103995 baseEnd_1103995 := by
    simpa [prefixWord, tailWord_1103995, baseEnd_1103995] using wordTrace_append hprefix tailTrace_1103995
  have hstable : (prefixWord ++ tailWord_1103995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1103995).length < 2 ^ (prefixWord ++ tailWord_1103995).sum := by decide
  have hdescent : baseEnd_1103995 < baseStart_1103995 := by decide
  rcases family_descends (prefixWord ++ tailWord_1103995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104023 : List Nat := [1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 3]
def baseStart_1104023 : Nat := 118140960795 + 1104023 * 2 ^ 59
def prefixEnd_1104023 : Nat := 4983230072969 + 3 ^ 40 * 1104023 * 2
def baseEnd_1104023 : Nat := 566894452618839238635197

theorem tailTrace_1104023 : CollatzResearch.WordTrace tailWord_1104023 prefixEnd_1104023 566894452618839238635197 := by
  unfold tailWord_1104023
  simp only [CollatzResearch.WordTrace]
  refine ⟨40267026879320697962108723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26844684586213798641405815 40267026879320697962108723)
  ·
    refine ⟨60400540318981046943163085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40267026879320697962108723 60400540318981046943163085)
    ·
      refine ⟨22650202619617892603686157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60400540318981046943163085 22650202619617892603686157)
      ·
        refine ⟨8493825982356709726382309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22650202619617892603686157 8493825982356709726382309)
        ·
          refine ⟨1592592371691883073696683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8493825982356709726382309 1592592371691883073696683)
          ·
            refine ⟨2388888557537824610545025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592592371691883073696683 2388888557537824610545025)
            ·
              refine ⟨1791666418153368457908769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2388888557537824610545025 1791666418153368457908769)
              ·
                refine ⟨1343749813615026343431577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791666418153368457908769 1343749813615026343431577)
                ·
                  refine ⟨1007812360211269757573683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1343749813615026343431577 1007812360211269757573683)
                  ·
                    refine ⟨1511718540316904636360525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1007812360211269757573683 1511718540316904636360525)
                    ·
                      refine ⟨566894452618839238635197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1511718540316904636360525 566894452618839238635197)
                      ·
                        rfl

theorem cell23_1104023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 2, 2, 2, 1, 3].length) (baseStart_1104023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104023 prefixEnd_1104023 := by exact prefixLift 1104023
  have htrace : WordTrace (prefixWord ++ tailWord_1104023) baseStart_1104023 baseEnd_1104023 := by
    simpa [prefixWord, tailWord_1104023, baseEnd_1104023] using wordTrace_append hprefix tailTrace_1104023
  have hstable : (prefixWord ++ tailWord_1104023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104023).length < 2 ^ (prefixWord ++ tailWord_1104023).sum := by decide
  have hdescent : baseEnd_1104023 < baseStart_1104023 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104024 : List Nat := [2, 1, 2, 4, 4, 1, 2, 2, 1, 2, 2]
def baseStart_1104024 : Nat := 118140960795 + 1104024 * 2 ^ 59
def prefixEnd_1104024 : Nat := 4983230072969 + 3 ^ 40 * 1104024 * 2
def baseEnd_1104024 : Nat := 566894966099493734722693

theorem tailTrace_1104024 : CollatzResearch.WordTrace tailWord_1104024 prefixEnd_1104024 566894966099493734722693 := by
  unfold tailWord_1104024
  simp only [CollatzResearch.WordTrace]
  refine ⟨20133531676158537566447563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26844708901544716755263417 20133531676158537566447563)
  ·
    refine ⟨30200297514237806349671345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20133531676158537566447563 30200297514237806349671345)
    ·
      refine ⟨22650223135678354762253509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30200297514237806349671345 22650223135678354762253509)
      ·
        refine ⟨4246916837939691517922533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22650223135678354762253509 4246916837939691517922533)
        ·
          refine ⟨796296907113692159610475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4246916837939691517922533 796296907113692159610475)
          ·
            refine ⟨1194445360670538239415713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796296907113692159610475 1194445360670538239415713)
            ·
              refine ⟨895834020502903679561785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1194445360670538239415713 895834020502903679561785)
              ·
                refine ⟨671875515377177759671339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 895834020502903679561785 671875515377177759671339)
                ·
                  refine ⟨1007813273065766639507009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 671875515377177759671339 1007813273065766639507009)
                  ·
                    refine ⟨755859954799324979630257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1007813273065766639507009 755859954799324979630257)
                    ·
                      refine ⟨566894966099493734722693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755859954799324979630257 566894966099493734722693)
                      ·
                        rfl

theorem cell23_1104024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 4, 1, 2, 2, 1, 2, 2].length) (baseStart_1104024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104024 prefixEnd_1104024 := by exact prefixLift 1104024
  have htrace : WordTrace (prefixWord ++ tailWord_1104024) baseStart_1104024 baseEnd_1104024 := by
    simpa [prefixWord, tailWord_1104024, baseEnd_1104024] using wordTrace_append hprefix tailTrace_1104024
  have hstable : (prefixWord ++ tailWord_1104024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104024).length < 2 ^ (prefixWord ++ tailWord_1104024).sum := by decide
  have hdescent : baseEnd_1104024 < baseStart_1104024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104069 : List Nat := [1, 3, 1, 1, 1, 1, 5, 5, 5]
def baseStart_1104069 : Nat := 118140960795 + 1104069 * 2 ^ 59
def prefixEnd_1104069 : Nat := 4983230072969 + 3 ^ 40 * 1104069 * 2
def baseEnd_1104069 : Nat := 62990896969882895406665

theorem tailTrace_1104069 : CollatzResearch.WordTrace tailWord_1104069 prefixEnd_1104069 62990896969882895406665 := by
  unfold tailWord_1104069
  simp only [CollatzResearch.WordTrace]
  refine ⟨40268704637154047818283261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26845803091436031878855507 40268704637154047818283261)
  ·
    refine ⟨15100764238932767931856223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40268704637154047818283261 15100764238932767931856223)
    ·
      refine ⟨22651146358399151897784335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15100764238932767931856223 22651146358399151897784335)
      ·
        refine ⟨33976719537598727846676503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22651146358399151897784335 33976719537598727846676503)
        ·
          refine ⟨50965079306398091770014755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33976719537598727846676503 50965079306398091770014755)
          ·
            refine ⟨76447618959597137655022133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50965079306398091770014755 76447618959597137655022133)
            ·
              refine ⟨7166964277462231655158325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76447618959597137655022133 7166964277462231655158325)
              ·
                refine ⟨671902901012084217671093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7166964277462231655158325 671902901012084217671093)
                ·
                  refine ⟨62990896969882895406665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 671902901012084217671093 62990896969882895406665)
                  ·
                    rfl

theorem cell23_1104069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_1104069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104069 prefixEnd_1104069 := by exact prefixLift 1104069
  have htrace : WordTrace (prefixWord ++ tailWord_1104069) baseStart_1104069 baseEnd_1104069 := by
    simpa [prefixWord, tailWord_1104069, baseEnd_1104069] using wordTrace_append hprefix tailTrace_1104069
  have hstable : (prefixWord ++ tailWord_1104069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104069).length < 2 ^ (prefixWord ++ tailWord_1104069).sum := by decide
  have hdescent : baseEnd_1104069 < baseStart_1104069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104086 : List Nat := [5, 2, 1, 2, 1, 1, 1, 3, 7]
def baseStart_1104086 : Nat := 118140960795 + 1104086 * 2 ^ 59
def prefixEnd_1104086 : Nat := 4983230072969 + 3 ^ 40 * 1104086 * 2
def baseEnd_1104086 : Nat := 62991866877785832460823

theorem tailTrace_1104086 : CollatzResearch.WordTrace tailWord_1104086 prefixEnd_1104086 62991866877785832460823 := by
  unfold tailWord_1104086
  simp only [CollatzResearch.WordTrace]
  refine ⟨2516832792380778732603257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26846216452061639814434741 2516832792380778732603257)
  ·
    refine ⟨1887624594285584049452443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2516832792380778732603257 1887624594285584049452443)
    ·
      refine ⟨2831436891428376074178665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1887624594285584049452443 2831436891428376074178665)
      ·
        refine ⟨2123577668571282055633999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831436891428376074178665 2123577668571282055633999)
        ·
          refine ⟨3185366502856923083450999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123577668571282055633999 3185366502856923083450999)
          ·
            refine ⟨4778049754285384625176499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185366502856923083450999 4778049754285384625176499)
            ·
              refine ⟨7167074631428076937764749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778049754285384625176499 7167074631428076937764749)
              ·
                refine ⟨2687652986785528851661781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7167074631428076937764749 2687652986785528851661781)
                ·
                  refine ⟨62991866877785832460823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2687652986785528851661781 62991866877785832460823)
                  ·
                    rfl

theorem cell23_1104086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_1104086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104086 prefixEnd_1104086 := by exact prefixLift 1104086
  have htrace : WordTrace (prefixWord ++ tailWord_1104086) baseStart_1104086 baseEnd_1104086 := by
    simpa [prefixWord, tailWord_1104086, baseEnd_1104086] using wordTrace_append hprefix tailTrace_1104086
  have hstable : (prefixWord ++ tailWord_1104086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104086).length < 2 ^ (prefixWord ++ tailWord_1104086).sum := by decide
  have hdescent : baseEnd_1104086 < baseStart_1104086 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104089 : List Nat := [1, 2, 1, 2, 3, 1, 2, 1, 1, 7, 2]
def baseStart_1104089 : Nat := 118140960795 + 1104089 * 2 ^ 59
def prefixEnd_1104089 : Nat := 4983230072969 + 3 ^ 40 * 1104089 * 2
def baseEnd_1104089 : Nat := 566928342342035980409893

theorem tailTrace_1104089 : CollatzResearch.WordTrace tailWord_1104089 prefixEnd_1104089 566928342342035980409893 := by
  unfold tailWord_1104089
  simp only [CollatzResearch.WordTrace]
  refine ⟨40269434097081591234011321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26846289398054394156007547 40269434097081591234011321)
  ·
    refine ⟨30202075572811193425508491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40269434097081591234011321 30202075572811193425508491)
    ·
      refine ⟨45303113359216790138262737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30202075572811193425508491 45303113359216790138262737)
      ·
        refine ⟨33977335019412592603697053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45303113359216790138262737 33977335019412592603697053)
        ·
          refine ⟨12741500632279722226386395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33977335019412592603697053 12741500632279722226386395)
          ·
            refine ⟨19112250948419583339579593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12741500632279722226386395 19112250948419583339579593)
            ·
              refine ⟨14334188211314687504684695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19112250948419583339579593 14334188211314687504684695)
              ·
                refine ⟨21501282316972031257027043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14334188211314687504684695 21501282316972031257027043)
                ·
                  refine ⟨32251923475458046885540565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21501282316972031257027043 32251923475458046885540565)
                  ·
                    refine ⟨755904456456047973879857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32251923475458046885540565 755904456456047973879857)
                    ·
                      refine ⟨566928342342035980409893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 755904456456047973879857 566928342342035980409893)
                      ·
                        rfl

theorem cell23_1104089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 1, 1, 7, 2].length) (baseStart_1104089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104089 prefixEnd_1104089 := by exact prefixLift 1104089
  have htrace : WordTrace (prefixWord ++ tailWord_1104089) baseStart_1104089 baseEnd_1104089 := by
    simpa [prefixWord, tailWord_1104089, baseEnd_1104089] using wordTrace_append hprefix tailTrace_1104089
  have hstable : (prefixWord ++ tailWord_1104089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104089).length < 2 ^ (prefixWord ++ tailWord_1104089).sum := by decide
  have hdescent : baseEnd_1104089 < baseStart_1104089 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104136 : List Nat := [2, 1, 3, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1104136 : Nat := 118140960795 + 1104136 * 2 ^ 59
def prefixEnd_1104136 : Nat := 4983230072969 + 3 ^ 40 * 1104136 * 2
def baseEnd_1104136 : Nat := 566952475932797296522177

theorem tailTrace_1104136 : CollatzResearch.WordTrace tailWord_1104136 prefixEnd_1104136 566952475932797296522177 := by
  unfold tailWord_1104136
  simp only [CollatzResearch.WordTrace]
  refine ⟨20135574163955659130486131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26847432218607545507314841 20135574163955659130486131)
  ·
    refine ⟨30203361245933488695729197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20135574163955659130486131 30203361245933488695729197)
    ·
      refine ⟨11326260467225058260898449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30203361245933488695729197 11326260467225058260898449)
      ·
        refine ⟨8494695350418793695673837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11326260467225058260898449 8494695350418793695673837)
        ·
          refine ⟨3185510756407047635877689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8494695350418793695673837 3185510756407047635877689)
          ·
            refine ⟨2389133067305285726908267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3185510756407047635877689 2389133067305285726908267)
            ·
              refine ⟨3583699600957928590362401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2389133067305285726908267 3583699600957928590362401)
              ·
                refine ⟨2687774700718446442771801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3583699600957928590362401 2687774700718446442771801)
                ·
                  refine ⟨2015831025538834832078851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2687774700718446442771801 2015831025538834832078851)
                  ·
                    refine ⟨3023746538308252248118277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2015831025538834832078851 3023746538308252248118277)
                    ·
                      refine ⟨566952475932797296522177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3023746538308252248118277 566952475932797296522177)
                      ·
                        rfl

theorem cell23_1104136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1104136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104136 prefixEnd_1104136 := by exact prefixLift 1104136
  have htrace : WordTrace (prefixWord ++ tailWord_1104136) baseStart_1104136 baseEnd_1104136 := by
    simpa [prefixWord, tailWord_1104136, baseEnd_1104136] using wordTrace_append hprefix tailTrace_1104136
  have hstable : (prefixWord ++ tailWord_1104136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104136).length < 2 ^ (prefixWord ++ tailWord_1104136).sum := by decide
  have hdescent : baseEnd_1104136 < baseStart_1104136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104193 : List Nat := [1, 2, 5, 2, 2, 1, 2, 2, 6]
def baseStart_1104193 : Nat := 118140960795 + 1104193 * 2 ^ 59
def prefixEnd_1104193 : Nat := 4983230072969 + 3 ^ 40 * 1104193 * 2
def baseEnd_1104193 : Nat := 62997971592233730389935

theorem tailTrace_1104193 : CollatzResearch.WordTrace tailWord_1104193 prefixEnd_1104193 62997971592233730389935 := by
  unfold tailWord_1104193
  simp only [CollatzResearch.WordTrace]
  refine ⟨40273227288704816995797233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26848818192469877997198155 40273227288704816995797233)
  ·
    refine ⟨30204920466528612746847925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40273227288704816995797233 30204920466528612746847925)
    ·
      refine ⟨2831711293737057445016993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30204920466528612746847925 2831711293737057445016993)
      ·
        refine ⟨2123783470302793083762745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2831711293737057445016993 2123783470302793083762745)
        ·
          refine ⟨1592837602727094812822059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2123783470302793083762745 1592837602727094812822059)
          ·
            refine ⟨2389256404090642219233089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1592837602727094812822059 2389256404090642219233089)
            ·
              refine ⟨1791942303067981664424817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389256404090642219233089 1791942303067981664424817)
              ·
                refine ⟨1343956727300986248318613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1791942303067981664424817 1343956727300986248318613)
                ·
                  refine ⟨62997971592233730389935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1343956727300986248318613 62997971592233730389935)
                  ·
                    rfl

theorem cell23_1104193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 2, 2, 6].length) (baseStart_1104193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104193 prefixEnd_1104193 := by exact prefixLift 1104193
  have htrace : WordTrace (prefixWord ++ tailWord_1104193) baseStart_1104193 baseEnd_1104193 := by
    simpa [prefixWord, tailWord_1104193, baseEnd_1104193] using wordTrace_append hprefix tailTrace_1104193
  have hstable : (prefixWord ++ tailWord_1104193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104193).length < 2 ^ (prefixWord ++ tailWord_1104193).sum := by decide
  have hdescent : baseEnd_1104193 < baseStart_1104193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104239 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 4]
def baseStart_1104239 : Nat := 118140960795 + 1104239 * 2 ^ 59
def prefixEnd_1104239 : Nat := 4983230072969 + 3 ^ 40 * 1104239 * 2
def baseEnd_1104239 : Nat := 567005364440210393534203

theorem tailTrace_1104239 : CollatzResearch.WordTrace tailWord_1104239 prefixEnd_1104239 567005364440210393534203 := by
  unfold tailWord_1104239
  simp only [CollatzResearch.WordTrace]
  refine ⟨40274905046538166851971771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26849936697692111234647847 40274905046538166851971771)
  ·
    refine ⟨60412357569807250277957657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40274905046538166851971771 60412357569807250277957657)
    ·
      refine ⟨45309268177355437708468243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60412357569807250277957657 45309268177355437708468243)
      ·
        refine ⟨67963902266033156562702365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45309268177355437708468243 67963902266033156562702365)
        ·
          refine ⟨25486463349762433711013387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67963902266033156562702365 25486463349762433711013387)
          ·
            refine ⟨38229695024643650566520081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25486463349762433711013387 38229695024643650566520081)
            ·
              refine ⟨28672271268482737924890061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38229695024643650566520081 28672271268482737924890061)
              ·
                refine ⟨10752101725681026721833773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28672271268482737924890061 10752101725681026721833773)
                ·
                  refine ⟨4032038147130385020687665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10752101725681026721833773 4032038147130385020687665)
                  ·
                    refine ⟨3024028610347788765515749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4032038147130385020687665 3024028610347788765515749)
                    ·
                      refine ⟨567005364440210393534203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3024028610347788765515749 567005364440210393534203)
                      ·
                        rfl

theorem cell23_1104239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 3, 2, 4].length) (baseStart_1104239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104239 prefixEnd_1104239 := by exact prefixLift 1104239
  have htrace : WordTrace (prefixWord ++ tailWord_1104239) baseStart_1104239 baseEnd_1104239 := by
    simpa [prefixWord, tailWord_1104239, baseEnd_1104239] using wordTrace_append hprefix tailTrace_1104239
  have hstable : (prefixWord ++ tailWord_1104239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104239).length < 2 ^ (prefixWord ++ tailWord_1104239).sum := by decide
  have hdescent : baseEnd_1104239 < baseStart_1104239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104253 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 2, 4]
def baseStart_1104253 : Nat := 118140960795 + 1104253 * 2 ^ 59
def prefixEnd_1104253 : Nat := 4983230072969 + 3 ^ 40 * 1104253 * 2
def baseEnd_1104253 : Nat := 189004184389791112919713

theorem tailTrace_1104253 : CollatzResearch.WordTrace tailWord_1104253 prefixEnd_1104253 189004184389791112919713 := by
  unfold tailWord_1104253
  simp only [CollatzResearch.WordTrace]
  refine ⟨40275415668487447242981413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26850277112324964828654275 40275415668487447242981413)
  ·
    refine ⟨7551640437841396358059015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40275415668487447242981413 7551640437841396358059015)
    ·
      refine ⟨11327460656762094537088523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7551640437841396358059015 11327460656762094537088523)
      ·
        refine ⟨16991190985143141805632785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11327460656762094537088523 16991190985143141805632785)
        ·
          refine ⟨12743393238857356354224589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16991190985143141805632785 12743393238857356354224589)
          ·
            refine ⟨4778772464571508632834221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12743393238857356354224589 4778772464571508632834221)
            ·
              refine ⟨1792039674214315737312833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4778772464571508632834221 1792039674214315737312833)
              ·
                refine ⟨1344029755660736802984625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792039674214315737312833 1344029755660736802984625)
                ·
                  refine ⟨1008022316745552602238469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344029755660736802984625 1008022316745552602238469)
                  ·
                    refine ⟨189004184389791112919713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008022316745552602238469 189004184389791112919713)
                    ·
                      rfl

theorem cell23_1104253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 2, 4].length) (baseStart_1104253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104253 prefixEnd_1104253 := by exact prefixLift 1104253
  have htrace : WordTrace (prefixWord ++ tailWord_1104253) baseStart_1104253 baseEnd_1104253 := by
    simpa [prefixWord, tailWord_1104253, baseEnd_1104253] using wordTrace_append hprefix tailTrace_1104253
  have hstable : (prefixWord ++ tailWord_1104253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104253).length < 2 ^ (prefixWord ++ tailWord_1104253).sum := by decide
  have hdescent : baseEnd_1104253 < baseStart_1104253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104260 : List Nat := [2, 3, 2, 1, 1, 2, 4, 1, 3, 2, 2]
def baseStart_1104260 : Nat := 118140960795 + 1104260 * 2 ^ 59
def prefixEnd_1104260 : Nat := 4983230072969 + 3 ^ 40 * 1104260 * 2
def baseEnd_1104260 : Nat := 567016147533954811371607

theorem tailTrace_1104260 : CollatzResearch.WordTrace tailWord_1104260 prefixEnd_1104260 567016147533954811371607 := by
  unfold tailWord_1104260
  simp only [CollatzResearch.WordTrace]
  refine ⟨20137835489731043719243117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26850447319641391625657489 20137835489731043719243117)
  ·
    refine ⟨7551688308649141394716169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20137835489731043719243117 7551688308649141394716169)
    ·
      refine ⟨5663766231486856046037127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7551688308649141394716169 5663766231486856046037127)
      ·
        refine ⟨8495649347230284069055691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5663766231486856046037127 8495649347230284069055691)
        ·
          refine ⟨12743474020845426103583537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8495649347230284069055691 12743474020845426103583537)
          ·
            refine ⟨9557605515634069577687653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12743474020845426103583537 9557605515634069577687653)
            ·
              refine ⟨1792051034181388045816435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9557605515634069577687653 1792051034181388045816435)
              ·
                refine ⟨2688076551272082068724653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792051034181388045816435 2688076551272082068724653)
                ·
                  refine ⟨1008028706727030775771745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2688076551272082068724653 1008028706727030775771745)
                  ·
                    refine ⟨756021530045273081828809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1008028706727030775771745 756021530045273081828809)
                    ·
                      refine ⟨567016147533954811371607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756021530045273081828809 567016147533954811371607)
                      ·
                        rfl

theorem cell23_1104260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 4, 1, 3, 2, 2].length) (baseStart_1104260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104260 prefixEnd_1104260 := by exact prefixLift 1104260
  have htrace : WordTrace (prefixWord ++ tailWord_1104260) baseStart_1104260 baseEnd_1104260 := by
    simpa [prefixWord, tailWord_1104260, baseEnd_1104260] using wordTrace_append hprefix tailTrace_1104260
  have hstable : (prefixWord ++ tailWord_1104260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104260).length < 2 ^ (prefixWord ++ tailWord_1104260).sum := by decide
  have hdescent : baseEnd_1104260 < baseStart_1104260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104279 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 2, 7]
def baseStart_1104279 : Nat := 118140960795 + 1104279 * 2 ^ 59
def prefixEnd_1104279 : Nat := 4983230072969 + 3 ^ 40 * 1104279 * 2
def baseEnd_1104279 : Nat := 189008634555463412344673

theorem tailTrace_1104279 : CollatzResearch.WordTrace tailWord_1104279 prefixEnd_1104279 189008634555463412344673 := by
  unfold tailWord_1104279
  simp only [CollatzResearch.WordTrace]
  refine ⟨40276363966393253683427891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26850909310928835788951927 40276363966393253683427891)
  ·
    refine ⟨60414545949589880525141837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40276363966393253683427891 60414545949589880525141837)
    ·
      refine ⟨22655454731096205196928189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60414545949589880525141837 22655454731096205196928189)
      ·
        refine ⟨8495795524161076948848071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22655454731096205196928189 8495795524161076948848071)
        ·
          refine ⟨12743693286241615423272107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8495795524161076948848071 12743693286241615423272107)
          ·
            refine ⟨19115539929362423134908161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12743693286241615423272107 19115539929362423134908161)
            ·
              refine ⟨14336654947021817351181121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19115539929362423134908161 14336654947021817351181121)
              ·
                refine ⟨10752491210266363013385841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14336654947021817351181121 10752491210266363013385841)
                ·
                  refine ⟨8064368407699772260039381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10752491210266363013385841 8064368407699772260039381)
                  ·
                    refine ⟨189008634555463412344673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8064368407699772260039381 189008634555463412344673)
                    ·
                      rfl

theorem cell23_1104279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 7].length) (baseStart_1104279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104279 prefixEnd_1104279 := by exact prefixLift 1104279
  have htrace : WordTrace (prefixWord ++ tailWord_1104279) baseStart_1104279 baseEnd_1104279 := by
    simpa [prefixWord, tailWord_1104279, baseEnd_1104279] using wordTrace_append hprefix tailTrace_1104279
  have hstable : (prefixWord ++ tailWord_1104279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104279).length < 2 ^ (prefixWord ++ tailWord_1104279).sum := by decide
  have hdescent : baseEnd_1104279 < baseStart_1104279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104280 : List Nat := [2, 1, 2, 5, 1, 2, 2, 2, 1, 2, 3]
def baseStart_1104280 : Nat := 118140960795 + 1104280 * 2 ^ 59
def prefixEnd_1104280 : Nat := 4983230072969 + 3 ^ 40 * 1104280 * 2
def baseEnd_1104280 : Nat := 567026417147044733121515

theorem tailTrace_1104280 : CollatzResearch.WordTrace tailWord_1104280 prefixEnd_1104280 567026417147044733121515 := by
  unfold tailWord_1104280
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138200219694815427107147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26850933626259753902809529 20138200219694815427107147)
  ·
    refine ⟨30207300329542223140660721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20138200219694815427107147 30207300329542223140660721)
    ·
      refine ⟨22655475247156667355495541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30207300329542223140660721 22655475247156667355495541)
      ·
        refine ⟨2123950804420937564577707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22655475247156667355495541 2123950804420937564577707)
        ·
          refine ⟨3185926206631406346866561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2123950804420937564577707 3185926206631406346866561)
          ·
            refine ⟨2389444654973554760149921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3185926206631406346866561 2389444654973554760149921)
            ·
              refine ⟨1792083491230166070112441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389444654973554760149921 1792083491230166070112441)
              ·
                refine ⟨1344062618422624552584331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1792083491230166070112441 1344062618422624552584331)
                ·
                  refine ⟨2016093927633936828876497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344062618422624552584331 2016093927633936828876497)
                  ·
                    refine ⟨1512070445725452621657373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2016093927633936828876497 1512070445725452621657373)
                    ·
                      refine ⟨567026417147044733121515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1512070445725452621657373 567026417147044733121515)
                      ·
                        rfl

theorem cell23_1104280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 2, 2, 1, 2, 3].length) (baseStart_1104280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104280 prefixEnd_1104280 := by exact prefixLift 1104280
  have htrace : WordTrace (prefixWord ++ tailWord_1104280) baseStart_1104280 baseEnd_1104280 := by
    simpa [prefixWord, tailWord_1104280, baseEnd_1104280] using wordTrace_append hprefix tailTrace_1104280
  have hstable : (prefixWord ++ tailWord_1104280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104280).length < 2 ^ (prefixWord ++ tailWord_1104280).sum := by decide
  have hdescent : baseEnd_1104280 < baseStart_1104280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104321 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 2, 4]
def baseStart_1104321 : Nat := 118140960795 + 1104321 * 2 ^ 59
def prefixEnd_1104321 : Nat := 4983230072969 + 3 ^ 40 * 1104321 * 2
def baseEnd_1104321 : Nat := 189015823284626357569609

theorem tailTrace_1104321 : CollatzResearch.WordTrace tailWord_1104321 prefixEnd_1104321 189015823284626357569609 := by
  unfold tailWord_1104321
  simp only [CollatzResearch.WordTrace]
  refine ⟨40277895832241094856456817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26851930554827396570971211 40277895832241094856456817)
  ·
    refine ⟨30208421874180821142342613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40277895832241094856456817 30208421874180821142342613)
    ·
      refine ⟨708009887676112995523655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 30208421874180821142342613 708009887676112995523655)
      ·
        refine ⟨1062014831514169493285483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708009887676112995523655 1062014831514169493285483)
        ·
          refine ⟨1593022247271254239928225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062014831514169493285483 1593022247271254239928225)
          ·
            refine ⟨1194766685453440679946169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1593022247271254239928225 1194766685453440679946169)
            ·
              refine ⟨896075014090080509959627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1194766685453440679946169 896075014090080509959627)
              ·
                refine ⟨1344112521135120764939441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896075014090080509959627 1344112521135120764939441)
                ·
                  refine ⟨1008084390851340573704581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344112521135120764939441 1008084390851340573704581)
                  ·
                    refine ⟨189015823284626357569609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008084390851340573704581 189015823284626357569609)
                    ·
                      rfl

theorem cell23_1104321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_1104321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104321 prefixEnd_1104321 := by exact prefixLift 1104321
  have htrace : WordTrace (prefixWord ++ tailWord_1104321) baseStart_1104321 baseEnd_1104321 := by
    simpa [prefixWord, tailWord_1104321, baseEnd_1104321] using wordTrace_append hprefix tailTrace_1104321
  have hstable : (prefixWord ++ tailWord_1104321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104321).length < 2 ^ (prefixWord ++ tailWord_1104321).sum := by decide
  have hdescent : baseEnd_1104321 < baseStart_1104321 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104327 : List Nat := [1, 1, 4, 1, 1, 6, 2, 1, 2, 1, 3]
def baseStart_1104327 : Nat := 118140960795 + 1104327 * 2 ^ 59
def prefixEnd_1104327 : Nat := 4983230072969 + 3 ^ 40 * 1104327 * 2
def baseEnd_1104327 : Nat := 567050550737806049233799

theorem tailTrace_1104327 : CollatzResearch.WordTrace tailWord_1104327 prefixEnd_1104327 567050550737806049233799 := by
  unfold tailWord_1104327
  simp only [CollatzResearch.WordTrace]
  refine ⟨40278114670219357881175235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26852076446812905254116823 40278114670219357881175235)
  ·
    refine ⟨60417172005329036821762853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40278114670219357881175235 60417172005329036821762853)
    ·
      refine ⟨11328219750999194404080535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60417172005329036821762853 11328219750999194404080535)
      ·
        refine ⟨16992329626498791606120803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11328219750999194404080535 16992329626498791606120803)
        ·
          refine ⟨25488494439748187409181205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16992329626498791606120803 25488494439748187409181205)
          ·
            refine ⟨1194773176863196284805369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 25488494439748187409181205 1194773176863196284805369)
            ·
              refine ⟨896079882647397213604027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1194773176863196284805369 896079882647397213604027)
              ·
                refine ⟨1344119823971095820406041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896079882647397213604027 1344119823971095820406041)
                ·
                  refine ⟨1008089867978321865304531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344119823971095820406041 1008089867978321865304531)
                  ·
                    refine ⟨1512134801967482797956797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1008089867978321865304531 1512134801967482797956797)
                    ·
                      refine ⟨567050550737806049233799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1512134801967482797956797 567050550737806049233799)
                      ·
                        rfl

theorem cell23_1104327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 2, 1, 2, 1, 3].length) (baseStart_1104327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104327 prefixEnd_1104327 := by exact prefixLift 1104327
  have htrace : WordTrace (prefixWord ++ tailWord_1104327) baseStart_1104327 baseEnd_1104327 := by
    simpa [prefixWord, tailWord_1104327, baseEnd_1104327] using wordTrace_append hprefix tailTrace_1104327
  have hstable : (prefixWord ++ tailWord_1104327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104327).length < 2 ^ (prefixWord ++ tailWord_1104327).sum := by decide
  have hdescent : baseEnd_1104327 < baseStart_1104327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104407 : List Nat := [1, 1, 3, 6, 1, 1, 2, 3, 5]
def baseStart_1104407 : Nat := 118140960795 + 1104407 * 2 ^ 59
def prefixEnd_1104407 : Nat := 4983230072969 + 3 ^ 40 * 1104407 * 2
def baseEnd_1104407 : Nat := 63010181021129526248159

theorem tailTrace_1104407 : CollatzResearch.WordTrace tailWord_1104407 prefixEnd_1104407 63010181021129526248159 := by
  unfold tailWord_1104407
  simp only [CollatzResearch.WordTrace]
  refine ⟨40281032509929531544087475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26854021673286354362724983 40281032509929531544087475)
  ·
    refine ⟨60421548764894297316131213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40281032509929531544087475 60421548764894297316131213)
    ·
      refine ⟨22658080786835361493549205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60421548764894297316131213 22658080786835361493549205)
      ·
        refine ⟨1062097536882907570010119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 22658080786835361493549205 1062097536882907570010119)
        ·
          refine ⟨1593146305324361355015179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062097536882907570010119 1593146305324361355015179)
          ·
            refine ⟨2389719457986542032522769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593146305324361355015179 2389719457986542032522769)
            ·
              refine ⟨1792289593489906524392077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389719457986542032522769 1792289593489906524392077)
              ·
                refine ⟨672108597558714946647029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1792289593489906524392077 672108597558714946647029)
                ·
                  refine ⟨63010181021129526248159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 672108597558714946647029 63010181021129526248159)
                  ·
                    rfl

theorem cell23_1104407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 2, 3, 5].length) (baseStart_1104407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104407 prefixEnd_1104407 := by exact prefixLift 1104407
  have htrace : WordTrace (prefixWord ++ tailWord_1104407) baseStart_1104407 baseEnd_1104407 := by
    simpa [prefixWord, tailWord_1104407, baseEnd_1104407] using wordTrace_append hprefix tailTrace_1104407
  have hstable : (prefixWord ++ tailWord_1104407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104407).length < 2 ^ (prefixWord ++ tailWord_1104407).sum := by decide
  have hdescent : baseEnd_1104407 < baseStart_1104407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104433 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 3, 4]
def baseStart_1104433 : Nat := 118140960795 + 1104433 * 2 ^ 59
def prefixEnd_1104433 : Nat := 4983230072969 + 3 ^ 40 * 1104433 * 2
def baseEnd_1104433 : Nat := 189034993229060878169437

theorem tailTrace_1104433 : CollatzResearch.WordTrace tailWord_1104433 prefixEnd_1104433 189034993229060878169437 := by
  unfold tailWord_1104433
  simp only [CollatzResearch.WordTrace]
  refine ⟨40281980807835337984533953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26854653871890225323022635 40281980807835337984533953)
  ·
    refine ⟨30211485605876503488400465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40281980807835337984533953 30211485605876503488400465)
    ·
      refine ⟨22658614204407377616300349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30211485605876503488400465 22658614204407377616300349)
      ·
        refine ⟨8496980326652766606112631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22658614204407377616300349 8496980326652766606112631)
        ·
          refine ⟨12745470489979149909168947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8496980326652766606112631 12745470489979149909168947)
          ·
            refine ⟨19118205734968724863753421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12745470489979149909168947 19118205734968724863753421)
            ·
              refine ⟨7169327150613271823907533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19118205734968724863753421 7169327150613271823907533)
              ·
                refine ⟨2688497681479976933965325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7169327150613271823907533 2688497681479976933965325)
                ·
                  refine ⟨1008186630554991350236997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2688497681479976933965325 1008186630554991350236997)
                  ·
                    refine ⟨189034993229060878169437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008186630554991350236997 189034993229060878169437)
                    ·
                      rfl

theorem cell23_1104433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 3, 4].length) (baseStart_1104433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104433 prefixEnd_1104433 := by exact prefixLift 1104433
  have htrace : WordTrace (prefixWord ++ tailWord_1104433) baseStart_1104433 baseEnd_1104433 := by
    simpa [prefixWord, tailWord_1104433, baseEnd_1104433] using wordTrace_append hprefix tailTrace_1104433
  have hstable : (prefixWord ++ tailWord_1104433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104433).length < 2 ^ (prefixWord ++ tailWord_1104433).sum := by decide
  have hdescent : baseEnd_1104433 < baseStart_1104433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104517 : List Nat := [1, 3, 1, 1, 4, 3, 2, 1, 2, 3, 2]
def baseStart_1104517 : Nat := 118140960795 + 1104517 * 2 ^ 59
def prefixEnd_1104517 : Nat := 4983230072969 + 3 ^ 40 * 1104517 * 2
def baseEnd_1104517 : Nat := 567148112062160305857925

theorem tailTrace_1104517 : CollatzResearch.WordTrace tailWord_1104517 prefixEnd_1104517 567148112062160305857925 := by
  unfold tailWord_1104517
  simp only [CollatzResearch.WordTrace]
  refine ⟨40285044539531020330591805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26856696359687346887061203 40285044539531020330591805)
  ·
    refine ⟨15106891702324132623971927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40285044539531020330591805 15106891702324132623971927)
    ·
      refine ⟨22660337553486198935957891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15106891702324132623971927 22660337553486198935957891)
      ·
        refine ⟨33990506330229298403936837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22660337553486198935957891 33990506330229298403936837)
        ·
          refine ⟨6373219936917993450738157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 33990506330229298403936837 6373219936917993450738157)
          ·
            refine ⟨2389957476344247544026809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6373219936917993450738157 2389957476344247544026809)
            ·
              refine ⟨1792468107258185658020107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2389957476344247544026809 1792468107258185658020107)
              ·
                refine ⟨2688702160887278487030161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792468107258185658020107 2688702160887278487030161)
                ·
                  refine ⟨2016526620665458865272621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2688702160887278487030161 2016526620665458865272621)
                  ·
                    refine ⟨756197482749547074477233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2016526620665458865272621 756197482749547074477233)
                    ·
                      refine ⟨567148112062160305857925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756197482749547074477233 567148112062160305857925)
                      ·
                        rfl

theorem cell23_1104517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 3, 2, 1, 2, 3, 2].length) (baseStart_1104517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104517 prefixEnd_1104517 := by exact prefixLift 1104517
  have htrace : WordTrace (prefixWord ++ tailWord_1104517) baseStart_1104517 baseEnd_1104517 := by
    simpa [prefixWord, tailWord_1104517, baseEnd_1104517] using wordTrace_append hprefix tailTrace_1104517
  have hstable : (prefixWord ++ tailWord_1104517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104517).length < 2 ^ (prefixWord ++ tailWord_1104517).sum := by decide
  have hdescent : baseEnd_1104517 < baseStart_1104517 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104523 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 4, 4]
def baseStart_1104523 : Nat := 118140960795 + 1104523 * 2 ^ 59
def prefixEnd_1104523 : Nat := 4983230072969 + 3 ^ 40 * 1104523 * 2
def baseEnd_1104523 : Nat := 189050397648695760794299

theorem tailTrace_1104523 : CollatzResearch.WordTrace tailWord_1104523 prefixEnd_1104523 189050397648695760794299 := by
  unfold tailWord_1104523
  simp only [CollatzResearch.WordTrace]
  refine ⟨40285263377509283355310223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26856842251672855570206815 40285263377509283355310223)
  ·
    refine ⟨60427895066263925032965335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40285263377509283355310223 60427895066263925032965335)
    ·
      refine ⟨90641842599395887549448003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60427895066263925032965335 90641842599395887549448003)
      ·
        refine ⟨135962763899093831324172005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90641842599395887549448003 135962763899093831324172005)
        ·
          refine ⟨25493018231080093373282251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135962763899093831324172005 25493018231080093373282251)
          ·
            refine ⟨38239527346620140059923377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25493018231080093373282251 38239527346620140059923377)
            ·
              refine ⟨28679645509965105044942533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38239527346620140059923377 28679645509965105044942533)
              ·
                refine ⟨5377433533118457195926725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28679645509965105044942533 5377433533118457195926725)
                ·
                  refine ⟨1008268787459710724236261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5377433533118457195926725 1008268787459710724236261)
                  ·
                    refine ⟨189050397648695760794299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008268787459710724236261 189050397648695760794299)
                    ·
                      rfl

theorem cell23_1104523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 4, 4].length) (baseStart_1104523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104523 prefixEnd_1104523 := by exact prefixLift 1104523
  have htrace : WordTrace (prefixWord ++ tailWord_1104523) baseStart_1104523 baseEnd_1104523 := by
    simpa [prefixWord, tailWord_1104523, baseEnd_1104523] using wordTrace_append hprefix tailTrace_1104523
  have hstable : (prefixWord ++ tailWord_1104523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104523).length < 2 ^ (prefixWord ++ tailWord_1104523).sum := by decide
  have hdescent : baseEnd_1104523 < baseStart_1104523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104557 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 2, 4]
def baseStart_1104557 : Nat := 118140960795 + 1104557 * 2 ^ 59
def prefixEnd_1104557 : Nat := 4983230072969 + 3 ^ 40 * 1104557 * 2
def baseEnd_1104557 : Nat := 189056217096113383119247

theorem tailTrace_1104557 : CollatzResearch.WordTrace tailWord_1104557 prefixEnd_1104557 189056217096113383119247 := by
  unfold tailWord_1104557
  simp only [CollatzResearch.WordTrace]
  refine ⟨40286503459386107162047925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26857668972924071441365283 40286503459386107162047925)
  ·
    refine ⟨3776859699317447546441993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40286503459386107162047925 3776859699317447546441993)
    ·
      refine ⟨2832644774488085659831495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3776859699317447546441993 2832644774488085659831495)
      ·
        refine ⟨4248967161732128489747243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2832644774488085659831495 4248967161732128489747243)
        ·
          refine ⟨6373450742598192734620865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4248967161732128489747243 6373450742598192734620865)
          ·
            refine ⟨4780088056948644550965649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6373450742598192734620865 4780088056948644550965649)
            ·
              refine ⟨3585066042711483413224237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4780088056948644550965649 3585066042711483413224237)
              ·
                refine ⟨1344399766016806279959089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3585066042711483413224237 1344399766016806279959089)
                ·
                  refine ⟨1008299824512604709969317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344399766016806279959089 1008299824512604709969317)
                  ·
                    refine ⟨189056217096113383119247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008299824512604709969317 189056217096113383119247)
                    ·
                      rfl

theorem cell23_1104557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_1104557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104557 prefixEnd_1104557 := by exact prefixLift 1104557
  have htrace : WordTrace (prefixWord ++ tailWord_1104557) baseStart_1104557 baseEnd_1104557 := by
    simpa [prefixWord, tailWord_1104557, baseEnd_1104557] using wordTrace_append hprefix tailTrace_1104557
  have hstable : (prefixWord ++ tailWord_1104557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104557).length < 2 ^ (prefixWord ++ tailWord_1104557).sum := by decide
  have hdescent : baseEnd_1104557 < baseStart_1104557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104584 : List Nat := [2, 1, 3, 1, 2, 5, 2, 1, 1, 2, 3]
def baseStart_1104584 : Nat := 118140960795 + 1104584 * 2 ^ 59
def prefixEnd_1104584 : Nat := 4983230072969 + 3 ^ 40 * 1104584 * 2
def baseEnd_1104584 : Nat := 567182515266011543720117

theorem tailTrace_1104584 : CollatzResearch.WordTrace tailWord_1104584 prefixEnd_1104584 567182515266011543720117 := by
  unfold tailWord_1104584
  simp only [CollatzResearch.WordTrace]
  refine ⟨20143744115144145386640403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26858325486858860515520537 20143744115144145386640403)
  ·
    refine ⟨30215616172716218079960605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20143744115144145386640403 30215616172716218079960605)
    ·
      refine ⟨11330856064768581779985227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30215616172716218079960605 11330856064768581779985227)
      ·
        refine ⟨16996284097152872669977841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11330856064768581779985227 16996284097152872669977841)
        ·
          refine ⟨12747213072864654502483381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16996284097152872669977841 12747213072864654502483381)
          ·
            refine ⟨1195051225581061359607817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12747213072864654502483381 1195051225581061359607817)
            ·
              refine ⟨896288419185796019705863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1195051225581061359607817 896288419185796019705863)
              ·
                refine ⟨1344432628778694029558795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896288419185796019705863 1344432628778694029558795)
                ·
                  refine ⟨2016648943168041044338193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1344432628778694029558795 2016648943168041044338193)
                  ·
                    refine ⟨1512486707376030783253645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2016648943168041044338193 1512486707376030783253645)
                    ·
                      refine ⟨567182515266011543720117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1512486707376030783253645 567182515266011543720117)
                      ·
                        rfl

theorem cell23_1104584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 2, 1, 1, 2, 3].length) (baseStart_1104584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104584 prefixEnd_1104584 := by exact prefixLift 1104584
  have htrace : WordTrace (prefixWord ++ tailWord_1104584) baseStart_1104584 baseEnd_1104584 := by
    simpa [prefixWord, tailWord_1104584, baseEnd_1104584] using wordTrace_append hprefix tailTrace_1104584
  have hstable : (prefixWord ++ tailWord_1104584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104584).length < 2 ^ (prefixWord ++ tailWord_1104584).sum := by decide
  have hdescent : baseEnd_1104584 < baseStart_1104584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104633 : List Nat := [1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 4]
def baseStart_1104633 : Nat := 118140960795 + 1104633 * 2 ^ 59
def prefixEnd_1104633 : Nat := 4983230072969 + 3 ^ 40 * 1104633 * 2
def baseEnd_1104633 : Nat := 567207675818081852007391

theorem tailTrace_1104633 : CollatzResearch.WordTrace tailWord_1104633 prefixEnd_1104633 567207675818081852007391 := by
  unfold tailWord_1104633
  simp only [CollatzResearch.WordTrace]
  refine ⟨40289275407110772141814553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26859516938073848094543035 40289275407110772141814553)
  ·
    refine ⟨30216956555333079106360915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40289275407110772141814553 30216956555333079106360915)
    ·
      refine ⟨45325434832999618659541373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30216956555333079106360915 45325434832999618659541373)
      ·
        refine ⟨16997038062374856997328015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45325434832999618659541373 16997038062374856997328015)
        ·
          refine ⟨25495557093562285495992023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16997038062374856997328015 25495557093562285495992023)
          ·
            refine ⟨38243335640343428243988035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25495557093562285495992023 38243335640343428243988035)
            ·
              refine ⟨57365003460515142365982053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38243335640343428243988035 57365003460515142365982053)
              ·
                refine ⟨10755938148846589193621635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57365003460515142365982053 10755938148846589193621635)
                ·
                  refine ⟨16133907223269883790432453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10755938148846589193621635 16133907223269883790432453)
                  ·
                    refine ⟨3025107604363103210706085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16133907223269883790432453 3025107604363103210706085)
                    ·
                      refine ⟨567207675818081852007391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3025107604363103210706085 567207675818081852007391)
                      ·
                        rfl

theorem cell23_1104633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 4, 4].length) (baseStart_1104633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104633 prefixEnd_1104633 := by exact prefixLift 1104633
  have htrace : WordTrace (prefixWord ++ tailWord_1104633) baseStart_1104633 baseEnd_1104633 := by
    simpa [prefixWord, tailWord_1104633, baseEnd_1104633] using wordTrace_append hprefix tailTrace_1104633
  have hstable : (prefixWord ++ tailWord_1104633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104633).length < 2 ^ (prefixWord ++ tailWord_1104633).sum := by decide
  have hdescent : baseEnd_1104633 < baseStart_1104633 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104637 : List Nat := [1, 4, 1, 1, 1, 1, 3, 1, 6, 2, 2]
def baseStart_1104637 : Nat := 118140960795 + 1104637 * 2 ^ 59
def prefixEnd_1104637 : Nat := 4983230072969 + 3 ^ 40 * 1104637 * 2
def baseEnd_1104637 : Nat := 567209729740699836357373

theorem tailTrace_1104637 : CollatzResearch.WordTrace tailWord_1104637 prefixEnd_1104637 567209729740699836357373 := by
  unfold tailWord_1104637
  simp only [CollatzResearch.WordTrace]
  refine ⟨40289421299096280824960165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26859614199397520549973443 40289421299096280824960165)
  ·
    refine ⟨7554266493580552654680031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40289421299096280824960165 7554266493580552654680031)
    ·
      refine ⟨11331399740370828982020047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7554266493580552654680031 11331399740370828982020047)
      ·
        refine ⟨16997099610556243473030071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11331399740370828982020047 16997099610556243473030071)
        ·
          refine ⟨25495649415834365209545107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16997099610556243473030071 25495649415834365209545107)
          ·
            refine ⟨38243474123751547814317661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25495649415834365209545107 38243474123751547814317661)
            ·
              refine ⟨14341302796406830430369123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38243474123751547814317661 14341302796406830430369123)
              ·
                refine ⟨21511954194610245645553685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14341302796406830430369123 21511954194610245645553685)
                ·
                  refine ⟨1008372852872355264635329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21511954194610245645553685 1008372852872355264635329)
                  ·
                    refine ⟨756279639654266448476497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1008372852872355264635329 756279639654266448476497)
                    ·
                      refine ⟨567209729740699836357373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756279639654266448476497 567209729740699836357373)
                      ·
                        rfl

theorem cell23_1104637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 3, 1, 6, 2, 2].length) (baseStart_1104637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104637 prefixEnd_1104637 := by exact prefixLift 1104637
  have htrace : WordTrace (prefixWord ++ tailWord_1104637) baseStart_1104637 baseEnd_1104637 := by
    simpa [prefixWord, tailWord_1104637, baseEnd_1104637] using wordTrace_append hprefix tailTrace_1104637
  have hstable : (prefixWord ++ tailWord_1104637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104637).length < 2 ^ (prefixWord ++ tailWord_1104637).sum := by decide
  have hdescent : baseEnd_1104637 < baseStart_1104637 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104654 : List Nat := [4, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2]
def baseStart_1104654 : Nat := 118140960795 + 1104654 * 2 ^ 59
def prefixEnd_1104654 : Nat := 4983230072969 + 3 ^ 40 * 1104654 * 2
def baseEnd_1104654 : Nat := 567218458911826269844795

theorem tailTrace_1104654 : CollatzResearch.WordTrace tailWord_1104654 prefixEnd_1104654 567218458911826269844795 := by
  unfold tailWord_1104654
  simp only [CollatzResearch.WordTrace]
  refine ⟨5036255167504336591041127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26860027560023128485552677 5036255167504336591041127)
  ·
    refine ⟨7554382751256504886561691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5036255167504336591041127 7554382751256504886561691)
    ·
      refine ⟨11331574126884757329842537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7554382751256504886561691 11331574126884757329842537)
      ·
        refine ⟨8498680595163567997381903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11331574126884757329842537 8498680595163567997381903)
        ·
          refine ⟨12748020892745351996072855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8498680595163567997381903 12748020892745351996072855)
          ·
            refine ⟨19122031339118027994109283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12748020892745351996072855 19122031339118027994109283)
            ·
              refine ⟨28683047008677041991163925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19122031339118027994109283 28683047008677041991163925)
              ·
                refine ⟨1344517828531736343335809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 28683047008677041991163925 1344517828531736343335809)
                ·
                  refine ⟨1008388371398802257501857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344517828531736343335809 1008388371398802257501857)
                  ·
                    refine ⟨756291278549101693126393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1008388371398802257501857 756291278549101693126393)
                    ·
                      refine ⟨567218458911826269844795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756291278549101693126393 567218458911826269844795)
                      ·
                        rfl

theorem cell23_1104654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_1104654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104654 prefixEnd_1104654 := by exact prefixLift 1104654
  have htrace : WordTrace (prefixWord ++ tailWord_1104654) baseStart_1104654 baseEnd_1104654 := by
    simpa [prefixWord, tailWord_1104654, baseEnd_1104654] using wordTrace_append hprefix tailTrace_1104654
  have hstable : (prefixWord ++ tailWord_1104654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104654).length < 2 ^ (prefixWord ++ tailWord_1104654).sum := by decide
  have hdescent : baseEnd_1104654 < baseStart_1104654 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104671 : List Nat := [1, 1, 2, 4, 2, 2, 4, 1, 2, 2, 2]
def baseStart_1104671 : Nat := 118140960795 + 1104671 * 2 ^ 59
def prefixEnd_1104671 : Nat := 4983230072969 + 3 ^ 40 * 1104671 * 2
def baseEnd_1104671 : Nat := 567227188082952703332217

theorem tailTrace_1104671 : CollatzResearch.WordTrace tailWord_1104671 prefixEnd_1104671 567227188082952703332217 := by
  unfold tailWord_1104671
  simp only [CollatzResearch.WordTrace]
  refine ⟨40290661380973104631697867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26860440920648736421131911 40290661380973104631697867)
  ·
    refine ⟨60435992071459656947546801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40290661380973104631697867 60435992071459656947546801)
    ·
      refine ⟨45326994053594742710660101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60435992071459656947546801 45326994053594742710660101)
      ·
        refine ⟨8498811385049014258248769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45326994053594742710660101 8498811385049014258248769)
        ·
          refine ⟨6374108538786760693686577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8498811385049014258248769 6374108538786760693686577)
          ·
            refine ⟨4780581404090070520264933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6374108538786760693686577 4780581404090070520264933)
            ·
              refine ⟨896359013266888222549675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4780581404090070520264933 896359013266888222549675)
              ·
                refine ⟨1344538519900332333824513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896359013266888222549675 1344538519900332333824513)
                ·
                  refine ⟨1008403889925249250368385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344538519900332333824513 1008403889925249250368385)
                  ·
                    refine ⟨756302917443936937776289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1008403889925249250368385 756302917443936937776289)
                    ·
                      refine ⟨567227188082952703332217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756302917443936937776289 567227188082952703332217)
                      ·
                        rfl

theorem cell23_1104671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_1104671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104671 prefixEnd_1104671 := by exact prefixLift 1104671
  have htrace : WordTrace (prefixWord ++ tailWord_1104671) baseStart_1104671 baseEnd_1104671 := by
    simpa [prefixWord, tailWord_1104671, baseEnd_1104671] using wordTrace_append hprefix tailTrace_1104671
  have hstable : (prefixWord ++ tailWord_1104671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104671).length < 2 ^ (prefixWord ++ tailWord_1104671).sum := by decide
  have hdescent : baseEnd_1104671 < baseStart_1104671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104683 : List Nat := [1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5]
def baseStart_1104683 : Nat := 118140960795 + 1104683 * 2 ^ 59
def prefixEnd_1104683 : Nat := 4983230072969 + 3 ^ 40 * 1104683 * 2
def baseEnd_1104683 : Nat := 567233349850806656382161

theorem tailTrace_1104683 : CollatzResearch.WordTrace tailWord_1104683 prefixEnd_1104683 567233349850806656382161 := by
  unfold tailWord_1104683
  simp only [CollatzResearch.WordTrace]
  refine ⟨40291099056929630681134703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26860732704619753787423135 40291099056929630681134703)
  ·
    refine ⟨60436648585394446021702055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40291099056929630681134703 60436648585394446021702055)
    ·
      refine ⟨90654972878091669032553083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60436648585394446021702055 90654972878091669032553083)
      ·
        refine ⟨135982459317137503548829625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90654972878091669032553083 135982459317137503548829625)
        ·
          refine ⟨101986844487853127661622219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135982459317137503548829625 101986844487853127661622219)
          ·
            refine ⟨152980266731779691492433329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101986844487853127661622219 152980266731779691492433329)
            ·
              refine ⟨114735200048834768619324997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152980266731779691492433329 114735200048834768619324997)
              ·
                refine ⟨21512850009156519116123437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114735200048834768619324997 21512850009156519116123437)
                ·
                  refine ⟨8067318753433694668546289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21512850009156519116123437 8067318753433694668546289)
                  ·
                    refine ⟨6050489065075271001409717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8067318753433694668546289 6050489065075271001409717)
                    ·
                      refine ⟨567233349850806656382161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6050489065075271001409717 567233349850806656382161)
                      ·
                        rfl

theorem cell23_1104683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_1104683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104683 prefixEnd_1104683 := by exact prefixLift 1104683
  have htrace : WordTrace (prefixWord ++ tailWord_1104683) baseStart_1104683 baseEnd_1104683 := by
    simpa [prefixWord, tailWord_1104683, baseEnd_1104683] using wordTrace_append hprefix tailTrace_1104683
  have hstable : (prefixWord ++ tailWord_1104683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104683).length < 2 ^ (prefixWord ++ tailWord_1104683).sum := by decide
  have hdescent : baseEnd_1104683 < baseStart_1104683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104727 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 1, 6, 2]
def baseStart_1104727 : Nat := 118140960795 + 1104727 * 2 ^ 59
def prefixEnd_1104727 : Nat := 4983230072969 + 3 ^ 40 * 1104727 * 2
def baseEnd_1104727 : Nat := 567255942999604484231959

theorem tailTrace_1104727 : CollatzResearch.WordTrace tailWord_1104727 prefixEnd_1104727 567255942999604484231959 := by
  unfold tailWord_1104727
  simp only [CollatzResearch.WordTrace]
  refine ⟨40292703868770226195736435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26861802579180150797157623 40292703868770226195736435)
  ·
    refine ⟨60439055803155339293604653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40292703868770226195736435 60439055803155339293604653)
    ·
      refine ⟨22664645926183252235101745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60439055803155339293604653 22664645926183252235101745)
      ·
        refine ⟨16998484444637439176326309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22664645926183252235101745 16998484444637439176326309)
        ·
          refine ⟨3187215833369519845561183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16998484444637439176326309 3187215833369519845561183)
          ·
            refine ⟨4780823750054279768341775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187215833369519845561183 4780823750054279768341775)
            ·
              refine ⟨7171235625081419652512663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4780823750054279768341775 7171235625081419652512663)
              ·
                refine ⟨10756853437622129478768995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7171235625081419652512663 10756853437622129478768995)
                ·
                  refine ⟨16135280156433194218153493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10756853437622129478768995 16135280156433194218153493)
                  ·
                    refine ⟨756341257332805978975945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16135280156433194218153493 756341257332805978975945)
                    ·
                      refine ⟨567255942999604484231959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756341257332805978975945 567255942999604484231959)
                      ·
                        rfl

theorem cell23_1104727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_1104727 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104727 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104727 prefixEnd_1104727 := by exact prefixLift 1104727
  have htrace : WordTrace (prefixWord ++ tailWord_1104727) baseStart_1104727 baseEnd_1104727 := by
    simpa [prefixWord, tailWord_1104727, baseEnd_1104727] using wordTrace_append hprefix tailTrace_1104727
  have hstable : (prefixWord ++ tailWord_1104727).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104727).length < 2 ^ (prefixWord ++ tailWord_1104727).sum := by decide
  have hdescent : baseEnd_1104727 < baseStart_1104727 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104744 : List Nat := [2, 1, 4, 2, 1, 4, 1, 1, 2, 1, 4]
def baseStart_1104744 : Nat := 118140960795 + 1104744 * 2 ^ 59
def prefixEnd_1104744 : Nat := 4983230072969 + 3 ^ 40 * 1104744 * 2
def baseEnd_1104744 : Nat := 567264672170730917719381

theorem tailTrace_1104744 : CollatzResearch.WordTrace tailWord_1104744 prefixEnd_1104744 567264672170730917719381 := by
  unfold tailWord_1104744
  simp only [CollatzResearch.WordTrace]
  refine ⟨20146661954854319049552643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26862215939805758732736857 20146661954854319049552643)
  ·
    refine ⟨30219992932281478574328965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20146661954854319049552643 30219992932281478574328965)
    ·
      refine ⟨5666248674802777232686681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30219992932281478574328965 5666248674802777232686681)
      ·
        refine ⟨4249686506102082924515011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5666248674802777232686681 4249686506102082924515011)
        ·
          refine ⟨6374529759153124386772517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4249686506102082924515011 6374529759153124386772517)
          ·
            refine ⟨1195224329841210822519847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6374529759153124386772517 1195224329841210822519847)
            ·
              refine ⟨1792836494761816233779771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195224329841210822519847 1792836494761816233779771)
              ·
                refine ⟨2689254742142724350669657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792836494761816233779771 2689254742142724350669657)
                ·
                  refine ⟨2016941056607043263002243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2689254742142724350669657 2016941056607043263002243)
                  ·
                    refine ⟨3025411584910564894503365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2016941056607043263002243 3025411584910564894503365)
                    ·
                      refine ⟨567264672170730917719381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3025411584910564894503365 567264672170730917719381)
                      ·
                        rfl

theorem cell23_1104744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 4, 1, 1, 2, 1, 4].length) (baseStart_1104744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104744 prefixEnd_1104744 := by exact prefixLift 1104744
  have htrace : WordTrace (prefixWord ++ tailWord_1104744) baseStart_1104744 baseEnd_1104744 := by
    simpa [prefixWord, tailWord_1104744, baseEnd_1104744] using wordTrace_append hprefix tailTrace_1104744
  have hstable : (prefixWord ++ tailWord_1104744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104744).length < 2 ^ (prefixWord ++ tailWord_1104744).sum := by decide
  have hdescent : baseEnd_1104744 < baseStart_1104744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104747 : List Nat := [1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 3]
def baseStart_1104747 : Nat := 118140960795 + 1104747 * 2 ^ 59
def prefixEnd_1104747 : Nat := 4983230072969 + 3 ^ 40 * 1104747 * 2
def baseEnd_1104747 : Nat := 567266212612694405981867

theorem tailTrace_1104747 : CollatzResearch.WordTrace tailWord_1104747 prefixEnd_1104747 567266212612694405981867 := by
  unfold tailWord_1104747
  simp only [CollatzResearch.WordTrace]
  refine ⟨40293433328697769611464495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26862288885798513074309663 40293433328697769611464495)
  ·
    refine ⟨60440149993046654417196743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40293433328697769611464495 60440149993046654417196743)
    ·
      refine ⟨90660224989569981625795115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60440149993046654417196743 90660224989569981625795115)
      ·
        refine ⟨135990337484354972438692673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90660224989569981625795115 135990337484354972438692673)
        ·
          refine ⟨101992753113266229329019505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135990337484354972438692673 101992753113266229329019505)
          ·
            refine ⟨76494564834949671996764629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101992753113266229329019505 76494564834949671996764629)
            ·
              refine ⟨1792841363319132937424171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 76494564834949671996764629 1792841363319132937424171)
              ·
                refine ⟨2689262044978699406136257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792841363319132937424171 2689262044978699406136257)
                ·
                  refine ⟨2016946533734024554602193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2689262044978699406136257 2016946533734024554602193)
                  ·
                    refine ⟨1512709900300518415951645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2016946533734024554602193 1512709900300518415951645)
                    ·
                      refine ⟨567266212612694405981867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1512709900300518415951645 567266212612694405981867)
                      ·
                        rfl

theorem cell23_1104747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 1, 2, 2, 3].length) (baseStart_1104747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104747 prefixEnd_1104747 := by exact prefixLift 1104747
  have htrace : WordTrace (prefixWord ++ tailWord_1104747) baseStart_1104747 baseEnd_1104747 := by
    simpa [prefixWord, tailWord_1104747, baseEnd_1104747] using wordTrace_append hprefix tailTrace_1104747
  have hstable : (prefixWord ++ tailWord_1104747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104747).length < 2 ^ (prefixWord ++ tailWord_1104747).sum := by decide
  have hdescent : baseEnd_1104747 < baseStart_1104747 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104754 : List Nat := [3, 2, 1, 2, 1, 1, 3, 5, 1, 4]
def baseStart_1104754 : Nat := 118140960795 + 1104754 * 2 ^ 59
def prefixEnd_1104754 : Nat := 4983230072969 + 3 ^ 40 * 1104754 * 2
def baseEnd_1104754 : Nat := 189089935659091959531445

theorem tailTrace_1104754 : CollatzResearch.WordTrace tailWord_1104754 prefixEnd_1104754 189089935659091959531445 := by
  unfold tailWord_1104754
  simp only [CollatzResearch.WordTrace]
  refine ⟨10073422159918102451742329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26862459093114939871312877 10073422159918102451742329)
  ·
    refine ⟨7555066619938576838806747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10073422159918102451742329 7555066619938576838806747)
    ·
      refine ⟨11332599929907865258210121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7555066619938576838806747 11332599929907865258210121)
      ·
        refine ⟨8499449947430898943657591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11332599929907865258210121 8499449947430898943657591)
        ·
          refine ⟨12749174921146348415486387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8499449947430898943657591 12749174921146348415486387)
          ·
            refine ⟨19123762381719522623229581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12749174921146348415486387 19123762381719522623229581)
            ·
              refine ⟨7171410893144820983711093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19123762381719522623229581 7171410893144820983711093)
              ·
                refine ⟨672319771232326967222915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7171410893144820983711093 672319771232326967222915)
                ·
                  refine ⟨1008479656848490450834373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672319771232326967222915 1008479656848490450834373)
                  ·
                    refine ⟨189089935659091959531445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008479656848490450834373 189089935659091959531445)
                    ·
                      rfl

theorem cell23_1104754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 5, 1, 4].length) (baseStart_1104754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104754 prefixEnd_1104754 := by exact prefixLift 1104754
  have htrace : WordTrace (prefixWord ++ tailWord_1104754) baseStart_1104754 baseEnd_1104754 := by
    simpa [prefixWord, tailWord_1104754, baseEnd_1104754] using wordTrace_append hprefix tailTrace_1104754
  have hstable : (prefixWord ++ tailWord_1104754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104754).length < 2 ^ (prefixWord ++ tailWord_1104754).sum := by decide
  have hdescent : baseEnd_1104754 < baseStart_1104754 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104780 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 5, 5]
def baseStart_1104780 : Nat := 118140960795 + 1104780 * 2 ^ 59
def prefixEnd_1104780 : Nat := 4983230072969 + 3 ^ 40 * 1104780 * 2
def baseEnd_1104780 : Nat := 189094385824764258956405

theorem tailTrace_1104780 : CollatzResearch.WordTrace tailWord_1104780 prefixEnd_1104780 189094385824764258956405 := by
  unfold tailWord_1104780
  simp only [CollatzResearch.WordTrace]
  refine ⟨20147318468789108123707897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26863091291718810831610529 20147318468789108123707897)
  ·
    refine ⟨15110488851591831092780923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20147318468789108123707897 15110488851591831092780923)
    ·
      refine ⟨22665733277387746639171385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15110488851591831092780923 22665733277387746639171385)
      ·
        refine ⟨16999299958040809979378539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22665733277387746639171385 16999299958040809979378539)
        ·
          refine ⟨25498949937061214969067809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16999299958040809979378539 25498949937061214969067809)
          ·
            refine ⟨19124212452795911226800857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25498949937061214969067809 19124212452795911226800857)
            ·
              refine ⟨14343159339596933420100643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19124212452795911226800857 14343159339596933420100643)
              ·
                refine ⟨21514739009395400130150965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14343159339596933420100643 21514739009395400130150965)
                ·
                  refine ⟨2017006782130818762201653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 21514739009395400130150965 2017006782130818762201653)
                  ·
                    refine ⟨189094385824764258956405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2017006782130818762201653 189094385824764258956405)
                    ·
                      rfl

theorem cell23_1104780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 5, 5].length) (baseStart_1104780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104780 prefixEnd_1104780 := by exact prefixLift 1104780
  have htrace : WordTrace (prefixWord ++ tailWord_1104780) baseStart_1104780 baseEnd_1104780 := by
    simpa [prefixWord, tailWord_1104780, baseEnd_1104780] using wordTrace_append hprefix tailTrace_1104780
  have hstable : (prefixWord ++ tailWord_1104780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104780).length < 2 ^ (prefixWord ++ tailWord_1104780).sum := by decide
  have hdescent : baseEnd_1104780 < baseStart_1104780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104787 : List Nat := [1, 1, 1, 2, 1, 2, 1, 3, 6, 3, 2]
def baseStart_1104787 : Nat := 118140960795 + 1104787 * 2 ^ 59
def prefixEnd_1104787 : Nat := 4983230072969 + 3 ^ 40 * 1104787 * 2
def baseEnd_1104787 : Nat := 567286751838874249481683

theorem tailTrace_1104787 : CollatzResearch.WordTrace tailWord_1104787 prefixEnd_1104787 567286751838874249481683 := by
  unfold tailWord_1104787
  simp only [CollatzResearch.WordTrace]
  refine ⟨40294892248552856442920615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26863261499035237628613743 40294892248552856442920615)
  ·
    refine ⟨60442338372829284664380923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40294892248552856442920615 60442338372829284664380923)
    ·
      refine ⟨90663507559243926996571385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60442338372829284664380923 90663507559243926996571385)
      ·
        refine ⟨67997630669432945247428539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90663507559243926996571385 67997630669432945247428539)
        ·
          refine ⟨101996446004149417871142809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67997630669432945247428539 101996446004149417871142809)
          ·
            refine ⟨76497334503112063403357107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101996446004149417871142809 76497334503112063403357107)
            ·
              refine ⟨114746001754668095105035661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76497334503112063403357107 114746001754668095105035661)
              ·
                refine ⟨43029750658000535664388373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114746001754668095105035661 43029750658000535664388373)
                ·
                  refine ⟨2017019562093775109268205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 43029750658000535664388373 2017019562093775109268205)
                  ·
                    refine ⟨756382335785165665975577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017019562093775109268205 756382335785165665975577)
                    ·
                      refine ⟨567286751838874249481683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756382335785165665975577 567286751838874249481683)
                      ·
                        rfl

theorem cell23_1104787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 3, 6, 3, 2].length) (baseStart_1104787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104787 prefixEnd_1104787 := by exact prefixLift 1104787
  have htrace : WordTrace (prefixWord ++ tailWord_1104787) baseStart_1104787 baseEnd_1104787 := by
    simpa [prefixWord, tailWord_1104787, baseEnd_1104787] using wordTrace_append hprefix tailTrace_1104787
  have hstable : (prefixWord ++ tailWord_1104787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104787).length < 2 ^ (prefixWord ++ tailWord_1104787).sum := by decide
  have hdescent : baseEnd_1104787 < baseStart_1104787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104804 : List Nat := [2, 3, 1, 2, 1, 2, 2, 3, 2, 3, 2]
def baseStart_1104804 : Nat := 118140960795 + 1104804 * 2 ^ 59
def prefixEnd_1104804 : Nat := 4983230072969 + 3 ^ 40 * 1104804 * 2
def baseEnd_1104804 : Nat := 567295481010000682969105

theorem tailTrace_1104804 : CollatzResearch.WordTrace tailWord_1104804 prefixEnd_1104804 567295481010000682969105 := by
  unfold tailWord_1104804
  simp only [CollatzResearch.WordTrace]
  refine ⟨20147756144745634173144733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26863674859660845564192977 20147756144745634173144733)
  ·
    refine ⟨7555408554279612814929275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20147756144745634173144733 7555408554279612814929275)
    ·
      refine ⟨11333112831419419222393913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7555408554279612814929275 11333112831419419222393913)
      ·
        refine ⟨8499834623564564416795435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11333112831419419222393913 8499834623564564416795435)
        ·
          refine ⟨12749751935346846625193153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8499834623564564416795435 12749751935346846625193153)
          ·
            refine ⟨9562313951510134968894865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12749751935346846625193153 9562313951510134968894865)
            ·
              refine ⟨7171735463632601226671149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9562313951510134968894865 7171735463632601226671149)
              ·
                refine ⟨2689400798862225460001681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7171735463632601226671149 2689400798862225460001681)
                ·
                  refine ⟨2017050599146669095001261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2689400798862225460001681 2017050599146669095001261)
                  ·
                    refine ⟨756393974680000910625473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017050599146669095001261 756393974680000910625473)
                    ·
                      refine ⟨567295481010000682969105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756393974680000910625473 567295481010000682969105)
                      ·
                        rfl

theorem cell23_1104804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_1104804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104804 prefixEnd_1104804 := by exact prefixLift 1104804
  have htrace : WordTrace (prefixWord ++ tailWord_1104804) baseStart_1104804 baseEnd_1104804 := by
    simpa [prefixWord, tailWord_1104804, baseEnd_1104804] using wordTrace_append hprefix tailTrace_1104804
  have hstable : (prefixWord ++ tailWord_1104804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104804).length < 2 ^ (prefixWord ++ tailWord_1104804).sum := by decide
  have hdescent : baseEnd_1104804 < baseStart_1104804 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104822 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 3, 4]
def baseStart_1104822 : Nat := 118140960795 + 1104822 * 2 ^ 59
def prefixEnd_1104822 : Nat := 4983230072969 + 3 ^ 40 * 1104822 * 2
def baseEnd_1104822 : Nat := 189101574553927204181341

theorem tailTrace_1104822 : CollatzResearch.WordTrace tailWord_1104822 prefixEnd_1104822 189101574553927204181341 := by
  unfold tailWord_1104822
  simp only [CollatzResearch.WordTrace]
  refine ⟨2518510550214128588777795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26864112535617371613629813 2518510550214128588777795)
  ·
    refine ⟨3777765825321192883166693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2518510550214128588777795 3777765825321192883166693)
    ·
      refine ⟨708331092247723665593755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3777765825321192883166693 708331092247723665593755)
      ·
        refine ⟨1062496638371585498390633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708331092247723665593755 1062496638371585498390633)
        ·
          refine ⟨796872478778689123792975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1062496638371585498390633 796872478778689123792975)
          ·
            refine ⟨1195308718168033685689463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 796872478778689123792975 1195308718168033685689463)
            ·
              refine ⟨1792963077252050528534195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195308718168033685689463 1792963077252050528534195)
              ·
                refine ⟨2689444615878075792801293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1792963077252050528534195 2689444615878075792801293)
                ·
                  refine ⟨1008541730954278422300485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2689444615878075792801293 1008541730954278422300485)
                  ·
                    refine ⟨189101574553927204181341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008541730954278422300485 189101574553927204181341)
                    ·
                      rfl

theorem cell23_1104822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_1104822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104822 prefixEnd_1104822 := by exact prefixLift 1104822
  have htrace : WordTrace (prefixWord ++ tailWord_1104822) baseStart_1104822 baseEnd_1104822 := by
    simpa [prefixWord, tailWord_1104822, baseEnd_1104822] using wordTrace_append hprefix tailTrace_1104822
  have hstable : (prefixWord ++ tailWord_1104822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104822).length < 2 ^ (prefixWord ++ tailWord_1104822).sum := by decide
  have hdescent : baseEnd_1104822 < baseStart_1104822 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104844 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 2, 4]
def baseStart_1104844 : Nat := 118140960795 + 1104844 * 2 ^ 59
def prefixEnd_1104844 : Nat := 4983230072969 + 3 ^ 40 * 1104844 * 2
def baseEnd_1104844 : Nat := 189105340078726842156307

theorem tailTrace_1104844 : CollatzResearch.WordTrace tailWord_1104844 prefixEnd_1104844 189105340078726842156307 := by
  unfold tailWord_1104844
  simp only [CollatzResearch.WordTrace]
  refine ⟨20148485604673177588872793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26864647472897570118497057 20148485604673177588872793)
  ·
    refine ⟨15111364203504883191654595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20148485604673177588872793 15111364203504883191654595)
    ·
      refine ⟨22667046305257324787481893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15111364203504883191654595 22667046305257324787481893)
      ·
        refine ⟨4250071182235748397652855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22667046305257324787481893 4250071182235748397652855)
        ·
          refine ⟨6375106773353622596479283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4250071182235748397652855 6375106773353622596479283)
          ·
            refine ⟨9562660160030433894718925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6375106773353622596479283 9562660160030433894718925)
            ·
              refine ⟨3585997560011412710519597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9562660160030433894718925 3585997560011412710519597)
              ·
                refine ⟨1344749085004279766444849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3585997560011412710519597 1344749085004279766444849)
                ·
                  refine ⟨1008561813753209824833637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344749085004279766444849 1008561813753209824833637)
                  ·
                    refine ⟨189105340078726842156307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008561813753209824833637 189105340078726842156307)
                    ·
                      rfl

theorem cell23_1104844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 2, 4].length) (baseStart_1104844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104844 prefixEnd_1104844 := by exact prefixLift 1104844
  have htrace : WordTrace (prefixWord ++ tailWord_1104844) baseStart_1104844 baseEnd_1104844 := by
    simpa [prefixWord, tailWord_1104844, baseEnd_1104844] using wordTrace_append hprefix tailTrace_1104844
  have hstable : (prefixWord ++ tailWord_1104844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104844).length < 2 ^ (prefixWord ++ tailWord_1104844).sum := by decide
  have hdescent : baseEnd_1104844 < baseStart_1104844 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104898 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 1, 2, 4]
def baseStart_1104898 : Nat := 118140960795 + 1104898 * 2 ^ 59
def prefixEnd_1104898 : Nat := 4983230072969 + 3 ^ 40 * 1104898 * 2
def baseEnd_1104898 : Nat := 567343748191523315193673

theorem tailTrace_1104898 : CollatzResearch.WordTrace tailWord_1104898 prefixEnd_1104898 567343748191523315193673 := by
  unfold tailWord_1104898
  simp only [CollatzResearch.WordTrace]
  refine ⟨10074735187787680600052837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26865960500767148266807565 10074735187787680600052837)
  ·
    refine ⟨1889012847710190112509907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10074735187787680600052837 1889012847710190112509907)
    ·
      refine ⟨2833519271565285168764861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1889012847710190112509907 2833519271565285168764861)
      ·
        refine ⟨1062569726836981938286823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2833519271565285168764861 1062569726836981938286823)
        ·
          refine ⟨1593854590255472907430235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1062569726836981938286823 1593854590255472907430235)
          ·
            refine ⟨2390781885383209361145353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1593854590255472907430235 2390781885383209361145353)
            ·
              refine ⟨1793086414037407020859015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2390781885383209361145353 1793086414037407020859015)
              ·
                refine ⟨2689629621056110531288523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793086414037407020859015 2689629621056110531288523)
                ·
                  refine ⟨4034444431584165796932785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689629621056110531288523 4034444431584165796932785)
                  ·
                    refine ⟨3025833323688124347699589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4034444431584165796932785 3025833323688124347699589)
                    ·
                      refine ⟨567343748191523315193673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3025833323688124347699589 567343748191523315193673)
                      ·
                        rfl

theorem cell23_1104898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_1104898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104898 prefixEnd_1104898 := by exact prefixLift 1104898
  have htrace : WordTrace (prefixWord ++ tailWord_1104898) baseStart_1104898 baseEnd_1104898 := by
    simpa [prefixWord, tailWord_1104898, baseEnd_1104898] using wordTrace_append hprefix tailTrace_1104898
  have hstable : (prefixWord ++ tailWord_1104898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104898).length < 2 ^ (prefixWord ++ tailWord_1104898).sum := by decide
  have hdescent : baseEnd_1104898 < baseStart_1104898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104935 : List Nat := [1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1104935 : Nat := 118140960795 + 1104935 * 2 ^ 59
def prefixEnd_1104935 : Nat := 4983230072969 + 3 ^ 40 * 1104935 * 2
def baseEnd_1104935 : Nat := 567362746975739670431003

theorem tailTrace_1104935 : CollatzResearch.WordTrace tailWord_1104935 prefixEnd_1104935 567362746975739670431003 := by
  unfold tailWord_1104935
  simp only [CollatzResearch.WordTrace]
  refine ⟨40300290252016677719308259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26866860168011118479538839 40300290252016677719308259)
  ·
    refine ⟨60450435378025016578962389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40300290252016677719308259 60450435378025016578962389)
    ·
      refine ⟨1416807079172461326069431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 60450435378025016578962389 1416807079172461326069431)
      ·
        refine ⟨2125210618758691989104147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1416807079172461326069431 2125210618758691989104147)
        ·
          refine ⟨3187815928138037983656221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125210618758691989104147 3187815928138037983656221)
          ·
            refine ⟨1195430973051764243871083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3187815928138037983656221 1195430973051764243871083)
            ·
              refine ⟨1793146459577646365806625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195430973051764243871083 1793146459577646365806625)
              ·
                refine ⟨1344859844683234774354969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1793146459577646365806625 1344859844683234774354969)
                ·
                  refine ⟨1008644883512426080766227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1344859844683234774354969 1008644883512426080766227)
                  ·
                    refine ⟨1512967325268639121149341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1008644883512426080766227 1512967325268639121149341)
                    ·
                      refine ⟨567362746975739670431003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1512967325268639121149341 567362746975739670431003)
                      ·
                        rfl

theorem cell23_1104935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1104935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104935 prefixEnd_1104935 := by exact prefixLift 1104935
  have htrace : WordTrace (prefixWord ++ tailWord_1104935) baseStart_1104935 baseEnd_1104935 := by
    simpa [prefixWord, tailWord_1104935, baseEnd_1104935] using wordTrace_append hprefix tailTrace_1104935
  have hstable : (prefixWord ++ tailWord_1104935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104935).length < 2 ^ (prefixWord ++ tailWord_1104935).sum := by decide
  have hdescent : baseEnd_1104935 < baseStart_1104935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104958 : List Nat := [4, 2, 1, 3, 1, 1, 3, 1, 1, 4, 2]
def baseStart_1104958 : Nat := 118140960795 + 1104958 * 2 ^ 59
def prefixEnd_1104958 : Nat := 4983230072969 + 3 ^ 40 * 1104958 * 2
def baseEnd_1104958 : Nat := 567374557030793080443397

theorem tailTrace_1104958 : CollatzResearch.WordTrace tailWord_1104958 prefixEnd_1104958 567374557030793080443397 := by
  unfold tailWord_1104958
  simp only [CollatzResearch.WordTrace]
  refine ⟨5037641141366669080924441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26867419420622235098263685 5037641141366669080924441)
  ·
    refine ⟨3778230856025001810693331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5037641141366669080924441 3778230856025001810693331)
    ·
      refine ⟨5667346284037502716039997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3778230856025001810693331 5667346284037502716039997)
      ·
        refine ⟨2125254856514063518514999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5667346284037502716039997 2125254856514063518514999)
        ·
          refine ⟨3187882284771095277772499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2125254856514063518514999 3187882284771095277772499)
          ·
            refine ⟨4781823427156642916658749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3187882284771095277772499 4781823427156642916658749)
            ·
              refine ⟨1793183785183741093747031, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4781823427156642916658749 1793183785183741093747031)
              ·
                refine ⟨2689775677775611640620547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793183785183741093747031 2689775677775611640620547)
                ·
                  refine ⟨4034663516663417460930821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2689775677775611640620547 4034663516663417460930821)
                  ·
                    refine ⟨756499409374390773924529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4034663516663417460930821 756499409374390773924529)
                    ·
                      refine ⟨567374557030793080443397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756499409374390773924529 567374557030793080443397)
                      ·
                        rfl

theorem cell23_1104958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_1104958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104958 prefixEnd_1104958 := by exact prefixLift 1104958
  have htrace : WordTrace (prefixWord ++ tailWord_1104958) baseStart_1104958 baseEnd_1104958 := by
    simpa [prefixWord, tailWord_1104958, baseEnd_1104958] using wordTrace_append hprefix tailTrace_1104958
  have hstable : (prefixWord ++ tailWord_1104958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104958).length < 2 ^ (prefixWord ++ tailWord_1104958).sum := by decide
  have hdescent : baseEnd_1104958 < baseStart_1104958 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1104977 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 1, 7]
def baseStart_1104977 : Nat := 118140960795 + 1104977 * 2 ^ 59
def prefixEnd_1104977 : Nat := 4983230072969 + 3 ^ 40 * 1104977 * 2
def baseEnd_1104977 : Nat := 189128104387742835368603

theorem tailTrace_1104977 : CollatzResearch.WordTrace tailWord_1104977 prefixEnd_1104977 189128104387742835368603 := by
  unfold tailWord_1104977
  simp only [CollatzResearch.WordTrace]
  refine ⟨40301822117864518892337185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26867881411909679261558123 40301822117864518892337185)
  ·
    refine ⟨30226366588398389169252889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40301822117864518892337185 30226366588398389169252889)
    ·
      refine ⟨22669774941298791876939667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30226366588398389169252889 22669774941298791876939667)
      ·
        refine ⟨34004662411948187815409501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22669774941298791876939667 34004662411948187815409501)
        ·
          refine ⟨12751748404480570430778563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34004662411948187815409501 12751748404480570430778563)
          ·
            refine ⟨19127622606720855646167845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12751748404480570430778563 19127622606720855646167845)
            ·
              refine ⟨3586429238760160433656471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19127622606720855646167845 3586429238760160433656471)
              ·
                refine ⟨5379643858140240650484707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3586429238760160433656471 5379643858140240650484707)
                ·
                  refine ⟨8069465787210360975727061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5379643858140240650484707 8069465787210360975727061)
                  ·
                    refine ⟨189128104387742835368603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8069465787210360975727061 189128104387742835368603)
                    ·
                      rfl

theorem cell23_1104977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 1, 7].length) (baseStart_1104977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1104977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1104977 prefixEnd_1104977 := by exact prefixLift 1104977
  have htrace : WordTrace (prefixWord ++ tailWord_1104977) baseStart_1104977 baseEnd_1104977 := by
    simpa [prefixWord, tailWord_1104977, baseEnd_1104977] using wordTrace_append hprefix tailTrace_1104977
  have hstable : (prefixWord ++ tailWord_1104977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1104977).length < 2 ^ (prefixWord ++ tailWord_1104977).sum := by decide
  have hdescent : baseEnd_1104977 < baseStart_1104977 := by decide
  rcases family_descends (prefixWord ++ tailWord_1104977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105024 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 3, 4]
def baseStart_1105024 : Nat := 118140960795 + 1105024 * 2 ^ 59
def prefixEnd_1105024 : Nat := 4983230072969 + 3 ^ 40 * 1105024 * 2
def baseEnd_1105024 : Nat := 189136148917996607406031

theorem tailTrace_1105024 : CollatzResearch.WordTrace tailWord_1105024 prefixEnd_1105024 189136148917996607406031 := by
  unfold tailWord_1105024
  simp only [CollatzResearch.WordTrace]
  refine ⟨20151768174347122959649063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26869024232462830612865417 20151768174347122959649063)
  ·
    refine ⟨30227652261520684439473595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20151768174347122959649063 30227652261520684439473595)
    ·
      refine ⟨45341478392281026659210393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30227652261520684439473595 45341478392281026659210393)
      ·
        refine ⟨34006108794210769994407795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45341478392281026659210393 34006108794210769994407795)
        ·
          refine ⟨51009163191316154991611693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34006108794210769994407795 51009163191316154991611693)
          ·
            refine ⟨19128436196743558121854385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 51009163191316154991611693 19128436196743558121854385)
            ·
              refine ⟨14346327147557668591390789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19128436196743558121854385 14346327147557668591390789)
              ·
                refine ⟨2689936340167062860885773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14346327147557668591390789 2689936340167062860885773)
                ·
                  refine ⟨1008726127562648572832165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2689936340167062860885773 1008726127562648572832165)
                  ·
                    refine ⟨189136148917996607406031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008726127562648572832165 189136148917996607406031)
                    ·
                      rfl

theorem cell23_1105024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 3, 4].length) (baseStart_1105024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105024 prefixEnd_1105024 := by exact prefixLift 1105024
  have htrace : WordTrace (prefixWord ++ tailWord_1105024) baseStart_1105024 baseEnd_1105024 := by
    simpa [prefixWord, tailWord_1105024, baseEnd_1105024] using wordTrace_append hprefix tailTrace_1105024
  have hstable : (prefixWord ++ tailWord_1105024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105024).length < 2 ^ (prefixWord ++ tailWord_1105024).sum := by decide
  have hdescent : baseEnd_1105024 < baseStart_1105024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105081 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 3]
def baseStart_1105081 : Nat := 118140960795 + 1105081 * 2 ^ 59
def prefixEnd_1105081 : Nat := 4983230072969 + 3 ^ 40 * 1105081 * 2
def baseEnd_1105081 : Nat := 567437715151296099205331

theorem tailTrace_1105081 : CollatzResearch.WordTrace tailWord_1105081 prefixEnd_1105081 567437715151296099205331 := by
  unfold tailWord_1105081
  simp only [CollatzResearch.WordTrace]
  refine ⟨40305615309487744654123097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26870410206325163102748731 40305615309487744654123097)
  ·
    refine ⟨30229211482115808490592323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40305615309487744654123097 30229211482115808490592323)
    ·
      refine ⟨45343817223173712735888485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30229211482115808490592323 45343817223173712735888485)
      ·
        refine ⟨8501965729345071137979091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45343817223173712735888485 8501965729345071137979091)
        ·
          refine ⟨12752948594017606706968637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8501965729345071137979091 12752948594017606706968637)
          ·
            refine ⟨4782355722756602515113239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12752948594017606706968637 4782355722756602515113239)
            ·
              refine ⟨7173533584134903772669859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4782355722756602515113239 7173533584134903772669859)
              ·
                refine ⟨10760300376202355659004789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7173533584134903772669859 10760300376202355659004789)
                ·
                  refine ⟨1008778160268970843031699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10760300376202355659004789 1008778160268970843031699)
                  ·
                    refine ⟨1513167240403456264547549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1008778160268970843031699 1513167240403456264547549)
                    ·
                      refine ⟨567437715151296099205331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1513167240403456264547549 567437715151296099205331)
                      ·
                        rfl

theorem cell23_1105081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 5, 1, 3].length) (baseStart_1105081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105081 prefixEnd_1105081 := by exact prefixLift 1105081
  have htrace : WordTrace (prefixWord ++ tailWord_1105081) baseStart_1105081 baseEnd_1105081 := by
    simpa [prefixWord, tailWord_1105081, baseEnd_1105081] using wordTrace_append hprefix tailTrace_1105081
  have hstable : (prefixWord ++ tailWord_1105081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105081).length < 2 ^ (prefixWord ++ tailWord_1105081).sum := by decide
  have hdescent : baseEnd_1105081 < baseStart_1105081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105091 : List Nat := [1, 1, 1, 3, 1, 1, 1, 7, 2, 3, 2]
def baseStart_1105091 : Nat := 118140960795 + 1105091 * 2 ^ 59
def prefixEnd_1105091 : Nat := 4983230072969 + 3 ^ 40 * 1105091 * 2
def baseEnd_1105091 : Nat := 567442849957841060080285

theorem tailTrace_1105091 : CollatzResearch.WordTrace tailWord_1105091 prefixEnd_1105091 567442849957841060080285 := by
  unfold tailWord_1105091
  simp only [CollatzResearch.WordTrace]
  refine ⟨40305980039451516361987127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26870653359634344241324751 40305980039451516361987127)
  ·
    refine ⟨60458970059177274542980691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40305980039451516361987127 60458970059177274542980691)
    ·
      refine ⟨90688455088765911814471037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60458970059177274542980691 90688455088765911814471037)
      ·
        refine ⟨34008170658287216930426639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90688455088765911814471037 34008170658287216930426639)
        ·
          refine ⟨51012255987430825395639959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34008170658287216930426639 51012255987430825395639959)
          ·
            refine ⟨76518383981146238093459939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51012255987430825395639959 76518383981146238093459939)
            ·
              refine ⟨114777575971719357140189909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76518383981146238093459939 114777575971719357140189909)
              ·
                refine ⟨2690099436837172432973201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 114777575971719357140189909 2690099436837172432973201)
                ·
                  refine ⟨2017574577627879324729901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2690099436837172432973201 2017574577627879324729901)
                  ·
                    refine ⟨756590466610454746773713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2017574577627879324729901 756590466610454746773713)
                    ·
                      refine ⟨567442849957841060080285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756590466610454746773713 567442849957841060080285)
                      ·
                        rfl

theorem cell23_1105091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 7, 2, 3, 2].length) (baseStart_1105091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105091 prefixEnd_1105091 := by exact prefixLift 1105091
  have htrace : WordTrace (prefixWord ++ tailWord_1105091) baseStart_1105091 baseEnd_1105091 := by
    simpa [prefixWord, tailWord_1105091, baseEnd_1105091] using wordTrace_append hprefix tailTrace_1105091
  have hstable : (prefixWord ++ tailWord_1105091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105091).length < 2 ^ (prefixWord ++ tailWord_1105091).sum := by decide
  have hdescent : baseEnd_1105091 < baseStart_1105091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105097 : List Nat := [1, 2, 1, 1, 2, 1, 1, 2, 2, 10]
def baseStart_1105097 : Nat := 118140960795 + 1105097 * 2 ^ 59
def prefixEnd_1105097 : Nat := 4983230072969 + 3 ^ 40 * 1105097 * 2
def baseEnd_1105097 : Nat := 189148643613922678868419

theorem tailTrace_1105097 : CollatzResearch.WordTrace tailWord_1105097 prefixEnd_1105097 189148643613922678868419 := by
  unfold tailWord_1105097
  simp only [CollatzResearch.WordTrace]
  refine ⟨40306198877429779386705545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26870799251619852924470363 40306198877429779386705545)
  ·
    refine ⟨30229649158072334540029159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40306198877429779386705545 30229649158072334540029159)
    ·
      refine ⟨45344473737108501810043739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30229649158072334540029159 45344473737108501810043739)
      ·
        refine ⟨68016710605662752715065609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45344473737108501810043739 68016710605662752715065609)
        ·
          refine ⟨51012532954247064536299207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 68016710605662752715065609 51012532954247064536299207)
          ·
            refine ⟨76518799431370596804448811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51012532954247064536299207 76518799431370596804448811)
            ·
              refine ⟨114778199147055895206673217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76518799431370596804448811 114778199147055895206673217)
              ·
                refine ⟨86083649360291921405004913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114778199147055895206673217 86083649360291921405004913)
                ·
                  refine ⟨64562737020218941053753685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86083649360291921405004913 64562737020218941053753685)
                  ·
                    refine ⟨189148643613922678868419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 64562737020218941053753685 189148643613922678868419)
                    ·
                      rfl

theorem cell23_1105097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 2, 2, 10].length) (baseStart_1105097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105097 prefixEnd_1105097 := by exact prefixLift 1105097
  have htrace : WordTrace (prefixWord ++ tailWord_1105097) baseStart_1105097 baseEnd_1105097 := by
    simpa [prefixWord, tailWord_1105097, baseEnd_1105097] using wordTrace_append hprefix tailTrace_1105097
  have hstable : (prefixWord ++ tailWord_1105097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105097).length < 2 ^ (prefixWord ++ tailWord_1105097).sum := by decide
  have hdescent : baseEnd_1105097 < baseStart_1105097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105124 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 3, 1, 5]
def baseStart_1105124 : Nat := 118140960795 + 1105124 * 2 ^ 59
def prefixEnd_1105124 : Nat := 4983230072969 + 3 ^ 40 * 1105124 * 2
def baseEnd_1105124 : Nat := 567459794819439430967633

theorem tailTrace_1105124 : CollatzResearch.WordTrace tailWord_1105124 prefixEnd_1105124 567459794819439430967633 := by
  unfold tailWord_1105124
  simp only [CollatzResearch.WordTrace]
  refine ⟨20153591824165981498969213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26871455765554641998625617 20153591824165981498969213)
  ·
    refine ⟨7557596934062243062113455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20153591824165981498969213 7557596934062243062113455)
    ·
      refine ⟨11336395401093364593170183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7557596934062243062113455 11336395401093364593170183)
      ·
        refine ⟨17004593101640046889755275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11336395401093364593170183 17004593101640046889755275)
        ·
          refine ⟨25506889652460070334632913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17004593101640046889755275 25506889652460070334632913)
          ·
            refine ⟨19130167239345052750974685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25506889652460070334632913 19130167239345052750974685)
            ·
              refine ⟨7173812714754394781615507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19130167239345052750974685 7173812714754394781615507)
              ·
                refine ⟨10760719072131592172423261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7173812714754394781615507 10760719072131592172423261)
                ·
                  refine ⟨4035269652049347064658723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10760719072131592172423261 4035269652049347064658723)
                  ·
                    refine ⟨6052904478074020596988085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4035269652049347064658723 6052904478074020596988085)
                    ·
                      refine ⟨567459794819439430967633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6052904478074020596988085 567459794819439430967633)
                      ·
                        rfl

theorem cell23_1105124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 3, 1, 5].length) (baseStart_1105124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105124 prefixEnd_1105124 := by exact prefixLift 1105124
  have htrace : WordTrace (prefixWord ++ tailWord_1105124) baseStart_1105124 baseEnd_1105124 := by
    simpa [prefixWord, tailWord_1105124, baseEnd_1105124] using wordTrace_append hprefix tailTrace_1105124
  have hstable : (prefixWord ++ tailWord_1105124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105124).length < 2 ^ (prefixWord ++ tailWord_1105124).sum := by decide
  have hdescent : baseEnd_1105124 < baseStart_1105124 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105131 : List Nat := [1, 1, 1, 1, 2, 8, 1, 1, 1, 6]
def baseStart_1105131 : Nat := 118140960795 + 1105131 * 2 ^ 59
def prefixEnd_1105131 : Nat := 4983230072969 + 3 ^ 40 * 1105131 * 2
def baseEnd_1105131 : Nat := 189154463061340301193367

theorem tailTrace_1105131 : CollatzResearch.WordTrace tailWord_1105131 prefixEnd_1105131 189154463061340301193367 := by
  unfold tailWord_1105131
  simp only [CollatzResearch.WordTrace]
  refine ⟨40307438959306603193443247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26871625972871068795628831 40307438959306603193443247)
  ·
    refine ⟨60461158438959904790164871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40307438959306603193443247 60461158438959904790164871)
    ·
      refine ⟨90691737658439857185247307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60461158438959904790164871 90691737658439857185247307)
      ·
        refine ⟨136037606487659785777870961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90691737658439857185247307 136037606487659785777870961)
        ·
          refine ⟨102028204865744839333403221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136037606487659785777870961 102028204865744839333403221)
          ·
            refine ⟨1195643025770447335938319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 102028204865744839333403221 1195643025770447335938319)
            ·
              refine ⟨1793464538655671003907479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1195643025770447335938319 1793464538655671003907479)
              ·
                refine ⟨2690196807983506505861219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1793464538655671003907479 2690196807983506505861219)
                ·
                  refine ⟨4035295211975259758791829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690196807983506505861219 4035295211975259758791829)
                  ·
                    refine ⟨189154463061340301193367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4035295211975259758791829 189154463061340301193367)
                    ·
                      rfl

theorem cell23_1105131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 1, 1, 1, 6].length) (baseStart_1105131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105131 prefixEnd_1105131 := by exact prefixLift 1105131
  have htrace : WordTrace (prefixWord ++ tailWord_1105131) baseStart_1105131 baseEnd_1105131 := by
    simpa [prefixWord, tailWord_1105131, baseEnd_1105131] using wordTrace_append hprefix tailTrace_1105131
  have hstable : (prefixWord ++ tailWord_1105131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105131).length < 2 ^ (prefixWord ++ tailWord_1105131).sum := by decide
  have hdescent : baseEnd_1105131 < baseStart_1105131 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105182 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_1105182 : Nat := 118140960795 + 1105182 * 2 ^ 59
def prefixEnd_1105182 : Nat := 4983230072969 + 3 ^ 40 * 1105182 * 2
def baseEnd_1105182 : Nat := 189163192232466734680789

theorem tailTrace_1105182 : CollatzResearch.WordTrace tailWord_1105182 prefixEnd_1105182 189163192232466734680789 := by
  unfold tailWord_1105182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5038662385265229862943725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26872866054747892602366533 5038662385265229862943725)
  ·
    refine ⟨1889498394474461198603897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5038662385265229862943725 1889498394474461198603897)
    ·
      refine ⟨1417123795855845898952923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1889498394474461198603897 1417123795855845898952923)
      ·
        refine ⟨2125685693783768848429385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417123795855845898952923 2125685693783768848429385)
        ·
          refine ⟨1594264270337826636322039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2125685693783768848429385 1594264270337826636322039)
          ·
            refine ⟨2391396405506739954483059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594264270337826636322039 2391396405506739954483059)
            ·
              refine ⟨3587094608260109931724589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391396405506739954483059 3587094608260109931724589)
              ·
                refine ⟨1345160478097541224396721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3587094608260109931724589 1345160478097541224396721)
                ·
                  refine ⟨1008870358573155918297541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1345160478097541224396721 1008870358573155918297541)
                  ·
                    refine ⟨189163192232466734680789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1008870358573155918297541 189163192232466734680789)
                    ·
                      rfl

theorem cell23_1105182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_1105182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105182 prefixEnd_1105182 := by exact prefixLift 1105182
  have htrace : WordTrace (prefixWord ++ tailWord_1105182) baseStart_1105182 baseEnd_1105182 := by
    simpa [prefixWord, tailWord_1105182, baseEnd_1105182] using wordTrace_append hprefix tailTrace_1105182
  have hstable : (prefixWord ++ tailWord_1105182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105182).length < 2 ^ (prefixWord ++ tailWord_1105182).sum := by decide
  have hdescent : baseEnd_1105182 < baseStart_1105182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105224 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 3, 6]
def baseStart_1105224 : Nat := 118140960795 + 1105224 * 2 ^ 59
def prefixEnd_1105224 : Nat := 4983230072969 + 3 ^ 40 * 1105224 * 2
def baseEnd_1105224 : Nat := 567511142884889039717173

theorem tailTrace_1105224 : CollatzResearch.WordTrace tailWord_1105224 prefixEnd_1105224 567511142884889039717173 := by
  unfold tailWord_1105224
  simp only [CollatzResearch.WordTrace]
  refine ⟨20155415473984840038289363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26873887298646453384385817 20155415473984840038289363)
  ·
    refine ⟨30233123210977260057434045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20155415473984840038289363 30233123210977260057434045)
    ·
      refine ⟨11337421204116472521537767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30233123210977260057434045 11337421204116472521537767)
      ·
        refine ⟨17006131806174708782306651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11337421204116472521537767 17006131806174708782306651)
        ·
          refine ⟨25509197709262063173459977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17006131806174708782306651 25509197709262063173459977)
          ·
            refine ⟨19131898281946547380094983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25509197709262063173459977 19131898281946547380094983)
            ·
              refine ⟨28697847422919821070142475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19131898281946547380094983 28697847422919821070142475)
              ·
                refine ⟨43046771134379731605213713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28697847422919821070142475 43046771134379731605213713)
                ·
                  refine ⟨32285078350784798703910285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43046771134379731605213713 32285078350784798703910285)
                  ·
                    refine ⟨12106904381544299513966357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32285078350784798703910285 12106904381544299513966357)
                    ·
                      refine ⟨567511142884889039717173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12106904381544299513966357 567511142884889039717173)
                      ·
                        rfl

theorem cell23_1105224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_1105224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105224 prefixEnd_1105224 := by exact prefixLift 1105224
  have htrace : WordTrace (prefixWord ++ tailWord_1105224) baseStart_1105224 baseEnd_1105224 := by
    simpa [prefixWord, tailWord_1105224, baseEnd_1105224] using wordTrace_append hprefix tailTrace_1105224
  have hstable : (prefixWord ++ tailWord_1105224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105224).length < 2 ^ (prefixWord ++ tailWord_1105224).sum := by decide
  have hdescent : baseEnd_1105224 < baseStart_1105224 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105251 : List Nat := [1, 1, 1, 5, 2, 3, 1, 2, 7]
def baseStart_1105251 : Nat := 118140960795 + 1105251 * 2 ^ 59
def prefixEnd_1105251 : Nat := 4983230072969 + 3 ^ 40 * 1105251 * 2
def baseEnd_1105251 : Nat := 63058334095840048231061

theorem tailTrace_1105251 : CollatzResearch.WordTrace tailWord_1105251 prefixEnd_1105251 63058334095840048231061 := by
  unfold tailWord_1105251
  simp only [CollatzResearch.WordTrace]
  refine ⟨40311815718871863687811607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26874543812581242458541071 40311815718871863687811607)
  ·
    refine ⟨60467723578307795531717411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40311815718871863687811607 60467723578307795531717411)
    ·
      refine ⟨90701585367461693297576117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60467723578307795531717411 90701585367461693297576117)
      ·
        refine ⟨8503273628199533746647761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90701585367461693297576117 8503273628199533746647761)
        ·
          refine ⟨6377455221149650309985821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8503273628199533746647761 6377455221149650309985821)
          ·
            refine ⟨2391545707931118866244683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6377455221149650309985821 2391545707931118866244683)
            ·
              refine ⟨3587318561896678299367025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2391545707931118866244683 3587318561896678299367025)
              ·
                refine ⟨2690488921422508724525269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3587318561896678299367025 2690488921422508724525269)
                ·
                  refine ⟨63058334095840048231061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2690488921422508724525269 63058334095840048231061)
                  ·
                    rfl

theorem cell23_1105251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 2, 7].length) (baseStart_1105251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105251 prefixEnd_1105251 := by exact prefixLift 1105251
  have htrace : WordTrace (prefixWord ++ tailWord_1105251) baseStart_1105251 baseEnd_1105251 := by
    simpa [prefixWord, tailWord_1105251, baseEnd_1105251] using wordTrace_append hprefix tailTrace_1105251
  have hstable : (prefixWord ++ tailWord_1105251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105251).length < 2 ^ (prefixWord ++ tailWord_1105251).sum := by decide
  have hdescent : baseEnd_1105251 < baseStart_1105251 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105301 : List Nat := [1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 4]
def baseStart_1105301 : Nat := 118140960795 + 1105301 * 2 ^ 59
def prefixEnd_1105301 : Nat := 4983230072969 + 3 ^ 40 * 1105301 * 2
def baseEnd_1105301 : Nat := 567550680895285238454319

theorem tailTrace_1105301 : CollatzResearch.WordTrace tailWord_1105301 prefixEnd_1105301 567550680895285238454319 := by
  unfold tailWord_1105301
  simp only [CollatzResearch.WordTrace]
  refine ⟨40313639368690722227131757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26875759579127148151421171 40313639368690722227131757)
  ·
    refine ⟨15117614763259020835174409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40313639368690722227131757 15117614763259020835174409)
    ·
      refine ⟨11338211072444265626380807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15117614763259020835174409 11338211072444265626380807)
      ·
        refine ⟨17007316608666398439571211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11338211072444265626380807 17007316608666398439571211)
        ·
          refine ⟨25510974912999597659356817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17007316608666398439571211 25510974912999597659356817)
          ·
            refine ⟨19133231184749698244517613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25510974912999597659356817 19133231184749698244517613)
            ·
              refine ⟨7174961694281136841694105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19133231184749698244517613 7174961694281136841694105)
              ·
                refine ⟨5381221270710852631270579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7174961694281136841694105 5381221270710852631270579)
                ·
                  refine ⟨8071831906066278946905869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5381221270710852631270579 8071831906066278946905869)
                  ·
                    refine ⟨3026936964774854605089701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8071831906066278946905869 3026936964774854605089701)
                    ·
                      refine ⟨567550680895285238454319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3026936964774854605089701 567550680895285238454319)
                      ·
                        rfl

theorem cell23_1105301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_1105301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105301 prefixEnd_1105301 := by exact prefixLift 1105301
  have htrace : WordTrace (prefixWord ++ tailWord_1105301) baseStart_1105301 baseEnd_1105301 := by
    simpa [prefixWord, tailWord_1105301, baseEnd_1105301] using wordTrace_append hprefix tailTrace_1105301
  have hstable : (prefixWord ++ tailWord_1105301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105301).length < 2 ^ (prefixWord ++ tailWord_1105301).sum := by decide
  have hdescent : baseEnd_1105301 < baseStart_1105301 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105341 : List Nat := [1, 4, 1, 2, 2, 1, 1, 3, 8]
def baseStart_1105341 : Nat := 118140960795 + 1105341 * 2 ^ 59
def prefixEnd_1105341 : Nat := 4983230072969 + 3 ^ 40 * 1105341 * 2
def baseEnd_1105341 : Nat := 63063468902385009106015

theorem tailTrace_1105341 : CollatzResearch.WordTrace tailWord_1105341 prefixEnd_1105341 63063468902385009106015 := by
  unfold tailWord_1105341
  simp only [CollatzResearch.WordTrace]
  refine ⟨40315098288545809058587877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26876732192363872705725251 40315098288545809058587877)
  ·
    refine ⟨7559080929102339198485227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40315098288545809058587877 7559080929102339198485227)
    ·
      refine ⟨11338621393653508797727841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7559080929102339198485227 11338621393653508797727841)
      ·
        refine ⟨8503966045240131598295881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11338621393653508797727841 8503966045240131598295881)
        ·
          refine ⟨6377974533930098698721911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8503966045240131598295881 6377974533930098698721911)
          ·
            refine ⟨9566961800895148048082867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6377974533930098698721911 9566961800895148048082867)
            ·
              refine ⟨14350442701342722072124301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9566961800895148048082867 14350442701342722072124301)
              ·
                refine ⟨5381416013003520777046613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14350442701342722072124301 5381416013003520777046613)
                ·
                  refine ⟨63063468902385009106015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 5381416013003520777046613 63063468902385009106015)
                  ·
                    rfl

theorem cell23_1105341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 3, 8].length) (baseStart_1105341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105341 prefixEnd_1105341 := by exact prefixLift 1105341
  have htrace : WordTrace (prefixWord ++ tailWord_1105341) baseStart_1105341 baseEnd_1105341 := by
    simpa [prefixWord, tailWord_1105341, baseEnd_1105341] using wordTrace_append hprefix tailTrace_1105341
  have hstable : (prefixWord ++ tailWord_1105341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105341).length < 2 ^ (prefixWord ++ tailWord_1105341).sum := by decide
  have hdescent : baseEnd_1105341 < baseStart_1105341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105401 : List Nat := [1, 2, 1, 3, 1, 2, 1, 1, 5, 6]
def baseStart_1105401 : Nat := 118140960795 + 1105401 * 2 ^ 59
def prefixEnd_1105401 : Nat := 4983230072969 + 3 ^ 40 * 1105401 * 2
def baseEnd_1105401 : Nat := 189200676320244949067953

theorem tailTrace_1105401 : CollatzResearch.WordTrace tailWord_1105401 prefixEnd_1105401 189200676320244949067953 := by
  unfold tailWord_1105401
  simp only [CollatzResearch.WordTrace]
  refine ⟨40317286668328439305772057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26878191112218959537181371 40317286668328439305772057)
  ·
    refine ⟨30237965001246329479329043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40317286668328439305772057 30237965001246329479329043)
    ·
      refine ⟨45356947501869494218993565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30237965001246329479329043 45356947501869494218993565)
      ·
        refine ⟨17008855313201060332122587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45356947501869494218993565 17008855313201060332122587)
        ·
          refine ⟨25513282969801590498183881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17008855313201060332122587 25513282969801590498183881)
          ·
            refine ⟨19134962227351192873637911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25513282969801590498183881 19134962227351192873637911)
            ·
              refine ⟨28702443341026789310456867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19134962227351192873637911 28702443341026789310456867)
              ·
                refine ⟨43053665011540183965685301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28702443341026789310456867 43053665011540183965685301)
                ·
                  refine ⟨4036281094831892246782997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 43053665011540183965685301 4036281094831892246782997)
                  ·
                    refine ⟨189200676320244949067953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4036281094831892246782997 189200676320244949067953)
                    ·
                      rfl

theorem cell23_1105401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 1, 1, 5, 6].length) (baseStart_1105401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105401 prefixEnd_1105401 := by exact prefixLift 1105401
  have htrace : WordTrace (prefixWord ++ tailWord_1105401) baseStart_1105401 baseEnd_1105401 := by
    simpa [prefixWord, tailWord_1105401, baseEnd_1105401] using wordTrace_append hprefix tailTrace_1105401
  have hstable : (prefixWord ++ tailWord_1105401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105401).length < 2 ^ (prefixWord ++ tailWord_1105401).sum := by decide
  have hdescent : baseEnd_1105401 < baseStart_1105401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105402 : List Nat := [3, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3]
def baseStart_1105402 : Nat := 118140960795 + 1105402 * 2 ^ 59
def prefixEnd_1105402 : Nat := 4983230072969 + 3 ^ 40 * 1105402 * 2
def baseEnd_1105402 : Nat := 567602542441389343291355

theorem tailTrace_1105402 : CollatzResearch.WordTrace tailWord_1105402 prefixEnd_1105402 567602542441389343291355 := by
  unfold tailWord_1105402
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079330785331204119139615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26878215427549877651038973 10079330785331204119139615)
  ·
    refine ⟨15118996177996806178709423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10079330785331204119139615 15118996177996806178709423)
    ·
      refine ⟨22678494266995209268064135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15118996177996806178709423 22678494266995209268064135)
      ·
        refine ⟨34017741400492813902096203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22678494266995209268064135 34017741400492813902096203)
        ·
          refine ⟨51026612100739220853144305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34017741400492813902096203 51026612100739220853144305)
          ·
            refine ⟨38269959075554415639858229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51026612100739220853144305 38269959075554415639858229)
            ·
              refine ⟨3587808663333226466236709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38269959075554415639858229 3587808663333226466236709)
              ·
                refine ⟨672714124374979962419383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3587808663333226466236709 672714124374979962419383)
                ·
                  refine ⟨1009071186562469943629075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672714124374979962419383 1009071186562469943629075)
                  ·
                    refine ⟨1513606779843704915443613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009071186562469943629075 1513606779843704915443613)
                    ·
                      refine ⟨567602542441389343291355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1513606779843704915443613 567602542441389343291355)
                      ·
                        rfl

theorem cell23_1105402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 4, 1, 1, 3].length) (baseStart_1105402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105402 prefixEnd_1105402 := by exact prefixLift 1105402
  have htrace : WordTrace (prefixWord ++ tailWord_1105402) baseStart_1105402 baseEnd_1105402 := by
    simpa [prefixWord, tailWord_1105402, baseEnd_1105402] using wordTrace_append hprefix tailTrace_1105402
  have hstable : (prefixWord ++ tailWord_1105402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105402).length < 2 ^ (prefixWord ++ tailWord_1105402).sum := by decide
  have hdescent : baseEnd_1105402 < baseStart_1105402 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105418 : List Nat := [3, 1, 2, 2, 2, 2, 1, 3, 1, 6]
def baseStart_1105418 : Nat := 118140960795 + 1105418 * 2 ^ 59
def prefixEnd_1105418 : Nat := 4983230072969 + 3 ^ 40 * 1105418 * 2
def baseEnd_1105418 : Nat := 189203586043953760230427

theorem tailTrace_1105418 : CollatzResearch.WordTrace tailWord_1105418 prefixEnd_1105418 189203586043953760230427 := by
  unfold tailWord_1105418
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079476677316712802285227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26878604472844567472760605 10079476677316712802285227)
  ·
    refine ⟨15119215015975069203427841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10079476677316712802285227 15119215015975069203427841)
    ·
      refine ⟨11339411261981301902570881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15119215015975069203427841 11339411261981301902570881)
      ·
        refine ⟨8504558446485976426928161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11339411261981301902570881 8504558446485976426928161)
        ·
          refine ⟨6378418834864482320196121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8504558446485976426928161 6378418834864482320196121)
          ·
            refine ⟨4783814126148361740147091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6378418834864482320196121 4783814126148361740147091)
            ·
              refine ⟨7175721189222542610220637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4783814126148361740147091 7175721189222542610220637)
              ·
                refine ⟨2690895445958453478832739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7175721189222542610220637 2690895445958453478832739)
                ·
                  refine ⟨4036343168937680218249109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2690895445958453478832739 4036343168937680218249109)
                  ·
                    refine ⟨189203586043953760230427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4036343168937680218249109 189203586043953760230427)
                    ·
                      rfl

theorem cell23_1105418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 1, 3, 1, 6].length) (baseStart_1105418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105418 prefixEnd_1105418 := by exact prefixLift 1105418
  have htrace : WordTrace (prefixWord ++ tailWord_1105418) baseStart_1105418 baseEnd_1105418 := by
    simpa [prefixWord, tailWord_1105418, baseEnd_1105418] using wordTrace_append hprefix tailTrace_1105418
  have hstable : (prefixWord ++ tailWord_1105418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105418).length < 2 ^ (prefixWord ++ tailWord_1105418).sum := by decide
  have hdescent : baseEnd_1105418 < baseStart_1105418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105442 : List Nat := [3, 3, 1, 1, 1, 1, 6, 1, 1, 1, 4]
def baseStart_1105442 : Nat := 118140960795 + 1105442 * 2 ^ 59
def prefixEnd_1105442 : Nat := 4983230072969 + 3 ^ 40 * 1105442 * 2
def baseEnd_1105442 : Nat := 567623081667569186791171

theorem tailTrace_1105442 : CollatzResearch.WordTrace tailWord_1105442 prefixEnd_1105442 567623081667569186791171 := by
  unfold tailWord_1105442
  simp only [CollatzResearch.WordTrace]
  refine ⟨10079695515294975827003645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26879188040786602205343053 10079695515294975827003645)
  ·
    refine ⟨3779885818235615935126367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10079695515294975827003645 3779885818235615935126367)
    ·
      refine ⟨5669828727353423902689551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3779885818235615935126367 5669828727353423902689551)
      ·
        refine ⟨8504743091030135854034327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5669828727353423902689551 8504743091030135854034327)
        ·
          refine ⟨12757114636545203781051491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8504743091030135854034327 12757114636545203781051491)
          ·
            refine ⟨19135671954817805671577237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12757114636545203781051491 19135671954817805671577237)
            ·
              refine ⟨896984622882084640855183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 19135671954817805671577237 896984622882084640855183)
              ·
                refine ⟨1345476934323126961282775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 896984622882084640855183 1345476934323126961282775)
                ·
                  refine ⟨2018215401484690441924163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345476934323126961282775 2018215401484690441924163)
                  ·
                    refine ⟨3027323102227035662886245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2018215401484690441924163 3027323102227035662886245)
                    ·
                      refine ⟨567623081667569186791171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3027323102227035662886245 567623081667569186791171)
                      ·
                        rfl

theorem cell23_1105442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_1105442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105442 prefixEnd_1105442 := by exact prefixLift 1105442
  have htrace : WordTrace (prefixWord ++ tailWord_1105442) baseStart_1105442 baseEnd_1105442 := by
    simpa [prefixWord, tailWord_1105442, baseEnd_1105442] using wordTrace_append hprefix tailTrace_1105442
  have hstable : (prefixWord ++ tailWord_1105442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105442).length < 2 ^ (prefixWord ++ tailWord_1105442).sum := by decide
  have hdescent : baseEnd_1105442 < baseStart_1105442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105451 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6]
def baseStart_1105451 : Nat := 118140960795 + 1105451 * 2 ^ 59
def prefixEnd_1105451 : Nat := 4983230072969 + 3 ^ 40 * 1105451 * 2
def baseEnd_1105451 : Nat := 567627702993459651578629

theorem tailTrace_1105451 : CollatzResearch.WordTrace tailWord_1105451 prefixEnd_1105451 567627702993459651578629 := by
  unfold tailWord_1105451
  simp only [CollatzResearch.WordTrace]
  refine ⟨40319110318147297845092207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26879406878764865230061471 40319110318147297845092207)
  ·
    refine ⟨60478665477220946767638311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40319110318147297845092207 60478665477220946767638311)
    ·
      refine ⟨90717998215831420151457467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60478665477220946767638311 90717998215831420151457467)
      ·
        refine ⟨136076997323747130227186201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90717998215831420151457467 136076997323747130227186201)
        ·
          refine ⟨102057747992810347670389651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136076997323747130227186201 102057747992810347670389651)
          ·
            refine ⟨153086621989215521505584477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102057747992810347670389651 153086621989215521505584477)
            ·
              refine ⟨57407483245955820564594179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 153086621989215521505584477 57407483245955820564594179)
              ·
                refine ⟨86111224868933730846891269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57407483245955820564594179 86111224868933730846891269)
                ·
                  refine ⟨16145854662925074533792113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 86111224868933730846891269 16145854662925074533792113)
                  ·
                    refine ⟨12109390997193805900344085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16145854662925074533792113 12109390997193805900344085)
                    ·
                      refine ⟨567627702993459651578629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12109390997193805900344085 567627702993459651578629)
                      ·
                        rfl

theorem cell23_1105451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_1105451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105451 prefixEnd_1105451 := by exact prefixLift 1105451
  have htrace : WordTrace (prefixWord ++ tailWord_1105451) baseStart_1105451 baseEnd_1105451 := by
    simpa [prefixWord, tailWord_1105451, baseEnd_1105451] using wordTrace_append hprefix tailTrace_1105451
  have hstable : (prefixWord ++ tailWord_1105451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105451).length < 2 ^ (prefixWord ++ tailWord_1105451).sum := by decide
  have hdescent : baseEnd_1105451 < baseStart_1105451 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105459 : List Nat := [1, 1, 1, 2, 4, 3, 2, 4, 1, 2, 2]
def baseStart_1105459 : Nat := 118140960795 + 1105459 * 2 ^ 59
def prefixEnd_1105459 : Nat := 4983230072969 + 3 ^ 40 * 1105459 * 2
def baseEnd_1105459 : Nat := 567631810838695620278593

theorem tailTrace_1105459 : CollatzResearch.WordTrace tailWord_1105459 prefixEnd_1105459 567631810838695620278593 := by
  unfold tailWord_1105459
  simp only [CollatzResearch.WordTrace]
  refine ⟨40319402102118315211383431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26879601401412210140922287 40319402102118315211383431)
  ·
    refine ⟨60479103153177472817075147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40319402102118315211383431 60479103153177472817075147)
    ·
      refine ⟨90718654729766209225612721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60479103153177472817075147 90718654729766209225612721)
      ·
        refine ⟨68038991047324656919209541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90718654729766209225612721 68038991047324656919209541)
        ·
          refine ⟨12757310821373373172351789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 68038991047324656919209541 12757310821373373172351789)
          ·
            refine ⟨4783991558015014939631921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12757310821373373172351789 4783991558015014939631921)
            ·
              refine ⟨3587993668511261204723941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4783991558015014939631921 3587993668511261204723941)
              ·
                refine ⟨672748812845861475885739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3587993668511261204723941 672748812845861475885739)
                ·
                  refine ⟨1009123219268792213828609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672748812845861475885739 1009123219268792213828609)
                  ·
                    refine ⟨756842414451594160371457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1009123219268792213828609 756842414451594160371457)
                    ·
                      refine ⟨567631810838695620278593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756842414451594160371457 567631810838695620278593)
                      ·
                        rfl

theorem cell23_1105459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 2, 4, 1, 2, 2].length) (baseStart_1105459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105459 prefixEnd_1105459 := by exact prefixLift 1105459
  have htrace : WordTrace (prefixWord ++ tailWord_1105459) baseStart_1105459 baseEnd_1105459 := by
    simpa [prefixWord, tailWord_1105459, baseEnd_1105459] using wordTrace_append hprefix tailTrace_1105459
  have hstable : (prefixWord ++ tailWord_1105459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105459).length < 2 ^ (prefixWord ++ tailWord_1105459).sum := by decide
  have hdescent : baseEnd_1105459 < baseStart_1105459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105462 : List Nat := [5, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1105462 : Nat := 118140960795 + 1105462 * 2 ^ 59
def prefixEnd_1105462 : Nat := 4983230072969 + 3 ^ 40 * 1105462 * 2
def baseEnd_1105462 : Nat := 567633351280659108541079

theorem tailTrace_1105462 : CollatzResearch.WordTrace tailWord_1105462 prefixEnd_1105462 567633351280659108541079 := by
  unfold tailWord_1105462
  simp only [CollatzResearch.WordTrace]
  refine ⟨2519969470069215420233915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26879674347404964482495093 2519969470069215420233915)
  ·
    refine ⟨3779954205103823130350873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2519969470069215420233915 3779954205103823130350873)
    ·
      refine ⟨2834965653827867347763155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3779954205103823130350873 2834965653827867347763155)
      ·
        refine ⟨4252448480741801021644733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2834965653827867347763155 4252448480741801021644733)
        ·
          refine ⟨1594668180278175383116775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4252448480741801021644733 1594668180278175383116775)
          ·
            refine ⟨2392002270417263074675163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594668180278175383116775 2392002270417263074675163)
            ·
              refine ⟨3588003405625894612012745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392002270417263074675163 3588003405625894612012745)
              ·
                refine ⟨2691002554219420959009559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588003405625894612012745 2691002554219420959009559)
                ·
                  refine ⟨4036503831329131438514339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691002554219420959009559 4036503831329131438514339)
                  ·
                    refine ⟨6054755746993697157771509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4036503831329131438514339 6054755746993697157771509)
                    ·
                      refine ⟨567633351280659108541079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6054755746993697157771509 567633351280659108541079)
                      ·
                        rfl

theorem cell23_1105462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1105462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105462 prefixEnd_1105462 := by exact prefixLift 1105462
  have htrace : WordTrace (prefixWord ++ tailWord_1105462) baseStart_1105462 baseEnd_1105462 := by
    simpa [prefixWord, tailWord_1105462, baseEnd_1105462] using wordTrace_append hprefix tailTrace_1105462
  have hstable : (prefixWord ++ tailWord_1105462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105462).length < 2 ^ (prefixWord ++ tailWord_1105462).sum := by decide
  have hdescent : baseEnd_1105462 < baseStart_1105462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105469 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 2, 4]
def baseStart_1105469 : Nat := 118140960795 + 1105469 * 2 ^ 59
def prefixEnd_1105469 : Nat := 4983230072969 + 3 ^ 40 * 1105469 * 2
def baseEnd_1105469 : Nat := 189212315215080193717849

theorem tailTrace_1105469 : CollatzResearch.WordTrace tailWord_1105469 prefixEnd_1105469 189212315215080193717849 := by
  unfold tailWord_1105469
  simp only [CollatzResearch.WordTrace]
  refine ⟨40319766832082086919247461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26879844554721391279498307 40319766832082086919247461)
  ·
    refine ⟨7559956281015391297358899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40319766832082086919247461 7559956281015391297358899)
    ·
      refine ⟨11339934421523086946038349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7559956281015391297358899 11339934421523086946038349)
      ·
        refine ⟨4252475408071157604764381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11339934421523086946038349 4252475408071157604764381)
        ·
          refine ⟨1594678278026684101786643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4252475408071157604764381 1594678278026684101786643)
          ·
            refine ⟨2392017417040026152679965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594678278026684101786643 2392017417040026152679965)
            ·
              refine ⟨897006531390009807254987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2392017417040026152679965 897006531390009807254987)
              ·
                refine ⟨1345509797085014710882481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897006531390009807254987 1345509797085014710882481)
                ·
                  refine ⟨1009132347813761033161861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1345509797085014710882481 1009132347813761033161861)
                  ·
                    refine ⟨189212315215080193717849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1009132347813761033161861 189212315215080193717849)
                    ·
                      rfl

theorem cell23_1105469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 2, 4].length) (baseStart_1105469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105469 prefixEnd_1105469 := by exact prefixLift 1105469
  have htrace : WordTrace (prefixWord ++ tailWord_1105469) baseStart_1105469 baseEnd_1105469 := by
    simpa [prefixWord, tailWord_1105469, baseEnd_1105469] using wordTrace_append hprefix tailTrace_1105469
  have hstable : (prefixWord ++ tailWord_1105469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105469).length < 2 ^ (prefixWord ++ tailWord_1105469).sum := by decide
  have hdescent : baseEnd_1105469 < baseStart_1105469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105526 : List Nat := [5, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3]
def baseStart_1105526 : Nat := 118140960795 + 1105526 * 2 ^ 59
def prefixEnd_1105526 : Nat := 4983230072969 + 3 ^ 40 * 1105526 * 2
def baseEnd_1105526 : Nat := 567666214042546858140785

theorem tailTrace_1105526 : CollatzResearch.WordTrace tailWord_1105526 prefixEnd_1105526 567666214042546858140785 := by
  unfold tailWord_1105526
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520115362054724103379527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26881230528583723769381621 2520115362054724103379527)
  ·
    refine ⟨3780173043082086155069291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2520115362054724103379527 3780173043082086155069291)
    ·
      refine ⟨5670259564623129232603937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3780173043082086155069291 5670259564623129232603937)
      ·
        refine ⟨4252694673467346924452953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5670259564623129232603937 4252694673467346924452953)
        ·
          refine ⟨3189521005100510193339715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4252694673467346924452953 3189521005100510193339715)
          ·
            refine ⟨4784281507650765290009573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3189521005100510193339715 4784281507650765290009573)
            ·
              refine ⟨897052782684518491876795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4784281507650765290009573 897052782684518491876795)
              ·
                refine ⟨1345579174026777737815193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897052782684518491876795 1345579174026777737815193)
                ·
                  refine ⟨1009184380520083303361395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1345579174026777737815193 1009184380520083303361395)
                  ·
                    refine ⟨1513776570780124955042093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009184380520083303361395 1513776570780124955042093)
                    ·
                      refine ⟨567666214042546858140785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1513776570780124955042093 567666214042546858140785)
                      ·
                        rfl

theorem cell23_1105526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 4, 1, 2, 1, 3].length) (baseStart_1105526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105526 prefixEnd_1105526 := by exact prefixLift 1105526
  have htrace : WordTrace (prefixWord ++ tailWord_1105526) baseStart_1105526 baseEnd_1105526 := by
    simpa [prefixWord, tailWord_1105526, baseEnd_1105526] using wordTrace_append hprefix tailTrace_1105526
  have hstable : (prefixWord ++ tailWord_1105526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105526).length < 2 ^ (prefixWord ++ tailWord_1105526).sum := by decide
  have hdescent : baseEnd_1105526 < baseStart_1105526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105565 : List Nat := [1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 3]
def baseStart_1105565 : Nat := 118140960795 + 1105565 * 2 ^ 59
def prefixEnd_1105565 : Nat := 4983230072969 + 3 ^ 40 * 1105565 * 2
def baseEnd_1105565 : Nat := 567686239788072205553105

theorem tailTrace_1105565 : CollatzResearch.WordTrace tailWord_1105565 prefixEnd_1105565 567686239788072205553105 := by
  unfold tailWord_1105565
  simp only [CollatzResearch.WordTrace]
  refine ⟨40323268239734295314742149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26882178826489530209828099 40323268239734295314742149)
  ·
    refine ⟨7560612794950180371514153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40323268239734295314742149 7560612794950180371514153)
    ·
      refine ⟨5670459596212635278635615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7560612794950180371514153 5670459596212635278635615)
      ·
        refine ⟨8505689394318952917953423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5670459596212635278635615 8505689394318952917953423)
        ·
          refine ⟨12758534091478429376930135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8505689394318952917953423 12758534091478429376930135)
          ·
            refine ⟨19137801137217644065395203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12758534091478429376930135 19137801137217644065395203)
            ·
              refine ⟨28706701705826466098092805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19137801137217644065395203 28706701705826466098092805)
              ·
                refine ⟨5382506569842462393392401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28706701705826466098092805 5382506569842462393392401)
                ·
                  refine ⟨4036879927381846795044301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5382506569842462393392401 4036879927381846795044301)
                  ·
                    refine ⟨1513829972768192548141613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4036879927381846795044301 1513829972768192548141613)
                    ·
                      refine ⟨567686239788072205553105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1513829972768192548141613 567686239788072205553105)
                      ·
                        rfl

theorem cell23_1105565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 4, 2, 3, 3].length) (baseStart_1105565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105565 prefixEnd_1105565 := by exact prefixLift 1105565
  have htrace : WordTrace (prefixWord ++ tailWord_1105565) baseStart_1105565 baseEnd_1105565 := by
    simpa [prefixWord, tailWord_1105565, baseEnd_1105565] using wordTrace_append hprefix tailTrace_1105565
  have hstable : (prefixWord ++ tailWord_1105565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105565).length < 2 ^ (prefixWord ++ tailWord_1105565).sum := by decide
  have hdescent : baseEnd_1105565 < baseStart_1105565 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105566 : List Nat := [4, 3, 1, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_1105566 : Nat := 118140960795 + 1105566 * 2 ^ 59
def prefixEnd_1105566 : Nat := 4983230072969 + 3 ^ 40 * 1105566 * 2
def baseEnd_1105566 : Nat := 567686753268726701640601

theorem tailTrace_1105566 : CollatzResearch.WordTrace tailWord_1105566 prefixEnd_1105566 567686753268726701640601 := by
  unfold tailWord_1105566
  simp only [CollatzResearch.WordTrace]
  refine ⟨5040413089091334060691069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26882203141820448323685701 5040413089091334060691069)
  ·
    refine ⟨1890154908409250272759151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5040413089091334060691069 1890154908409250272759151)
    ·
      refine ⟨2835232362613875409138727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890154908409250272759151 2835232362613875409138727)
      ·
        refine ⟨4252848543920813113708091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835232362613875409138727 4252848543920813113708091)
        ·
          refine ⟨6379272815881219670562137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4252848543920813113708091 6379272815881219670562137)
          ·
            refine ⟨4784454611910914752921603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6379272815881219670562137 4784454611910914752921603)
            ·
              refine ⟨7176681917866372129382405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4784454611910914752921603 7176681917866372129382405)
              ·
                refine ⟨1345627859599944774259201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7176681917866372129382405 1345627859599944774259201)
                ·
                  refine ⟨1009220894699958580694401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1345627859599944774259201 1009220894699958580694401)
                  ·
                    refine ⟨756915671024968935520801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1009220894699958580694401 756915671024968935520801)
                    ·
                      refine ⟨567686753268726701640601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 756915671024968935520801 567686753268726701640601)
                      ·
                        rfl

theorem cell23_1105566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_1105566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105566 prefixEnd_1105566 := by exact prefixLift 1105566
  have htrace : WordTrace (prefixWord ++ tailWord_1105566) baseStart_1105566 baseEnd_1105566 := by
    simpa [prefixWord, tailWord_1105566, baseEnd_1105566] using wordTrace_append hprefix tailTrace_1105566
  have hstable : (prefixWord ++ tailWord_1105566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105566).length < 2 ^ (prefixWord ++ tailWord_1105566).sum := by decide
  have hdescent : baseEnd_1105566 < baseStart_1105566 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105572 : List Nat := [2, 3, 1, 2, 2, 3, 1, 4, 5]
def baseStart_1105572 : Nat := 118140960795 + 1105572 * 2 ^ 59
def prefixEnd_1105572 : Nat := 4983230072969 + 3 ^ 40 * 1105572 * 2
def baseEnd_1105572 : Nat := 63076648239183742018397

theorem tailTrace_1105572 : CollatzResearch.WordTrace tailWord_1105572 prefixEnd_1105572 63076648239183742018397 := by
  unfold tailWord_1105572
  simp only [CollatzResearch.WordTrace]
  refine ⟨20161761775354467755123485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26882349033805957006831313 20161761775354467755123485)
  ·
    refine ⟨7560660665757925408171307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20161761775354467755123485 7560660665757925408171307)
    ·
      refine ⟨11340990998636888112256961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7560660665757925408171307 11340990998636888112256961)
      ·
        refine ⟨8505743248977666084192721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11340990998636888112256961 8505743248977666084192721)
        ·
          refine ⟨6379307436733249563144541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8505743248977666084192721 6379307436733249563144541)
          ·
            refine ⟨2392240288774968586179203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6379307436733249563144541 2392240288774968586179203)
            ·
              refine ⟨3588360433162452879268805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392240288774968586179203 3588360433162452879268805)
              ·
                refine ⟨672817581217959914862901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3588360433162452879268805 672817581217959914862901)
                ·
                  refine ⟨63076648239183742018397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 672817581217959914862901 63076648239183742018397)
                  ·
                    rfl

theorem cell23_1105572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 4, 5].length) (baseStart_1105572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105572 prefixEnd_1105572 := by exact prefixLift 1105572
  have htrace : WordTrace (prefixWord ++ tailWord_1105572) baseStart_1105572 baseEnd_1105572 := by
    simpa [prefixWord, tailWord_1105572, baseEnd_1105572] using wordTrace_append hprefix tailTrace_1105572
  have hstable : (prefixWord ++ tailWord_1105572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105572).length < 2 ^ (prefixWord ++ tailWord_1105572).sum := by decide
  have hdescent : baseEnd_1105572 < baseStart_1105572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105606 : List Nat := [6, 1, 2, 1, 1, 1, 1, 5, 5]
def baseStart_1105606 : Nat := 118140960795 + 1105606 * 2 ^ 59
def prefixEnd_1105606 : Nat := 4983230072969 + 3 ^ 40 * 1105606 * 2
def baseEnd_1105606 : Nat := 63078588054989616126713

theorem tailTrace_1105606 : CollatzResearch.WordTrace tailWord_1105606 prefixEnd_1105606 63078588054989616126713 := by
  unfold tailWord_1105606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260148863518304978655771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26883175755057172877989781 1260148863518304978655771)
  ·
    refine ⟨1890223295277457467983657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1260148863518304978655771 1890223295277457467983657)
    ·
      refine ⟨1417667471458093100987743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1890223295277457467983657 1417667471458093100987743)
      ·
        refine ⟨2126501207187139651481615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1417667471458093100987743 2126501207187139651481615)
        ·
          refine ⟨3189751810780709477222423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2126501207187139651481615 3189751810780709477222423)
          ·
            refine ⟨4784627716171064215833635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3189751810780709477222423 4784627716171064215833635)
            ·
              refine ⟨7176941574256596323750453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4784627716171064215833635 7176941574256596323750453)
              ·
                refine ⟨672838272586555905351605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 7176941574256596323750453 672838272586555905351605)
                ·
                  refine ⟨63078588054989616126713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 672838272586555905351605 63078588054989616126713)
                  ·
                    rfl

theorem cell23_1105606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 5, 5].length) (baseStart_1105606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105606 prefixEnd_1105606 := by exact prefixLift 1105606
  have htrace : WordTrace (prefixWord ++ tailWord_1105606) baseStart_1105606 baseEnd_1105606 := by
    simpa [prefixWord, tailWord_1105606, baseEnd_1105606] using wordTrace_append hprefix tailTrace_1105606
  have hstable : (prefixWord ++ tailWord_1105606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105606).length < 2 ^ (prefixWord ++ tailWord_1105606).sum := by decide
  have hdescent : baseEnd_1105606 < baseStart_1105606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105670 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1105670 : Nat := 118140960795 + 1105670 * 2 ^ 59
def prefixEnd_1105670 : Nat := 4983230072969 + 3 ^ 40 * 1105670 * 2
def baseEnd_1105670 : Nat := 189246718418931431580041

theorem tailTrace_1105670 : CollatzResearch.WordTrace tailWord_1105670 prefixEnd_1105670 189246718418931431580041 := by
  unfold tailWord_1105670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1260221809511059320228577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26884731936235932164876309 1260221809511059320228577)
  ·
    refine ⟨945166357133294490171433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1260221809511059320228577 945166357133294490171433)
    ·
      refine ⟨708874767849970867628575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 945166357133294490171433 708874767849970867628575)
      ·
        refine ⟨1063312151774956301442863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 708874767849970867628575 1063312151774956301442863)
        ·
          refine ⟨1594968227662434452164295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063312151774956301442863 1594968227662434452164295)
          ·
            refine ⟨2392452341493651678246443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1594968227662434452164295 2392452341493651678246443)
            ·
              refine ⟨3588678512240477517369665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392452341493651678246443 3588678512240477517369665)
              ·
                refine ⟨2691508884180358138027249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588678512240477517369665 2691508884180358138027249)
                ·
                  refine ⟨2018631663135268603520437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2691508884180358138027249 2018631663135268603520437)
                  ·
                    refine ⟨189246718418931431580041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2018631663135268603520437 189246718418931431580041)
                    ·
                      rfl

theorem cell23_1105670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1105670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105670 prefixEnd_1105670 := by exact prefixLift 1105670
  have htrace : WordTrace (prefixWord ++ tailWord_1105670) baseStart_1105670 baseEnd_1105670 := by
    simpa [prefixWord, tailWord_1105670, baseEnd_1105670] using wordTrace_append hprefix tailTrace_1105670
  have hstable : (prefixWord ++ tailWord_1105670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105670).length < 2 ^ (prefixWord ++ tailWord_1105670).sum := by decide
  have hdescent : baseEnd_1105670 < baseStart_1105670 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105716 : List Nat := [2, 5, 1, 1, 2, 1, 1, 3, 2, 3, 2]
def baseStart_1105716 : Nat := 118140960795 + 1105716 * 2 ^ 59
def prefixEnd_1105716 : Nat := 4983230072969 + 3 ^ 40 * 1105716 * 2
def baseEnd_1105716 : Nat := 567763775366901114764911

theorem tailTrace_1105716 : CollatzResearch.WordTrace tailWord_1105716 prefixEnd_1105716 567763775366901114764911 := by
  unfold tailWord_1105716
  simp only [CollatzResearch.WordTrace]
  refine ⟨20164387831093624051744501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26885850441458165402326001 20164387831093624051744501)
  ·
    refine ⟨1890411359165027254851047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20164387831093624051744501 1890411359165027254851047)
    ·
      refine ⟨2835617038747540882276571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1890411359165027254851047 2835617038747540882276571)
      ·
        refine ⟨4253425558121311323414857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2835617038747540882276571 4253425558121311323414857)
        ·
          refine ⟨3190069168590983492561143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4253425558121311323414857 3190069168590983492561143)
          ·
            refine ⟨4785103752886475238841715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190069168590983492561143 4785103752886475238841715)
            ·
              refine ⟨7177655629329712858262573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4785103752886475238841715 7177655629329712858262573)
              ·
                refine ⟨2691620860998642321848465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7177655629329712858262573 2691620860998642321848465)
                ·
                  refine ⟨2018715645748981741386349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2691620860998642321848465 2018715645748981741386349)
                  ·
                    refine ⟨757018367155868153019881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018715645748981741386349 757018367155868153019881)
                    ·
                      refine ⟨567763775366901114764911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757018367155868153019881 567763775366901114764911)
                      ·
                        rfl

theorem cell23_1105716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 1, 1, 3, 2, 3, 2].length) (baseStart_1105716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105716 prefixEnd_1105716 := by exact prefixLift 1105716
  have htrace : WordTrace (prefixWord ++ tailWord_1105716) baseStart_1105716 baseEnd_1105716 := by
    simpa [prefixWord, tailWord_1105716, baseEnd_1105716] using wordTrace_append hprefix tailTrace_1105716
  have hstable : (prefixWord ++ tailWord_1105716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105716).length < 2 ^ (prefixWord ++ tailWord_1105716).sum := by decide
  have hdescent : baseEnd_1105716 < baseStart_1105716 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105722 : List Nat := [3, 1, 1, 1, 5, 2, 1, 2, 1, 6]
def baseStart_1105722 : Nat := 118140960795 + 1105722 * 2 ^ 59
def prefixEnd_1105722 : Nat := 4983230072969 + 3 ^ 40 * 1105722 * 2
def baseEnd_1105722 : Nat := 189255618750276030429961

theorem tailTrace_1105722 : CollatzResearch.WordTrace tailWord_1105722 prefixEnd_1105722 189255618750276030429961 := by
  unfold tailWord_1105722
  simp only [CollatzResearch.WordTrace]
  refine ⟨10082248625041377782051855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26885996333443674085471613 10082248625041377782051855)
  ·
    refine ⟨15123372937562066673077783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10082248625041377782051855 15123372937562066673077783)
    ·
      refine ⟨22685059406343100009616675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15123372937562066673077783 22685059406343100009616675)
      ·
        refine ⟨34027589109514650014425013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22685059406343100009616675 34027589109514650014425013)
        ·
          refine ⟨3190086479016998438852345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34027589109514650014425013 3190086479016998438852345)
          ·
            refine ⟨2392564859262748829139259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3190086479016998438852345 2392564859262748829139259)
            ·
              refine ⟨3588847288894123243708889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2392564859262748829139259 3588847288894123243708889)
              ·
                refine ⟨2691635466670592432781667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3588847288894123243708889 2691635466670592432781667)
                ·
                  refine ⟨4037453200005888649172501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2691635466670592432781667 4037453200005888649172501)
                  ·
                    refine ⟨189255618750276030429961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4037453200005888649172501 189255618750276030429961)
                    ·
                      rfl

theorem cell23_1105722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 2, 1, 2, 1, 6].length) (baseStart_1105722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105722 prefixEnd_1105722 := by exact prefixLift 1105722
  have htrace : WordTrace (prefixWord ++ tailWord_1105722) baseStart_1105722 baseEnd_1105722 := by
    simpa [prefixWord, tailWord_1105722, baseEnd_1105722] using wordTrace_append hprefix tailTrace_1105722
  have hstable : (prefixWord ++ tailWord_1105722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105722).length < 2 ^ (prefixWord ++ tailWord_1105722).sum := by decide
  have hdescent : baseEnd_1105722 < baseStart_1105722 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105726 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_1105726 : Nat := 118140960795 + 1105726 * 2 ^ 59
def prefixEnd_1105726 : Nat := 4983230072969 + 3 ^ 40 * 1105726 * 2
def baseEnd_1105726 : Nat := 189256303391148691879955

theorem tailTrace_1105726 : CollatzResearch.WordTrace tailWord_1105726 prefixEnd_1105726 189256303391148691879955 := by
  unfold tailWord_1105726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5041142549018877476419129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26886093594767346540902021 5041142549018877476419129)
  ·
    refine ⟨3780856911764158107314347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5041142549018877476419129 3780856911764158107314347)
    ·
      refine ⟨5671285367646237160971521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3780856911764158107314347 5671285367646237160971521)
      ·
        refine ⟨4253464025734677870728641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5671285367646237160971521 4253464025734677870728641)
        ·
          refine ⟨3190098019301008403046481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4253464025734677870728641 3190098019301008403046481)
          ·
            refine ⟨2392573514475756302284861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3190098019301008403046481 2392573514475756302284861)
            ·
              refine ⟨897215067928408613356823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2392573514475756302284861 897215067928408613356823)
              ·
                refine ⟨1345822601892612920035235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 897215067928408613356823 1345822601892612920035235)
                ·
                  refine ⟨2018733902838919380052853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345822601892612920035235 2018733902838919380052853)
                  ·
                    refine ⟨189256303391148691879955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2018733902838919380052853 189256303391148691879955)
                    ·
                      rfl

theorem cell23_1105726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_1105726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105726 prefixEnd_1105726 := by exact prefixLift 1105726
  have htrace : WordTrace (prefixWord ++ tailWord_1105726) baseStart_1105726 baseEnd_1105726 := by
    simpa [prefixWord, tailWord_1105726, baseEnd_1105726] using wordTrace_append hprefix tailTrace_1105726
  have hstable : (prefixWord ++ tailWord_1105726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105726).length < 2 ^ (prefixWord ++ tailWord_1105726).sum := by decide
  have hdescent : baseEnd_1105726 < baseStart_1105726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105740 : List Nat := [2, 2, 1, 3, 4, 2, 2, 2, 1, 1, 3]
def baseStart_1105740 : Nat := 118140960795 + 1105740 * 2 ^ 59
def prefixEnd_1105740 : Nat := 4983230072969 + 3 ^ 40 * 1105740 * 2
def baseEnd_1105740 : Nat := 567776098902609020864801

theorem tailTrace_1105740 : CollatzResearch.WordTrace tailWord_1105740 prefixEnd_1105740 567776098902609020864801 := by
  unfold tailWord_1105740
  simp only [CollatzResearch.WordTrace]
  refine ⟨20164825507050150101181337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26886434009400200134908449 20164825507050150101181337)
  ·
    refine ⟨15123619130287612575886003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20164825507050150101181337 15123619130287612575886003)
    ·
      refine ⟨22685428695431418863829005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15123619130287612575886003 22685428695431418863829005)
      ·
        refine ⟨8507035760786782073935877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22685428695431418863829005 8507035760786782073935877)
        ·
          refine ⟨1595069205147521638862977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8507035760786782073935877 1595069205147521638862977)
          ·
            refine ⟨1196301903860641229147233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595069205147521638862977 1196301903860641229147233)
            ·
              refine ⟨897226427895480921860425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196301903860641229147233 897226427895480921860425)
              ·
                refine ⟨672919820921610691395319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897226427895480921860425 672919820921610691395319)
                ·
                  refine ⟨1009379731382416037092979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 672919820921610691395319 1009379731382416037092979)
                  ·
                    refine ⟨1514069597073624055639469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009379731382416037092979 1514069597073624055639469)
                    ·
                      refine ⟨567776098902609020864801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514069597073624055639469 567776098902609020864801)
                      ·
                        rfl

theorem cell23_1105740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_1105740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105740 prefixEnd_1105740 := by exact prefixLift 1105740
  have htrace : WordTrace (prefixWord ++ tailWord_1105740) baseStart_1105740 baseEnd_1105740 := by
    simpa [prefixWord, tailWord_1105740, baseEnd_1105740] using wordTrace_append hprefix tailTrace_1105740
  have hstable : (prefixWord ++ tailWord_1105740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105740).length < 2 ^ (prefixWord ++ tailWord_1105740).sum := by decide
  have hdescent : baseEnd_1105740 < baseStart_1105740 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105765 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 4, 7]
def baseStart_1105765 : Nat := 118140960795 + 1105765 * 2 ^ 59
def prefixEnd_1105765 : Nat := 4983230072969 + 3 ^ 40 * 1105765 * 2
def baseEnd_1105765 : Nat := 189262978639657141017395

theorem tailTrace_1105765 : CollatzResearch.WordTrace tailWord_1105765 prefixEnd_1105765 189262978639657141017395 := by
  unfold tailWord_1105765
  simp only [CollatzResearch.WordTrace]
  refine ⟨40330562839009729472022749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26887041892673152981348499 40330562839009729472022749)
  ·
    refine ⟨15123961064628648552008531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40330562839009729472022749 15123961064628648552008531)
    ·
      refine ⟨22685941596942972828012797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15123961064628648552008531 22685941596942972828012797)
      ·
        refine ⟨8507228098853614810504799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22685941596942972828012797 8507228098853614810504799)
        ·
          refine ⟨12760842148280422215757199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507228098853614810504799 12760842148280422215757199)
          ·
            refine ⟨19141263222420633323635799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12760842148280422215757199 19141263222420633323635799)
            ·
              refine ⟨28711894833630949985453699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19141263222420633323635799 28711894833630949985453699)
              ·
                refine ⟨43067842250446424978180549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28711894833630949985453699 43067842250446424978180549)
                ·
                  refine ⟨8075220421958704683408853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 43067842250446424978180549 8075220421958704683408853)
                  ·
                    refine ⟨189262978639657141017395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 8075220421958704683408853 189262978639657141017395)
                    ·
                      rfl

theorem cell23_1105765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 7].length) (baseStart_1105765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105765 prefixEnd_1105765 := by exact prefixLift 1105765
  have htrace : WordTrace (prefixWord ++ tailWord_1105765) baseStart_1105765 baseEnd_1105765 := by
    simpa [prefixWord, tailWord_1105765, baseEnd_1105765] using wordTrace_append hprefix tailTrace_1105765
  have hstable : (prefixWord ++ tailWord_1105765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105765).length < 2 ^ (prefixWord ++ tailWord_1105765).sum := by decide
  have hdescent : baseEnd_1105765 < baseStart_1105765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105796 : List Nat := [2, 3, 2, 1, 1, 1, 5, 2, 2, 1, 3]
def baseStart_1105796 : Nat := 118140960795 + 1105796 * 2 ^ 59
def prefixEnd_1105796 : Nat := 4983230072969 + 3 ^ 40 * 1105796 * 2
def baseEnd_1105796 : Nat := 567804853819260801764543

theorem tailTrace_1105796 : CollatzResearch.WordTrace tailWord_1105796 prefixEnd_1105796 567804853819260801764543 := by
  unfold tailWord_1105796
  simp only [CollatzResearch.WordTrace]
  refine ⟨20165846750948710883200621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26887795667931614510934161 20165846750948710883200621)
  ·
    refine ⟨7562192531605766581200233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20165846750948710883200621 7562192531605766581200233)
    ·
      refine ⟨5671644398704324935900175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7562192531605766581200233 5671644398704324935900175)
      ·
        refine ⟨8507466598056487403850263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5671644398704324935900175 8507466598056487403850263)
        ·
          refine ⟨12761199897084731105775395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8507466598056487403850263 12761199897084731105775395)
          ·
            refine ⟨19141799845627096658663093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12761199897084731105775395 19141799845627096658663093)
            ·
              refine ⟨1794543735527540311749665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19141799845627096658663093 1794543735527540311749665)
              ·
                refine ⟨1345907801645655233812249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794543735527540311749665 1345907801645655233812249)
                ·
                  refine ⟨1009430851234241425359187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1345907801645655233812249 1009430851234241425359187)
                  ·
                    refine ⟨1514146276851362138038781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009430851234241425359187 1514146276851362138038781)
                    ·
                      refine ⟨567804853819260801764543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514146276851362138038781 567804853819260801764543)
                      ·
                        rfl

theorem cell23_1105796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 5, 2, 2, 1, 3].length) (baseStart_1105796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105796 prefixEnd_1105796 := by exact prefixLift 1105796
  have htrace : WordTrace (prefixWord ++ tailWord_1105796) baseStart_1105796 baseEnd_1105796 := by
    simpa [prefixWord, tailWord_1105796, baseEnd_1105796] using wordTrace_append hprefix tailTrace_1105796
  have hstable : (prefixWord ++ tailWord_1105796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105796).length < 2 ^ (prefixWord ++ tailWord_1105796).sum := by decide
  have hdescent : baseEnd_1105796 < baseStart_1105796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105823 : List Nat := [1, 1, 2, 5, 3, 1, 2, 2, 1, 3, 2]
def baseStart_1105823 : Nat := 118140960795 + 1105823 * 2 ^ 59
def prefixEnd_1105823 : Nat := 4983230072969 + 3 ^ 40 * 1105823 * 2
def baseEnd_1105823 : Nat := 567818717796932196126919

theorem tailTrace_1105823 : CollatzResearch.WordTrace tailWord_1105823 prefixEnd_1105823 567818717796932196126919 := by
  unfold tailWord_1105823
  simp only [CollatzResearch.WordTrace]
  refine ⟨40332678272799605377634123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26888452181866403585089415 40332678272799605377634123)
  ·
    refine ⟨60499017409199408066451185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40332678272799605377634123 60499017409199408066451185)
    ·
      refine ⟨45374263056899556049838389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60499017409199408066451185 45374263056899556049838389)
      ·
        refine ⟨4253837161584333379672349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45374263056899556049838389 4253837161584333379672349)
        ·
          refine ⟨1595188935594125017377131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4253837161584333379672349 1595188935594125017377131)
          ·
            refine ⟨2392783403391187526065697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595188935594125017377131 2392783403391187526065697)
            ·
              refine ⟨1794587552543390644549273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2392783403391187526065697 1794587552543390644549273)
              ·
                refine ⟨1345940664407542983411955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794587552543390644549273 1345940664407542983411955)
                ·
                  refine ⟨2018910996611314475117933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1345940664407542983411955 2018910996611314475117933)
                  ·
                    refine ⟨757091623729242928169225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2018910996611314475117933 757091623729242928169225)
                    ·
                      refine ⟨567818717796932196126919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757091623729242928169225 567818717796932196126919)
                      ·
                        rfl

theorem cell23_1105823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_1105823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105823 prefixEnd_1105823 := by exact prefixLift 1105823
  have htrace : WordTrace (prefixWord ++ tailWord_1105823) baseStart_1105823 baseEnd_1105823 := by
    simpa [prefixWord, tailWord_1105823, baseEnd_1105823] using wordTrace_append hprefix tailTrace_1105823
  have hstable : (prefixWord ++ tailWord_1105823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105823).length < 2 ^ (prefixWord ++ tailWord_1105823).sum := by decide
  have hdescent : baseEnd_1105823 < baseStart_1105823 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105835 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7]
def baseStart_1105835 : Nat := 118140960795 + 1105835 * 2 ^ 59
def prefixEnd_1105835 : Nat := 4983230072969 + 3 ^ 40 * 1105835 * 2
def baseEnd_1105835 : Nat := 567824879564786149176863

theorem tailTrace_1105835 : CollatzResearch.WordTrace tailWord_1105835 prefixEnd_1105835 567824879564786149176863 := by
  unfold tailWord_1105835
  simp only [CollatzResearch.WordTrace]
  refine ⟨40333115948756131427070959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26888743965837420951380639 40333115948756131427070959)
  ·
    refine ⟨60499673923134197140606439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40333115948756131427070959 60499673923134197140606439)
    ·
      refine ⟨90749510884701295710909659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60499673923134197140606439 90749510884701295710909659)
      ·
        refine ⟨136124266327051943566364489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90749510884701295710909659 136124266327051943566364489)
        ·
          refine ⟨102093199745288957674773367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 136124266327051943566364489 102093199745288957674773367)
          ·
            refine ⟨153139799617933436512160051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 102093199745288957674773367 153139799617933436512160051)
            ·
              refine ⟨229709699426900154768240077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 153139799617933436512160051 229709699426900154768240077)
              ·
                refine ⟨86141137285087558038090029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229709699426900154768240077 86141137285087558038090029)
                ·
                  refine ⟨32302926481907834264283761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86141137285087558038090029 32302926481907834264283761)
                  ·
                    refine ⟨24227194861430875698212821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32302926481907834264283761 24227194861430875698212821)
                    ·
                      refine ⟨567824879564786149176863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24227194861430875698212821 567824879564786149176863)
                      ·
                        rfl

theorem cell23_1105835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_1105835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105835 prefixEnd_1105835 := by exact prefixLift 1105835
  have htrace : WordTrace (prefixWord ++ tailWord_1105835) baseStart_1105835 baseEnd_1105835 := by
    simpa [prefixWord, tailWord_1105835, baseEnd_1105835] using wordTrace_append hprefix tailTrace_1105835
  have hstable : (prefixWord ++ tailWord_1105835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105835).length < 2 ^ (prefixWord ++ tailWord_1105835).sum := by decide
  have hdescent : baseEnd_1105835 < baseStart_1105835 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105910 : List Nat := [5, 1, 1, 1, 4, 2, 2, 2, 5]
def baseStart_1105910 : Nat := 118140960795 + 1105910 * 2 ^ 59
def prefixEnd_1105910 : Nat := 4983230072969 + 3 ^ 40 * 1105910 * 2
def baseEnd_1105910 : Nat := 63095932290430372859891

theorem tailTrace_1105910 : CollatzResearch.WordTrace tailWord_1105910 prefixEnd_1105910 63095932290430372859891 := by
  unfold tailWord_1105910
  simp only [CollatzResearch.WordTrace]
  refine ⟨2520990713967776202253199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26890567615656279490700789 2520990713967776202253199)
  ·
    refine ⟨3781486070951664303379799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2520990713967776202253199 3781486070951664303379799)
    ·
      refine ⟨5672229106427496455069699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3781486070951664303379799 5672229106427496455069699)
      ·
        refine ⟨8508343659641244682604549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5672229106427496455069699 8508343659641244682604549)
        ·
          refine ⟨1595314436182733377988353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8508343659641244682604549 1595314436182733377988353)
          ·
            refine ⟨1196485827137050033491265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595314436182733377988353 1196485827137050033491265)
            ·
              refine ⟨897364370352787525118449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1196485827137050033491265 897364370352787525118449)
              ·
                refine ⟨673023277764590643838837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897364370352787525118449 673023277764590643838837)
                ·
                  refine ⟨63095932290430372859891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 673023277764590643838837 63095932290430372859891)
                  ·
                    rfl

theorem cell23_1105910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_1105910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105910 prefixEnd_1105910 := by exact prefixLift 1105910
  have htrace : WordTrace (prefixWord ++ tailWord_1105910) baseStart_1105910 baseEnd_1105910 := by
    simpa [prefixWord, tailWord_1105910, baseEnd_1105910] using wordTrace_append hprefix tailTrace_1105910
  have hstable : (prefixWord ++ tailWord_1105910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105910).length < 2 ^ (prefixWord ++ tailWord_1105910).sum := by decide
  have hdescent : baseEnd_1105910 < baseStart_1105910 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105940 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 2, 5]
def baseStart_1105940 : Nat := 118140960795 + 1105940 * 2 ^ 59
def prefixEnd_1105940 : Nat := 4983230072969 + 3 ^ 40 * 1105940 * 2
def baseEnd_1105940 : Nat := 189292931677836079454627

theorem tailTrace_1105940 : CollatzResearch.WordTrace tailWord_1105940 prefixEnd_1105940 189292931677836079454627 := by
  unfold tailWord_1105940
  simp only [CollatzResearch.WordTrace]
  refine ⟨20168472806687867179821637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26891297075583822906428849 20168472806687867179821637)
  ·
    refine ⟨3781588651253975096216557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20168472806687867179821637 3781588651253975096216557)
    ·
      refine ⟨1418095744220240661081209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3781588651253975096216557 1418095744220240661081209)
      ·
        refine ⟨1063571808165180495810907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1418095744220240661081209 1063571808165180495810907)
        ·
          refine ⟨1595357712247770743716361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063571808165180495810907 1595357712247770743716361)
          ·
            refine ⟨1196518284185828057787271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595357712247770743716361 1196518284185828057787271)
            ·
              refine ⟨1794777426278742086680907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196518284185828057787271 1794777426278742086680907)
              ·
                refine ⟨2692166139418113130021361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794777426278742086680907 2692166139418113130021361)
                ·
                  refine ⟨2019124604563584847516021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2692166139418113130021361 2019124604563584847516021)
                  ·
                    refine ⟨189292931677836079454627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2019124604563584847516021 189292931677836079454627)
                    ·
                      rfl

theorem cell23_1105940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_1105940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105940 prefixEnd_1105940 := by exact prefixLift 1105940
  have htrace : WordTrace (prefixWord ++ tailWord_1105940) baseStart_1105940 baseEnd_1105940 := by
    simpa [prefixWord, tailWord_1105940, baseEnd_1105940] using wordTrace_append hprefix tailTrace_1105940
  have hstable : (prefixWord ++ tailWord_1105940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105940).length < 2 ^ (prefixWord ++ tailWord_1105940).sum := by decide
  have hdescent : baseEnd_1105940 < baseStart_1105940 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105943 : List Nat := [1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 4]
def baseStart_1105943 : Nat := 118140960795 + 1105943 * 2 ^ 59
def prefixEnd_1105943 : Nat := 4983230072969 + 3 ^ 40 * 1105943 * 2
def baseEnd_1105943 : Nat := 567880335475471726626367

theorem tailTrace_1105943 : CollatzResearch.WordTrace tailWord_1105943 prefixEnd_1105943 567880335475471726626367 := by
  unfold tailWord_1105943
  simp only [CollatzResearch.WordTrace]
  refine ⟨40337055032364865872002483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26891370021576577248001655 40337055032364865872002483)
  ·
    refine ⟨60505582548547298808003725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40337055032364865872002483 60505582548547298808003725)
    ·
      refine ⟨22689593455705237053001397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60505582548547298808003725 22689593455705237053001397)
      ·
        refine ⟨2127149386472365973718881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 22689593455705237053001397 2127149386472365973718881)
        ·
          refine ⟨1595362039854274480289161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2127149386472365973718881 1595362039854274480289161)
          ·
            refine ⟨1196521529890705860216871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595362039854274480289161 1196521529890705860216871)
            ·
              refine ⟨1794782294836058790325307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196521529890705860216871 1794782294836058790325307)
              ·
                refine ⟨2692173442254088185487961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794782294836058790325307 2692173442254088185487961)
                ·
                  refine ⟨2019130081690566139115971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2692173442254088185487961 2019130081690566139115971)
                  ·
                    refine ⟨3028695122535849208673957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2019130081690566139115971 3028695122535849208673957)
                    ·
                      refine ⟨567880335475471726626367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3028695122535849208673957 567880335475471726626367)
                      ·
                        rfl

theorem cell23_1105943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_1105943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105943 prefixEnd_1105943 := by exact prefixLift 1105943
  have htrace : WordTrace (prefixWord ++ tailWord_1105943) baseStart_1105943 baseEnd_1105943 := by
    simpa [prefixWord, tailWord_1105943, baseEnd_1105943] using wordTrace_append hprefix tailTrace_1105943
  have hstable : (prefixWord ++ tailWord_1105943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105943).length < 2 ^ (prefixWord ++ tailWord_1105943).sum := by decide
  have hdescent : baseEnd_1105943 < baseStart_1105943 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105946 : List Nat := [3, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3]
def baseStart_1105946 : Nat := 118140960795 + 1105946 * 2 ^ 59
def prefixEnd_1105946 : Nat := 4983230072969 + 3 ^ 40 * 1105946 * 2
def baseEnd_1105946 : Nat := 567881875917435214888853

theorem tailTrace_1105946 : CollatzResearch.WordTrace tailWord_1105946 prefixEnd_1105946 567881875917435214888853 := by
  unfold tailWord_1105946
  simp only [CollatzResearch.WordTrace]
  refine ⟨10084291112838499346090423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26891442967569331589574461 10084291112838499346090423)
  ·
    refine ⟨15126436669257749019135635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10084291112838499346090423 15126436669257749019135635)
    ·
      refine ⟨22689655003886623528703453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15126436669257749019135635 22689655003886623528703453)
      ·
        refine ⟨8508620626457483823263795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22689655003886623528703453 8508620626457483823263795)
        ·
          refine ⟨12762930939686225734895693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8508620626457483823263795 12762930939686225734895693)
          ·
            refine ⟨4786099102382334650585885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12762930939686225734895693 4786099102382334650585885)
            ·
              refine ⟨1794787163393375493969707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4786099102382334650585885 1794787163393375493969707)
              ·
                refine ⟨2692180745090063240954561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1794787163393375493969707 2692180745090063240954561)
                ·
                  refine ⟨2019135558817547430715921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2692180745090063240954561 2019135558817547430715921)
                  ·
                    refine ⟨1514351669113160573036941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2019135558817547430715921 1514351669113160573036941)
                    ·
                      refine ⟨567881875917435214888853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514351669113160573036941 567881875917435214888853)
                      ·
                        rfl

theorem cell23_1105946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_1105946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105946 prefixEnd_1105946 := by exact prefixLift 1105946
  have htrace : WordTrace (prefixWord ++ tailWord_1105946) baseStart_1105946 baseEnd_1105946 := by
    simpa [prefixWord, tailWord_1105946, baseEnd_1105946] using wordTrace_append hprefix tailTrace_1105946
  have hstable : (prefixWord ++ tailWord_1105946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105946).length < 2 ^ (prefixWord ++ tailWord_1105946).sum := by decide
  have hdescent : baseEnd_1105946 < baseStart_1105946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1105966 : List Nat := [4, 1, 3, 1, 1, 2, 3, 2, 6]
def baseStart_1105966 : Nat := 118140960795 + 1105966 * 2 ^ 59
def prefixEnd_1105966 : Nat := 4983230072969 + 3 ^ 40 * 1105966 * 2
def baseEnd_1105966 : Nat := 63099127281169459626529

theorem tailTrace_1105966 : CollatzResearch.WordTrace tailWord_1105966 prefixEnd_1105966 63099127281169459626529 := by
  unfold tailWord_1105966
  simp only [CollatzResearch.WordTrace]
  refine ⟨5042236738910192600011219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26891929274187693866726501 5042236738910192600011219)
  ·
    refine ⟨7563355108365288900016829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5042236738910192600011219 7563355108365288900016829)
    ·
      refine ⟨2836258165636983337506311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7563355108365288900016829 2836258165636983337506311)
      ·
        refine ⟨4254387248455475006259467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2836258165636983337506311 4254387248455475006259467)
        ·
          refine ⟨6381580872683212509389201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4254387248455475006259467 6381580872683212509389201)
          ·
            refine ⟨4786185654512409382041901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6381580872683212509389201 4786185654512409382041901)
            ·
              refine ⟨1794819620442153518265713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4786185654512409382041901 1794819620442153518265713)
              ·
                refine ⟨1346114715331615138699285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794819620442153518265713 1346114715331615138699285)
                ·
                  refine ⟨63099127281169459626529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1346114715331615138699285 63099127281169459626529)
                  ·
                    rfl

theorem cell23_1105966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_1105966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1105966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1105966 prefixEnd_1105966 := by exact prefixLift 1105966
  have htrace : WordTrace (prefixWord ++ tailWord_1105966) baseStart_1105966 baseEnd_1105966 := by
    simpa [prefixWord, tailWord_1105966, baseEnd_1105966] using wordTrace_append hprefix tailTrace_1105966
  have hstable : (prefixWord ++ tailWord_1105966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1105966).length < 2 ^ (prefixWord ++ tailWord_1105966).sum := by decide
  have hdescent : baseEnd_1105966 < baseStart_1105966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1105966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106009 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 6, 4]
def baseStart_1106009 : Nat := 118140960795 + 1106009 * 2 ^ 59
def prefixEnd_1106009 : Nat := 4983230072969 + 3 ^ 40 * 1106009 * 2
def baseEnd_1106009 : Nat := 189304741732889489467021

theorem tailTrace_1106009 : CollatzResearch.WordTrace tailWord_1106009 prefixEnd_1106009 189304741732889489467021 := by
  unfold tailWord_1106009
  simp only [CollatzResearch.WordTrace]
  refine ⟨40339462250125759143905081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26892974833417172762603387 40339462250125759143905081)
  ·
    refine ⟨30254596687594319357928811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40339462250125759143905081 30254596687594319357928811)
    ·
      refine ⟨45381895031391479036893217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30254596687594319357928811 45381895031391479036893217)
      ·
        refine ⟨34036421273543609277669913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45381895031391479036893217 34036421273543609277669913)
        ·
          refine ⟨25527315955157706958252435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34036421273543609277669913 25527315955157706958252435)
          ·
            refine ⟨38290973932736560437378653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25527315955157706958252435 38290973932736560437378653)
            ·
              refine ⟨14359115224776210164016995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38290973932736560437378653 14359115224776210164016995)
              ·
                refine ⟨21538672837164315246025493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14359115224776210164016995 21538672837164315246025493)
                ·
                  refine ⟨1009625289242077277157445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 21538672837164315246025493 1009625289242077277157445)
                  ·
                    refine ⟨189304741732889489467021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1009625289242077277157445 189304741732889489467021)
                    ·
                      rfl

theorem cell23_1106009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 6, 4].length) (baseStart_1106009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106009 prefixEnd_1106009 := by exact prefixLift 1106009
  have htrace : WordTrace (prefixWord ++ tailWord_1106009) baseStart_1106009 baseEnd_1106009 := by
    simpa [prefixWord, tailWord_1106009, baseEnd_1106009] using wordTrace_append hprefix tailTrace_1106009
  have hstable : (prefixWord ++ tailWord_1106009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106009).length < 2 ^ (prefixWord ++ tailWord_1106009).sum := by decide
  have hdescent : baseEnd_1106009 < baseStart_1106009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106013 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 1, 5]
def baseStart_1106013 : Nat := 118140960795 + 1106013 * 2 ^ 59
def prefixEnd_1106013 : Nat := 4983230072969 + 3 ^ 40 * 1106013 * 2
def baseEnd_1106013 : Nat := 189305426373762150917015

theorem tailTrace_1106013 : CollatzResearch.WordTrace tailWord_1106013 prefixEnd_1106013 189305426373762150917015 := by
  unfold tailWord_1106013
  simp only [CollatzResearch.WordTrace]
  refine ⟨40339608142111267827050693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26893072094740845218033795 40339608142111267827050693)
  ·
    refine ⟨7563676526645862717572005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40339608142111267827050693 7563676526645862717572005)
    ·
      refine ⟨1418189348746099259544751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7563676526645862717572005 1418189348746099259544751)
      ·
        refine ⟨2127284023119148889317127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418189348746099259544751 2127284023119148889317127)
        ·
          refine ⟨3190926034678723333975691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127284023119148889317127 3190926034678723333975691)
          ·
            refine ⟨4786389052018085000963537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3190926034678723333975691 4786389052018085000963537)
            ·
              refine ⟨3589791789013563750722653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4786389052018085000963537 3589791789013563750722653)
              ·
                refine ⟨1346171920880086406520995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3589791789013563750722653 1346171920880086406520995)
                ·
                  refine ⟨2019257881320129609781493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346171920880086406520995 2019257881320129609781493)
                  ·
                    refine ⟨189305426373762150917015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2019257881320129609781493 189305426373762150917015)
                    ·
                      rfl

theorem cell23_1106013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 1, 5].length) (baseStart_1106013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106013 prefixEnd_1106013 := by exact prefixLift 1106013
  have htrace : WordTrace (prefixWord ++ tailWord_1106013) baseStart_1106013 baseEnd_1106013 := by
    simpa [prefixWord, tailWord_1106013, baseEnd_1106013] using wordTrace_append hprefix tailTrace_1106013
  have hstable : (prefixWord ++ tailWord_1106013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106013).length < 2 ^ (prefixWord ++ tailWord_1106013).sum := by decide
  have hdescent : baseEnd_1106013 < baseStart_1106013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106016 : List Nat := [2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4]
def baseStart_1106016 : Nat := 118140960795 + 1106016 * 2 ^ 59
def prefixEnd_1106016 : Nat := 4983230072969 + 3 ^ 40 * 1106016 * 2
def baseEnd_1106016 : Nat := 567917819563249941013531

theorem tailTrace_1106016 : CollatzResearch.WordTrace tailWord_1106016 prefixEnd_1106016 567917819563249941013531 := by
  unfold tailWord_1106016
  simp only [CollatzResearch.WordTrace]
  refine ⟨20169858780550199669704951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26893145040733599559606601 20169858780550199669704951)
  ·
    refine ⟨30254788170825299504557427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20169858780550199669704951 30254788170825299504557427)
    ·
      refine ⟨45382182256237949256836141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30254788170825299504557427 45382182256237949256836141)
      ·
        refine ⟨17018318346089230971313553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45382182256237949256836141 17018318346089230971313553)
        ·
          refine ⟨12763738759566923228485165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17018318346089230971313553 12763738759566923228485165)
          ·
            refine ⟨4786402034837596210681937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12763738759566923228485165 4786402034837596210681937)
            ·
              refine ⟨3589801526128197158011453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4786402034837596210681937 3589801526128197158011453)
              ·
                refine ⟨1346175572298073934254295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3589801526128197158011453 1346175572298073934254295)
                ·
                  refine ⟨2019263358447110901381443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346175572298073934254295 2019263358447110901381443)
                  ·
                    refine ⟨3028895037670666352072165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2019263358447110901381443 3028895037670666352072165)
                    ·
                      refine ⟨567917819563249941013531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3028895037670666352072165 567917819563249941013531)
                      ·
                        rfl

theorem cell23_1106016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 3, 1, 1, 4].length) (baseStart_1106016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106016 prefixEnd_1106016 := by exact prefixLift 1106016
  have htrace : WordTrace (prefixWord ++ tailWord_1106016) baseStart_1106016 baseEnd_1106016 := by
    simpa [prefixWord, tailWord_1106016, baseEnd_1106016] using wordTrace_append hprefix tailTrace_1106016
  have hstable : (prefixWord ++ tailWord_1106016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106016).length < 2 ^ (prefixWord ++ tailWord_1106016).sum := by decide
  have hdescent : baseEnd_1106016 < baseStart_1106016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106019 : List Nat := [1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5]
def baseStart_1106019 : Nat := 118140960795 + 1106019 * 2 ^ 59
def prefixEnd_1106019 : Nat := 4983230072969 + 3 ^ 40 * 1106019 * 2
def baseEnd_1106019 : Nat := 567919360005213429276017

theorem tailTrace_1106019 : CollatzResearch.WordTrace tailWord_1106019 prefixEnd_1106019 567919360005213429276017 := by
  unfold tailWord_1106019
  simp only [CollatzResearch.WordTrace]
  refine ⟨40339826980089530851769111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26893217986726353901179407 40339826980089530851769111)
  ·
    refine ⟨60509740470134296277653667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40339826980089530851769111 60509740470134296277653667)
    ·
      refine ⟨90764610705201444416480501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60509740470134296277653667 90764610705201444416480501)
      ·
        refine ⟨8509182253612635414045047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 90764610705201444416480501 8509182253612635414045047)
        ·
          refine ⟨12763773380418953121067571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8509182253612635414045047 12763773380418953121067571)
          ·
            refine ⟨19145660070628429681601357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12763773380418953121067571 19145660070628429681601357)
            ·
              refine ⟨7179622526485661130600509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19145660070628429681601357 7179622526485661130600509)
              ·
                refine ⟨2692358447432122923975191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7179622526485661130600509 2692358447432122923975191)
                ·
                  refine ⟨4038537671148184385962787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692358447432122923975191 4038537671148184385962787)
                  ·
                    refine ⟨6057806506722276578944181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4038537671148184385962787 6057806506722276578944181)
                    ·
                      refine ⟨567919360005213429276017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6057806506722276578944181 567919360005213429276017)
                      ·
                        rfl

theorem cell23_1106019_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 5].length) (baseStart_1106019 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106019 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106019 prefixEnd_1106019 := by exact prefixLift 1106019
  have htrace : WordTrace (prefixWord ++ tailWord_1106019) baseStart_1106019 baseEnd_1106019 := by
    simpa [prefixWord, tailWord_1106019, baseEnd_1106019] using wordTrace_append hprefix tailTrace_1106019
  have hstable : (prefixWord ++ tailWord_1106019).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106019).length < 2 ^ (prefixWord ++ tailWord_1106019).sum := by decide
  have hdescent : baseEnd_1106019 < baseStart_1106019 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106019) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106029 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 6]
def baseStart_1106029 : Nat := 118140960795 + 1106029 * 2 ^ 59
def prefixEnd_1106029 : Nat := 4983230072969 + 3 ^ 40 * 1106029 * 2
def baseEnd_1106029 : Nat := 567924494811758390150971

theorem tailTrace_1106029 : CollatzResearch.WordTrace tailWord_1106029 prefixEnd_1106029 567924494811758390150971 := by
  unfold tailWord_1106029
  simp only [CollatzResearch.WordTrace]
  refine ⟨40340191710053302559633141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26893461140035535039755427 40340191710053302559633141)
  ·
    refine ⟨3781892972817497114965607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40340191710053302559633141 3781892972817497114965607)
    ·
      refine ⟨5672839459226245672448411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3781892972817497114965607 5672839459226245672448411)
      ·
        refine ⟨8509259188839368508672617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5672839459226245672448411 8509259188839368508672617)
        ·
          refine ⟨6381944391629526381504463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8509259188839368508672617 6381944391629526381504463)
          ·
            refine ⟨9572916587444289572256695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6381944391629526381504463 9572916587444289572256695)
            ·
              refine ⟨14359374881166434358385043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9572916587444289572256695 14359374881166434358385043)
              ·
                refine ⟨21539062321749651537577565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14359374881166434358385043 21539062321749651537577565)
                ·
                  refine ⟨8077148370656119326591587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21539062321749651537577565 8077148370656119326591587)
                  ·
                    refine ⟨12115722555984178989887381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8077148370656119326591587 12115722555984178989887381)
                    ·
                      refine ⟨567924494811758390150971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 12115722555984178989887381 567924494811758390150971)
                      ·
                        rfl

theorem cell23_1106029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 1, 6].length) (baseStart_1106029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106029 prefixEnd_1106029 := by exact prefixLift 1106029
  have htrace : WordTrace (prefixWord ++ tailWord_1106029) baseStart_1106029 baseEnd_1106029 := by
    simpa [prefixWord, tailWord_1106029, baseEnd_1106029] using wordTrace_append hprefix tailTrace_1106029
  have hstable : (prefixWord ++ tailWord_1106029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106029).length < 2 ^ (prefixWord ++ tailWord_1106029).sum := by decide
  have hdescent : baseEnd_1106029 < baseStart_1106029 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106039 : List Nat := [1, 1, 3, 1, 1, 6, 2, 8]
def baseStart_1106039 : Nat := 118140960795 + 1106039 * 2 ^ 59
def prefixEnd_1106039 : Nat := 4983230072969 + 3 ^ 40 * 1106039 * 2
def baseEnd_1106039 : Nat := 21034430726603827815775

theorem tailTrace_1106039 : CollatzResearch.WordTrace tailWord_1106039 prefixEnd_1106039 21034430726603827815775 := by
  unfold tailWord_1106039
  simp only [CollatzResearch.WordTrace]
  refine ⟨40340556440017074267497171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26893704293344716178331447 40340556440017074267497171)
  ·
    refine ⟨60510834660025611401245757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40340556440017074267497171 60510834660025611401245757)
    ·
      refine ⟨22691562997509604275467159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60510834660025611401245757 22691562997509604275467159)
      ·
        refine ⟨34037344496264406413200739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22691562997509604275467159 34037344496264406413200739)
        ·
          refine ⟨51056016744396609619801109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34037344496264406413200739 51056016744396609619801109)
          ·
            refine ⟨2393250784893591075928177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 51056016744396609619801109 2393250784893591075928177)
            ·
              refine ⟨1794938088670193306946133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2393250784893591075928177 1794938088670193306946133)
              ·
                refine ⟨21034430726603827815775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1794938088670193306946133 21034430726603827815775)
                ·
                  rfl

theorem cell23_1106039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 2, 8].length) (baseStart_1106039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106039 prefixEnd_1106039 := by exact prefixLift 1106039
  have htrace : WordTrace (prefixWord ++ tailWord_1106039) baseStart_1106039 baseEnd_1106039 := by
    simpa [prefixWord, tailWord_1106039, baseEnd_1106039] using wordTrace_append hprefix tailTrace_1106039
  have hstable : (prefixWord ++ tailWord_1106039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106039).length < 2 ^ (prefixWord ++ tailWord_1106039).sum := by decide
  have hdescent : baseEnd_1106039 < baseStart_1106039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106053 : List Nat := [1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 3]
def baseStart_1106053 : Nat := 118140960795 + 1106053 * 2 ^ 59
def prefixEnd_1106053 : Nat := 4983230072969 + 3 ^ 40 * 1106053 * 2
def baseEnd_1106053 : Nat := 567936818347466296250861

theorem tailTrace_1106053 : CollatzResearch.WordTrace tailWord_1106053 prefixEnd_1106053 567936818347466296250861 := by
  unfold tailWord_1106053
  simp only [CollatzResearch.WordTrace]
  refine ⟨40341067061966354658506813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26894044707977569772337875 40341067061966354658506813)
  ·
    refine ⟨15127900148237382996940055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40341067061966354658506813 15127900148237382996940055)
    ·
      refine ⟨22691850222356074495410083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15127900148237382996940055 22691850222356074495410083)
      ·
        refine ⟨34037775333534111743115125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22691850222356074495410083 34037775333534111743115125)
        ·
          refine ⟨3191041437518822975917043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 34037775333534111743115125 3191041437518822975917043)
          ·
            refine ⟨4786562156278234463875565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191041437518822975917043 4786562156278234463875565)
            ·
              refine ⟨1794960808604337923953337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4786562156278234463875565 1794960808604337923953337)
              ·
                refine ⟨1346220606453253442965003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1794960808604337923953337 1346220606453253442965003)
                ·
                  refine ⟨2019330909679880164447505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346220606453253442965003 2019330909679880164447505)
                  ·
                    refine ⟨1514498182259910123335629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2019330909679880164447505 1514498182259910123335629)
                    ·
                      refine ⟨567936818347466296250861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514498182259910123335629 567936818347466296250861)
                      ·
                        rfl

theorem cell23_1106053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 3, 2, 1, 2, 3].length) (baseStart_1106053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106053 prefixEnd_1106053 := by exact prefixLift 1106053
  have htrace : WordTrace (prefixWord ++ tailWord_1106053) baseStart_1106053 baseEnd_1106053 := by
    simpa [prefixWord, tailWord_1106053, baseEnd_1106053] using wordTrace_append hprefix tailTrace_1106053
  have hstable : (prefixWord ++ tailWord_1106053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106053).length < 2 ^ (prefixWord ++ tailWord_1106053).sum := by decide
  have hdescent : baseEnd_1106053 < baseStart_1106053 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106090 : List Nat := [3, 1, 5, 1, 3, 1, 1, 8]
def baseStart_1106090 : Nat := 118140960795 + 1106090 * 2 ^ 59
def prefixEnd_1106090 : Nat := 4983230072969 + 3 ^ 40 * 1106090 * 2
def baseEnd_1106090 : Nat := 21035400634506764869933

theorem tailTrace_1106090 : CollatzResearch.WordTrace tailWord_1106090 prefixEnd_1106090 21035400634506764869933 := by
  unfold tailWord_1106090
  simp only [CollatzResearch.WordTrace]
  refine ⟨10085604140708077494400931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26894944375221539985069149 10085604140708077494400931)
  ·
    refine ⟨15128406211062116241601397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10085604140708077494400931 15128406211062116241601397)
    ·
      refine ⟨1418288082287073397650131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15128406211062116241601397 1418288082287073397650131)
      ·
        refine ⟨2127432123430610096475197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418288082287073397650131 2127432123430610096475197)
        ·
          refine ⟨797787046286478786178199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2127432123430610096475197 797787046286478786178199)
          ·
            refine ⟨1196680569429718179267299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 797787046286478786178199 1196680569429718179267299)
            ·
              refine ⟨1795020854144577268900949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196680569429718179267299 1795020854144577268900949)
              ·
                refine ⟨21035400634506764869933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1795020854144577268900949 21035400634506764869933)
                ·
                  rfl

theorem cell23_1106090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 3, 1, 1, 8].length) (baseStart_1106090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106090 prefixEnd_1106090 := by exact prefixLift 1106090
  have htrace : WordTrace (prefixWord ++ tailWord_1106090) baseStart_1106090 baseEnd_1106090 := by
    simpa [prefixWord, tailWord_1106090, baseEnd_1106090] using wordTrace_append hprefix tailTrace_1106090
  have hstable : (prefixWord ++ tailWord_1106090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106090).length < 2 ^ (prefixWord ++ tailWord_1106090).sum := by decide
  have hdescent : baseEnd_1106090 < baseStart_1106090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106123 : List Nat := [1, 1, 1, 1, 3, 2, 4, 2, 4, 2, 2]
def baseStart_1106123 : Nat := 118140960795 + 1106123 * 2 ^ 59
def prefixEnd_1106123 : Nat := 4983230072969 + 3 ^ 40 * 1106123 * 2
def baseEnd_1106123 : Nat := 567972761993281022375539

theorem tailTrace_1106123 : CollatzResearch.WordTrace tailWord_1106123 prefixEnd_1106123 567972761993281022375539 := by
  unfold tailWord_1106123
  simp only [CollatzResearch.WordTrace]
  refine ⟨40343620171712756613555023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26895746781141837742370015 40343620171712756613555023)
  ·
    refine ⟨60515430257569134920332535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40343620171712756613555023 60515430257569134920332535)
    ·
      refine ⟨90773145386353702380498803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60515430257569134920332535 90773145386353702380498803)
      ·
        refine ⟨136159718079530553570748205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90773145386353702380498803 136159718079530553570748205)
        ·
          refine ⟨51059894279823957589030577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 136159718079530553570748205 51059894279823957589030577)
          ·
            refine ⟨38294920709867968191772933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 51059894279823957589030577 38294920709867968191772933)
            ·
              refine ⟨7180297633100244035957425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38294920709867968191772933 7180297633100244035957425)
              ·
                refine ⟨5385223224825183026968069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7180297633100244035957425 5385223224825183026968069)
                ·
                  refine ⟨1009729354654721817556513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5385223224825183026968069 1009729354654721817556513)
                  ·
                    refine ⟨757297015991041363167385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1009729354654721817556513 757297015991041363167385)
                    ·
                      refine ⟨567972761993281022375539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757297015991041363167385 567972761993281022375539)
                      ·
                        rfl

theorem cell23_1106123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 2, 4, 2, 2].length) (baseStart_1106123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106123 prefixEnd_1106123 := by exact prefixLift 1106123
  have htrace : WordTrace (prefixWord ++ tailWord_1106123) baseStart_1106123 baseEnd_1106123 := by
    simpa [prefixWord, tailWord_1106123, baseEnd_1106123] using wordTrace_append hprefix tailTrace_1106123
  have hstable : (prefixWord ++ tailWord_1106123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106123).length < 2 ^ (prefixWord ++ tailWord_1106123).sum := by decide
  have hdescent : baseEnd_1106123 < baseStart_1106123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106134 : List Nat := [5, 2, 1, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1106134 : Nat := 118140960795 + 1106134 * 2 ^ 59
def prefixEnd_1106134 : Nat := 4983230072969 + 3 ^ 40 * 1106134 * 2
def baseEnd_1106134 : Nat := 567978410280480479337989

theorem tailTrace_1106134 : CollatzResearch.WordTrace tailWord_1106134 prefixEnd_1106134 567978410280480479337989 := by
  unfold tailWord_1106134
  simp only [CollatzResearch.WordTrace]
  refine ⟨2521501335917056593262841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 26896014249781936994803637 2521501335917056593262841)
  ·
    refine ⟨1891126001937792444947131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2521501335917056593262841 1891126001937792444947131)
    ·
      refine ⟨2836689002906688667420697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1891126001937792444947131 2836689002906688667420697)
      ·
        refine ⟨2127516752180016500565523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2836689002906688667420697 2127516752180016500565523)
        ·
          refine ⟨3191275128270024750848285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2127516752180016500565523 3191275128270024750848285)
          ·
            refine ⟨1196728173101259281568107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3191275128270024750848285 1196728173101259281568107)
            ·
              refine ⟨1795092259651888922352161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196728173101259281568107 1795092259651888922352161)
              ·
                refine ⟨1346319194738916691764121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1795092259651888922352161 1346319194738916691764121)
                ·
                  refine ⟨1009739396054187518823091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1346319194738916691764121 1009739396054187518823091)
                  ·
                    refine ⟨1514609094081281278234637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009739396054187518823091 1514609094081281278234637)
                    ·
                      refine ⟨567978410280480479337989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514609094081281278234637 567978410280480479337989)
                      ·
                        rfl

theorem cell23_1106134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1106134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106134 prefixEnd_1106134 := by exact prefixLift 1106134
  have htrace : WordTrace (prefixWord ++ tailWord_1106134) baseStart_1106134 baseEnd_1106134 := by
    simpa [prefixWord, tailWord_1106134, baseEnd_1106134] using wordTrace_append hprefix tailTrace_1106134
  have hstable : (prefixWord ++ tailWord_1106134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106134).length < 2 ^ (prefixWord ++ tailWord_1106134).sum := by decide
  have hdescent : baseEnd_1106134 < baseStart_1106134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106136 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 2, 2, 4]
def baseStart_1106136 : Nat := 118140960795 + 1106136 * 2 ^ 59
def prefixEnd_1106136 : Nat := 4983230072969 + 3 ^ 40 * 1106136 * 2
def baseEnd_1106136 : Nat := 567979437241789471512979

theorem tailTrace_1106136 : CollatzResearch.WordTrace tailWord_1106136 prefixEnd_1106136 567979437241789471512979 := by
  unfold tailWord_1106136
  simp only [CollatzResearch.WordTrace]
  refine ⟨20172047160332829916889131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26896062880443773222518841 20172047160332829916889131)
  ·
    refine ⟨30258070740499244875333697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20172047160332829916889131 30258070740499244875333697)
    ·
      refine ⟨22693553055374433656500273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30258070740499244875333697 22693553055374433656500273)
      ·
        refine ⟨17020164791530825242375205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22693553055374433656500273 17020164791530825242375205)
        ·
          refine ⟨3191280898412029732945351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17020164791530825242375205 3191280898412029732945351)
          ·
            refine ⟨4786921347618044599418027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191280898412029732945351 4786921347618044599418027)
            ·
              refine ⟨7180382021427066899127041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4786921347618044599418027 7180382021427066899127041)
              ·
                refine ⟨5385286516070300174345281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7180382021427066899127041 5385286516070300174345281)
                ·
                  refine ⟨4038964887052725130758961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5385286516070300174345281 4038964887052725130758961)
                  ·
                    refine ⟨3029223665289543848069221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4038964887052725130758961 3029223665289543848069221)
                    ·
                      refine ⟨567979437241789471512979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3029223665289543848069221 567979437241789471512979)
                      ·
                        rfl

theorem cell23_1106136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_1106136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106136 prefixEnd_1106136 := by exact prefixLift 1106136
  have htrace : WordTrace (prefixWord ++ tailWord_1106136) baseStart_1106136 baseEnd_1106136 := by
    simpa [prefixWord, tailWord_1106136, baseEnd_1106136] using wordTrace_append hprefix tailTrace_1106136
  have hstable : (prefixWord ++ tailWord_1106136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106136).length < 2 ^ (prefixWord ++ tailWord_1106136).sum := by decide
  have hdescent : baseEnd_1106136 < baseStart_1106136 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106156 : List Nat := [2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 3]
def baseStart_1106156 : Nat := 118140960795 + 1106156 * 2 ^ 59
def prefixEnd_1106156 : Nat := 4983230072969 + 3 ^ 40 * 1106156 * 2
def baseEnd_1106156 : Nat := 567989706854879393262887

theorem tailTrace_1106156 : CollatzResearch.WordTrace tailWord_1106156 prefixEnd_1106156 567989706854879393262887 := by
  unfold tailWord_1106156
  simp only [CollatzResearch.WordTrace]
  refine ⟨20172411890296601624753161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26896549187062135499670881 20172411890296601624753161)
  ·
    refine ⟨15129308917722451218564871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20172411890296601624753161 15129308917722451218564871)
    ·
      refine ⟨22693963376583676827847307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15129308917722451218564871 22693963376583676827847307)
      ·
        refine ⟨34040945064875515241770961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22693963376583676827847307 34040945064875515241770961)
        ·
          refine ⟨25530708798656636431328221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34040945064875515241770961 25530708798656636431328221)
          ·
            refine ⟨9574015799496238661748083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25530708798656636431328221 9574015799496238661748083)
            ·
              refine ⟨14361023699244357992622125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9574015799496238661748083 14361023699244357992622125)
              ·
                refine ⟨5385383887216634247233297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14361023699244357992622125 5385383887216634247233297)
                ·
                  refine ⟨4039037915412475685424973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5385383887216634247233297 4039037915412475685424973)
                  ·
                    refine ⟨1514639218279678382034365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4039037915412475685424973 1514639218279678382034365)
                    ·
                      refine ⟨567989706854879393262887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514639218279678382034365 567989706854879393262887)
                      ·
                        rfl

theorem cell23_1106156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 3].length) (baseStart_1106156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106156 prefixEnd_1106156 := by exact prefixLift 1106156
  have htrace : WordTrace (prefixWord ++ tailWord_1106156) baseStart_1106156 baseEnd_1106156 := by
    simpa [prefixWord, tailWord_1106156, baseEnd_1106156] using wordTrace_append hprefix tailTrace_1106156
  have hstable : (prefixWord ++ tailWord_1106156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106156).length < 2 ^ (prefixWord ++ tailWord_1106156).sum := by decide
  have hdescent : baseEnd_1106156 < baseStart_1106156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106157 : List Nat := [1, 5, 1, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_1106157 : Nat := 118140960795 + 1106157 * 2 ^ 59
def prefixEnd_1106157 : Nat := 4983230072969 + 3 ^ 40 * 1106157 * 2
def baseEnd_1106157 : Nat := 567990220335533889350383

theorem tailTrace_1106157 : CollatzResearch.WordTrace tailWord_1106157 prefixEnd_1106157 567990220335533889350383 := by
  unfold tailWord_1106157
  simp only [CollatzResearch.WordTrace]
  refine ⟨40344860253589580420292725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26896573502393053613528483 40344860253589580420292725)
  ·
    refine ⟨3782330648774023164402443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 40344860253589580420292725 3782330648774023164402443)
    ·
      refine ⟨5673495973161034746603665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3782330648774023164402443 5673495973161034746603665)
      ·
        refine ⟨4255121979870776059952749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5673495973161034746603665 4255121979870776059952749)
        ·
          refine ⟨1595670742451541022482281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4255121979870776059952749 1595670742451541022482281)
          ·
            refine ⟨1196753056838655766861711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1595670742451541022482281 1196753056838655766861711)
            ·
              refine ⟨1795129585257983650292567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196753056838655766861711 1795129585257983650292567)
              ·
                refine ⟨2692694377886975475438851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795129585257983650292567 2692694377886975475438851)
                ·
                  refine ⟨4039041566830463213158277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2692694377886975475438851 4039041566830463213158277)
                  ·
                    refine ⟨757320293780711852467177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4039041566830463213158277 757320293780711852467177)
                    ·
                      refine ⟨567990220335533889350383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757320293780711852467177 567990220335533889350383)
                      ·
                        rfl

theorem cell23_1106157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_1106157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106157 prefixEnd_1106157 := by exact prefixLift 1106157
  have htrace : WordTrace (prefixWord ++ tailWord_1106157) baseStart_1106157 baseEnd_1106157 := by
    simpa [prefixWord, tailWord_1106157, baseEnd_1106157] using wordTrace_append hprefix tailTrace_1106157
  have hstable : (prefixWord ++ tailWord_1106157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106157).length < 2 ^ (prefixWord ++ tailWord_1106157).sum := by decide
  have hdescent : baseEnd_1106157 < baseStart_1106157 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106169 : List Nat := [1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 7]
def baseStart_1106169 : Nat := 118140960795 + 1106169 * 2 ^ 59
def prefixEnd_1106169 : Nat := 4983230072969 + 3 ^ 40 * 1106169 * 2
def baseEnd_1106169 : Nat := 567996382103387842400327

theorem tailTrace_1106169 : CollatzResearch.WordTrace tailWord_1106169 prefixEnd_1106169 567996382103387842400327 := by
  unfold tailWord_1106169
  simp only [CollatzResearch.WordTrace]
  refine ⟨40345297929546106469729561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26896865286364070979819707 40345297929546106469729561)
  ·
    refine ⟨30258973447159579852297171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40345297929546106469729561 30258973447159579852297171)
    ·
      refine ⟨45388460170739369778445757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30258973447159579852297171 45388460170739369778445757)
      ·
        refine ⟨17020672564027263666917159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45388460170739369778445757 17020672564027263666917159)
        ·
          refine ⟨25531008846040895500375739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17020672564027263666917159 25531008846040895500375739)
          ·
            refine ⟨38296513269061343250563609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25531008846040895500375739 38296513269061343250563609)
            ·
              refine ⟨28722384951796007437922707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38296513269061343250563609 28722384951796007437922707)
              ·
                refine ⟨43083577427694011156884061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28722384951796007437922707 43083577427694011156884061)
                ·
                  refine ⟨16156341535385254183831523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43083577427694011156884061 16156341535385254183831523)
                  ·
                    refine ⟨24234512303077881275747285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16156341535385254183831523 24234512303077881275747285)
                    ·
                      refine ⟨567996382103387842400327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24234512303077881275747285 567996382103387842400327)
                      ·
                        rfl

theorem cell23_1106169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 7].length) (baseStart_1106169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106169 prefixEnd_1106169 := by exact prefixLift 1106169
  have htrace : WordTrace (prefixWord ++ tailWord_1106169) baseStart_1106169 baseEnd_1106169 := by
    simpa [prefixWord, tailWord_1106169, baseEnd_1106169] using wordTrace_append hprefix tailTrace_1106169
  have hstable : (prefixWord ++ tailWord_1106169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106169).length < 2 ^ (prefixWord ++ tailWord_1106169).sum := by decide
  have hdescent : baseEnd_1106169 < baseStart_1106169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106257 : List Nat := [1, 2, 2, 1, 4, 2, 4, 2, 1, 4]
def baseStart_1106257 : Nat := 118140960795 + 1106257 * 2 ^ 59
def prefixEnd_1106257 : Nat := 4983230072969 + 3 ^ 40 * 1106257 * 2
def baseEnd_1106257 : Nat := 189347189466994499366641

theorem tailTrace_1106257 : CollatzResearch.WordTrace tailWord_1106257 prefixEnd_1106257 189347189466994499366641 := by
  unfold tailWord_1106257
  simp only [CollatzResearch.WordTrace]
  refine ⟨40348507553227297498933025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26899005035484864999288683 40348507553227297498933025)
  ·
    refine ⟨30261380664920473124199769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40348507553227297498933025 30261380664920473124199769)
    ·
      refine ⟨22696035498690354843149827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30261380664920473124199769 22696035498690354843149827)
      ·
        refine ⟨34044053248035532264724741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22696035498690354843149827 34044053248035532264724741)
        ·
          refine ⟨6383259984006662299635889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34044053248035532264724741 6383259984006662299635889)
          ·
            refine ⟨4787444988004996724726917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6383259984006662299635889 4787444988004996724726917)
            ·
              refine ⟨897645935250936885886297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4787444988004996724726917 897645935250936885886297)
              ·
                refine ⟨673234451438202664414723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 897645935250936885886297 673234451438202664414723)
                ·
                  refine ⟨1009851677157303996622085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 673234451438202664414723 1009851677157303996622085)
                  ·
                    refine ⟨189347189466994499366641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1009851677157303996622085 189347189466994499366641)
                    ·
                      rfl

theorem cell23_1106257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 2, 1, 4].length) (baseStart_1106257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106257 prefixEnd_1106257 := by exact prefixLift 1106257
  have htrace : WordTrace (prefixWord ++ tailWord_1106257) baseStart_1106257 baseEnd_1106257 := by
    simpa [prefixWord, tailWord_1106257, baseEnd_1106257] using wordTrace_append hprefix tailTrace_1106257
  have hstable : (prefixWord ++ tailWord_1106257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106257).length < 2 ^ (prefixWord ++ tailWord_1106257).sum := by decide
  have hdescent : baseEnd_1106257 < baseStart_1106257 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106276 : List Nat := [2, 3, 1, 1, 3, 1, 1, 1, 2, 1, 7]
def baseStart_1106276 : Nat := 118140960795 + 1106276 * 2 ^ 59
def prefixEnd_1106276 : Nat := 4983230072969 + 3 ^ 40 * 1106276 * 2
def baseEnd_1106276 : Nat := 568051324533418923762335

theorem tailTrace_1106276 : CollatzResearch.WordTrace tailWord_1106276 prefixEnd_1106276 568051324533418923762335 := by
  unfold tailWord_1106276
  simp only [CollatzResearch.WordTrace]
  refine ⟨20174600270079231871937341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26899467026772309162583121 20174600270079231871937341)
  ·
    refine ⟨7565475101279711951976503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20174600270079231871937341 7565475101279711951976503)
    ·
      refine ⟨11348212651919567927964755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565475101279711951976503 11348212651919567927964755)
      ·
        refine ⟨17022318977879351891947133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11348212651919567927964755 17022318977879351891947133)
        ·
          refine ⟨6383369616704756959480175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17022318977879351891947133 6383369616704756959480175)
          ·
            refine ⟨9575054425057135439220263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6383369616704756959480175 9575054425057135439220263)
            ·
              refine ⟨14362581637585703158830395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9575054425057135439220263 14362581637585703158830395)
              ·
                refine ⟨21543872456378554738245593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14362581637585703158830395 21543872456378554738245593)
                ·
                  refine ⟨16157904342283916053684195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21543872456378554738245593 16157904342283916053684195)
                  ·
                    refine ⟨24236856513425874080526293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16157904342283916053684195 24236856513425874080526293)
                    ·
                      refine ⟨568051324533418923762335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 24236856513425874080526293 568051324533418923762335)
                      ·
                        rfl

theorem cell23_1106276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_1106276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106276 prefixEnd_1106276 := by exact prefixLift 1106276
  have htrace : WordTrace (prefixWord ++ tailWord_1106276) baseStart_1106276 baseEnd_1106276 := by
    simpa [prefixWord, tailWord_1106276, baseEnd_1106276] using wordTrace_append hprefix tailTrace_1106276
  have hstable : (prefixWord ++ tailWord_1106276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106276).length < 2 ^ (prefixWord ++ tailWord_1106276).sum := by decide
  have hdescent : baseEnd_1106276 < baseStart_1106276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106280 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 5, 1, 3]
def baseStart_1106280 : Nat := 118140960795 + 1106280 * 2 ^ 59
def prefixEnd_1106280 : Nat := 4983230072969 + 3 ^ 40 * 1106280 * 2
def baseEnd_1106280 : Nat := 568053378456036908112317

theorem tailTrace_1106280 : CollatzResearch.WordTrace tailWord_1106280 prefixEnd_1106280 568053378456036908112317 := by
  unfold tailWord_1106280
  simp only [CollatzResearch.WordTrace]
  refine ⟨20174673216071986213510147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26899564288095981618013529 20174673216071986213510147)
  ·
    refine ⟨30262009824107979320265221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20174673216071986213510147 30262009824107979320265221)
    ·
      refine ⟨5674126842020246122549729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30262009824107979320265221 5674126842020246122549729)
      ·
        refine ⟨4255595131515184591912297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5674126842020246122549729 4255595131515184591912297)
        ·
          refine ⟨3191696348636388443934223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4255595131515184591912297 3191696348636388443934223)
          ·
            refine ⟨4787544522954582665901335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3191696348636388443934223 4787544522954582665901335)
            ·
              refine ⟨7181316784431873998852003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4787544522954582665901335 7181316784431873998852003)
              ·
                refine ⟨10771975176647810998278005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7181316784431873998852003 10771975176647810998278005)
                ·
                  refine ⟨1009872672810732281088563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10771975176647810998278005 1009872672810732281088563)
                  ·
                    refine ⟨1514809009216098421632845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009872672810732281088563 1514809009216098421632845)
                    ·
                      refine ⟨568053378456036908112317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514809009216098421632845 568053378456036908112317)
                      ·
                        rfl

theorem cell23_1106280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 5, 1, 3].length) (baseStart_1106280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106280 prefixEnd_1106280 := by exact prefixLift 1106280
  have htrace : WordTrace (prefixWord ++ tailWord_1106280) baseStart_1106280 baseEnd_1106280 := by
    simpa [prefixWord, tailWord_1106280, baseEnd_1106280] using wordTrace_append hprefix tailTrace_1106280
  have hstable : (prefixWord ++ tailWord_1106280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106280).length < 2 ^ (prefixWord ++ tailWord_1106280).sum := by decide
  have hdescent : baseEnd_1106280 < baseStart_1106280 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106290 : List Nat := [3, 2, 1, 2, 1, 4, 1, 1, 1, 5, 2]
def baseStart_1106290 : Nat := 118140960795 + 1106290 * 2 ^ 59
def prefixEnd_1106290 : Nat := 4983230072969 + 3 ^ 40 * 1106290 * 2
def baseEnd_1106290 : Nat := 568058513262581868987271

theorem tailTrace_1106290 : CollatzResearch.WordTrace tailWord_1106290 prefixEnd_1106290 568058513262581868987271 := by
  unfold tailWord_1106290
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087427790526936033721081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26899807441405162756589549 10087427790526936033721081)
  ·
    refine ⟨7565570842895202025290811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10087427790526936033721081 7565570842895202025290811)
    ·
      refine ⟨11348356264342803037936217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565570842895202025290811 11348356264342803037936217)
      ·
        refine ⟨8511267198257102278452163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11348356264342803037936217 8511267198257102278452163)
        ·
          refine ⟨12766900797385653417678245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511267198257102278452163 12766900797385653417678245)
          ·
            refine ⟨2393793899509810015814671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12766900797385653417678245 2393793899509810015814671)
            ·
              refine ⟨3590690849264715023722007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393793899509810015814671 3590690849264715023722007)
              ·
                refine ⟨5386036273897072535583011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3590690849264715023722007 5386036273897072535583011)
                ·
                  refine ⟨8079054410845608803374517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5386036273897072535583011 8079054410845608803374517)
                  ·
                    refine ⟨757411351016775825316361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8079054410845608803374517 757411351016775825316361)
                    ·
                      refine ⟨568058513262581868987271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757411351016775825316361 568058513262581868987271)
                      ·
                        rfl

theorem cell23_1106290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 1, 1, 5, 2].length) (baseStart_1106290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106290 prefixEnd_1106290 := by exact prefixLift 1106290
  have htrace : WordTrace (prefixWord ++ tailWord_1106290) baseStart_1106290 baseEnd_1106290 := by
    simpa [prefixWord, tailWord_1106290, baseEnd_1106290] using wordTrace_append hprefix tailTrace_1106290
  have hstable : (prefixWord ++ tailWord_1106290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106290).length < 2 ^ (prefixWord ++ tailWord_1106290).sum := by decide
  have hdescent : baseEnd_1106290 < baseStart_1106290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106303 : List Nat := [1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 4]
def baseStart_1106303 : Nat := 118140960795 + 1106303 * 2 ^ 59
def prefixEnd_1106303 : Nat := 4983230072969 + 3 ^ 40 * 1106303 * 2
def baseEnd_1106303 : Nat := 568065188511090318124711

theorem tailTrace_1106303 : CollatzResearch.WordTrace tailWord_1106303 prefixEnd_1106303 568065188511090318124711 := by
  unfold tailWord_1106303
  simp only [CollatzResearch.WordTrace]
  refine ⟨40350185311060647355107563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26900123540707098236738375 40350185311060647355107563)
  ·
    refine ⟨60525277966590971032661345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40350185311060647355107563 60525277966590971032661345)
    ·
      refine ⟨45393958474943228274496009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60525277966590971032661345 45393958474943228274496009)
      ·
        refine ⟨34045468856207421205872007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45393958474943228274496009 34045468856207421205872007)
        ·
          refine ⟨51068203284311131808808011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34045468856207421205872007 51068203284311131808808011)
          ·
            refine ⟨76602304926466697713212017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 51068203284311131808808011 76602304926466697713212017)
            ·
              refine ⟨57451728694850023284909013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76602304926466697713212017 57451728694850023284909013)
              ·
                refine ⟨1346524891285547420740055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 57451728694850023284909013 1346524891285547420740055)
                ·
                  refine ⟨2019787336928321131110083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346524891285547420740055 2019787336928321131110083)
                  ·
                    refine ⟨3029681005392481696665125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2019787336928321131110083 3029681005392481696665125)
                    ·
                      refine ⟨568065188511090318124711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3029681005392481696665125 568065188511090318124711)
                      ·
                        rfl

theorem cell23_1106303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 7, 1, 1, 4].length) (baseStart_1106303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106303 prefixEnd_1106303 := by exact prefixLift 1106303
  have htrace : WordTrace (prefixWord ++ tailWord_1106303) baseStart_1106303 baseEnd_1106303 := by
    simpa [prefixWord, tailWord_1106303, baseEnd_1106303] using wordTrace_append hprefix tailTrace_1106303
  have hstable : (prefixWord ++ tailWord_1106303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106303).length < 2 ^ (prefixWord ++ tailWord_1106303).sum := by decide
  have hdescent : baseEnd_1106303 < baseStart_1106303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106314 : List Nat := [3, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3]
def baseStart_1106314 : Nat := 118140960795 + 1106314 * 2 ^ 59
def prefixEnd_1106314 : Nat := 4983230072969 + 3 ^ 40 * 1106314 * 2
def baseEnd_1106314 : Nat := 568070836798289775087161

theorem tailTrace_1106314 : CollatzResearch.WordTrace tailWord_1106314 prefixEnd_1106314 568070836798289775087161 := by
  unfold tailWord_1106314
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087646628505199058439499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26900391009347197489171997 10087646628505199058439499)
  ·
    refine ⟨15131469942757798587659249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10087646628505199058439499 15131469942757798587659249)
    ·
      refine ⟨11348602457068348940744437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15131469942757798587659249 11348602457068348940744437)
      ·
        refine ⟨1063931480350157713194791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 11348602457068348940744437 1063931480350157713194791)
        ·
          refine ⟨1595897220525236569792187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1063931480350157713194791 1595897220525236569792187)
          ·
            refine ⟨2393845830787854854688281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1595897220525236569792187 2393845830787854854688281)
            ·
              refine ⟨1795384373090891141016211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2393845830787854854688281 1795384373090891141016211)
              ·
                refine ⟨2693076559636336711524317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795384373090891141016211 2693076559636336711524317)
                ·
                  refine ⟨1009903709863626266821619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2693076559636336711524317 1009903709863626266821619)
                  ·
                    refine ⟨1514855564795439400232429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1009903709863626266821619 1514855564795439400232429)
                    ·
                      refine ⟨568070836798289775087161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514855564795439400232429 568070836798289775087161)
                      ·
                        rfl

theorem cell23_1106314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 1, 3, 1, 3].length) (baseStart_1106314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106314 prefixEnd_1106314 := by exact prefixLift 1106314
  have htrace : WordTrace (prefixWord ++ tailWord_1106314) baseStart_1106314 baseEnd_1106314 := by
    simpa [prefixWord, tailWord_1106314, baseEnd_1106314] using wordTrace_append hprefix tailTrace_1106314
  have hstable : (prefixWord ++ tailWord_1106314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106314).length < 2 ^ (prefixWord ++ tailWord_1106314).sum := by decide
  have hdescent : baseEnd_1106314 < baseStart_1106314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106330 : List Nat := [3, 1, 1, 4, 1, 4, 1, 1, 1, 6]
def baseStart_1106330 : Nat := 118140960795 + 1106330 * 2 ^ 59
def prefixEnd_1106330 : Nat := 4983230072969 + 3 ^ 40 * 1106330 * 2
def baseEnd_1106330 : Nat := 189359684162920570829029

theorem tailTrace_1106330 : CollatzResearch.WordTrace tailWord_1106330 prefixEnd_1106330 189359684162920570829029 := by
  unfold tailWord_1106330
  simp only [CollatzResearch.WordTrace]
  refine ⟨10087792520490707741585111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26900780054641887310893629 10087792520490707741585111)
  ·
    refine ⟨15131688780736061612377667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10087792520490707741585111 15131688780736061612377667)
    ·
      refine ⟨22697533171104092418566501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15131688780736061612377667 22697533171104092418566501)
      ·
        refine ⟨4255787469582017328481219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22697533171104092418566501 4255787469582017328481219)
        ·
          refine ⟨6383681204373025992721829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4255787469582017328481219 6383681204373025992721829)
          ·
            refine ⟨1196940225819942373635343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6383681204373025992721829 1196940225819942373635343)
            ·
              refine ⟨1795410338729913560453015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1196940225819942373635343 1795410338729913560453015)
              ·
                refine ⟨2693115508094870340679523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795410338729913560453015 2693115508094870340679523)
                ·
                  refine ⟨4039673262142305511019285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2693115508094870340679523 4039673262142305511019285)
                  ·
                    refine ⟨189359684162920570829029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4039673262142305511019285 189359684162920570829029)
                    ·
                      rfl

theorem cell23_1106330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 1, 1, 1, 6].length) (baseStart_1106330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106330 prefixEnd_1106330 := by exact prefixLift 1106330
  have htrace : WordTrace (prefixWord ++ tailWord_1106330) baseStart_1106330 baseEnd_1106330 := by
    simpa [prefixWord, tailWord_1106330, baseEnd_1106330] using wordTrace_append hprefix tailTrace_1106330
  have hstable : (prefixWord ++ tailWord_1106330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106330).length < 2 ^ (prefixWord ++ tailWord_1106330).sum := by decide
  have hdescent : baseEnd_1106330 < baseStart_1106330 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106340 : List Nat := [2, 3, 1, 2, 1, 1, 3, 4, 1, 2, 3]
def baseStart_1106340 : Nat := 118140960795 + 1106340 * 2 ^ 59
def prefixEnd_1106340 : Nat := 4983230072969 + 3 ^ 40 * 1106340 * 2
def baseEnd_1106340 : Nat := 568084187295306673362041

theorem tailTrace_1106340 : CollatzResearch.WordTrace tailWord_1106340 prefixEnd_1106340 568084187295306673362041 := by
  unfold tailWord_1106340
  simp only [CollatzResearch.WordTrace]
  refine ⟨20175767405963301337102237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26901023207951068449469649 20175767405963301337102237)
  ·
    refine ⟨7565912777236238001413339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20175767405963301337102237 7565912777236238001413339)
    ·
      refine ⟨11348869165854357002120009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7565912777236238001413339 11348869165854357002120009)
      ·
        refine ⟨8511651874390767751590007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11348869165854357002120009 8511651874390767751590007)
        ·
          refine ⟨12767477811586151627385011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8511651874390767751590007 12767477811586151627385011)
          ·
            refine ⟨19151216717379227441077517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12767477811586151627385011 19151216717379227441077517)
            ·
              refine ⟨7181706269017210290404069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19151216717379227441077517 7181706269017210290404069)
              ·
                refine ⟨1346569925440726929450763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7181706269017210290404069 1346569925440726929450763)
                ·
                  refine ⟨2019854888161090394176145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1346569925440726929450763 2019854888161090394176145)
                  ·
                    refine ⟨1514891166120817795632109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2019854888161090394176145 1514891166120817795632109)
                    ·
                      refine ⟨568084187295306673362041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1514891166120817795632109 568084187295306673362041)
                      ·
                        rfl

theorem cell23_1106340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 4, 1, 2, 3].length) (baseStart_1106340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106340 prefixEnd_1106340 := by exact prefixLift 1106340
  have htrace : WordTrace (prefixWord ++ tailWord_1106340) baseStart_1106340 baseEnd_1106340 := by
    simpa [prefixWord, tailWord_1106340, baseEnd_1106340] using wordTrace_append hprefix tailTrace_1106340
  have hstable : (prefixWord ++ tailWord_1106340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106340).length < 2 ^ (prefixWord ++ tailWord_1106340).sum := by decide
  have hdescent : baseEnd_1106340 < baseStart_1106340 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106343 : List Nat := [1, 1, 6, 1, 1, 3, 1, 9]
def baseStart_1106343 : Nat := 118140960795 + 1106343 * 2 ^ 59
def prefixEnd_1106343 : Nat := 4983230072969 + 3 ^ 40 * 1106343 * 2
def baseEnd_1106343 : Nat := 21040212138417413393501

theorem tailTrace_1106343 : CollatzResearch.WordTrace tailWord_1106343 prefixEnd_1106343 21040212138417413393501 := by
  unfold tailWord_1106343
  simp only [CollatzResearch.WordTrace]
  refine ⟨40351644230915734186563683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26901096153943822791042455 40351644230915734186563683)
  ·
    refine ⟨60527466346373601279845525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40351644230915734186563683 60527466346373601279845525)
    ·
      refine ⟨2837224984986262559992759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 60527466346373601279845525 2837224984986262559992759)
      ·
        refine ⟨4255837477479393839989139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837224984986262559992759 4255837477479393839989139)
        ·
          refine ⟨6383756216219090759983709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4255837477479393839989139 6383756216219090759983709)
          ·
            refine ⟨2393908581082159034993891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6383756216219090759983709 2393908581082159034993891)
            ·
              refine ⟨3590862871623238552490837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2393908581082159034993891 3590862871623238552490837)
              ·
                refine ⟨21040212138417413393501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 3590862871623238552490837 21040212138417413393501)
                ·
                  rfl

theorem cell23_1106343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 3, 1, 9].length) (baseStart_1106343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106343 prefixEnd_1106343 := by exact prefixLift 1106343
  have htrace : WordTrace (prefixWord ++ tailWord_1106343) baseStart_1106343 baseEnd_1106343 := by
    simpa [prefixWord, tailWord_1106343, baseEnd_1106343] using wordTrace_append hprefix tailTrace_1106343
  have hstable : (prefixWord ++ tailWord_1106343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106343).length < 2 ^ (prefixWord ++ tailWord_1106343).sum := by decide
  have hdescent : baseEnd_1106343 < baseStart_1106343 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106397 : List Nat := [1, 4, 3, 1, 1, 1, 3, 1, 3, 3, 2]
def baseStart_1106397 : Nat := 118140960795 + 1106397 * 2 ^ 59
def prefixEnd_1106397 : Nat := 4983230072969 + 3 ^ 40 * 1106397 * 2
def baseEnd_1106397 : Nat := 568113455692612950349279

theorem tailTrace_1106397 : CollatzResearch.WordTrace tailWord_1106397 prefixEnd_1106397 568113455692612950349279 := by
  unfold tailWord_1106397
  simp only [CollatzResearch.WordTrace]
  refine ⟨40353613772720101409029445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26902409181813400939352963 40353613772720101409029445)
  ·
    refine ⟨7566302582385019014193021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40353613772720101409029445 7566302582385019014193021)
    ·
      refine ⟨2837363468394382130322383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7566302582385019014193021 2837363468394382130322383)
      ·
        refine ⟨4256045202591573195483575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837363468394382130322383 4256045202591573195483575)
        ·
          refine ⟨6384067803887359793225363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4256045202591573195483575 6384067803887359793225363)
          ·
            refine ⟨9576101705831039689838045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6384067803887359793225363 9576101705831039689838045)
            ·
              refine ⟨3591038139686639883689267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9576101705831039689838045 3591038139686639883689267)
              ·
                refine ⟨5386557209529959825533901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591038139686639883689267 5386557209529959825533901)
                ·
                  refine ⟨2019958953573734934575213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5386557209529959825533901 2019958953573734934575213)
                  ·
                    refine ⟨757484607590150600465705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2019958953573734934575213 757484607590150600465705)
                    ·
                      refine ⟨568113455692612950349279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757484607590150600465705 568113455692612950349279)
                      ·
                        rfl

theorem cell23_1106397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 1, 3, 3, 2].length) (baseStart_1106397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106397 prefixEnd_1106397 := by exact prefixLift 1106397
  have htrace : WordTrace (prefixWord ++ tailWord_1106397) baseStart_1106397 baseEnd_1106397 := by
    simpa [prefixWord, tailWord_1106397, baseEnd_1106397] using wordTrace_append hprefix tailTrace_1106397
  have hstable : (prefixWord ++ tailWord_1106397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106397).length < 2 ^ (prefixWord ++ tailWord_1106397).sum := by decide
  have hdescent : baseEnd_1106397 < baseStart_1106397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106421 : List Nat := [1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1106421 : Nat := 118140960795 + 1106421 * 2 ^ 59
def prefixEnd_1106421 : Nat := 4983230072969 + 3 ^ 40 * 1106421 * 2
def baseEnd_1106421 : Nat := 568125779228320856449169

theorem tailTrace_1106421 : CollatzResearch.WordTrace tailWord_1106421 prefixEnd_1106421 568125779228320856449169 := by
  unfold tailWord_1106421
  simp only [CollatzResearch.WordTrace]
  refine ⟨40354489124633153507903117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26902992749755435671935411 40354489124633153507903117)
  ·
    refine ⟨15132933421737432565463669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40354489124633153507903117 15132933421737432565463669)
    ·
      refine ⟨1418712508287884303012219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 15132933421737432565463669 1418712508287884303012219)
      ·
        refine ⟨2128068762431826454518329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418712508287884303012219 2128068762431826454518329)
        ·
          refine ⟨1596051571823869840888747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2128068762431826454518329 1596051571823869840888747)
          ·
            refine ⟨2394077357735804761333121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596051571823869840888747 2394077357735804761333121)
            ·
              refine ⟨1795558018301853570999841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394077357735804761333121 1795558018301853570999841)
              ·
                refine ⟨1346668513726390178249881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1795558018301853570999841 1346668513726390178249881)
                ·
                  refine ⟨1010001385294792633687411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1346668513726390178249881 1010001385294792633687411)
                  ·
                    refine ⟨1515002077942188950531117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1010001385294792633687411 1515002077942188950531117)
                    ·
                      refine ⟨568125779228320856449169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1515002077942188950531117 568125779228320856449169)
                      ·
                        rfl

theorem cell23_1106421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1106421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106421 prefixEnd_1106421 := by exact prefixLift 1106421
  have htrace : WordTrace (prefixWord ++ tailWord_1106421) baseStart_1106421 baseEnd_1106421 := by
    simpa [prefixWord, tailWord_1106421, baseEnd_1106421] using wordTrace_append hprefix tailTrace_1106421
  have hstable : (prefixWord ++ tailWord_1106421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106421).length < 2 ^ (prefixWord ++ tailWord_1106421).sum := by decide
  have hdescent : baseEnd_1106421 < baseStart_1106421 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106438 : List Nat := [6, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_1106438 : Nat := 118140960795 + 1106438 * 2 ^ 59
def prefixEnd_1106438 : Nat := 4983230072969 + 3 ^ 40 * 1106438 * 2
def baseEnd_1106438 : Nat := 568134508399447289936591

theorem tailTrace_1106438 : CollatzResearch.WordTrace tailWord_1106438 prefixEnd_1106438 568134508399447289936591 := by
  unfold tailWord_1106438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1261097161424111419102249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 26903406110381043607514645 1261097161424111419102249)
  ·
    refine ⟨945822871068083564326687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1261097161424111419102249 945822871068083564326687)
    ·
      refine ⟨1418734306602125346490031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 945822871068083564326687 1418734306602125346490031)
      ·
        refine ⟨2128101459903188019735047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1418734306602125346490031 2128101459903188019735047)
        ·
          refine ⟨3192152189854782029602571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2128101459903188019735047 3192152189854782029602571)
          ·
            refine ⟨4788228284782173044403857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192152189854782029602571 4788228284782173044403857)
            ·
              refine ⟨3591171213586629783302893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4788228284782173044403857 3591171213586629783302893)
              ·
                refine ⟨1346689205094986168738585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3591171213586629783302893 1346689205094986168738585)
                ·
                  refine ⟨1010016903821239626553939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1346689205094986168738585 1010016903821239626553939)
                  ·
                    refine ⟨1515025355731859439830909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1010016903821239626553939 1515025355731859439830909)
                    ·
                      refine ⟨568134508399447289936591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1515025355731859439830909 568134508399447289936591)
                      ·
                        rfl

theorem cell23_1106438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_1106438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106438 prefixEnd_1106438 := by exact prefixLift 1106438
  have htrace : WordTrace (prefixWord ++ tailWord_1106438) baseStart_1106438 baseEnd_1106438 := by
    simpa [prefixWord, tailWord_1106438, baseEnd_1106438] using wordTrace_append hprefix tailTrace_1106438
  have hstable : (prefixWord ++ tailWord_1106438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106438).length < 2 ^ (prefixWord ++ tailWord_1106438).sum := by decide
  have hdescent : baseEnd_1106438 < baseStart_1106438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106444 : List Nat := [2, 2, 1, 2, 4, 1, 2, 3, 2, 2, 2]
def baseStart_1106444 : Nat := 118140960795 + 1106444 * 2 ^ 59
def prefixEnd_1106444 : Nat := 4983230072969 + 3 ^ 40 * 1106444 * 2
def baseEnd_1106444 : Nat := 568137589283374266461563

theorem tailTrace_1106444 : CollatzResearch.WordTrace tailWord_1106444 prefixEnd_1106444 568137589283374266461563 := by
  unfold tailWord_1106444
  simp only [CollatzResearch.WordTrace]
  refine ⟨20177664001774914217995193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26903552002366552290660257 20177664001774914217995193)
  ·
    refine ⟨15133248001331185663496395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20177664001774914217995193 15133248001331185663496395)
    ·
      refine ⟨22699872001996778495244593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15133248001331185663496395 22699872001996778495244593)
      ·
        refine ⟨17024904001497583871433445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22699872001996778495244593 17024904001497583871433445)
        ·
          refine ⟨3192169500280796975893771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17024904001497583871433445 3192169500280796975893771)
          ·
            refine ⟨4788254250421195463840657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3192169500280796975893771 4788254250421195463840657)
            ·
              refine ⟨3591190687815896597880493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4788254250421195463840657 3591190687815896597880493)
              ·
                refine ⟨1346696507930961224205185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3591190687815896597880493 1346696507930961224205185)
                ·
                  refine ⟨1010022380948220918153889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1346696507930961224205185 1010022380948220918153889)
                  ·
                    refine ⟨757516785711165688615417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1010022380948220918153889 757516785711165688615417)
                    ·
                      refine ⟨568137589283374266461563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757516785711165688615417 568137589283374266461563)
                      ·
                        rfl

theorem cell23_1106444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_1106444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106444 prefixEnd_1106444 := by exact prefixLift 1106444
  have htrace : WordTrace (prefixWord ++ tailWord_1106444) baseStart_1106444 baseEnd_1106444 := by
    simpa [prefixWord, tailWord_1106444, baseEnd_1106444] using wordTrace_append hprefix tailTrace_1106444
  have hstable : (prefixWord ++ tailWord_1106444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106444).length < 2 ^ (prefixWord ++ tailWord_1106444).sum := by decide
  have hdescent : baseEnd_1106444 < baseStart_1106444 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106467 : List Nat := [1, 1, 1, 4, 4, 2, 2, 3, 5]
def baseStart_1106467 : Nat := 118140960795 + 1106467 * 2 ^ 59
def prefixEnd_1106467 : Nat := 4983230072969 + 3 ^ 40 * 1106467 * 2
def baseEnd_1106467 : Nat := 63127711037603075163773

theorem tailTrace_1106467 : CollatzResearch.WordTrace tailWord_1106467 prefixEnd_1106467 63127711037603075163773 := by
  unfold tailWord_1106467
  simp only [CollatzResearch.WordTrace]
  refine ⟨40356166882466503364077655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26904111254977668909385103 40356166882466503364077655)
  ·
    refine ⟨60534250323699755046116483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40356166882466503364077655 60534250323699755046116483)
    ·
      refine ⟨90801375485549632569174725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60534250323699755046116483 90801375485549632569174725)
      ·
        refine ⟨17025257903540556106720261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90801375485549632569174725 17025257903540556106720261)
        ·
          refine ⟨3192235856913854270010049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17025257903540556106720261 3192235856913854270010049)
          ·
            refine ⟨2394176892685390702507537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3192235856913854270010049 2394176892685390702507537)
            ·
              refine ⟨1795632669514043026880653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394176892685390702507537 1795632669514043026880653)
              ·
                refine ⟨673362251067766135080245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1795632669514043026880653 673362251067766135080245)
                ·
                  refine ⟨63127711037603075163773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 673362251067766135080245 63127711037603075163773)
                  ·
                    rfl

theorem cell23_1106467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 2, 3, 5].length) (baseStart_1106467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106467 prefixEnd_1106467 := by exact prefixLift 1106467
  have htrace : WordTrace (prefixWord ++ tailWord_1106467) baseStart_1106467 baseEnd_1106467 := by
    simpa [prefixWord, tailWord_1106467, baseEnd_1106467] using wordTrace_append hprefix tailTrace_1106467
  have hstable : (prefixWord ++ tailWord_1106467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106467).length < 2 ^ (prefixWord ++ tailWord_1106467).sum := by decide
  have hdescent : baseEnd_1106467 < baseStart_1106467 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106478 : List Nat := [4, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_1106478 : Nat := 118140960795 + 1106478 * 2 ^ 59
def prefixEnd_1106478 : Nat := 4983230072969 + 3 ^ 40 * 1106478 * 2
def baseEnd_1106478 : Nat := 568155047625627133436407

theorem tailTrace_1106478 : CollatzResearch.WordTrace tailWord_1106478 prefixEnd_1106478 568155047625627133436407 := by
  unfold tailWord_1106478
  simp only [CollatzResearch.WordTrace]
  refine ⟨5044571010678331530341011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 26904378723617768161818725 5044571010678331530341011)
  ·
    refine ⟨7566856516017497295511517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5044571010678331530341011 7566856516017497295511517)
    ·
      refine ⟨2837571193506561485816819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7566856516017497295511517 2837571193506561485816819)
      ·
        refine ⟨4256356790259842228725229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2837571193506561485816819 4256356790259842228725229)
        ·
          refine ⟨1596133796347440835771961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4256356790259842228725229 1596133796347440835771961)
          ·
            refine ⟨1197100347260580626828971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1596133796347440835771961 1197100347260580626828971)
            ·
              refine ⟨1795650520890870940243457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197100347260580626828971 1795650520890870940243457)
              ·
                refine ⟨1346737890668153205182593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1795650520890870940243457 1346737890668153205182593)
                ·
                  refine ⟨1010053418001114903886945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1346737890668153205182593 1010053418001114903886945)
                  ·
                    refine ⟨757540063500836177915209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1010053418001114903886945 757540063500836177915209)
                    ·
                      refine ⟨568155047625627133436407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757540063500836177915209 568155047625627133436407)
                      ·
                        rfl

theorem cell23_1106478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_1106478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106478 prefixEnd_1106478 := by exact prefixLift 1106478
  have htrace : WordTrace (prefixWord ++ tailWord_1106478) baseStart_1106478 baseEnd_1106478 := by
    simpa [prefixWord, tailWord_1106478, baseEnd_1106478] using wordTrace_append hprefix tailTrace_1106478
  have hstable : (prefixWord ++ tailWord_1106478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106478).length < 2 ^ (prefixWord ++ tailWord_1106478).sum := by decide
  have hdescent : baseEnd_1106478 < baseStart_1106478 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106484 : List Nat := [2, 5, 1, 3, 1, 1, 2, 1, 7]
def baseStart_1106484 : Nat := 118140960795 + 1106484 * 2 ^ 59
def prefixEnd_1106484 : Nat := 4983230072969 + 3 ^ 40 * 1106484 * 2
def baseEnd_1106484 : Nat := 63128680945506012217931

theorem tailTrace_1106484 : CollatzResearch.WordTrace tailWord_1106484 prefixEnd_1106484 63128680945506012217931 := by
  unfold tailWord_1106484
  simp only [CollatzResearch.WordTrace]
  refine ⟨20178393461702457633723253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26904524615603276844964337 20178393461702457633723253)
  ·
    refine ⟨1891724387034605403161555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20178393461702457633723253 1891724387034605403161555)
    ·
      refine ⟨2837586580551908104742333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1891724387034605403161555 2837586580551908104742333)
      ·
        refine ⟨1064094967706965539278375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2837586580551908104742333 1064094967706965539278375)
        ·
          refine ⟨1596142451560448308917563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1064094967706965539278375 1596142451560448308917563)
          ·
            refine ⟨2394213677340672463376345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596142451560448308917563 2394213677340672463376345)
            ·
              refine ⟨1795660258005504347532259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2394213677340672463376345 1795660258005504347532259)
              ·
                refine ⟨2693490387008256521298389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795660258005504347532259 2693490387008256521298389)
                ·
                  refine ⟨63128680945506012217931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2693490387008256521298389 63128680945506012217931)
                  ·
                    rfl

theorem cell23_1106484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_1106484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106484 prefixEnd_1106484 := by exact prefixLift 1106484
  have htrace : WordTrace (prefixWord ++ tailWord_1106484) baseStart_1106484 baseEnd_1106484 := by
    simpa [prefixWord, tailWord_1106484, baseEnd_1106484] using wordTrace_append hprefix tailTrace_1106484
  have hstable : (prefixWord ++ tailWord_1106484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106484).length < 2 ^ (prefixWord ++ tailWord_1106484).sum := by decide
  have hdescent : baseEnd_1106484 < baseStart_1106484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106520 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 1, 4, 3]
def baseStart_1106520 : Nat := 118140960795 + 1106520 * 2 ^ 59
def prefixEnd_1106520 : Nat := 4983230072969 + 3 ^ 40 * 1106520 * 2
def baseEnd_1106520 : Nat := 568176613813115969111213

theorem tailTrace_1106520 : CollatzResearch.WordTrace tailWord_1106520 prefixEnd_1106520 568176613813115969111213 := by
  unfold tailWord_1106520
  simp only [CollatzResearch.WordTrace]
  refine ⟨20179049975637246707878507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26905399967516328943838009 20179049975637246707878507)
  ·
    refine ⟨30268574963455870061817761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20179049975637246707878507 30268574963455870061817761)
    ·
      refine ⟨22701431222591902546363321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30268574963455870061817761 22701431222591902546363321)
      ·
        refine ⟨17026073416943926909772491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22701431222591902546363321 17026073416943926909772491)
        ·
          refine ⟨25539110125415890364658737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17026073416943926909772491 25539110125415890364658737)
          ·
            refine ⟨19154332594061917773494053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25539110125415890364658737 19154332594061917773494053)
            ·
              refine ⟨3591437361386609582530135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19154332594061917773494053 3591437361386609582530135)
              ·
                refine ⟨5387156042079914373795203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3591437361386609582530135 5387156042079914373795203)
                ·
                  refine ⟨8080734063119871560692805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5387156042079914373795203 8080734063119871560692805)
                  ·
                    refine ⟨1515137636834975917629901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8080734063119871560692805 1515137636834975917629901)
                    ·
                      refine ⟨568176613813115969111213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1515137636834975917629901 568176613813115969111213)
                      ·
                        rfl

theorem cell23_1106520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_1106520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106520 prefixEnd_1106520 := by exact prefixLift 1106520
  have htrace : WordTrace (prefixWord ++ tailWord_1106520) baseStart_1106520 baseEnd_1106520 := by
    simpa [prefixWord, tailWord_1106520, baseEnd_1106520] using wordTrace_append hprefix tailTrace_1106520
  have hstable : (prefixWord ++ tailWord_1106520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106520).length < 2 ^ (prefixWord ++ tailWord_1106520).sum := by decide
  have hdescent : baseEnd_1106520 < baseStart_1106520 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106543 : List Nat := [1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 8]
def baseStart_1106543 : Nat := 118140960795 + 1106543 * 2 ^ 59
def prefixEnd_1106543 : Nat := 4983230072969 + 3 ^ 40 * 1106543 * 2
def baseEnd_1106543 : Nat := 568188423868169379123607

theorem tailTrace_1106543 : CollatzResearch.WordTrace tailWord_1106543 prefixEnd_1106543 568188423868169379123607 := by
  unfold tailWord_1106543
  simp only [CollatzResearch.WordTrace]
  refine ⟨40358938830191168343844283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26905959220127445562562855 40358938830191168343844283)
  ·
    refine ⟨60538408245286752515766425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40358938830191168343844283 60538408245286752515766425)
    ·
      refine ⟨45403806183965064386824819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60538408245286752515766425 45403806183965064386824819)
      ·
        refine ⟨68105709275947596580237229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45403806183965064386824819 68105709275947596580237229)
        ·
          refine ⟨25539640978480348717588961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 68105709275947596580237229 25539640978480348717588961)
          ·
            refine ⟨19154730733860261538191721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25539640978480348717588961 19154730733860261538191721)
            ·
              refine ⟨14366048050395196153643791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19154730733860261538191721 14366048050395196153643791)
              ·
                refine ⟨21549072075592794230465687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14366048050395196153643791 21549072075592794230465687)
                ·
                  refine ⟨32323608113389191345698531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21549072075592794230465687 32323608113389191345698531)
                  ·
                    refine ⟨48485412170083787018547797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32323608113389191345698531 48485412170083787018547797)
                    ·
                      refine ⟨568188423868169379123607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 48485412170083787018547797 568188423868169379123607)
                      ·
                        rfl

theorem cell23_1106543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 1, 1, 1, 8].length) (baseStart_1106543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106543 prefixEnd_1106543 := by exact prefixLift 1106543
  have htrace : WordTrace (prefixWord ++ tailWord_1106543) baseStart_1106543 baseEnd_1106543 := by
    simpa [prefixWord, tailWord_1106543, baseEnd_1106543] using wordTrace_append hprefix tailTrace_1106543
  have hstable : (prefixWord ++ tailWord_1106543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106543).length < 2 ^ (prefixWord ++ tailWord_1106543).sum := by decide
  have hdescent : baseEnd_1106543 < baseStart_1106543 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106544 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 3, 4]
def baseStart_1106544 : Nat := 118140960795 + 1106544 * 2 ^ 59
def prefixEnd_1106544 : Nat := 4983230072969 + 3 ^ 40 * 1106544 * 2
def baseEnd_1106544 : Nat := 189396312449607958403701

theorem tailTrace_1106544 : CollatzResearch.WordTrace tailWord_1106544 prefixEnd_1106544 189396312449607958403701 := by
  unfold tailWord_1106544
  simp only [CollatzResearch.WordTrace]
  refine ⟨20179487651593772757315343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26905983535458363676420457 20179487651593772757315343)
  ·
    refine ⟨30269231477390659135973015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20179487651593772757315343 30269231477390659135973015)
    ·
      refine ⟨45403847216085988703959523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30269231477390659135973015 45403847216085988703959523)
      ·
        refine ⟨68105770824128983055939285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45403847216085988703959523 68105770824128983055939285)
        ·
          refine ⟨1596229003690523040373577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 68105770824128983055939285 1596229003690523040373577)
          ·
            refine ⟨1197171752767892280280183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1596229003690523040373577 1197171752767892280280183)
            ·
              refine ⟨1795757629151838420420275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1197171752767892280280183 1795757629151838420420275)
              ·
                refine ⟨2693636443727757630630413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1795757629151838420420275 2693636443727757630630413)
                ·
                  refine ⟨1010113666397909111486405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2693636443727757630630413 1010113666397909111486405)
                  ·
                    refine ⟨189396312449607958403701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1010113666397909111486405 189396312449607958403701)
                    ·
                      rfl

theorem cell23_1106544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 3, 4].length) (baseStart_1106544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106544 prefixEnd_1106544 := by exact prefixLift 1106544
  have htrace : WordTrace (prefixWord ++ tailWord_1106544) baseStart_1106544 baseEnd_1106544 := by
    simpa [prefixWord, tailWord_1106544, baseEnd_1106544] using wordTrace_append hprefix tailTrace_1106544
  have hstable : (prefixWord ++ tailWord_1106544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106544).length < 2 ^ (prefixWord ++ tailWord_1106544).sum := by decide
  have hdescent : baseEnd_1106544 < baseStart_1106544 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106557 : List Nat := [1, 4, 1, 1, 5, 1, 1, 3, 6]
def baseStart_1106557 : Nat := 118140960795 + 1106557 * 2 ^ 59
def prefixEnd_1106557 : Nat := 4983230072969 + 3 ^ 40 * 1106557 * 2
def baseEnd_1106557 : Nat := 63132845844148036038727

theorem tailTrace_1106557 : CollatzResearch.WordTrace tailWord_1106557 prefixEnd_1106557 63132845844148036038727 := by
  unfold tailWord_1106557
  simp only [CollatzResearch.WordTrace]
  refine ⟨40359449452140448734853925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26906299634760299156569283 40359449452140448734853925)
  ·
    refine ⟨7567396772276334137785111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40359449452140448734853925 7567396772276334137785111)
    ·
      refine ⟨11351095158414501206677667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7567396772276334137785111 11351095158414501206677667)
      ·
        refine ⟨17026642737621751810016501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11351095158414501206677667 17026642737621751810016501)
        ·
          refine ⟨1596247756652039232189047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17026642737621751810016501 1596247756652039232189047)
          ·
            refine ⟨2394371634978058848283571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1596247756652039232189047 2394371634978058848283571)
            ·
              refine ⟨3591557452467088272425357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2394371634978058848283571 3591557452467088272425357)
              ·
                refine ⟨1346834044675158102159509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3591557452467088272425357 1346834044675158102159509)
                ·
                  refine ⟨63132845844148036038727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1346834044675158102159509 63132845844148036038727)
                  ·
                    rfl

theorem cell23_1106557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 3, 6].length) (baseStart_1106557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106557 prefixEnd_1106557 := by exact prefixLift 1106557
  have htrace : WordTrace (prefixWord ++ tailWord_1106557) baseStart_1106557 baseEnd_1106557 := by
    simpa [prefixWord, tailWord_1106557, baseEnd_1106557] using wordTrace_append hprefix tailTrace_1106557
  have hstable : (prefixWord ++ tailWord_1106557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106557).length < 2 ^ (prefixWord ++ tailWord_1106557).sum := by decide
  have hdescent : baseEnd_1106557 < baseStart_1106557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106567 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 3]
def baseStart_1106567 : Nat := 118140960795 + 1106567 * 2 ^ 59
def prefixEnd_1106567 : Nat := 4983230072969 + 3 ^ 40 * 1106567 * 2
def baseEnd_1106567 : Nat := 568200747403877285223497

theorem tailTrace_1106567 : CollatzResearch.WordTrace tailWord_1106567 prefixEnd_1106567 568200747403877285223497 := by
  unfold tailWord_1106567
  simp only [CollatzResearch.WordTrace]
  refine ⟨40359814182104220442717955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 26906542788069480295145303 40359814182104220442717955)
  ·
    refine ⟨60539721273156330664076933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40359814182104220442717955 60539721273156330664076933)
    ·
      refine ⟨11351197738716811999514425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60539721273156330664076933 11351197738716811999514425)
      ·
        refine ⟨8513398304037608999635819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11351197738716811999514425 8513398304037608999635819)
        ·
          refine ⟨12770097456056413499453729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8513398304037608999635819 12770097456056413499453729)
          ·
            refine ⟨9577573092042310124590297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12770097456056413499453729 9577573092042310124590297)
            ·
              refine ⟨7183179819031732593442723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9577573092042310124590297 7183179819031732593442723)
              ·
                refine ⟨10774769728547598890164085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7183179819031732593442723 10774769728547598890164085)
                ·
                  refine ⟨1010134662051337395952883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10774769728547598890164085 1010134662051337395952883)
                  ·
                    refine ⟨1515201993077006093929325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1010134662051337395952883 1515201993077006093929325)
                    ·
                      refine ⟨568200747403877285223497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1515201993077006093929325 568200747403877285223497)
                      ·
                        rfl

theorem cell23_1106567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 5, 1, 3].length) (baseStart_1106567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106567 prefixEnd_1106567 := by exact prefixLift 1106567
  have htrace : WordTrace (prefixWord ++ tailWord_1106567) baseStart_1106567 baseEnd_1106567 := by
    simpa [prefixWord, tailWord_1106567, baseEnd_1106567] using wordTrace_append hprefix tailTrace_1106567
  have hstable : (prefixWord ++ tailWord_1106567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106567).length < 2 ^ (prefixWord ++ tailWord_1106567).sum := by decide
  have hdescent : baseEnd_1106567 < baseStart_1106567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106610 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5]
def baseStart_1106610 : Nat := 118140960795 + 1106610 * 2 ^ 59
def prefixEnd_1106610 : Nat := 4983230072969 + 3 ^ 40 * 1106610 * 2
def baseEnd_1106610 : Nat := 568222827072020616985799

theorem tailTrace_1106610 : CollatzResearch.WordTrace tailWord_1106610 prefixEnd_1106610 568222827072020616985799 := by
  unfold tailWord_1106610
  simp only [CollatzResearch.WordTrace]
  refine ⟨10090345630237109696633321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 26907588347298959191022189 10090345630237109696633321)
  ·
    refine ⟨7567759222677832272474991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10090345630237109696633321 7567759222677832272474991)
    ·
      refine ⟨11351638834016748408712487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7567759222677832272474991 11351638834016748408712487)
      ·
        refine ⟨17027458251025122613068731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11351638834016748408712487 17027458251025122613068731)
        ·
          refine ⟨25541187376537683919603097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17027458251025122613068731 25541187376537683919603097)
          ·
            refine ⟨19155890532403262939702323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25541187376537683919603097 19155890532403262939702323)
            ·
              refine ⟨28733835798604894409553485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19155890532403262939702323 28733835798604894409553485)
              ·
                refine ⟨10775188424476835403582557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28733835798604894409553485 10775188424476835403582557)
                ·
                  refine ⟨4040695659178813276343459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10775188424476835403582557 4040695659178813276343459)
                  ·
                    refine ⟨6061043488768219914515189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4040695659178813276343459 6061043488768219914515189)
                    ·
                      refine ⟨568222827072020616985799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6061043488768219914515189 568222827072020616985799)
                      ·
                        rfl

theorem cell23_1106610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 3, 1, 5].length) (baseStart_1106610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106610 prefixEnd_1106610 := by exact prefixLift 1106610
  have htrace : WordTrace (prefixWord ++ tailWord_1106610) baseStart_1106610 baseEnd_1106610 := by
    simpa [prefixWord, tailWord_1106610, baseEnd_1106610] using wordTrace_append hprefix tailTrace_1106610
  have hstable : (prefixWord ++ tailWord_1106610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106610).length < 2 ^ (prefixWord ++ tailWord_1106610).sum := by decide
  have hdescent : baseEnd_1106610 < baseStart_1106610 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106624 : List Nat := [2, 1, 1, 2, 4, 2, 1, 1, 5, 2, 2]
def baseStart_1106624 : Nat := 118140960795 + 1106624 * 2 ^ 59
def prefixEnd_1106624 : Nat := 4983230072969 + 3 ^ 40 * 1106624 * 2
def baseEnd_1106624 : Nat := 568230015801183562210735

theorem tailTrace_1106624 : CollatzResearch.WordTrace tailWord_1106624 prefixEnd_1106624 568230015801183562210735 := by
  unfold tailWord_1106624
  simp only [CollatzResearch.WordTrace]
  refine ⟨20180946571448859588771463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26907928761931812785028617 20180946571448859588771463)
  ·
    refine ⟨30271419857173289383157195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20180946571448859588771463 30271419857173289383157195)
    ·
      refine ⟨45407129785759934074735793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30271419857173289383157195 45407129785759934074735793)
      ·
        refine ⟨34055347339319950556051845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45407129785759934074735793 34055347339319950556051845)
        ·
          refine ⟨6385377626122490729259721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34055347339319950556051845 6385377626122490729259721)
          ·
            refine ⟨4789033219591868046944791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6385377626122490729259721 4789033219591868046944791)
            ·
              refine ⟨7183549829387802070417187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4789033219591868046944791 7183549829387802070417187)
              ·
                refine ⟨10775324744081703105625781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7183549829387802070417187 10775324744081703105625781)
                ·
                  refine ⟨1010186694757659666152417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10775324744081703105625781 1010186694757659666152417)
                  ·
                    refine ⟨757640021068244749614313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1010186694757659666152417 757640021068244749614313)
                    ·
                      refine ⟨568230015801183562210735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 757640021068244749614313 568230015801183562210735)
                      ·
                        rfl

theorem cell23_1106624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 2, 1, 1, 5, 2, 2].length) (baseStart_1106624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106624 prefixEnd_1106624 := by exact prefixLift 1106624
  have htrace : WordTrace (prefixWord ++ tailWord_1106624) baseStart_1106624 baseEnd_1106624 := by
    simpa [prefixWord, tailWord_1106624, baseEnd_1106624] using wordTrace_append hprefix tailTrace_1106624
  have hstable : (prefixWord ++ tailWord_1106624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106624).length < 2 ^ (prefixWord ++ tailWord_1106624).sum := by decide
  have hdescent : baseEnd_1106624 < baseStart_1106624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1106640 : List Nat := [2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3]
def baseStart_1106640 : Nat := 118140960795 + 1106640 * 2 ^ 59
def prefixEnd_1106640 : Nat := 4983230072969 + 3 ^ 40 * 1106640 * 2
def baseEnd_1106640 : Nat := 568238231491655499610661

theorem tailTrace_1106640 : CollatzResearch.WordTrace tailWord_1106640 prefixEnd_1106640 568238231491655499610661 := by
  unfold tailWord_1106640
  simp only [CollatzResearch.WordTrace]
  refine ⟨20181238355419876955062687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 26908317807226502606750249 20181238355419876955062687)
  ·
    refine ⟨30271857533129815432594031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20181238355419876955062687 30271857533129815432594031)
    ·
      refine ⟨45407786299694723148891047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30271857533129815432594031 45407786299694723148891047)
      ·
        refine ⟨68111679449542084723336571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45407786299694723148891047 68111679449542084723336571)
        ·
          refine ⟨102167519174313127085004857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 68111679449542084723336571 102167519174313127085004857)
          ·
            refine ⟨76625639380734845313753643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 102167519174313127085004857 76625639380734845313753643)
            ·
              refine ⟨114938459071102267970630465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76625639380734845313753643 114938459071102267970630465)
              ·
                refine ⟨86203844303326700977972849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114938459071102267970630465 86203844303326700977972849)
                ·
                  refine ⟨64652883227495025733479637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 86203844303326700977972849 64652883227495025733479637)
                  ·
                    refine ⟨1515301950644414665628429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 64652883227495025733479637 1515301950644414665628429)
                    ·
                      refine ⟨568238231491655499610661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1515301950644414665628429 568238231491655499610661)
                      ·
                        rfl

theorem cell23_1106640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 7, 3].length) (baseStart_1106640 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1106640 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1106640 prefixEnd_1106640 := by exact prefixLift 1106640
  have htrace : WordTrace (prefixWord ++ tailWord_1106640) baseStart_1106640 baseEnd_1106640 := by
    simpa [prefixWord, tailWord_1106640, baseEnd_1106640] using wordTrace_append hprefix tailTrace_1106640
  have hstable : (prefixWord ++ tailWord_1106640).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1106640).length < 2 ^ (prefixWord ++ tailWord_1106640).sum := by decide
  have hdescent : baseEnd_1106640 < baseStart_1106640 := by decide
  rcases family_descends (prefixWord ++ tailWord_1106640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
